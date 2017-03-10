exception NotFound

type 'e rel = 'e -> 'e list
type 'e prop = 'e -> bool

type ('a, 'set) set_operations = {
  empty : 'set;              (* The empty set. *)
  mem : 'a -> 'set -> bool;  (* [mem x s = true] iff [x] is in [s]. *)
  add : 'a -> 'set -> 'set;  (* [add s x] is the set [s] union {x}. *)
}

type ('configuration, 'move) puzzle = {
  move : 'configuration -> 'move -> 'configuration;
  possible_moves : 'configuration -> 'move list;
  final : 'configuration -> bool
}

type piece_kind = S | H | V | C | X
type piece = piece_kind * int
let x = (X, 0) and s = (S, 0) and h = (H, 0)
let (c0, c1, c2, c3) = ((C, 0), (C, 1), (C, 2), (C, 3))
let (v0, v1, v2, v3) = ((V, 0), (V, 1), (V, 2), (V, 3))
let all_pieces : piece list = [ s; h; c0; c1; c2; c3; v0; v1; v2; v3 ]

type board = piece array array
let initial_board =
  [| [| v0 ; s  ; s  ; v1 |];
     [| v0 ; s  ; s  ; v1 |];
     [| v2 ; h  ; h  ; v3 |];
     [| v2 ; c0 ; c1 ; v3 |];
     [| c2 ; x  ; x  ; c3 |] |]

let initial_board_simpler =
  [| [| c2 ; s  ; s  ; c1 |] ;
     [| c0 ; s  ; s  ; c3 |] ;
     [| v1 ; v2 ; v3 ; v0 |] ;
     [| v1 ; v2 ; v3 ; v0 |] ;
     [| x  ; x  ; x  ; x  |] |]

let initial_board_trivial =
  [| [| x  ; s  ; s  ; x  |] ;
     [| x  ; s  ; s  ; x  |] ;
     [| x  ; x  ; x  ; x  |] ;
     [| x  ; x  ; x  ; x  |] ;
     [| x  ; x  ; x  ; x  |] |]

type direction = { dcol : int; drow : int; }
type move = Move of piece * direction * board
let move _ (Move (_, _, b)) = b

(* ----------------------------------------------------------- *)

let iota i e =
  let rec lewp j l =
    if j <= e then
      j :: lewp (1 + j) l
    else
      l
  in lewp i []

(* 1 *)
let rec loop p f x =
  if p x then x else loop p f (f x)

(* 2 *)
let rec exists p = function
  | [] -> false
  | x :: _ when p x -> true
  | _ :: xs -> exists p xs

(* 3 *)
let rec find p = function
  | [] -> raise NotFound
  | x :: _ when p x -> x
  | _ :: xs -> find p xs

(* --- Part A: A Generic Problem Solver --- *)

(* 4 *)
let near x =
  let c = ref  0 and l = ref [] and m = x + 2 in
  while !c < 5 do l := (m - !c) :: !l; incr c done;
  !l

(* 5 *)
let rec flat_map (r : 'e rel) : 'e list -> 'e list = function
  | [] -> []
  | x :: xs -> r x @ flat_map r xs

(* 6 *)
let rec iter_rel (rel : 'e rel) (n : int) : 'e rel =
  if n > 0 then
    function x -> flat_map rel ((iter_rel rel (n - 1)) x)
  else
    function x -> [x] 		(* iter_rel rel 0 = id 0 *)

(* 7 *)
let solve r p x =
  loop (exists p) (flat_map r) [x] |> find p

(* 8 *)
let solve_path r p x =
  (* r: next steps... over all previous boards
        List.rev [[0] ; (near 0) ; (flat_map near) (near 0); (flat_map near) ((flat_map near) (near 0))] ;;
     p: is solution?... over all current boards (union of paths)
     x: initial state... is now [inital state] *)
  let r_path next cur = List.map (fun intermediate_step -> intermediate_step :: cur) (next (List.hd cur))
  (* First, we compute the list of next possible RELATIONS (not boards) via next.
     Then,  we build up a path on the next boards for each possible next starting point:
     r_path near [0] = [[-2; 0]; [-1; 0]; [0; 0]; [1; 0]; [2; 0]]
     flat_map (r_path near) (r_path near [0]);;
     - : int list list =
     [[-4; -2; 0]; [-3; -2; 0]; [-2; -2; 0]; [-1; -2; 0]; [0; -2; 0]; [-3; -1; 0];
      [-2; -1; 0]; [-1; -1; 0]; [0; -1; 0]; [1; -1; 0]; [-2; 0; 0]; [-1; 0; 0];
      [0; 0; 0]; [1; 0; 0]; [2; 0; 0]; [-1; 1; 0]; [0; 1; 0]; [1; 1; 0];
      [2; 1; 0]; [3; 1; 0]; [0; 2; 0]; [1; 2; 0]; [2; 2; 0]; [3; 2; 0]; [4; 2; 0]]
 *)
  and p_path soln cur = soln (List.hd cur) in
  (* Does the path of relations e1...en s.t. Z R e1 R e2 ... eN R Y to this board contain the solution Y?
     Then this path is valid. *)
  solve (r_path r) (p_path p) [x] |> List.rev
  (* This takes the last step in every board and computes the next:
     0 R 2 -> [... 0 1 2 ]
     2 R 4 -> [... 4 5 6 ]
     4 R 6 -> [... 6 7 8 ] ... 0 R 12 via e_0 ... e_n = 0, 2, ... 12 *)

(* 9 *)
let archive_map opset (r : 'a rel) ((s, l) : 'set * 'a list) =
  (* Build l' and s' in parallel to avoid stack overflow *)
  (* Be sure to avoid duplicates *)
  List.fold_left (fun (s'', l'') n ->
      if not (opset.mem n s'') then
        opset.add n s'', n :: l''
      else
        s'', l'') (s, []) ((flat_map r) l)

(* 10 *)
let solve' opset r p x =
  let p' = function (_  , cur) -> exists p cur
  and r' = function (arc, cur) -> archive_map opset r (arc, cur)
  and x' = (opset.empty, [x]) in
  loop p' r' x' |> function (_, cur) -> find p cur

(* x 11 *)
let solve_path' opset r p x =
  List.(rev @@ solve' opset
		      (function l -> map (function a -> a::l)(r (hd l)))
		      (function l -> p (hd l)) [x])

(* 12 *)
let solve_puzzle p opset c =
  let nxt_confs (conf : 'c) : 'c list =
    List.map (fun m -> p.move conf m) (p.possible_moves conf)
  in solve_path' opset nxt_confs p.final c

(* --- Part B: A Solver for Klotski --- *)

(* 13 *)
let final board =
  let sq = [(3, 1);(3,2);(4,1);(4,2)] in
  List.fold_left (fun accu (i, j) -> accu && S = fst board.(i).(j)) true sq

let move_piece board piece { drow; dcol } =
  let size = function X -> 1, 1
                    | V -> 2, 1 | H -> 1, 2
                    | C -> 1, 1 | S -> 2, 2 in
  let rows = Array.length board
  and cols = Array.length board.(0) in
  let rec iterate b (i, j) (io, jo) (mi, mj) f =
    match i, j with
    | i, _ when i >= mi -> (-1, -1)
    | i, j when j >= mj -> iterate b (1 + i, jo) (io, jo) (mi, mj) f
    | _ ->
        if f b.(i).(j) then i, j
        else iterate b (i, 1 + j) (io, jo) (mi, mj) f
  in
  (* Search the piece *)
  let r, c = iterate board (0, 0) (0, 0) (rows, cols) ((=) piece)
  and h, w = size @@ fst piece
  and (--) i j = let rec aux n acc =
                   if n < i then acc else aux (n - 1) (n :: acc)
    in aux (j - 1) []
  in
  let r_range, c_range = (r -- (r + h), c -- (c + w)) in
  let fill, erase = match drow, dcol with
    | -1,  _ -> (List.map (fun c' -> r - 1    , c'       ) c_range
                ,List.map (fun c' -> r + h - 1, c'       ) c_range)
    |  1,  _ -> (List.map (fun c' -> r + h    , c'       ) c_range
                ,List.map (fun c' -> r        , c'       ) c_range)
    |  _, -1 -> (List.map (fun r' -> r'       , c - 1    ) r_range
                ,List.map (fun r' -> r'       , c + w - 1) r_range)
    |  _,  1 -> (List.map (fun r' -> r'       , c + w    ) r_range
                ,List.map (fun r' -> r'       , c        ) r_range)
  in
  let is_occupied = List.fold_left (fun p (i, j) -> p
                                                    || i >= rows || j >= cols
                                                    || i <  0    || j <  0
                                                    || (X, 0) <> board.(i).(j)) false fill
  in
  if is_occupied then None
  else (* Draw the new board state *)
    let matrix_copy m =
      let outer = Array.copy m
      and n  = Array.length m - 1 in
      for i = 0 to n do
        outer.(i) <- Array.copy m.(i)
      done;
      outer
    in
    let board' = matrix_copy board in
    begin
      List.map (function (i, j) -> board'.(i).(j) <- X, 0) erase;
      List.map (function (i, j) -> board'.(i).(j) <- piece) fill;
      Some board'
    end

(*15*)
let possible_moves board =
  let dirs = [(-1,  0) ; ( 0, -1) ; ( 1,  0) ; ( 0,  1)] in
  let gen_moves piece =
    List.fold_right (fun (dx, dy) accu ->
        let dir = {drow = dx; dcol = dy} in
        match move_piece board piece dir
        with None -> accu
           | Some board' -> (Move (piece, dir, board')) :: accu) dirs []
  in List.(map gen_moves all_pieces |> flatten)

module BoardSet = Set.Make (struct
    type t = board
    let compare (b1 : board) (b2 : board) =
      let compare_piece (v1, i1) (v2, i2) =
        let ord = [ X,0 ; V,1 ; C,2 ; H,3 ; S,4 ] in
        let a1 = List.assoc v1 ord
        and a2 = List.assoc v2 ord in
        if a1 > a2 then 1 else if a1 < a2 then -1
        else compare i1 i2
      in
      let cmp = ref 0 in
      try
        begin
          for r = 0 to 4 do
            let row1 = b1.(r) and row2 = b2.(r) in
            for c = 0 to 3 do
              begin
                cmp := compare_piece row1.(c) row2.(c);
                if 0 <> !cmp then raise NotFound
              end
            done
          done;
          0
        end
      with _ -> !cmp
  end)

let solve_klotski initial_board  =
  let klotski = { move ; possible_moves ; final }
  and opset = { empty = BoardSet.empty
              ; mem = (fun l s -> BoardSet.mem (List.hd l) s)
              ; add = (fun l s -> BoardSet.add (List.hd l) s) }
  in solve_puzzle klotski opset initial_board
