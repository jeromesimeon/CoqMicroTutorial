
(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val double : int -> int **)

let double n =
  mul n (Pervasives.succ (Pervasives.succ 0))

(** val sum : int list -> int **)

let rec sum = function
| [] -> 0
| x :: l1 -> add x (sum l1)

(** val f1 : int list -> int **)

let f1 l =
  sum (map double l)

(** val f2 : int list -> int **)

let f2 l =
  double (sum l)
