(***********************************************************************)
(*                                                                     *)
(*  OCaml library from the book ``Apprendre à programmer avec OCaml''  *)
(*                                                                     *)
(*  Sylvain Conchon and Jean-Christophe Filliâtre                      *)
(*  Université Paris Sud                                               *)
(*                                                                     *)
(*  Copyright 2014 Université Paris Sud.  All rights reserved. This    *)
(*  file is distributed under the terms of the GNU Library General     *)
(*  Public License, with the same special exception on linking as the  *)
(*  OCaml library. See http://caml.inria.fr/ocaml/license.fr.html      *)
(*                                                                     *)
(***********************************************************************)

type 'a zipper = { left: 'a list; right: 'a list; }
  
val empty: 'a zipper

val of_list: 'a list -> 'a zipper
    
val move_right: 'a zipper -> 'a zipper
      
val move_left: 'a zipper -> 'a zipper
      
val to_list: 'a zipper -> 'a list
      
val insert: 'a zipper -> 'a -> 'a zipper
    
val delete_left: 'a zipper -> 'a zipper
    
val delete_right: 'a zipper -> 'a zipper

val get_left: 'a zipper -> 'a

val get_right: 'a zipper -> 'a

val reset_left: 'a zipper -> 'a zipper

val reset_right: 'a zipper -> 'a zipper

val iter: ('a -> unit) -> 'a zipper -> unit
(*
val exists_right: ('a -> bool) -> 'a zipper -> bool

val exists_left: ('a -> bool) -> 'a zipper -> bool
*)
