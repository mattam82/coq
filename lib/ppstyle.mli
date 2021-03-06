(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Highlighting of printers. Used for pretty-printing terms that should be
    displayed on a color-capable terminal. *)

(** {5 Style tags} *)

type t = string

(** Style tags *)

val make : ?style:Terminal.style -> string list -> t
(** Create a new tag with the given name. Each name must be unique. The optional
    style is taken as the default one. *)

val repr : t -> string list
(** Gives back the original name of the style tag where each string has been
    concatenated and separated with a dot. *)

val tag : t Pp.Tag.key
(** An annotation for styles *)

(** {5 Manipulating global styles} *)

val get_style : t -> Terminal.style option
(** Get the style associated to a tag. *)

val set_style : t -> Terminal.style option -> unit
(** Set a style associated to a tag. *)

val clear_styles : unit -> unit
(** Clear all styles. *)

val parse_config : string -> unit
(** Add all styles from the given string as parsed by {!Terminal.parse}.
    Unregistered tags are ignored. *)

val dump : unit -> (t * Terminal.style option) list
(** Recover the list of known tags together with their current style. *)

(** {5 Setting color output} *)

val init_color_output : unit -> unit

val color_msg : ?header:string * Format.tag ->
  Format.formatter -> Pp.std_ppcmds -> unit
(** {!color_msg ?header fmt pp} will format according to the tags
     defined in this file *)

val pp_tag : Pp.tag_handler
(** Returns the name of a style tag that is understandable by the formatters
    that have been inititialized through {!init_color_output}. To be used with
    {!Pp.pp_with}. *)

(** {5 Tags} *)

val error_tag : t
(** Tag used by the {!Pp.msg_error} function. *)

val warning_tag : t
(** Tag used by the {!Pp.msg_warning} function. *)

val debug_tag : t
(** Tag used by the {!Pp.msg_debug} function. *)
