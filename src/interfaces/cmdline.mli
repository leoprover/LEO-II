(* ========================================================================= *)
(* Advanced command-line interface                                           *)
(* ========================================================================= *)

(** Module Cmdline implements a command-line interface with line editing functions
   @author Arnaud 
   @since 29-03-07 *)



val interactive : bool ref
val save_tcio : unit -> unit

type filetype = FNone | FDir | FExt of string list
type argtype = AInt | AStr | AFile of filetype
(** See type [arginfo]. *)

type arginfo = {
  argtype : argtype;
  argname : string;
  argrequired : bool;
  arghistcontext : int;
  argstrvalues : string list
}
(** Type of information about a command argument.
    Field [argrequired] indicates whether the argument is required (true) or optional (false).
    Field [arghistcontext] stores the history context that should be used when the argument
    is entered on a separate line.
    Field [argstrvalues] allows to define a list of strings that will be used for tab completion in
    case [argtype] has value [AStr].
    The function [execute_command] will ask the user to supply missing required arguments before calling
    the command function.
    See type [command]. *)

type argdata = IntArg of int | StrArg of string | FileArg of string
(** Type of arguments passed to functions associated to commands.
    See type [command]. *)


type command = string * string * arginfo list * (argdata list -> bool)
(** Type of a command.
    The first component is the name of the command;
    the second component is a description of the command, displayed along with the name
    when more than one command matches;
    the third component describes the arity and types of arguments the command expects,
    used for smart tab completion;
    the last component is the actual function which executes the command. *)
    

val get_int_arg : argdata list -> int * argdata list
(** Pop an integer off the argument list, raises [Failure "get_int_arg"] if first argument is
    not an integer, or the list is empty. *)
    
val get_str_arg : argdata list -> string * argdata list
(** Pop a string off the argument list, raises [Failure "get_string_arg"] if first argument is
    not a string, or the list is empty. *)
     
val get_file_arg : argdata list -> string * argdata list
(** Pop a filename (string) off the argument list, raises [Failure "get_file_arg"] if first argument is
    not a string, or the list is empty. *)


val mkarg : ?required:bool -> ?histcontext:int -> ?strvalues:string list -> argtype -> string -> arginfo
(** [arginfo] constructor.
    Optional argument [required] is [true] by default.
    Optional argument [histcontext] is [-1] by default, i.e. the history function
    is deactivated when missing arguments are entered.
    Optional argument [strvalues] is empty by default. *)


val set_commands : command list -> unit
(** Set the global command list. *)

val add_command : command -> unit
(** Add a command to the global command list. *)

val get_commands : unit -> command list
(** Return the global command list. *)


exception Escape_pressed

val empty_newlines : bool ref
(** Controls whether a newline character is printed when the entered line is empty.
    Default is [true]. *)


val getline : ?expectedtype:argtype option -> ?raise_esc:bool -> ?history_context:int -> ?strvalues:string list -> string -> string
(** [getline ~expectedtype:e ~raise_esc:b prompt] runs the line editor, using [prompt] as prompt;
    the optional argument [expectedtype] can be set to force a specific tab completion behavior,
    e.g. calling with [~expectedtype:(Some AFile)] will try to expand filenames;
    the optional argument [raise_esc], when set to [true], causes [Escape_pressed] to be raised
    when the user presses Esc twice;
    the optional argument [history_context] sets the history context, default context is 0;
    to disable the history function (e.g. for "yes/no" prompts), set [history_context] to [-1].
    The optional argument [strvalues] allows to set the strings that will be used for tab completion;
    tab completion will first consider [expectedtype] to determine possible tab completions,
    then the expected type of the command being typed, and finally [strvalues].    
    When the user presses Enter, the edited line is returned.
    
    Currently implemented features:
     - left/right arrow keys, backspace, home, end
     - history (up/down arrow keys)
     - tab completion *)


val split : char -> string -> string list
(* [split separator s] splits [s] into substrings according to [separator]. *)


exception Bad_command

val execute_command : string -> bool
(* [execute_command s] tries to interpret [s] as a command, optionally followed by arguments.
   The global command list is used to infer the expected argument types, convert them to
   a [argdata list] and call the associated function.
   If arguments are missing in [s], the user is prompted to enter them.
   The return value is the return value of the command function, unless the user has aborted
   argument input (then [true] is returned), or an error has occured during argument conversion
   (then [false] is returned).
   If no matching command is found in the global command list, then [Bad_command] is raised. *)

