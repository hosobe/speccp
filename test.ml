(*
  The running example used in the accompanying paper.
*)

open SpecCp

let days = [1; 2; 3]

let mas =
  let as_r =
    Agent_spec
      ([Default
	(1, ("av", [Typed_variable ("D", days)]), Internal_agent "a",
	([Variable "D"], (function [d] -> true | _ -> false), "$0:{1,2,3}"));
      Default
	(2, ("av", [Typed_variable ("D", days)]), Internal_agent "b",
	([Variable "D"], (function [d] -> true | _ -> false), "$0:{1,2,3}"))],
      [Rule
	(("rsv", [Variable "R"; Variable "L"; Typed_variable ("D", days)]),
	[Equality (Variable "R", Symbol "tr");
	Equality (Variable "L", Pair (Symbol "a", Pair (Symbol "b", Nil)))],
	[Askable (("av", [Variable "D"]), Internal_agent "a");
	Askable (("av", [Variable "D"]), Internal_agent "b")]);
      Rule
	(("rsv", [Variable "R"; Variable "L"; Typed_variable ("D", days)]),
	[Equality (Variable "R", Symbol "sr");
	Equality (Variable "L", Pair (Symbol "a", Nil))],
	[Askable (("av", [Variable "D"]), Internal_agent "a");
	Askable (("unav", [Variable "D"]), Internal_agent "b")]);
      Rule
	(("rsv", [Variable "R"; Variable "L"; Typed_variable ("D", days)]),
	[Equality (Variable "R", Symbol "sr");
	Equality (Variable "L", Pair (Symbol "b", Nil))],
	[Askable (("unav", [Variable "D"]), Internal_agent "a");
	Askable (("av", [Variable "D"]), Internal_agent "b")])]) in
  let as_a =
    Agent_spec
      ([Default
	(1, ("fr", [Typed_variable ("D", days)]), External_agent "a1",
	([Variable "D"], (function [d] -> d = 1 || d = 2 | _ -> false), "$0:{1,2}"));
      Default
	(2, ("bs", [Typed_variable ("D", days)]), External_agent "a1",
	([Variable "D"], (function [d] -> d = 3 | _ -> false), "$0:{3}"))],
      [Rule
	(("av", [Typed_variable ("D", days)]),
	[],
	[Askable (("fr", [Variable "D"]), External_agent "a1")]);
      Rule
	(("unav", [Typed_variable ("D", days)]),
	[],
	[Askable (("bs", [Variable "D"]), External_agent "a1")])]) in
  let as_b =
    Agent_spec
      ([Default
	(1, ("fr", [Typed_variable ("D", days)]), External_agent "b1",
	([Variable "D"], (function [d] -> d = 2 | _ -> false), "$0:{2}"))],
      [Rule
	(("av", [Typed_variable ("D", days)]),
	[],
	[Askable (("fr", [Variable "D"]), External_agent "b1")]);
      Rule
	(("unav", [Typed_variable ("D", days)]),
	[],
	[Askable (("bs", [Variable "D"]), External_agent "b1")])]) in
  Multiagent_system
    ([(Internal_agent "r", as_r); (Internal_agent "a", as_a);
    (Internal_agent "b", as_b)],
    [External_agent "a1"; External_agent "b1"])

(* The current implementation needs external agents' answers to be
   prepared beforehand. *)
let eaq =
  register_external_answers
    (("fr", [Typed_variable ("D", days)])) (External_agent "b1")
    [1, ([Variable "D"], (function [d] -> d = 2 || d = 3 | _ -> false), "$0:{2,3}")]
    []

let () =
  let goal = Askable (("rsv", [Variable "R"; Variable "L"; Typed_variable ("D", days)]), Internal_agent "r") in
  let s0 = create_initial_agent_states mas in
  let s1 = send_query Root_caller goal s0 in
  print_answers_and_labeled_processes (Internal_agent "r") s1;
  print_newline ();
  read_eval_print mas eaq s1 []
