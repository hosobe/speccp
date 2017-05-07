(*
  SpecCp: Speculative Constraint Processing for Multi-Agent Systems
  Copyright (C) 2009-2010 Hiroshi HOSOBE
*)

(**
   SpecCp is an implementation of speculative constraint processing
   for multi-agent systems.
*)

(**
   Multi-agent systems
*)

type agent =
    Root_caller
  | Internal_agent of string
  | External_agent of string

type term =
    Variable of string
  | Typed_variable of string * int list
  | Integer of int
  | Symbol of string
  | Compound of string * term list
  | Nil
  | Pair of term * term

type pre_atom =
    string * term list

type atom =
    Nonaskable of pre_atom
  | Askable of pre_atom * agent

type fd_constr =
    term list * (int list -> bool) * string

type constr =
    Equality of term * term
  | Fd of fd_constr

type default =
    Default of int * pre_atom * agent * fd_constr

type rule =
    Rule of pre_atom * constr list * atom list

type agent_spec =
    Agent_spec of default list * rule list

type multiagent_system =
    Multiagent_system of
      (agent * agent_spec) list (* Internal agents *)
      * agent list (* External agents *)

(**
   Agent states
*)

type binding =
    string * term

type domain =
    string * (int list)

type answer_id =
    Speculative_original_answer
  | Nonspeculative_original_answer
  | Default_answer of int
  | Ordinary_answer of int

type answer =
    {a_pre_atom: pre_atom;
    a_agent: agent;
    a_id: answer_id;
    a_bindings: binding list;
    a_fd_constr: fd_constr;
    a_process_ids: int list}

type labeled_answer =
    New_answer of answer (* First or alternative answer *)
  | Revised_answer of answer * answer_id

type labeled_atom =
    pre_atom * agent * answer_id

type process =
    {p_id: int;
    p_bindings: binding list;
    p_domains: domain list;
    p_fd_constrs: fd_constr list;
    p_goal: atom list;
    p_awaited_atoms: labeled_atom list;
    p_assumed_atoms: labeled_atom list;
    p_initial_goal: pre_atom;
    p_initial_goal_sender: agent}

type labeled_process =
    Ordinary_process of process
  | Finished_process of process

type agent_state =
    {s_agent: agent;
    s_answers: answer list;
    s_labeled_processes: labeled_process list;
    s_next_process_id: int;
    s_next_answer_application_id: int}

(**
   Bit arrays
*)

type bit_array =
    {ba_length: int;
    ba_data: (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout)
      Bigarray.Array1.t}

let create_bit_array (length: int):
    bit_array =
  let actual_length =
    if length mod 8 = 0
    then length / 8
    else length / 8 + 1 in
  let bit_array =
    {ba_length = length;
    ba_data = Bigarray.Array1.create Bigarray.int8_unsigned
	Bigarray.c_layout actual_length} in
  Bigarray.Array1.fill bit_array.ba_data 0;
  bit_array

let get_bit_array_length (bit_array: bit_array):
    int =
  bit_array.ba_length

let get_bit_array_value (bit_array: bit_array) (index: int):
    bool =
  let actual_index = index / 8 in
  let actual_subindex = index mod 8 in
  let byte = Bigarray.Array1.get bit_array.ba_data actual_index in
  let bit = (byte lsr actual_subindex) land 1 in
  bit = 1

let set_bit_array_value (bit_array: bit_array) (index: int)
    (value: bool):
    unit =
  let actual_index = index / 8 in
  let actual_subindex = index mod 8 in
  let old_byte = Bigarray.Array1.get bit_array.ba_data actual_index in
  let bit = 1 lsl actual_subindex in
  let new_byte =
    if value
    then old_byte lor bit
    else old_byte land (bit lxor 0xff) in
  Bigarray.Array1.set bit_array.ba_data actual_index new_byte

type md_bit_array =
    {mba_dimensions: int list;
    mba_array: bit_array}

let create_md_bit_array (dimensions: int list):
    md_bit_array =
  let actual_length =
    List.fold_left (fun product multiplier -> product * multiplier)
      1 dimensions in
  {mba_dimensions = dimensions;
  mba_array = create_bit_array actual_length}

let get_md_bit_array_dimensions (md_bit_array: md_bit_array):
    int list =
  md_bit_array.mba_dimensions

let get_md_bit_array_actual_index (md_bit_array: md_bit_array)
    (indices: int list):
    int =
  List.fold_left2
    (fun actual_index dimension index ->
      actual_index * dimension + index)
    0 md_bit_array.mba_dimensions indices

let get_md_bit_array_value (md_bit_array: md_bit_array)
    (indices: int list):
    bool =
  get_bit_array_value md_bit_array.mba_array
    (get_md_bit_array_actual_index md_bit_array indices)

let set_md_bit_array_value (md_bit_array: md_bit_array)
    (indices: int list) (value: bool):
    unit =
  set_bit_array_value md_bit_array.mba_array
    (get_md_bit_array_actual_index md_bit_array indices) value

(**
   Utility functions
*)

(** Lists *)

let is_element_included (element: 'a) (list: 'a list):
    bool =
  List.exists (fun current_element -> current_element = element) list

let get_element_index (element: 'a) (list: 'a list):
    int =
  let rec iterate index =
    function
      [] ->
	raise Not_found
    | current_element :: rest_elements ->
	if current_element = element
	then index
	else iterate (index + 1) rest_elements in
  iterate 0 list

let rec remove_element (element: 'a) (list: 'a list):
    'a list =
  match list with
    [] ->
      raise Not_found
  | current_element :: rest_elements ->
      if current_element = element
      then rest_elements
      else current_element :: (remove_element element rest_elements)

let rec remove_last_element (list: 'a list):
    'a * 'a list =
  match list with
    element :: rest_elements ->
      if rest_elements = []
      then (element, [])
      else
	let last_element, updated_rest_elements =
	  remove_last_element rest_elements in
	(last_element, element :: updated_rest_elements)
  | [] ->
      raise (Invalid_argument "remove_last_element")

let flat_map (func: 'a -> 'b list) (list: 'a list):
    'b list =
  List.fold_right (fun element result -> (func element) @ result)
    list []

let string_of_list (string_of_element: 'a -> string)
    (separator: string) (list: 'a list):
    string =
  List.fold_left
    (fun string element ->
      if string = ""
      then string_of_element element
      else string ^ separator ^ (string_of_element element))
    "" list

(** Agents *)

let get_agent_name (agent: agent):
    string =
  match agent with
    Root_caller ->
      raise (Invalid_argument "get_agent_name")
  | Internal_agent name | External_agent name ->
      name

(** Variables *)

let get_variable_name (variable: term):
    string =
  match variable with
    Variable name | Typed_variable (name, _) ->
      name
  | _ ->
      raise (Invalid_argument "get_variable_name")

let get_variable_index (variable_name_to_index: string)
    (variables: term list):
    int =
  let rec iterate index =
    function
      [] ->
	raise Not_found
    | variable :: rest_variables ->
	if (get_variable_name variable) = variable_name_to_index
	then index
	else iterate (index + 1) rest_variables in
  iterate 0 variables

(** Compound terms *)

let get_compound_term_functor (compound: term):
    string =
  match compound with
    Compound (ftr, _) ->
      ftr
  | _ ->
      raise (Invalid_argument "get_compound_term_functor")

let get_compound_term_arity (compound: term):
    int =
  match compound with
    Compound (_, arguments) ->
      List.length arguments
  | _ ->
      raise (Invalid_argument "get_compound_term_arity")

(** Pre-atoms *)

let get_pre_atom_predicate (pre_atom: pre_atom):
    string =
  let predicate, _ = pre_atom in
  predicate

let get_pre_atom_arity (pre_atom: pre_atom):
    int =
  let _, arguments = pre_atom in
  List.length arguments

let is_pre_atom_equal (pre_atom1: pre_atom) (pre_atom2: pre_atom):
    bool =
  ((get_pre_atom_predicate pre_atom1)
  = (get_pre_atom_predicate pre_atom2))
  && ((get_pre_atom_arity pre_atom1) = (get_pre_atom_arity pre_atom2))

let get_argument_variables_from_pre_atom (pre_atom: pre_atom):
    term list =
  let _, variables = pre_atom in
  List.map
    (fun variable ->
      match variable with
	Variable _ | Typed_variable _ ->
	  variable
      | _ ->
	  raise
	    (Invalid_argument "get_argument_variables_from_pre_atom"))
    variables

let get_typed_argument_variables_from_pre_atom (pre_atom: pre_atom)
    (domains: domain list):
    term list =
  let _, variables = pre_atom in
  List.fold_right
    (fun variable typed_variables ->
      match variable with
	Typed_variable _ ->
	  variable :: typed_variables
      | Variable name ->
	  (try
	    (Typed_variable (name, List.assoc name domains))
	    :: typed_variables
	  with Not_found ->
	    typed_variables)
      | _ ->
	  raise
	    (Invalid_argument
	      "get_typed_argument_variables_from_pre_atom"))
    variables []

(** Finite-domain constraints *)

let create_true_fd_constraint (variables: term list):
    fd_constr =
  (variables,
  (fun _ -> raise (Failure "Dummy constraint evaluated.")), "true")

let create_false_fd_constraint (variables: term list):
    fd_constr =
  (variables,
  (fun _ -> raise (Failure "Dummy constraint evaluated.")), "false")

let get_fd_constraint_arity (fd_constr: fd_constr):
    int =
  let variables, _, _ = fd_constr in
  List.length variables

let get_variables_from_fd_constraint (fd_constr: fd_constr):
    term list =
  let variables, _, _ = fd_constr in
  variables

let is_fd_constraint_satisfied (fd_constr: fd_constr)
    (values: int list):
    bool =
  let _, func, _ = fd_constr in
  func values

let negate_fd_constraint (fd_constr: fd_constr):
    fd_constr =
  let variables, func, expression = fd_constr in
  (variables, (fun values -> not (func values)), "not " ^ expression)

(** Constraints *)

let split_constraints (constrs: constr list):
    (term * term) list * fd_constr list =
  List.fold_left
    (fun (equality_constrs, fd_constrs) ->
      function
	Equality (lhs, rhs) ->
	  ((lhs, rhs) :: equality_constrs, fd_constrs)
      | Fd fd_constr ->
	  (equality_constrs, fd_constr :: fd_constrs))
    ([], []) constrs

(** Agent specifications *)

let get_defaults_on_askable_atom (pre_atom: pre_atom) (agent: agent)
    (spec: agent_spec):
    default list =
  let Agent_spec (defaults, _) = spec in
  List.filter
    (fun (Default (_, head, default_agent, _)) ->
      (default_agent = agent) && (is_pre_atom_equal head pre_atom))
    defaults

let get_rules_on_pre_atom (pre_atom: pre_atom) (spec: agent_spec):
    rule list =
  let Agent_spec (_, rules) = spec in
  List.filter
    (fun (Rule (head, _, _)) -> is_pre_atom_equal head pre_atom)
    rules

let get_all_askable_atoms (spec: agent_spec):
    (pre_atom * agent) list =
  let Agent_spec (_, rules) = spec in
  List.rev
    (List.fold_left
      (fun askable_atoms rule ->
	let Rule (_, _, body) = rule in
	List.fold_left
	  (fun askable_atoms atom ->
	    match atom with
	      Askable (pre_atom, agent) ->
		if is_element_included (pre_atom, agent) askable_atoms
		then askable_atoms
		else (pre_atom, agent) :: askable_atoms
	    | Nonaskable _ ->
		askable_atoms)
	  askable_atoms body)
      [] rules)

(** Multi-agent systems *)

let get_agent_spec (agent: agent) (system: multiagent_system):
    agent_spec =
  let Multiagent_system (specs, _) = system in
  List.assoc agent specs

let is_internal_agent (agent_name: string)
    (system: multiagent_system):
    bool =
  let Multiagent_system (specs, _) = system in
  List.exists (fun (agent, _) -> (get_agent_name agent) = agent_name)
    specs

(** Domains *)

let rec get_domains_from_term (term: term):
    domain list =
  match term with
    Typed_variable (name, values) ->
      [name, values]
  | Compound (_, arguments) ->
      flat_map get_domains_from_term arguments
  | Pair (argument1, argument2) ->
      (get_domains_from_term argument2)
      @ (get_domains_from_term argument1)
  | _ ->
      []

let get_domains_from_pre_atom (pre_atom: pre_atom):
    domain list =
  let _, arguments = pre_atom in
  flat_map get_domains_from_term arguments

let get_domains_from_atom (atom: atom):
    domain list =
  match atom with
    Nonaskable pre_atom | Askable (pre_atom, _) ->
      get_domains_from_pre_atom pre_atom

let get_domains_from_fd_constraint (fd_constr: fd_constr):
    domain list =
  let variables, _, _ = fd_constr in
  flat_map get_domains_from_term variables

let get_domains_from_constraint (constr: constr):
    domain list =
  match constr with
    Equality (lhs, rhs) ->
      (get_domains_from_term rhs) @ (get_domains_from_term lhs)
  | Fd fd_constr ->
      get_domains_from_fd_constraint fd_constr

(** Labeled atoms *)

let is_answer_included (answer: answer)
    (labeled_atoms: labeled_atom list):
    bool =
  List.exists
    (fun (pre_atom, agent, answer_id) ->
      (agent = answer.a_agent)
      && (is_pre_atom_equal pre_atom answer.a_pre_atom)
      && (answer_id = answer.a_id))
    labeled_atoms

let rec get_askable_atom (answer_id: answer_id)
    (labeled_atoms: labeled_atom list):
    pre_atom * agent =
  match labeled_atoms with
    [] ->
      raise Not_found
  | (pre_atom, agent, id) :: rest_labeled_atoms ->
      if id = answer_id
      then (pre_atom, agent)
      else get_askable_atom answer_id rest_labeled_atoms

let rec remove_labeled_atom (answer_id: answer_id)
    (labeled_atoms: labeled_atom list):
    pre_atom * agent * labeled_atom list =
  match labeled_atoms with
    [] ->
      raise Not_found
  | labeled_atom :: rest_labeled_atoms ->
      let pre_atom, agent, id = labeled_atom in
      if id = answer_id
      then (pre_atom, agent, rest_labeled_atoms)
      else
	let removed_pre_atom, removed_agent,
	  updated_rest_labeled_atoms =
	  remove_labeled_atom answer_id rest_labeled_atoms in
	(removed_pre_atom, removed_agent,
	labeled_atom :: updated_rest_labeled_atoms)

let rec replace_labeled_atom (original_answer_id: answer_id)
    (new_answer_id: answer_id) (labeled_atoms: labeled_atom list):
    labeled_atom list =
  match labeled_atoms with
    [] ->
      raise Not_found
  | labeled_atom :: rest_labeled_atoms ->
      let pre_atom, agent, answer_id = labeled_atom in
      if answer_id = original_answer_id
      then (pre_atom, agent, new_answer_id) :: rest_labeled_atoms
      else labeled_atom
	:: (replace_labeled_atom original_answer_id new_answer_id
	  rest_labeled_atoms)

(** Answers *)

let get_answer (answer_id: answer_id) (answers: answer list):
    answer =
  List.find (fun answer -> answer.a_id = answer_id) answers

let rec replace_answer (original_answer_id: answer_id)
    (new_answer: answer) (answers: answer list):
    answer list =
  match answers with
    [] ->
      raise Not_found
  | answer :: rest_answers ->
      if (answer.a_agent = new_answer.a_agent)
	&& (is_pre_atom_equal answer.a_pre_atom new_answer.a_pre_atom)
	&& (answer.a_id = original_answer_id)
      then new_answer :: rest_answers
      else answer
	:: (replace_answer original_answer_id new_answer rest_answers)

let get_answers_on_askable_atom (pre_atom: pre_atom) (agent: agent)
    (answers: answer list):
    answer list * answer list * answer list =
  List.fold_right
    (fun answer (o_answers, d_answers, p_answers) ->
      if (answer.a_agent = agent)
	&& (is_pre_atom_equal answer.a_pre_atom pre_atom)
      then
	match answer.a_id with
	  Speculative_original_answer
	| Nonspeculative_original_answer ->
	    (answer :: o_answers, d_answers, p_answers)
	| Default_answer _ ->
	    (o_answers, answer :: d_answers, p_answers)
	| Ordinary_answer _ ->
	    (o_answers, d_answers, answer :: p_answers)
      else (o_answers, d_answers, p_answers))
    answers ([], [], [])

let replace_process_ids_in_assumed_answers (new_process_ids: int list)
    (original_process: process) (answers: answer list):
    answer list =
  List.map
    (fun answer ->
      if is_answer_included answer original_process.p_assumed_atoms
      then {answer with
	a_process_ids = new_process_ids
	  @ (remove_element original_process.p_id
	    answer.a_process_ids)}
      else answer)
    answers

let add_process_ids_to_assumed_answers (new_process_ids: int list)
    (original_process: process) (answers: answer list):
    answer list =
  List.map
    (fun answer ->
      if is_answer_included answer original_process.p_assumed_atoms
      then {answer with
	a_process_ids = new_process_ids @ answer.a_process_ids}
      else answer)
    answers

let add_process_ids_to_answers_with_exception
    (new_process_ids: int list) (original_process: process)
    (exceptional_answer: answer) (answers: answer list):
    answer list =
  List.map
    (fun answer ->
      if (answer.a_id <> exceptional_answer.a_id)
	&& ((is_answer_included answer
	  original_process.p_awaited_atoms)
	|| (is_answer_included answer
	  original_process.p_assumed_atoms))
      then {answer with
	a_process_ids = new_process_ids @ answer.a_process_ids}
      else answer)
    answers

(** Labeled answers *)

let get_unlabeled_answer (labeled_answer: labeled_answer):
    answer =
  match labeled_answer with
    New_answer answer | Revised_answer (answer, _) ->
      answer

(** Labeled processes *)

let get_unlabeled_process (labeled_process: labeled_process):
    process =
  match labeled_process with
    Ordinary_process process | Finished_process process ->
      process

let get_labeled_process (process_id: int)
    (labeled_processes: labeled_process list):
    labeled_process =
  List.find
    (fun labeled_process ->
      (get_unlabeled_process labeled_process).p_id = process_id)
    labeled_processes

let rec remove_labeled_process (process_id: int)
    (labeled_processes: labeled_process list):
    labeled_process list =
  match labeled_processes with
    [] ->
      raise Not_found
  | labeled_process :: rest_labeled_processes ->
      if (get_unlabeled_process labeled_process).p_id = process_id
      then rest_labeled_processes
      else labeled_process
	:: (remove_labeled_process process_id rest_labeled_processes)

let rec replace_labeled_process
    (revised_labeled_process: labeled_process)
    (labeled_processes: labeled_process list):
    labeled_process list =
  match labeled_processes with
    [] ->
      raise Not_found
  | labeled_process :: rest_labeled_processes ->
      if (get_unlabeled_process labeled_process).p_id
	= (get_unlabeled_process revised_labeled_process).p_id
      then revised_labeled_process :: rest_labeled_processes
      else labeled_process
	:: (replace_labeled_process revised_labeled_process
	  rest_labeled_processes)

let split_labeled_processes (labeled_processes: labeled_process list):
    process list * process list =
  List.fold_right
    (fun labeled_process (o_processes, f_processes) ->
      match labeled_process with
	Ordinary_process process ->
	  (process :: o_processes, f_processes)
      | Finished_process process ->
	  (o_processes, process :: f_processes))
    labeled_processes ([], [])

(** Agent states *)

let get_agent_state (agent: agent) (states: agent_state list):
    agent_state =
  List.find (fun state -> state.s_agent = agent) states

let rec replace_agent_state (revised_state: agent_state)
    (states: agent_state list):
    agent_state list =
  match states with
    [] ->
      raise Not_found
  | state :: rest_states ->
      if state.s_agent = revised_state.s_agent
      then revised_state :: rest_states
      else state :: (replace_agent_state revised_state rest_states)

(**
   Pretty-printing
*)

let string_of_agent (agent: agent):
    string =
  match agent with
    Root_caller ->
      "Root_caller"
  | Internal_agent name | External_agent name ->
      name

let rec is_list_term (term: term):
    bool =
  match term with
    Nil ->
      true
  | Pair (_, argument2) ->
      is_list_term argument2
  | _ ->
      false

let rec string_of_list_term (term: term):
    string =
  let rec iterate string =
    function
      Nil ->
	string
    | Pair (argument1, argument2) ->
	let new_string =
	  if string = ""
	  then string_of_term argument1
	  else string ^ "," ^ (string_of_term argument1) in
	iterate new_string argument2
    | _ ->
	raise (Failure "string_of_list_term") in
  iterate "" term

and string_of_term (term: term):
    string =
  match term with
    Variable name | Typed_variable (name, _) ->
      name
  | Integer value ->
      string_of_int value
  | Symbol value ->
      value
  | Compound (ftr, arguments) ->
      ftr ^ "(" ^ (string_of_list string_of_term "," arguments) ^ ")"
  | Nil ->
      "[]"
  | Pair (argument1, argument2) ->
      if is_list_term term
      then "[" ^ (string_of_list_term term) ^ "]"
      else ".(" ^ (string_of_term argument1) ^ ","
	^ (string_of_term argument2) ^ ")"

let string_of_pre_atom (pre_atom: pre_atom):
    string =
  let predicate, arguments = pre_atom in
  predicate ^ "("
  ^ (string_of_list string_of_term "," arguments) ^ ")"

let string_of_atom (atom: atom):
    string =
  match atom with
    Nonaskable pre_atom ->
      string_of_pre_atom pre_atom
  | Askable (pre_atom, agent) ->
      (string_of_pre_atom pre_atom) ^ "@" ^ (string_of_agent agent)

let string_of_fd_constraint (fd_constr: fd_constr):
    string =
  let variables, _, expression = fd_constr in
  let length = String.length expression in
  let rec read_decimal string index =
    if index == length
    then (string, length)
    else
      let c = expression.[index] in
      if (c >= '0') && (c <= '9')
      then read_decimal (string ^ (String.make 1 c)) (index + 1)
      else (string, index) in
  let rec iterate string index =
    if index == length
    then string
    else
      let c = expression.[index] in
      if c = '$'
      then
	let decimal, new_index = read_decimal "" (index + 1) in
	let variable = List.nth variables (int_of_string decimal) in
	iterate (string ^ (string_of_term variable)) new_index
      else iterate (string ^ (String.make 1 c)) (index + 1) in
  iterate "" 0

let string_of_binding (binding: binding):
    string =
  let variable_name, term = binding in
  variable_name ^ "=" ^ (string_of_term term)

let string_of_answer_id (answer_id: answer_id):
    string =
  match answer_id with
    Speculative_original_answer ->
      "os"
  | Nonspeculative_original_answer ->
      "on"
  | Default_answer id ->
      "d(" ^ (string_of_int id) ^ ")"
  | Ordinary_answer id ->
      "p(" ^ (string_of_int id) ^ ")"

let string_of_answer (answer: answer):
    string =
  let constrs_string =
    let bindings = string_of_list string_of_binding ", "
      (List.rev answer.a_bindings) in
    let fd_constr = string_of_fd_constraint answer.a_fd_constr in
    if bindings <> ""
    then bindings ^ ", " ^ fd_constr
    else fd_constr in
  "(" ^ (string_of_pre_atom answer.a_pre_atom) ^ "@"
  ^ (string_of_agent answer.a_agent) ^ ", "
  ^ (string_of_answer_id answer.a_id) ^ ", {"
  ^ constrs_string ^ "}, {"
  ^ (string_of_list string_of_int "," (List.rev answer.a_process_ids))
  ^ "})"

let string_of_labeled_answer_type (labeled_answer: labeled_answer):
    string =
  match labeled_answer with
    New_answer _ ->
      "new"
  | Revised_answer _ ->
      "revised"

let string_of_labeled_answer (labeled_answer: labeled_answer):
    string =
  let answer = get_unlabeled_answer labeled_answer in
  let constrs_string =
    let bindings = string_of_list string_of_binding ", "
      (List.rev answer.a_bindings) in
    let fd_constr = string_of_fd_constraint answer.a_fd_constr in
    if bindings <> ""
    then bindings ^ ", " ^ fd_constr
    else fd_constr in
  "(" ^ (string_of_pre_atom answer.a_pre_atom) ^ "@"
  ^ (string_of_agent answer.a_agent) ^ ", "
  ^ (string_of_answer_id answer.a_id) ^ ", {"
  ^ constrs_string ^ "}, "
  ^ (match labeled_answer with
    New_answer _ ->
      "nil)"
  | Revised_answer (_, (Ordinary_answer previous_answer_id)) ->
      "p(" ^ (string_of_int previous_answer_id) ^ "))"
  | _ ->
      raise (Invalid_argument "string_of_labeled_answer"))

let string_of_labeled_atom (labeled_atom: labeled_atom):
    string =
  let pre_atom, agent, answer_id = labeled_atom in
  "(" ^ (string_of_pre_atom pre_atom) ^ "@"
  ^ (string_of_agent agent) ^ ", "
  ^ (string_of_answer_id answer_id) ^ ")"

let string_of_process (process: process):
    string =
  let constrs =
    let bindings = string_of_list string_of_binding ", "
      (List.rev process.p_bindings) in
    let fd_constrs = string_of_list string_of_fd_constraint ", "
      (List.rev process.p_fd_constrs) in
    if (bindings <> "") && (fd_constrs <> "")
    then bindings ^ ", " ^ fd_constrs
    else bindings ^ fd_constrs in
  "(" ^ (string_of_int process.p_id) ^ ", {" ^ constrs ^ "}, {"
  ^ (string_of_list string_of_atom ", " process.p_goal)
  ^ "}, {"
  ^ (string_of_list string_of_labeled_atom ", "
    (List.rev process.p_awaited_atoms))
  ^ "}, {"
  ^ (string_of_list string_of_labeled_atom ", "
    (List.rev process.p_assumed_atoms))
  ^ "})"

(**
   Variable renaming
*)

let rename_variable ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (variable_name: string) (agent_name: string) (process_id: int):
    string =
  let name = variable_name ^ "@" ^ agent_name ^ "#"
    ^ (string_of_int process_id) in
  if default_id > 0
  then name ^ "~" ^ (string_of_int default_id)
  else if answer_application_id > 0
  then name ^ "&" ^ (string_of_int answer_application_id)
  else name

let rec rename_variables_in_term ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (term: term) (agent_name: string) (process_id: int):
    term =
  let rename term =
    rename_variables_in_term ~default_id:default_id
      ~answer_application_id:answer_application_id term agent_name
      process_id in
  match term with
    Variable name ->
      Variable
	(rename_variable ~default_id:default_id
	  ~answer_application_id:answer_application_id name agent_name
	  process_id)
  | Typed_variable (name, domain) ->
      Typed_variable
	(rename_variable ~default_id:default_id
	  ~answer_application_id:answer_application_id name agent_name
	  process_id,
	domain)
  | Compound (ftr, arguments) ->
      Compound (ftr, List.map rename arguments)
  | Pair (argument1, argument2) ->
      Pair (rename argument1, rename argument2)
  | _ ->
      term

let rename_variables_in_fd_constraint
    ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (fd_constr: fd_constr) (agent_name: string) (process_id: int):
    fd_constr =
  let variables, func, expression = fd_constr in
  let renamed_variables =
    List.map
      (fun variable ->
	rename_variables_in_term ~default_id:default_id
	  ~answer_application_id:answer_application_id variable
	  agent_name process_id)
      variables in
  (renamed_variables, func, expression)

let rename_variables_in_constraint ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (constr: constr) (agent_name: string) (process_id: int):
    constr =
  match constr with
    Equality (lhs, rhs) ->
      let renamed_lhs = rename_variables_in_term ~default_id:default_id
	~answer_application_id:answer_application_id lhs agent_name
	process_id in
      let renamed_rhs = rename_variables_in_term ~default_id:default_id
	~answer_application_id:answer_application_id rhs agent_name
	process_id in
      Equality (renamed_lhs, renamed_rhs)
  | Fd fd_constr ->
      let renamed_fd_constr = rename_variables_in_fd_constraint
	~default_id:default_id
	~answer_application_id:answer_application_id fd_constr
	agent_name process_id in
      Fd renamed_fd_constr

let rename_variables_in_pre_atom ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (pre_atom: pre_atom) (agent_name: string) (process_id: int):
    pre_atom =
  let predicate, arguments = pre_atom in
  let renamed_arguments =
    List.map
      (fun argument ->
	rename_variables_in_term ~default_id:default_id
	  ~answer_application_id:answer_application_id argument
	  agent_name process_id)
      arguments in
  (predicate, renamed_arguments)

let rename_variables_in_atom ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (atom: atom) (agent_name: string) (process_id: int):
    atom =
  match atom with
    Nonaskable pre_atom ->
      let renamed_pre_atom = rename_variables_in_pre_atom
	~default_id:default_id
	~answer_application_id:answer_application_id pre_atom
	agent_name process_id in
      Nonaskable (renamed_pre_atom)
  | Askable (pre_atom, agent) ->
      let renamed_pre_atom = rename_variables_in_pre_atom
	~default_id:default_id
	~answer_application_id:answer_application_id pre_atom
	agent_name process_id in
      Askable (renamed_pre_atom, agent)

let rename_variables_in_default ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (default: default) (agent_name: string) (process_id: int):
    default =
  let Default (id, head, agent, fd_constr) = default in
  let renamed_head = rename_variables_in_pre_atom
    ~default_id:default_id
    ~answer_application_id:answer_application_id head agent_name
    process_id in
  let renamed_fd_constr = rename_variables_in_fd_constraint
    ~default_id:default_id
    ~answer_application_id:answer_application_id fd_constr agent_name
    process_id in
  (Default (id, renamed_head, agent, renamed_fd_constr))

let rename_variables_in_rule ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (rule: rule) (agent_name: string) (process_id: int):
    rule =
  let Rule (head, constrs, body) = rule in
  let renamed_head = rename_variables_in_pre_atom
    ~default_id:default_id
    ~answer_application_id:answer_application_id head agent_name
    process_id in
  let renamed_constrs =
    List.map
      (fun constr ->
	rename_variables_in_constraint ~default_id:default_id
	  ~answer_application_id:answer_application_id constr
	  agent_name process_id)
      constrs in
  let renamed_body =
    List.map
      (fun atom ->
	rename_variables_in_atom ~default_id:default_id
	  ~answer_application_id:answer_application_id atom agent_name
	  process_id)
      body in
  (Rule (renamed_head, renamed_constrs, renamed_body))

let rename_variables_in_binding ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (binding: binding) (agent_name: string) (process_id: int):
    binding =
  let variable_name, term = binding in
  let renamed_variable_name = rename_variable ~default_id:default_id
    ~answer_application_id:answer_application_id variable_name
    agent_name process_id in
  let renamed_term = rename_variables_in_term ~default_id:default_id
    ~answer_application_id:answer_application_id term agent_name
    process_id in
  (renamed_variable_name, renamed_term)

let rename_variables_in_bindings ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (bindings: binding list) (agent_name: string) (process_id: int):
    binding list =
  List.map
    (fun binding ->
      rename_variables_in_binding ~default_id:default_id
	~answer_application_id:answer_application_id binding
	agent_name process_id)
    bindings

let rename_variables_in_domain ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (domain: domain) (agent_name: string) (process_id: int):
    domain =
  let variable_name, variable_values = domain in
  let renamed_variable_name = rename_variable ~default_id:default_id
    ~answer_application_id:answer_application_id variable_name
    agent_name process_id in
  (renamed_variable_name, variable_values)

let rename_variables_in_domains ?default_id:((default_id: int) = 0)
    ?answer_application_id:((answer_application_id: int) = 0)
    (domains: domain list) (agent_name: string) (process_id: int):
    domain list =
  List.map
    (fun domain ->
      rename_variables_in_domain ~default_id:default_id
	~answer_application_id:answer_application_id domain agent_name
	process_id)
    domains

(**
   Unification
*)

exception Not_unifiable

let get_bound_value (variable_name: string) (bindings: binding list):
    term =
  List.assoc variable_name bindings

let rec is_dependent (term: term) (variable_name: string)
    (bindings: binding list):
    bool =
  match term with
    Variable name | Typed_variable (name, _) ->
      (name = variable_name)
      || (try
	is_dependent (get_bound_value name bindings) variable_name
	  bindings
      with Not_found ->
	false)
  | Compound (_, arguments) ->
      List.exists
	(fun argument -> is_dependent argument variable_name bindings)
	arguments
  | Pair (argument1, argument2) ->
      (is_dependent argument1 variable_name bindings)
      || (is_dependent argument2 variable_name bindings)
  | _ ->
      false

let rec unify_terms (term1: term) (term2: term)
    (bindings: binding list):
    binding list =
  if term1 == term2
  then bindings
  else
    match term1, term2 with
      Variable name1, Variable name2
    | Variable name1, Typed_variable (name2, _)
    | Typed_variable (name1, _), Variable name2
    | Typed_variable (name1, _), Typed_variable (name2, _) ->
	if name1 = name2
	then bindings
	else unify_variable_and_term name1 term2 bindings
    | Variable name1, _ | Typed_variable (name1, _), _ ->
	unify_variable_and_term name1 term2 bindings
    | _, Variable name2 | _, Typed_variable (name2, _)->
	unify_variable_and_term name2 term1 bindings
    | Integer value1, Integer value2 ->
	if value1 = value2
	then bindings
	else raise Not_unifiable
    | Symbol value1, Symbol value2 ->
	if value1 = value2
	then bindings
	else raise Not_unifiable
    | Compound (ftr1, arguments1), Compound (ftr2, arguments2) ->
	if (ftr1 <> ftr2)
	  || ((List.length arguments1) <> (List.length arguments2))
	then raise Not_unifiable
	else
	  List.fold_left2
	    (fun bindings argument1 argument2 ->
	      unify_terms argument1 argument2 bindings)
	    bindings arguments1 arguments2
    | Pair (argument11, argument12), Pair (argument21, argument22) ->
	let bindings1 = unify_terms argument11 argument21 bindings in
	unify_terms argument12 argument22 bindings1
    | _ ->
	raise Not_unifiable

and unify_variable_and_term (variable_name: string) (term: term)
    (bindings: binding list):
    binding list =
  try
    let value = get_bound_value variable_name bindings in
    unify_terms value term bindings
  with
    Not_found ->
      match term with
	Variable name1 | Typed_variable (name1, _) ->
	  (try
	    let value1 = get_bound_value name1 bindings in
	    unify_terms (Variable variable_name) value1 bindings
	  with Not_found ->
	    (variable_name, term) :: bindings)
      | _ ->
	  if is_dependent term variable_name bindings
	  then raise Not_unifiable (* Cyclic dependence *)
	  else (variable_name, term) :: bindings

let unify_pre_atoms (pre_atom1: pre_atom) (pre_atom2: pre_atom)
    (bindings: binding list):
    binding list =
  let predicate1, arguments1 = pre_atom1 in
  let predicate2, arguments2 = pre_atom2 in
  if (predicate1 <> predicate2)
    || ((List.length arguments1) <> (List.length arguments2))
  then raise Not_unifiable
  else
    List.fold_left2
      (fun bindings argument1 argument2 ->
	unify_terms argument1 argument2 bindings)
      bindings arguments1 arguments2

let rec get_term_value (term: term) (bindings: binding list):
    term =
  match term with
    Variable name | Typed_variable (name, _) ->
      (try
	get_term_value (get_bound_value name bindings) bindings
      with Not_found ->
	raise (Invalid_argument "get_term_value"))
  | Integer _ | Symbol _ | Nil ->
      term
  | Compound (ftr, arguments) ->
      let argument_values =
	List.map (fun argument -> get_term_value argument bindings)
	  arguments in
      Compound (ftr, argument_values)
  | Pair (argument1, argument2) ->
      let argument1_value = get_term_value argument1 bindings in
      let argument2_value = get_term_value argument2 bindings in
      Pair (argument1_value, argument2_value)

let solve_equality_constraints (equality_constrs: (term * term) list)
    (bindings: binding list):
    binding list =
  List.fold_left
    (fun bindings (lhs, rhs) -> unify_terms lhs rhs bindings)
    bindings equality_constrs

(**
   Binding simplification
*)

let simplify_term (eliminated_variables: (string * string) list)
    (term: term):
    term =
  match term with
    Variable name ->
      (try
	Variable (List.assoc name eliminated_variables)
      with Not_found ->
	term)
  | Typed_variable (name, values) ->
      (try
	Typed_variable (List.assoc name eliminated_variables, values)
      with Not_found ->
	term)
  | _ ->
      term

let rec eliminate_variable_from_bindings (bindings: binding list):
    string * string * binding list =
  let rec eliminate =
    function
      [] ->
	raise Not_found
    | (variable_name, term) :: rest_bindings ->
	match term with
	  Variable eliminated_variable_name
	| Typed_variable (eliminated_variable_name, _) ->
	    (eliminated_variable_name, variable_name, rest_bindings)
	| _ ->
	    let eliminated_variable_name, assigned_variable_name,
	      updated_rest_bindings =
	      eliminate_variable_from_bindings rest_bindings in
	    (eliminated_variable_name, assigned_variable_name,
	    (variable_name, term) :: updated_rest_bindings) in
  let eliminated_variable_name, assigned_variable_name, bindings1 =
    eliminate bindings in
  let bindings2 =
    List.map
      (fun (variable_name, term) ->
	let variable_name1 =
	  if variable_name = eliminated_variable_name
	  then assigned_variable_name
	  else variable_name in
	let term1 = simplify_term
	  [eliminated_variable_name, assigned_variable_name] term in
	(variable_name1, term1))
      bindings1 in
  (eliminated_variable_name, assigned_variable_name, bindings2)

let simplify_bindings (bindings: binding list):
    (string * string) list * binding list =
  let rec iterate eliminated_variables bindings =
    try
      let eliminated_variable_name, assigned_variable_name,
	updated_bindings =
	eliminate_variable_from_bindings bindings in
      let updated_eliminated_variables =
	List.map
	  (fun variable_names_pair ->
	    let e_v_name, a_v_name = variable_names_pair in
	    if a_v_name = eliminated_variable_name
	    then (e_v_name, assigned_variable_name)
	    else variable_names_pair)
	  eliminated_variables in
      iterate
	((eliminated_variable_name, assigned_variable_name)
	:: updated_eliminated_variables)
	updated_bindings
    with Not_found ->
      (eliminated_variables, bindings) in
  iterate [] bindings

let simplify_pre_atom (eliminated_variables: (string * string) list)
    (pre_atom: pre_atom):
    pre_atom =
  let predicate, terms = pre_atom in
  (predicate,
  List.map (simplify_term eliminated_variables) terms)

let simplify_atom (eliminated_variables: (string * string) list)
    (atom: atom):
    atom =
  match atom with
    Nonaskable pre_atom ->
      Nonaskable (simplify_pre_atom eliminated_variables pre_atom)
  | Askable (pre_atom, agent) ->
      Askable (simplify_pre_atom eliminated_variables pre_atom, agent)

let simplify_fd_constraint
    (eliminated_variables: (string * string) list)
    (fd_constr: fd_constr):
    fd_constr =
  let terms, func, expression = fd_constr in
  (List.map (simplify_term eliminated_variables) terms,
  func, expression)

let simplify_domain (eliminated_variables: (string * string) list)
    (domain: domain):
    domain =
  let name, values = domain in
  try
    (List.assoc name eliminated_variables, values)
  with Not_found ->
    (name, values)

let simplify_labeled_atom
    (eliminated_variables: (string * string) list)
    (labeled_atom: labeled_atom):
    labeled_atom =
  let pre_atom, agent, answer_id = labeled_atom in
  (simplify_pre_atom eliminated_variables pre_atom, agent, answer_id)

let simplify_process (process: process):
    process =
  let eliminated_variables, bindings = simplify_bindings
    process.p_bindings in
  {process with
    p_bindings = bindings;
    p_domains =
      List.map (simplify_domain eliminated_variables)
	process.p_domains;
    p_fd_constrs =
      List.map (simplify_fd_constraint eliminated_variables)
	process.p_fd_constrs;
    p_goal =
      List.map (simplify_atom eliminated_variables)
	process.p_goal;
    p_awaited_atoms =
      List.map (simplify_labeled_atom eliminated_variables)
	process.p_awaited_atoms;
    p_assumed_atoms =
      List.map (simplify_labeled_atom eliminated_variables)
	process.p_assumed_atoms;
    p_initial_goal = simplify_pre_atom eliminated_variables
      process.p_initial_goal}

(**
   Finite-domain constraint satisfaction
*)

exception Not_satisfiable

let check_fd_constraints (fd_constrs: fd_constr list)
    (integer_bindings: (string * int) list):
    fd_constr list =
  List.fold_left
    (fun constrs_to_check fd_constr ->
      try
	let variables = get_variables_from_fd_constraint fd_constr in
	let values =
	  List.map
	    (fun variable -> List.assoc variable integer_bindings)
	    (List.map get_variable_name variables) in
	if is_fd_constraint_satisfied fd_constr values
	then constrs_to_check
	else raise Not_satisfiable
      with Not_found ->
	fd_constr :: constrs_to_check)
    [] fd_constrs

let solve_fd_constraints (domains: domain list)
    (fd_constrs: fd_constr list) (bindings: binding list):
    binding list =
  let rec iterate rest_domains fd_constrs bindings integer_bindings
      variable =
    function
      [] ->
	raise Not_satisfiable
    | value :: rest_values ->
	try
	  let bindings1 = unify_terms (Variable variable)
	    (Integer value) bindings in
	  let integer_bindings1 = (variable, value)
	    :: integer_bindings in
	  let fd_constrs_to_check = check_fd_constraints fd_constrs
	    integer_bindings1 in
	  match rest_domains with
	    [] ->
	      bindings1
	  | (next_variable, next_values) :: next_rest_domains ->
	      iterate next_rest_domains fd_constrs_to_check bindings1
		integer_bindings1 next_variable next_values
	with Not_unifiable | Not_satisfiable ->
	  iterate rest_domains fd_constrs bindings integer_bindings
	    variable rest_values in
  match domains with
    [] ->
      bindings
  | (variable, values) :: rest_domains ->
      iterate rest_domains fd_constrs bindings [] variable values

let project_constraints (projection_variables: term list)
    (bindings: binding list) (domains: domain list)
    (fd_constrs: fd_constr list):
    (binding list) * fd_constr =
  let untyped_variables, typed_variables =
    List.fold_left
      (fun (untyped_variables, typed_variables) variable ->
	match variable with
	  Typed_variable _ ->
	    (untyped_variables, variable :: typed_variables)
	| Variable name ->
	    (try
	      (untyped_variables,
	      (Typed_variable (name, List.assoc name domains))
	      :: typed_variables)
	    with Not_found ->
	      (variable :: untyped_variables, typed_variables))
	| _ ->
	    raise (Invalid_argument "project_constraints"))
      ([], []) projection_variables in
  let projected_bindings =
    List.map
      (fun variable ->
	match variable with
	  Variable name ->
	    (name, get_term_value variable bindings)
	| _ ->
	    raise (Failure "project_constraints"))
      untyped_variables in
  let arity = List.length typed_variables in
  let variable_names = List.map get_variable_name typed_variables in
  let domain_values =
    List.map
      (function
	Typed_variable (_, values) ->
	  values
      | _ ->
	  raise (Failure "project_constraints"))
      typed_variables in
  let domain_dimensions =
    List.map
      (function
	Typed_variable (_, domain) ->
	  List.length domain
      | _ ->
	  raise (Failure "project_constraints"))
      typed_variables in
  let table = create_md_bit_array domain_dimensions in
  let get_value_indices values =
    List.map2
      (fun value domain_values ->
	get_element_index value domain_values)
      values domain_values in
  let string_of_tuple values =
    let string = string_of_list string_of_int "," values in
    if arity = 1
    then string
    else "<" ^ string ^ ">" in
  let rec iterate rest_domains fd_constrs bindings integer_bindings
      tuples_string variable =
    function
      [] ->
	tuples_string
    | value :: rest_values ->
	let tuples_string1 =
	  (try
	    let bindings1 = unify_terms (Variable variable)
	      (Integer value) bindings in
	    let integer_bindings1 = (variable, value)
	      :: integer_bindings in
	    let fd_constrs_to_check = check_fd_constraints fd_constrs
	      integer_bindings1 in
	    match rest_domains with
	      [] ->
		let assigned_values =
		  List.map
		    (fun name -> List.assoc name integer_bindings1)
		    variable_names in
		let assinged_value_indices = get_value_indices
		  assigned_values in
		set_md_bit_array_value table assinged_value_indices
		  true;
		(if tuples_string = ""
		then ""
		else tuples_string ^ ",")
		^ (string_of_tuple assigned_values)
	    | (next_variable, next_values) :: next_rest_domains ->
		iterate next_rest_domains fd_constrs_to_check
		  bindings1 integer_bindings1 tuples_string
		  next_variable next_values
	  with Not_unifiable | Not_satisfiable ->
	    tuples_string) in
	iterate rest_domains fd_constrs bindings integer_bindings
	  tuples_string1 variable rest_values in
  match domains with
    [] ->
      raise (Invalid_argument "project_constraints")
  | (variable, values) :: rest_domains ->
      let tuples_string = iterate rest_domains fd_constrs bindings []
	"" variable values in
      let get_transformed_index_string index =
	string_of_int
	  (get_variable_index
	    (get_variable_name (List.nth typed_variables index))
	    projection_variables) in
      let rec create_variables_string index string =
	if index < arity
	then create_variables_string (index + 1)
	  (string ^ "," ^ (get_transformed_index_string index))
	else string in
      let zeroth_string = get_transformed_index_string 0 in
      let expression =
	if arity = 1
	then "$" ^ zeroth_string ^ ":{" ^ tuples_string ^ "}"
	else "<" ^ (create_variables_string 1 zeroth_string)
	  ^ ">:{" ^ tuples_string ^ "}" in
      let func values =
	let indices = get_value_indices values in
	get_md_bit_array_value table indices in
      (projected_bindings,
      (projection_variables, func, expression))

(**
   Speculative computation
*)

(** Process reduction phase *)

(** Case 1 *)
let convert_ordinary_process_into_finished_process  (agent: agent)
    (o_process: labeled_process) (state: agent_state):
    agent_state * agent * labeled_answer =
  let process = get_unlabeled_process o_process in
  let state1 = {state with
    s_labeled_processes = replace_labeled_process
      (Finished_process process) state.s_labeled_processes} in
  let bindings, fd_constr = project_constraints
    (get_argument_variables_from_pre_atom process.p_initial_goal)
    process.p_bindings process.p_domains process.p_fd_constrs in
  let labeled_answer = New_answer
    {a_pre_atom = process.p_initial_goal;
    a_agent = agent;
    a_id = Ordinary_answer process.p_id;
    a_bindings = bindings;
    a_fd_constr = fd_constr;
    a_process_ids = []} in
  (state1, process.p_initial_goal_sender, labeled_answer)

(** Case 2 *)
let handle_nonaskable_atom_in_ordinary_process (pre_atom: pre_atom)
    (rest_subgoals: atom list) (agent: agent)
    (o_process: labeled_process) (spec: agent_spec)
    (state: agent_state):
    agent_state =
  let agent_name = get_agent_name agent in
  let process = get_unlabeled_process o_process in
  let state1, new_process_ids =
    List.fold_left
      (fun (state, new_process_ids) rule ->
	let next_process_id = state.s_next_process_id in
	let Rule (head, new_constrs, new_subgoals) =
	  rename_variables_in_rule rule agent_name next_process_id in
	try
	  let domains = (get_domains_from_pre_atom head)
	    @ (flat_map get_domains_from_constraint new_constrs)
	    @ (flat_map get_domains_from_atom new_subgoals)
	    @ process.p_domains in
	  let new_equality_constrs, new_fd_constrs = split_constraints
	    new_constrs in
	  let bindings1 = unify_pre_atoms pre_atom head
	    process.p_bindings in
	  let bindings2 = solve_equality_constraints new_equality_constrs
	    bindings1 in
	  let fd_constrs = new_fd_constrs @ process.p_fd_constrs in
	  let _ = solve_fd_constraints domains fd_constrs bindings2 in
	  let new_process = {process with
	    p_id = next_process_id;
	    p_bindings = bindings2;
	    p_domains = domains;
	    p_fd_constrs = fd_constrs;
	    p_goal = new_subgoals @ rest_subgoals} in
	  let state1 = {state with
	    s_labeled_processes = (Ordinary_process new_process)
	      :: state.s_labeled_processes;
	    s_next_process_id = next_process_id + 1} in
	  (state1, next_process_id :: new_process_ids)
	with Not_unifiable | Not_satisfiable ->
	  (state, new_process_ids))
      (state, []) (get_rules_on_pre_atom pre_atom spec) in
  {state1 with
    s_answers = replace_process_ids_in_assumed_answers new_process_ids
      process state1.s_answers;
    s_labeled_processes = remove_labeled_process process.p_id
      state1.s_labeled_processes}

(** Case 3a *)
let handle_askable_atom_with_default_answers (d_answers: answer list)
    (pre_atom: pre_atom) (remote_agent: agent)
    (rest_subgoals: atom list) (agent: agent)
    (o_process: labeled_process) (spec: agent_spec)
    (state: agent_state):
    agent_state * int list =
  let agent_name = get_agent_name agent in
  let process = get_unlabeled_process o_process in
  List.fold_left
    (fun (state, new_process_ids) default ->
      let next_process_id = state.s_next_process_id in
      let Default (default_id, head, _, new_fd_constr) =
	rename_variables_in_default default agent_name
	  next_process_id in
      try
	let domains = (get_domains_from_pre_atom head)
	  @ (get_domains_from_fd_constraint new_fd_constr)
	  @ process.p_domains in
	let bindings = unify_pre_atoms pre_atom head
	  process.p_bindings in
	let fd_constrs = new_fd_constr :: process.p_fd_constrs in
	let _ = solve_fd_constraints domains fd_constrs bindings in
	let new_process = {process with
	  p_id = next_process_id;
	  p_bindings = bindings;
	  p_domains = domains;
	  p_fd_constrs = fd_constrs;
	  p_goal = rest_subgoals;
	  p_assumed_atoms =
	    (pre_atom, remote_agent, Default_answer default_id)
	    :: process.p_assumed_atoms} in
	let d_answer = get_answer (Default_answer default_id)
	  d_answers in
	let updated_d_answer = {d_answer with
	  a_process_ids = next_process_id
	    :: d_answer.a_process_ids} in
	let state1 = {state with
	  s_answers = replace_answer d_answer.a_id updated_d_answer
	    state.s_answers;
	  s_labeled_processes = (Ordinary_process new_process)
	    :: state.s_labeled_processes;
	  s_next_process_id = next_process_id + 1} in
	(state1, next_process_id :: new_process_ids)
      with Not_unifiable | Not_satisfiable ->
	(state, new_process_ids))
    (state, [])
    (get_defaults_on_askable_atom pre_atom remote_agent spec)

(** Case 3b *)
let handle_askable_atom_with_ordinary_answers (p_answers: answer list)
    (pre_atom: pre_atom) (remote_agent: agent)
    (rest_subgoals: atom list) (agent: agent)
    (o_process: labeled_process) (state: agent_state):
    agent_state * int list =
  let agent_name = get_agent_name agent in
  let process = get_unlabeled_process o_process in
  List.fold_left
    (fun (state, new_process_ids) p_answer ->
      let next_process_id = state.s_next_process_id in
      let head = rename_variables_in_pre_atom p_answer.a_pre_atom
	agent_name next_process_id in
      try
	let domains = (rename_variables_in_domains
	  (get_domains_from_fd_constraint p_answer.a_fd_constr)
	  agent_name next_process_id)
	  @ process.p_domains in
	let bindings = unify_pre_atoms pre_atom head
	  process.p_bindings in
	let new_fd_constr = rename_variables_in_fd_constraint
	  p_answer.a_fd_constr agent_name next_process_id in
	let fd_constrs = new_fd_constr :: process.p_fd_constrs in
	let _ = solve_fd_constraints domains fd_constrs bindings in
	let new_process = {process with
	  p_id = next_process_id;
	  p_bindings = bindings;
	  p_domains = domains;
	  p_fd_constrs = fd_constrs;
	  p_goal = rest_subgoals;
	  p_assumed_atoms = (pre_atom, agent, p_answer.a_id)
	    :: process.p_assumed_atoms} in
	let updated_p_answer = {p_answer with
	  a_process_ids = next_process_id
	    :: p_answer.a_process_ids} in
	let state1 = {state with
	  s_answers = replace_answer p_answer.a_id updated_p_answer
	    state.s_answers;
	  s_labeled_processes = (Ordinary_process new_process)
	    :: state.s_labeled_processes;
	  s_next_process_id = next_process_id + 1} in
	(state1, next_process_id :: new_process_ids)
      with Not_unifiable | Not_satisfiable ->
	(state, new_process_ids))
    (state, []) p_answers

(** Case 3 *)
let handle_askable_atom_in_ordinary_process (pre_atom: pre_atom)
    (remote_agent: agent) (rest_subgoals: atom list)
    (agent: agent) (o_process: labeled_process) (spec: agent_spec)
    (state: agent_state):
    agent_state * atom list =
  let o_answers, d_answers, p_answers = get_answers_on_askable_atom
    pre_atom remote_agent state.s_answers in
  let state1, new_process_ids =
    if p_answers == []
    then (* Case 3a *)
      handle_askable_atom_with_default_answers d_answers pre_atom
	remote_agent rest_subgoals agent o_process spec state
    else (* Case 3b *)
      handle_askable_atom_with_ordinary_answers p_answers pre_atom
	remote_agent rest_subgoals agent o_process state in
  let process = get_unlabeled_process o_process in
  let answers2 = add_process_ids_to_assumed_answers new_process_ids
    process state1.s_answers in
  let o_answer =
    List.find
      (fun o_answer ->
	if p_answers == []
	then o_answer.a_id == Speculative_original_answer
	else o_answer.a_id == Nonspeculative_original_answer)
      o_answers in
  let answers3 =
    let updated_o_answer = {o_answer with
      a_process_ids = process.p_id :: o_answer.a_process_ids} in
    replace_answer o_answer.a_id updated_o_answer answers2 in
  let updated_o_process = Ordinary_process
    {process with
      p_goal = rest_subgoals;
      p_awaited_atoms = [pre_atom, remote_agent, o_answer.a_id]} in
  let state2 = {state1 with
    s_answers = answers3;
    s_labeled_processes = replace_labeled_process updated_o_process
      state1.s_labeled_processes} in
  let query_to_send =
    if o_answer.a_id == Speculative_original_answer
      && o_answer.a_process_ids == []
    then
      let predicate = get_pre_atom_predicate pre_atom in
      let typed_variables = get_typed_argument_variables_from_pre_atom
	pre_atom process.p_domains in
      [Askable ((predicate, typed_variables), remote_agent)]
    else [] in
  (state2, query_to_send)

let reduce_ordinary_process (agent: agent) (process_id: int)
    (system: multiagent_system) (states: agent_state list):
    agent_state list (* Updated agent states *)
    * (agent * labeled_answer) list (* Answer to return *)
    * atom list = (* Query to send *)
  let spec =
    try
      get_agent_spec agent system
    with Not_found ->
      raise (Invalid_argument "reduce_ordinary_process") in
  let state = get_agent_state agent states in
  let o_process =
    try
      get_labeled_process process_id state.s_labeled_processes
    with Not_found ->
      raise (Invalid_argument "reduce_ordinary_process") in
  let process =
    let process = get_unlabeled_process o_process in
    if process.p_awaited_atoms = []
    then process
    else raise (Invalid_argument "reduce_ordinary_process") in
  let state1, answer_to_return, query_to_send =
    match process.p_goal with
      [] -> (* Case 1 *)
	let state, initial_goal_sender, labeled_answer =
	  convert_ordinary_process_into_finished_process agent
	    o_process state in
	(state, [initial_goal_sender, labeled_answer], [])
    | (Nonaskable pre_atom) :: rest_subgoals -> (* Case 2 *)
	let state = handle_nonaskable_atom_in_ordinary_process
	  pre_atom rest_subgoals agent o_process spec state in
	(state, [], [])
    | (Askable (pre_atom, remote_agent))
      :: rest_subgoals -> (* Case 3 *)
	let state, query_to_send =
	  handle_askable_atom_in_ordinary_process pre_atom
	    remote_agent rest_subgoals agent o_process spec state in
	(state, [], query_to_send) in
  (replace_agent_state state1 states, answer_to_return, query_to_send)

(** Fact arrival phase *)

let handle_default_process_for_new_answer (agent: agent)
    (d_answer: answer)
    (new_answer, state, answers_to_return:
      answer * agent_state * (agent * labeled_answer) list)
    (process_id: int):
    answer * agent_state * (agent * labeled_answer) list =
  let agent_name = get_agent_name agent in
  (* Suspend the default process if it is not yet suspended. *)
  let labeled_process = get_labeled_process process_id
    state.s_labeled_processes in
  let process = get_unlabeled_process labeled_process in
  let original_pre_atom, remote_agent, awaited_atoms, assumed_atoms,
    updated_process =
    try
      let original_pre_atom, remote_agent, assumed_atoms =
	remove_labeled_atom d_answer.a_id process.p_assumed_atoms in
      let updated_process = {process with
	p_awaited_atoms =
	  (original_pre_atom, remote_agent, d_answer.a_id)
	  :: process.p_awaited_atoms;
	p_assumed_atoms = assumed_atoms} in
      (original_pre_atom, remote_agent, process.p_awaited_atoms,
      assumed_atoms, updated_process)
    with Not_found ->
      let original_atom, remote_agent, awaited_atoms =
	remove_labeled_atom d_answer.a_id process.p_awaited_atoms in
      (original_atom, remote_agent, awaited_atoms,
      process.p_assumed_atoms, process) in
  let updated_labeled_process =
    match labeled_process with
      Ordinary_process _ ->
	Ordinary_process updated_process
    | Finished_process _ ->
	Finished_process updated_process in
  let state1 = {state with
    s_labeled_processes = replace_labeled_process
      updated_labeled_process state.s_labeled_processes} in
  let new_answer2, state2, answer_to_return2 =
    let next_process_id = state1.s_next_process_id in
    let new_answer_pre_atom = rename_variables_in_pre_atom
      new_answer.a_pre_atom agent_name next_process_id in
    let new_answer_fd_constr = rename_variables_in_fd_constraint
      new_answer.a_fd_constr agent_name next_process_id in
    try
      let domains = (get_domains_from_pre_atom new_answer_pre_atom)
	@ process.p_domains in
      let bindings = unify_pre_atoms original_pre_atom
	new_answer_pre_atom process.p_bindings in
      let fd_constrs = new_answer_fd_constr :: process.p_fd_constrs in
      let _ = solve_fd_constraints domains fd_constrs bindings in
      (* Spawn a process with the new answer. *)
      let new_process = {process with
	p_id = next_process_id;
	p_bindings = bindings;
	p_domains = domains;
	p_fd_constrs = fd_constrs;
	p_awaited_atoms = awaited_atoms;
	p_assumed_atoms =
	  (original_pre_atom, remote_agent, new_answer.a_id)
	  :: assumed_atoms} in
      let new_labeled_process, answer_to_return =
	match labeled_process with
	  Ordinary_process _ ->
	    (Ordinary_process new_process, [])
	| Finished_process _ ->
	    let answer_to_return =
	      if new_process.p_awaited_atoms == []
	      then
		let bindings, fd_constr = project_constraints
		  (get_argument_variables_from_pre_atom
		    new_process.p_initial_goal)
		  new_process.p_bindings new_process.p_domains
		  new_process.p_fd_constrs in
		let answer =
		  {a_pre_atom = new_process.p_initial_goal;
		  a_agent = agent;
		  a_id = Ordinary_answer next_process_id;
		  a_bindings = bindings;
		  a_fd_constr = fd_constr;
		  a_process_ids = []} in
		let labeled_answer =
		  if process.p_awaited_atoms == []
		  then Revised_answer
		    (answer, Ordinary_answer process_id)
		  else New_answer answer in
		[new_process.p_initial_goal_sender, labeled_answer]
	      else [] in
	    (Finished_process new_process, answer_to_return) in
      let state2 = {state1 with
	s_answers = add_process_ids_to_answers_with_exception
	  [next_process_id] process d_answer state1.s_answers;
	s_labeled_processes = new_labeled_process
	  :: state1.s_labeled_processes;
	s_next_process_id = next_process_id + 1} in
      let new_answer2 = {new_answer with
	a_process_ids = next_process_id
	  :: new_answer.a_process_ids} in
      (new_answer2, state2, answer_to_return)
    with Not_unifiable | Not_satisfiable ->
      (* Invalidate the previous answer if necessary. *)
      let answer_to_return =
	match labeled_process with
	  Ordinary_process _ ->
	    []
	| Finished_process _ ->
	    if process.p_awaited_atoms == []
	    then
	      let labeled_answer = Revised_answer
		({a_pre_atom = process.p_initial_goal;
		a_agent = agent;
		a_id = Ordinary_answer process_id;
		a_bindings = [];
		a_fd_constr = create_false_fd_constraint
		    (get_argument_variables_from_pre_atom
		      process.p_initial_goal);
		a_process_ids = []},
		Ordinary_answer process_id) in
	      [process.p_initial_goal_sender, labeled_answer]
	    else [] in
      (new_answer, state1, answer_to_return) in
  (new_answer2, state2, answer_to_return2 @ answers_to_return)

let handle_original_process_for_new_answer (agent: agent)
    (spec: agent_spec) (o_answer: answer)
    (new_answer, state: answer * agent_state) (process_id: int):
    answer * agent_state =
  let agent_name = get_agent_name agent in
  let labeled_process = get_labeled_process process_id
    state.s_labeled_processes in
  let process = get_unlabeled_process labeled_process in
  let original_pre_atom, remote_agent, awaited_atoms =
    remove_labeled_atom o_answer.a_id process.p_awaited_atoms in
  let next_process_id = state.s_next_process_id in
  try
    let domains1, bindings1, fd_constrs1 =
      match o_answer.a_id with
	Speculative_original_answer ->
	  List.fold_left
	    (fun (domains, bindings, fd_constrs) default ->
	      let Default (_, head, _, fd_constr) =
		let Default (id, _, _, _) = default in
		rename_variables_in_default default agent_name
		  next_process_id ~default_id:id in
	      ((get_domains_from_pre_atom head) @ domains,
	      unify_pre_atoms original_pre_atom head bindings,
	      (negate_fd_constraint fd_constr) :: fd_constrs))
	    (process.p_domains, process.p_bindings,
	    process.p_fd_constrs)
	    (get_defaults_on_askable_atom new_answer.a_pre_atom
	      new_answer.a_agent spec)
      | _ ->
	  (process.p_domains, process.p_bindings,
	  process.p_fd_constrs) in
    let new_answer_pre_atom = rename_variables_in_pre_atom
      new_answer.a_pre_atom agent_name next_process_id in
    let new_answer_fd_constr = rename_variables_in_fd_constraint
      new_answer.a_fd_constr agent_name next_process_id in
    let domains2 = (get_domains_from_pre_atom new_answer_pre_atom)
      @ domains1 in
    let bindings2 = unify_pre_atoms original_pre_atom
      new_answer_pre_atom bindings1 in
    let fd_constrs2 = new_answer_fd_constr :: fd_constrs1 in
    let _ = solve_fd_constraints domains2 fd_constrs2 bindings2 in
    (* Spawn a process with the new answer. *)
    let new_labeled_process = Ordinary_process
      {process with
	p_id = next_process_id;
	p_bindings = bindings2;
	p_domains = domains2;
	p_fd_constrs = fd_constrs2;
	p_awaited_atoms = awaited_atoms;
	p_assumed_atoms =
	  (original_pre_atom, remote_agent, new_answer.a_id)
	  :: process.p_assumed_atoms} in
    let state1 = {state with
      s_answers = add_process_ids_to_answers_with_exception
	[next_process_id] process o_answer state.s_answers;
      s_labeled_processes = new_labeled_process
	:: state.s_labeled_processes;
      s_next_process_id = next_process_id + 1} in
    let new_answer1 = {new_answer with
      a_process_ids = next_process_id :: new_answer.a_process_ids} in
    (new_answer1, state1)
  with Not_unifiable | Not_satisfiable ->
    (new_answer, state)

(** Case 1 *)
let receive_new_answer (agent: agent) (new_answer: answer)
    (spec: agent_spec) (state: agent_state):
    agent_state * (agent * labeled_answer) list =
  let o_answers, d_answers, _ = get_answers_on_askable_atom
    new_answer.a_pre_atom new_answer.a_agent state.s_answers in
  let new_answer1, state1, answers_to_return1 =
    List.fold_left
      (fun (new_answer, state, answers_to_return) d_answer ->
	List.fold_left
	  (handle_default_process_for_new_answer agent d_answer)
	  (new_answer, state, answers_to_return)
	  d_answer.a_process_ids)
      (new_answer, state, []) d_answers in
  let new_answer2, state2 =
    List.fold_left
      (fun (new_answer, state) o_answer ->
	List.fold_left
	  (handle_original_process_for_new_answer agent spec o_answer)
	  (new_answer, state) o_answer.a_process_ids)
      (new_answer1, state1) o_answers in
  let state3 = {state2 with
    s_answers = new_answer2 :: state2.s_answers} in
  (state3, answers_to_return1)

let handle_process_for_revised_answer (agent: agent)
    (previous_answer: answer)
    (revised_answer, state, answers_to_return:
      answer * agent_state * (agent * labeled_answer) list)
    (process_id: int):
    answer * agent_state * (agent * labeled_answer) list =
  let agent_name = get_agent_name agent in
  let labeled_process = get_labeled_process process_id
    state.s_labeled_processes in
  let process = get_unlabeled_process labeled_process in
  let original_pre_atom, _ =
    get_askable_atom previous_answer.a_id process.p_assumed_atoms in
  let revised_answer1, state1, answer_to_return1 =
    let next_answer_application_id =
      state.s_next_answer_application_id in
    let revised_answer_pre_atom = rename_variables_in_pre_atom
      revised_answer.a_pre_atom agent_name process.p_id
      ~answer_application_id:next_answer_application_id in
    let revised_answer_fd_constr = rename_variables_in_fd_constraint
      revised_answer.a_fd_constr agent_name process.p_id
      ~answer_application_id:next_answer_application_id in
    try
      let domains =
	(get_domains_from_pre_atom revised_answer_pre_atom)
	@ process.p_domains in
      let bindings = unify_pre_atoms original_pre_atom
	revised_answer_pre_atom process.p_bindings in
      let fd_constrs = revised_answer_fd_constr
	:: process.p_fd_constrs in
      let _ = solve_fd_constraints domains fd_constrs bindings in
      (* Update the process using the revised answer. *)
      let assumed_atoms =
	if revised_answer.a_id = previous_answer.a_id
	then process.p_assumed_atoms
	else replace_labeled_atom previous_answer.a_id
	  revised_answer.a_id process.p_assumed_atoms in
      let updated_process = {process with
	p_bindings = bindings;
	p_domains = domains;
	p_fd_constrs = fd_constrs;
	p_assumed_atoms = assumed_atoms} in
      let updated_labeled_process, answer_to_return =
	match labeled_process with
	  Ordinary_process _ ->
	    (Ordinary_process updated_process, [])
	| Finished_process _ ->
	    let answer_to_return =
	      if updated_process.p_awaited_atoms == []
	      then
		let bindings, fd_constr = project_constraints
		  (get_argument_variables_from_pre_atom
		    updated_process.p_initial_goal)
		  updated_process.p_bindings updated_process.p_domains
		  updated_process.p_fd_constrs in
		let labeled_answer = Revised_answer
		  ({a_pre_atom = updated_process.p_initial_goal;
		  a_agent = agent;
		  a_id = Ordinary_answer process_id;
		  a_bindings = bindings;
		  a_fd_constr = fd_constr;
		  a_process_ids = []},
		  Ordinary_answer process_id) in
		[updated_process.p_initial_goal_sender,
		labeled_answer]
	      else [] in
	    (Finished_process updated_process, answer_to_return) in
      let state1 = {state with
	s_labeled_processes = replace_labeled_process
	  updated_labeled_process state.s_labeled_processes;
	s_next_answer_application_id =
	  next_answer_application_id + 1} in
      let revised_answer1 = {revised_answer with
	a_process_ids = process_id :: revised_answer.a_process_ids} in
      (revised_answer1, state1, answer_to_return)
    with Not_unifiable | Not_satisfiable ->
      (* Kill the process. *)
      let answer_to_return =
	match labeled_process with
	  Ordinary_process _ ->
	    []
	| Finished_process _ ->
	    if process.p_awaited_atoms == []
	    then
	      let labeled_answer = Revised_answer
		({a_pre_atom = process.p_initial_goal;
		a_agent = agent;
		a_id = Ordinary_answer process_id;
		a_bindings = [];
		a_fd_constr = create_false_fd_constraint
		    (get_argument_variables_from_pre_atom
		      process.p_initial_goal);
		a_process_ids = []},
		Ordinary_answer process_id) in
	      [process.p_initial_goal_sender, labeled_answer]
	    else [] in
      let state1 = {state with
	s_labeled_processes = remove_labeled_process process_id
	  state.s_labeled_processes} in
      (revised_answer, state1, answer_to_return) in
  (revised_answer1, state1, answer_to_return1 @ answers_to_return)

(** Case 2 *)
let receive_revised_answer (agent: agent) (revised_answer: answer)
    (previous_answer_id: answer_id) (spec: agent_spec)
    (state: agent_state):
    agent_state * (agent * labeled_answer) list =
  let previous_answer = get_answer previous_answer_id
    state.s_answers in
  let revised_answer1, state1, answers_to_return1 =
    List.fold_left
      (handle_process_for_revised_answer agent previous_answer)
      (revised_answer, state, []) previous_answer.a_process_ids in
  let state2 = {state1 with
    s_answers = replace_answer previous_answer.a_id revised_answer1
      state1.s_answers} in
  (state2, answers_to_return1)

let receive_answer (agent: agent) (labeled_answer: labeled_answer)
    (system: multiagent_system) (states: agent_state list):
    agent_state list (* Updated agent states *)
    * (agent * labeled_answer) list = (* Answers to return *)
  let spec =
    try
      get_agent_spec agent system
    with Not_found ->
      raise (Invalid_argument "receive_answer") in
  let state = get_agent_state agent states in
  let state1, answers_to_return =
    match labeled_answer with
      New_answer answer -> (* Case 1 *)
	receive_new_answer agent answer spec state
    | Revised_answer (answer, previous_answer_id) -> (* Case 2 *)
	receive_revised_answer agent answer previous_answer_id spec
	  state in
  (replace_agent_state state1 states, answers_to_return)

(** Miscellaneous *)

let create_initial_agent_states (system: multiagent_system):
    agent_state list =
  let Multiagent_system (specs, _) = system in
  List.map
    (fun (agent, spec) ->
      let answers =
	List.fold_left
	  (fun answers (pre_atom, agent) ->
	    let answers1 =
	      List.fold_left
		(fun answers answer_id ->
		  let o_answer =
		    {a_pre_atom = pre_atom;
		    a_agent = agent;
		    a_id = answer_id;
		    a_bindings = [];
		    a_fd_constr = create_true_fd_constraint
			(get_argument_variables_from_pre_atom
			  pre_atom);
		    a_process_ids = []} in
		  o_answer :: answers)
		answers
		[Speculative_original_answer;
		Nonspeculative_original_answer] in
	    List.fold_left
	      (fun answers (Default (id, head, _, fd_constr)) ->
		let d_answer =
		  {a_pre_atom = head;
		  a_agent = agent;
		  a_id = Default_answer id;
		  a_bindings = [];
		  a_fd_constr = fd_constr;
		  a_process_ids = []} in
		d_answer :: answers)
	      answers1
	      (get_defaults_on_askable_atom pre_atom agent spec))
	  [] (get_all_askable_atoms spec) in
      {s_agent = agent;
      s_answers = answers;
      s_labeled_processes = [];
      s_next_process_id = 1;
      s_next_answer_application_id = 1})
    specs

let send_query (sender: agent) (remote_goal: atom)
    (states: agent_state list):
    agent_state list =
  match remote_goal with
    Askable (goal, Internal_agent agent_name) ->
      let state = get_agent_state (Internal_agent agent_name)
	states in
      let next_process_id = state.s_next_process_id in
      let new_process =
	{p_id = next_process_id;
	p_bindings = [];
	p_domains = get_domains_from_pre_atom goal;
	p_fd_constrs = [];
	p_goal = [Nonaskable goal];
	p_awaited_atoms = [];
	p_assumed_atoms = [];
	p_initial_goal = goal;
	p_initial_goal_sender = sender} in
      let state1 = {state with
	s_labeled_processes = (Ordinary_process new_process)
	  :: state.s_labeled_processes;
	s_next_process_id = next_process_id + 1} in
      replace_agent_state state1 states
  | _ ->
      raise (Invalid_argument "send_query")

(**
   Interactive driver
*)

type answer_queue =
    {q_receiver: agent;
    q_sender: agent;
    q_labeled_answers: labeled_answer list}

type external_answer_queue =
    {e_pre_atom: pre_atom;
    e_agent: agent;
    e_answers: (int * fd_constr) list}

let add_labeled_answer_to_queues (receiver: agent)
    (labeled_answer: labeled_answer)
    (answer_queues: answer_queue list):
    answer_queue list =
  let answer = get_unlabeled_answer labeled_answer in
  let sender = answer.a_agent in
  let rec iterate =
    function
      [] ->
	raise Not_found
    | queue :: rest_queues ->
	if (queue.q_receiver = receiver) && (queue.q_sender = sender)
	then
	  let updated_queue = {queue with
	    q_labeled_answers = labeled_answer
	      :: queue.q_labeled_answers} in
	  updated_queue :: rest_queues
	else queue :: (iterate rest_queues) in
  try
    iterate answer_queues
  with Not_found ->
    let new_queue =
      {q_receiver = receiver;
      q_sender = sender;
      q_labeled_answers = [labeled_answer]} in
    new_queue :: answer_queues

let delete_labeled_answer_from_queues (receiver: agent)
    (sender: agent) (answer_queues: answer_queue list):
    labeled_answer * answer_queue list =
  let rec iterate =
    function
      [] ->
	raise Not_found
    | queue :: rest_queues ->
	if (queue.q_receiver = receiver) && (queue.q_sender = sender)
	then
	  let last_element, updated_list = remove_last_element
	    queue.q_labeled_answers in
	  let updated_queue = {queue with
	    q_labeled_answers = updated_list} in
	  (last_element, updated_queue :: rest_queues)
	else
	  let labeled_answer, updated_queues = iterate rest_queues in
	  (labeled_answer, queue :: updated_queues) in
  iterate answer_queues

let register_external_answers (pre_atom: pre_atom) (agent: agent)
    (answers: (int * fd_constr) list)
    (external_answer_queues: external_answer_queue list):
    external_answer_queue list =
  let external_answer_queue =
    {e_pre_atom = pre_atom;
    e_agent = agent;
    e_answers = answers} in
  external_answer_queue :: external_answer_queues

let rec get_external_answer_queue (pre_atom: pre_atom) (agent: agent)
    (external_answer_queues: external_answer_queue list):
    external_answer_queue =
  match external_answer_queues with
    [] ->
      raise Not_found
  | queue :: rest_queues ->
      if (queue.e_agent = agent)
	&& (is_pre_atom_equal queue.e_pre_atom pre_atom)
      then queue
      else get_external_answer_queue pre_atom agent rest_queues

let get_receivable_answers (answer_queues: answer_queue list):
    (agent * agent) list =
  List.rev
    (flat_map
      (fun queue ->
	match queue.q_receiver with
	  Root_caller ->
	    []
	| _ ->
	    if queue.q_labeled_answers == []
	    then []
	    else [queue.q_receiver, queue.q_sender])
      answer_queues)

let print_receivable_answers
    (receivable_answers: (agent * agent) list):
    unit =
  Printf.printf "Receivable answers (receiver sender):\n";
  if receivable_answers == []
  then Printf.printf "none\n"
  else Printf.printf "%s\n"
    (string_of_list
      (fun (receiver, sender) ->
	(string_of_agent receiver) ^ " " ^ (string_of_agent sender))
      ", " receivable_answers)

let get_reducible_processes (states: agent_state list):
    (agent * int) list =
  flat_map
    (fun state ->
      List.rev
	(flat_map
	  (function
	    Ordinary_process process ->
	      if process.p_awaited_atoms == []
	      then [state.s_agent, process.p_id]
	      else []
	  | Finished_process _ ->
	      [])
	  state.s_labeled_processes))
    states

let print_reducible_processes
    (reducible_processes: (agent * int) list):
    unit =
  Printf.printf "Reducible processes (agent pid):\n";
  if reducible_processes == []
  then Printf.printf "none\n"
  else Printf.printf "%s\n"
    (string_of_list
      (fun (agent, process_id) ->
	(string_of_agent agent) ^ " " ^ (string_of_int process_id))
      ", " reducible_processes)

let print_answers_and_labeled_processes (agent: agent)
    (states: agent_state list):
    unit =
  let state = get_agent_state agent states in
  Printf.printf "Answer entries:\n";
  List.iter
    (fun answer ->
      if answer.a_process_ids != []
      then Printf.printf "%s\n" (string_of_answer answer))
    (List.rev state.s_answers);
  let o_processes, f_processes = split_labeled_processes
    state.s_labeled_processes in
  let print_processes processes =
    List.iter
      (fun process ->
	Printf.printf "%s\n"
	  (string_of_process (simplify_process process)))
      (List.rev processes) in
  Printf.printf "Ordinary processes:\n";
  print_processes o_processes;
  Printf.printf "Finished processes:\n";
  print_processes f_processes

let execute_process_reduction_step (agent: agent) (process_id: int)
    (system: multiagent_system)
    (external_answer_queues: external_answer_queue list)
    (states: agent_state list) (answer_queues: answer_queue list):
    agent_state list * answer_queue list =
  let states1, answer_to_return, query_to_send =
    reduce_ordinary_process agent process_id system states in
  let queues1 =
    if answer_to_return == []
    then answer_queues
    else
      let receiver, labeled_answer = List.hd answer_to_return in
      Printf.printf "Agent %s returned to %s the %s answer:\n%s\n\n"
	(string_of_agent agent) (string_of_agent receiver)
	(string_of_labeled_answer_type labeled_answer)
	(string_of_labeled_answer labeled_answer);
      add_labeled_answer_to_queues receiver labeled_answer
	answer_queues in
  let states2, queues2 =
    if query_to_send = []
    then (states1, queues1)
    else
      let atom = List.hd query_to_send in
      Printf.printf "Agent %s asked: %s\n\n"
	(string_of_agent agent) (string_of_atom atom);
      match atom with
	Askable (_, Internal_agent _) ->
	  (send_query agent atom states1, queues1)
      | Askable (pre_atom, External_agent external_agent_name) ->
	  (try
	    let external_answer_queue = get_external_answer_queue
	      pre_atom (External_agent external_agent_name)
	      external_answer_queues in
	    let queues2 =
	      List.fold_left
		(fun queues (id, fd_constr) ->
		  let answer =
		    {a_pre_atom = external_answer_queue.e_pre_atom;
		    a_agent = External_agent external_agent_name;
		    a_id = Ordinary_answer id;
		    a_bindings = [];
		    a_fd_constr = fd_constr;
		    a_process_ids = []} in
		  let labeled_answer =
		    let first_fd_constr = List.assoc id
		      external_answer_queue.e_answers in
		    if first_fd_constr == fd_constr
		    then New_answer answer
		    else Revised_answer (answer, Ordinary_answer id) in
		  Printf.printf
		    "Agent %s returned to %s the %s answer:\n%s\n\n"
		    external_agent_name (string_of_agent agent)
		    (string_of_labeled_answer_type labeled_answer)
		    (string_of_labeled_answer labeled_answer);
		  add_labeled_answer_to_queues agent labeled_answer
		    queues)
		queues1 external_answer_queue.e_answers in
	    (states1, queues2)
	  with Not_found ->
	    (states1, queues1))
      | _ ->
	  raise (Failure "execute_process_reduction_step") in
  (states2, queues2)

let execute_answer_receipt_step (receiver: agent) (sender: agent)
    (system: multiagent_system)
    (external_answer_queues: external_answer_queue list)
    (states: agent_state list) (answer_queues: answer_queue list):
    agent_state list * answer_queue list =
  let labeled_answer, queues1 = delete_labeled_answer_from_queues
    receiver sender answer_queues in
  let states1, answers_to_return = receive_answer receiver
    labeled_answer system states in
  let queues2 =
    List.fold_right
      (fun (further_receiver, labeled_answer) queues ->
	Printf.printf "Agent %s returned to %s the %s answer:\n%s\n\n"
	  (string_of_agent receiver)
	  (string_of_agent further_receiver)
	  (string_of_labeled_answer_type labeled_answer)
	  (string_of_labeled_answer labeled_answer);
	add_labeled_answer_to_queues further_receiver labeled_answer
	  queues)
      answers_to_return queues1 in
  (states1, queues2)

let rec read_eval_print (system: multiagent_system)
    (external_answer_queues: external_answer_queue list)
    (states: agent_state list) (answer_queues: answer_queue list):
    unit =
  let receivable_answers = get_receivable_answers answer_queues in
  let reducible_processes = get_reducible_processes states in
  Printf.printf "SELECT NEXT STEP\n";
  print_reducible_processes reducible_processes;
  print_receivable_answers receivable_answers;
  Printf.printf "Which step?\n";
  let states1, queues1 =
    let line = read_line () in
    (try
      (* Process reduction phase *)
      let agent_name, process_id =
	Scanf.sscanf line "%s %d"
	  (fun agent_name process_id -> (agent_name, process_id)) in
      if List.exists
	(fun (agent, pid) ->
	  ((get_agent_name agent) = agent_name) && (pid = process_id))
	reducible_processes
      then
	(print_newline ();
	let agent = Internal_agent agent_name in
	let states1, queues1 = execute_process_reduction_step agent
	  process_id system external_answer_queues states
	  answer_queues in
	print_answers_and_labeled_processes agent states1;
	(states1, queues1))
      else
	(Printf.printf "Invalid command.\n";
	(states, answer_queues))
    with Scanf.Scan_failure _ ->
      (* Fact arrival phase *)
      let receiver_name, sender_name =
	Scanf.sscanf line "%s %s"
	  (fun receiver_name sender_name ->
	    (receiver_name, sender_name)) in
      if List.exists
	(fun (receiver, sender) ->
	  ((get_agent_name receiver) = receiver_name)
	  && ((get_agent_name sender) = sender_name))
	receivable_answers
      then
	(print_newline ();
	let receiver = Internal_agent receiver_name in
	let sender =
	  if is_internal_agent sender_name system
	  then Internal_agent sender_name
	  else External_agent sender_name in
	let states1, queues1 = execute_answer_receipt_step receiver
	  sender system external_answer_queues states
	  answer_queues in
	print_answers_and_labeled_processes receiver states1;
	(states1, queues1))
      else
	(Printf.printf "Invalid command.\n";
	(states, answer_queues))) in
  print_newline ();
  read_eval_print system external_answer_queues states1 queues1
