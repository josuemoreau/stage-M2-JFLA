Require Import Syntax BEnv BValues BMemory.

Definition extcall_sem : Type :=
  mem -> list value -> value -> mem -> Prop.

Parameter external_functions_sem: String.string -> signature -> extcall_sem.

Section EXTERNAL_FUNCTION_CALLS.

Definition external_call (ef: external_function) : extcall_sem :=
  match ef with
  | EF_external name sig => external_functions_sem name sig
  end.

End EXTERNAL_FUNCTION_CALLS.
