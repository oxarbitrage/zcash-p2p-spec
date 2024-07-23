-------------------------------- MODULE Utils -------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets


\* Utilities from the community modules:

(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class Functions.java   *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

SetToSeq(S) == 
(**************************************************************************)
(* Convert a set to some sequence that contains all the elements of the   *)
(* set exactly once, and contains no other elements.                      *)
(**************************************************************************)
CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

=============================================================================
