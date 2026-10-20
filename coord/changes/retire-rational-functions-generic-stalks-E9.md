# AlgebraicGeometry.Scheme.rationalFunctions_generic_stalks

## Reason

Retirement assigned in coord/retire-items.tsv and coord/queue.tsv, under the
human-approved hand-off in coord/changes/retire-sheaf-twins-20261020.md.
The upstream twin already proves exactly the same statement, under the name
AlgebraicGeometry.Scheme.exists_ringEquiv_rationalFunctionRing_pi_stalk.
The old API-difference entry listed the missing old name but missed this renamed theorem.
The earlier RationalFunctions retirement has already unified the underlying dense-open
and colimit definitions, so the two signatures now coincide without any conversion.

## Old

Module lean/Sheaf/AlgebraicGeometry/RationalFunctionsGenericStalks.lean contained:

```lean
theorem rationalFunctions_generic_stalks (X : Scheme.{u}) (n : ℕ) (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X}) (η : Fin n → X) (hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val) : ∃ hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val, ∃ e : (X.rationalFunctionRing : Type u) ≃+* ((i : Fin n) → X.presheaf.stalk (η i)), (∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n), e ((colimit.ι (denseOpenSections X) (op U)) f) i = X.presheaf.germ U.val (η i) (hDense U i) f) ∧ (IsIntegral X → n = 1 ∧ (∀ i : Fin n, (components i).val = Set.univ) ∧ IsField (X.rationalFunctionRing : Type u) ∧ ∀ i : Fin n, IsField (X.presheaf.stalk (η i)) ∧ ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i), ∀ r : X.rationalFunctionRing, ei r = e r i)
```

It also contained the proved private helpers generic_component_opens and
dense_of_generic_mem. Its public imports were Sheaf.AlgebraicGeometry.RationalFunctionRing
and Mathlib.AlgebraicGeometry.Properties.

## New

Withdraw that duplicate module via deleted.txt. Attach
lem-sc-rational-functions-generic-stalks to the existing, unmodified upstream theorem
in WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks:

```lean
theorem exists_ringEquiv_rationalFunctionRing_pi_stalk (X : Scheme.{u}) (n : ℕ) (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X}) (η : Fin n → X) (hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val) : ∃ hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val, ∃ e : (X.rationalFunctionRing : Type u) ≃+* ((i : Fin n) → X.presheaf.stalk (η i)), (∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n), e ((colimit.ι (denseOpenSections X) (op U)) f) i = X.presheaf.germ U.val (η i) (hDense U i) f) ∧ (IsIntegral X → n = 1 ∧ (∀ i : Fin n, (components i).val = Set.univ) ∧ IsField (X.rationalFunctionRing : Type u) ∧ ∀ i : Fin n, IsField (X.presheaf.stalk (η i)) ∧ ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i), ∀ r : X.rationalFunctionRing, ei r = e r i)
```

Update the node's proof description to match the upstream proof. The mathematical
statement, dependency set, and unit route are preserved. No upstream file is changed.
The exact former signature compiles with a one-line application of the upstream theorem.
Both the former-signature check and the upstream theorem have only propext,
Classical.choice, and Quot.sound in their axiom lists.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks | E9 | Retire duplicate theorem and private helpers. |

The downstream script reports zero import consumers and no declaration uses outside
this module. Source search across both library roots confirms this. The DAG parent
def-sc-function-field retains its reference to lem-sc-rational-functions-generic-stalks,
which now resolves to the upstream theorem. No unit statement or step is removed;
sk-def-av-pic has no realized attachment to the retiring module. The upstream import
closure uses its own RationalFunctions module and Mathlib, with no Sheaf twin conflict.

Empty schemes (n = 0), reducible and nonreduced schemes, arbitrary universe u, and the
integral clauses all remain covered by the identical statement. No target or underlying
definition changes meaning; this is a theorem attachment migration.

## Status

landed 20261020T151217-L-2647418 2026-10-20 (merge of deliver/E9/Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks)
