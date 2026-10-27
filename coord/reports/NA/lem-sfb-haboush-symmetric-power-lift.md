## Worker report

The module Sheaf.RepresentationTheory.HaboushSymmetricPowerLift states
AlgebraicGeometry.RationalRepresentation.exists_invariant_symmetric_power_lift.
Its sole theorem has the required `sorry` proof; no definitions or additional axioms
are introduced. The natural-language statement, proof plan, and proof dependencies
are unchanged. Three already landed definition nodes are added to stmt_deps: the reductive
terminology, Hopf-action module data, and canonical coordinate Hopf algebra.

Clause-by-clause correspondence:

- The arbitrary field is `{k : Type u} [Field k]`. There is no characteristic or
  algebraic-closedness binder.
- The k-group scheme is `(H : Scheme.{u}) [H.Over (Spec (.of k))]` with
  `[GrpObj (H.asOver (Spec (.of k)))]`. This is the recorded def-sc-group-scheme
  interface, described in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Reductivity is `hH : ReductiveTorusCentralizer.IsReductive (Grp.mk ...)`.
  Its definition requires affine finite type, smoothness, connectedness after
  algebraic closure, and triviality of every smooth connected normal closed
  unipotent subgroup after that extension. IsUnipotent is the recorded smooth,
  faithful closed-matrix representation predicate, testing nilpotence over all
  algebraically closed extensions. The explicit `[IsAffine H]` exposes the
  coordinate Hopf instance and is already implied by hH; thus it excludes no H.
- V is a vector space in independent universe v, with `[AddCommGroup V]`,
  `[Module k V]`, and `[FiniteDimensional k V]`.
- The rational action is the linear map `ρ : V →ₗ[k] V ⊗[k] Γ(H, ⊤)` and the two
  hypotheses `HopfAction.Coassociative ... ρ` and `HopfAction.Counital ... ρ`.
  These reuse the existing laws, including their actual tensor associator and
  right-unit equivalence, and the canonical Hopf algebra on the global sections.
- The quotient is `ell : V →ₗ[k] k`; `hell` requires
  `Function.Surjective ell`. Equivariance is `heq`: on every v,
  `(ell tensor id)(ρ v) = ell(v) tensor 1`, exactly the trivial target coaction.
- The witnesses are `N : ℕ`, `q : SymmetricAlgebra k V`, with `0 < N`.
- Membership `q ∈ (SymmetricAlgebra.ι k V).range ^ N` is the degree-N component:
  the submodule spanned by N-fold products of generators, exactly the component
  described by products of the generator range in Mathlib. An ambient element plus membership is the same object as a
  subtype element of Sym^N(V); it changes no existence assertion.
- The induced coaction is the actual algebra map `SymmetricAlgebra.lift
  ((SymmetricAlgebra.ι k V).rTensor Γ(H, ⊤) ∘ₗ ρ)`. On a generator v it is
  `(iota tensor id)(ρ v)`; multiplicativity gives the prescribed symmetric
  coaction. Its equality on q to `q tensor 1` expresses scheme-theoretic
  invariance, including nilpotent test algebras, rather than invariance on H(k).
  Since the degree inclusion is injective and tensoring over k is exact, testing
  the identity in the full symmetric algebra is equivalent to testing in Sym^N.
- `SymmetricAlgebra.lift ell q = 1` evaluates every generator v at ell(v).
  On the degree-N component this is precisely Sym^N(ell), followed by the
  canonical Sym^N(k) to k map sending the N-fold product of 1 to 1.

Recorded dependencies read and used:

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field).
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` and `Grp`, read
  together with WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`, with its underlying
  `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent` definitions read in full.
- Sheaf.RingTheory.HopfActionModuleData: `HopfAction.Coassociative` and `Counital`.
- Sheaf.AlgebraicGeometry.HopfCoactionLinearization:
  `HopfAction.coordinateHopfAlgebra`, owned by def-sfb-coordinate-hopf-algebra
  (canonical, not an arbitrary Hopf structure). No coaction-linearization theorem
  conclusion is used.
- Mathlib.LinearAlgebra.SymmetricAlgebra.Basic:
  `SymmetricAlgebra`, `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift`.
- Proof imports: Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure (`AlgebraicClosure`),
  Mathlib.LinearAlgebra.Matrix.Determinant.Basic (`Matrix.det`), and
  WeilConjectures.LinearAlgebra.Matrix.CauchyBinet (`Matrix.cauchy_binet`).
  The cover and Steinberg-detection proof nodes have no recorded Lean module in
  the read snapshot, so there is no module to import for them.

Source checked online: Alper, arXiv:1005.2398v3,
https://arxiv.org/html/1005.2398v3, Lemma 9.2.5(5-prime), Lemma 9.2.8(1),(2),(6),
and Theorem 9.7.5. The local Alper PDF is absent, as already recorded by the node.
The theorem docstring records all seven proof steps, including torus projection,
normalization of the endomorphism-valued map, determinant invariance, and explicit
coefficient descent. No change to the source theorem is needed.

Edge cases checked before writing: V = 0 admits no surjection to the nonzero
field, so no additional nonzero hypothesis is necessary. N = 0 is excluded
explicitly (otherwise the constant 1 would trivialize the result). For the
trivial group any preimage of 1 gives degree 1. Finite fields, nonperfect fields,
characteristic p dividing N!, rank-zero tori, and the trivial semisimple factor
remain included. Coordinate invariance does not pass to a mere point action.
The field and vector-space universes are separately bound.

Searches (2026-10-24):

- msearch.py leanfinder, query "Haboush reductive algebraic group invariant
  symmetric power lifts a surjection of finite dimensional rational
  representations to the trivial module": eight hits, all unrelated
  abstract-group coinvariants/projectivity/averaging results; no match.
- msearch.py loogle, query "SymmetricAlgebra.lift, SymmetricAlgebra.gradedAlgebra":
  zero hits, unknown identifier SymmetricAlgebra.gradedAlgebra.
- msearch.py loogle, query '"SymmetricAlgebra.lift"': eight hits, including
  the exact universal extension API SymmetricAlgebra.lift and lift_ι_apply.
- msearch.py grep, query "Haboush|[Rr]eductive|[Ss]ymmetric.*[Cc]oaction" in
  Mathlib/RepresentationTheory: zero hits.
- rg on Mathlib Coalgebra/HopfAlgebra and SymmetricAlgebra sources: no existing
  Haboush or symmetric-coaction lifting theorem; the free commutative algebra
  and its universal extension already exist and are reused directly.
- rg on lean/WeilConjectures for the item id: zero hits. rg for Haboush,
  invariant_symmetric_power_lift, symmetric.*coaction in lean/WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: only downstream mentions of
  Haboush in PGLGeometricReductivity and ProjectivePGLStableQuotient, no declaration.
- rg for reductive/coaction terminology in DAG and project Lean identified the
  landed reductive and Hopf-action definitions cited above. The grading theorem
  was read for comparison, but is not a statement dependency or import.
  The rational-comodule dictionary was read, but its CoordinateComodule alias
  ties the vector-space universe to the field universe; the present statement
  instead uses its existing underlying HopfAction laws directly, preserving
  arbitrary vector-space universes without duplicating the notion.

No STATEMENT-DISPUTED issue, new node, dependency repair, or statement correction.

## Second reading by NA

A second in-thread reading compared the node text with the final theorem and
its imported definitions. It checked every hypothesis and conclusion against
the correspondence above, especially positive degree, the degree component,
canonical induced coaction, trivial quotient coaction, and evaluation at 1.
The initial draft used the fixed-universe CoordinateComodule alias; this was
replaced by its existing coassociativity and counit laws on an independently
sized V. The Lean keyword lambda was replaced by the identifier ell. No
mathematical clause changed. The added affine instance is redundant with hH
and merely exposes canonical coordinate data. There is one postponed theorem
and no postponed data. No independent agent was started, as the dispatcher
brief prohibits delegation; the maintainer supplies the independent review.

## Returned-delivery repair

Repaired both points in L's review of immutable head eadf38e20975:

1. Replaced lem-sfb-hopf-coaction-linearization in stmt_deps with the landed
   definition node def-sfb-coordinate-hopf-algebra. Read that node and its
   recorded instance in Sheaf.AlgebraicGeometry.HopfCoactionLinearization.
   The public import remains the same because this is the owning declaration's
   module. No conclusion of the coaction-linearization theorem is assumed.
2. Removed lem-weil-pbc-symmetric-algebra-graded from stmt_deps and removed its
   public module import. Added the direct public import of
   Mathlib.LinearAlgebra.SymmetricAlgebra.Basic for the symmetric algebra and
   universal extension used by the signature. The grading theorem is not used
   in the supplied proof plan, so it was not added to proof_deps.

Compared the retained sandbox to the current main node: its mathematical
statement and proof dependencies agree, and main has no Lean record yet.
The delivery wrapper rebases the repaired packet onto current main.
The theorem signature is byte-for-byte equal to the retained lean.statement
from the returned delivery; no hypotheses, witnesses or conclusions changed.
Second in-thread reading verified both dependency repairs and this equality.

Validation of this repaired packet: scompile.py passed for both sandbox and
final library module with no errors or warnings. deliver2.py --no-push returned
OK for repaired commit 6ad41339c0d: preflight and compilation passed.
