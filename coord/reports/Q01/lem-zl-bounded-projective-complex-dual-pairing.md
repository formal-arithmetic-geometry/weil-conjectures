## Worker report

The delivery states `CochainComplex.boundedProjectiveComplexDualPairing`, with `sorry`,
from Stacks Project, More on Algebra, Tag 0FNK, converse of `lemma-left-dual-complex`.
The proof docstring includes all five DAG proof steps, including the dual-basis
calculation proving coevaluation is a chain map. No definition has postponed data.
There are no new nodes, dependency repairs, or statement corrections.

Hypothesis and conclusion correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`. No nonzero or characteristic assumption.
- An integer cochain complex: `P : CochainComplex (ModuleCat.{u} A) ℤ`.
- Integers a ≤ b: `(a b : ℤ) (hab : a ≤ b)`.
- Zero outside [a,b]: `hP : ∀ n, n < a ∨ b < n → IsZero (P.X n)`.
- Finitely generated and projective terms: the two dependent instance binders
  `[∀ n, Module.Finite A (P.X n)]` and `[∀ n, Module.Projective A (P.X n)]`.
- The explicit dual complex is expressed as an existential complex D together with
  degree identifications `e n : D.X (-n) ≅ ModuleCat.of A (Module.Dual A (P.X n))`.
  These identifications are part of the conclusion, not additional hypotheses.
  This is the usual bundled-category rendering of the displayed Hom modules: all
  subsequent formulas are transported through precisely these identifications.
  Every degree is covered since n ↦ -n is a bijection of ℤ.
- The differential equality for every n,m identifies `D.d (-n) (-m)` with
  `(e n).hom ≫ ofHom ((-m).negOnePow • (P.d m n).hom.dualMap) ≫ (e m).inv`.
  At consecutive dual degrees k,k+1, substitute n=-k, m=-k-1. Its sign is
  `(-m).negOnePow = (k+1).negOnePow`, and `dualMap` is precomposition with
  `P.d (-k-1) (-k)`, exactly the prescribed differential. Nonconsecutive entries
  are zero because P is already a complex. Being a cochain complex, D includes
  the square-zero property rather than leaving it unstated.
- D is zero outside [-b,-a]: the next universal `IsZero` clause.
- Each D term is finite projective: the next universal conjunction of
  `Module.Finite` and `Module.Projective`.
- The direct-sum total tensor is Mathlib's monoidal tensor on homological complexes,
  whose `tensorObj` is definitionally `HomologicalComplex.mapBifunctor` for
  `curriedTensor`. The imported BifunctorShift module supplies the cochain alias
  recorded for `def-pc-tensor-complex-sheaves`. The same algebraic construction
  applies to ordinary modules; no sheaf-category replacement is made.
- The unit `𝟙_ (CochainComplex (ModuleCat A) ℤ)` is the single complex A[0].
  `HomologicalComplex.singleObjXSelf` identifies its degree zero with A.
- Evaluation and coevaluation are actual complex morphisms `ε : D ⊗ P ⟶ 𝟙_ _`
  and `η : 𝟙_ _ ⟶ P ⊗ D`. Chain-map compatibility is built into their type.
- Evaluation on the summand D^(-n) tensor P^n is specified by the equality using
  `ιTensorObj D P (-n) n 0`, `(e n).hom ▷ P.X n`, and
  `LinearMap.finiteProjectiveEvaluation A (P.X n)` from the recorded dependency.
  This dependency is the actual contraction phi tensor x ↦ phi(x).
- Coevaluation in degree zero is exactly the sum over `Finset.Icc a b` of
  `finiteProjectiveCoevaluation` followed by `P.X n ◁ (e n).inv` and the
  corresponding total-tensor summand inclusion. The module dependency sends 1
  to the inverse image of the identity under its canonical tensor-End equivalence.
  Since P vanishes outside the bounds, its other summands vanish; specifying the
  sum determines every degree-zero component, including the zero components.
- Both maps in all other degrees are explicitly zero: `n ≠ 0 → ε.f n = 0 ∧ η.f n = 0`.
- The last two equalities spell out the two triangle identities with the canonical
  associator and unitors, first on P, then on D. The tensor orders agree with the node.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and its underlying integer `CochainComplex` interface.
  The present statement is at the complex level and needs no localization assumption.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`.
- `Mathlib.Algebra.Homology.Monoidal`: `HomologicalComplex.tensorObj`,
  `ιTensorObj`, `tensorUnit`, and its canonical monoidal structure.
- `Sheaf.ZetaWeil.FiniteProjectiveModuleDualPairing`:
  `LinearMap.finiteProjectiveModuleDualPairing`, `finiteProjectiveEvaluation`,
  `finiteProjectiveCoevaluation`, and `finiteProjectiveTensorEndEquiv`.
  The latter is tensor commutation followed by `dualTensorHomEquiv`.

Searches performed with the required msearch wrapper on 2026-10-18:

- LeanFinder: “A bounded complex of finite projective modules has an explicit dual
  complex with evaluation coevaluation satisfying triangle identities”: eight hits,
  including `Module.dual_projective`, `dual_finite`, reflexivity, FGModuleCat duality
  over fields, and K-projectivity. None states the complex-level assertion.
- Loogle: `CochainComplex, CategoryTheory.ExactPairing`: zero hits.
- Mathlib grep: `exactPairingRightDual|bounded.*dualizable|dualizable.*bounded`:
  zero hits.
- LeanSearch: “A bounded complex of finite projective modules has a dual complex
  with evaluation and coevaluation”: eight hits, including module finiteness,
  projectivity and FGModuleCat exact pairings; none is the assertion over a ring.
- Source/project rg: the node id, `exactPairing.*[Cc]omplex`, and `bounded.*[Dd]ual`
  in WeilConjectures and lean/Sheaf found the upstream
  `WeilConjectures.Algebra.Homology.Monoidal.Dual`. I read the whole file.
  `CochainComplex.exactPairingRightDual` constructs a pairing from already supplied
  `HasRightDual` structures on all terms. It does not supply finite-projective
  ModuleCat pairings or state their Hom identifications and termwise finiteness.
  It is therefore not an exact existing declaration for this node. This delivery
  does not copy its dual construction; the only declaration is the theorem
  asserting the fully characterized module dual exists.
- Source and Mathlib rg of `HasRightDual|ExactPairing|isDualizable|rightDual` in
  ModuleCat found no applicable finite-projective module pairing structure.
- Exact-name rg in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures, and
  lean/Sheaf found no declaration `boundedProjectiveComplexDualPairing`.

Edge cases checked mathematically against the formulas: the zero ring; zero
complex; singleton interval a=b; a rank-one module in an arbitrary integer
(including odd and negative) degree; zero terms at either endpoint; and a
complex in two adjacent degrees with a nonzero differential. The dual
sign is (-1)^(k+1), evaluation cancels the two signs, and coevaluation uses
no supertrace sign. Rank-one coevaluation in degree n is 1 tensor dual(1),
and both triangles are the identity also for odd n. All support endpoints
are inclusive and the dual bounds are reversed. No field, basis, freeness,
Noetherianity or characteristic restriction has been added. The shared module
universe is the existing ModuleCat monoidal convention; u is arbitrary, so
any ring and module family can be placed in a common universe.

## Second reading by Q01

This is the dispatcher's worker self-check; independent delivery review is left
to the maintainer, as prescribed by the brief. I reopened the node, Stacks 0FNK,
the recorded finite-projective module dependency, and the final Lean signature.
I checked all the correspondences above against the actual binders and conjuncts.
In particular the differential is indexed at -n,-m, so its sign must be -m,
not n or m; at output k+1 it is exactly (-1)^(k+1). Evaluation's tensor order
is D then P; coevaluation's order is P then D; the first associator is forward
and the second is inverse. The degree-zero unit is converted by the forward
singleObjXSelf map in both formulas. The coevaluation sum determines the
components outside [a,b] to be zero. No claim of an arbitrary uncharacterized
pairing is used. No statement mismatch or source correction was found.

Compilation uses the required scompile.py wrapper. The monoidal prerequisites are supplied
by ModuleCat.Colimits, ModuleCat.Monoidal.Closed, and Monoidal.Closed.Braided; these
provide the actual coproducts and their preservation by both tensor factors.
