## Worker report

The module `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear` states
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_linear` with a single
`sorry` proof. Its auxiliary definition `kInjectiveDerivedRepresentativeIso` constructs
exactly the comparison c_M in the node, with real data from the recorded derived unit.
No new nodes, dependency repairs, or statement corrections are needed. Only the item's
`lean` record changes.

Sources read: `literature/stacks-project/derived.tex`, `lemma-K-injective` (Tag 070I),
especially equivalence (1)/(3), and `lemma-K-injective-defined` (070Y) and
`lemma-enough-K-injectives-implies` (070K). The node explicitly extracts scalar linearity
from the Hom comparison and naturality; it does not claim that 070I literally states
scalar linearity. All five steps of the node's proof are reproduced in the theorem's
docstring for stage 3.

Hypothesis and clause correspondence:

- The arbitrary commutative ring is `(R : Type r) [CommRing R]`.
- The two abelian categories are `{A : Type uA} {B : Type uB}` with independently
  sized `[Category.{vA} A]`, `[Category.{vB} B]`, `[Abelian A]`, `[Abelian B]`.
  The scalar structures are `[CategoryTheory.Linear R A]` and
  `[CategoryTheory.Linear R B]`, using their existing abelian preadditive structures.
- Existence in the chosen derived morphism universes is expressed by independent
  `[HasDerivedCategory.{wA} A]` and `[HasDerivedCategory.{wB} B]`. Mathlib's
  `DerivedCategory.Linear` supplies the induced structures and linear Q and Qh.
- The resolution hypothesis is `enough : ∀ K : CochainComplex A ℤ, ∃ I s,
  I.IsKInjective ∧ QuasiIso s`. The full type in the module explicitly binds I and s.
  There is no monomorphism requirement. `CochainComplex.IsKInjective` says precisely
  that every map from an acyclic complex is homotopic to zero.
- The original functor is `(U : A ⥤ B) [U.Additive] [U.Linear R]`. No exactness or
  preservation-of-limits assumption is made. `U.mapHomotopyCategory (.up ℤ)` is U_K.
- RU and eta are the recorded
  `U.rightDerivedFunctorOfQuasiIsoResolutions enough` and
  `U.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough`. That dependency's universal
  property and unit characterize the pair up to its unique compatible isomorphism;
  the statement uses this defined pair, with no alternative definition of derivation.
- Additivity of RU is the first conjunct `.Additive`; its field `map_add` is exactly
  the node's first equality for every pair of parallel derived morphisms.
- Scalar linearity is the second conjunct `Functor.Linear R (...)`; `map_smul`
  is exactly the node's second equality for every scalar and derived morphism.
  Mathlib's `Functor.Linear` alone only specifies scalar compatibility, so the
  independent additive conjunct is deliberately retained.
- Every derived object is covered by `(M N : DerivedCategory A)`. Every specified
  K-injective representative is covered by `(I J : CochainComplex A ℤ)` and the two
  `IsKInjective` binders. The two isomorphisms `qM`, `qN` have exactly source M, N
  and target Qh of the corresponding quotient complex; there is no restriction
  that M or N be syntactically the localization of an input complex.
- `kInjectiveDerivedRepresentativeIso` is `RU.mapIso q` followed by the inverse of
  `asIso (eta.app (quotient.obj I))`. Its definition installs the dependency's
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso` theorem as an instance.
  Thus it is exactly c_M = eta_I inverse after RU(q_M), and its target is Q_B U_K(I).
- For every `(f : M ⟶ N)`, the third conjunct first asserts `∃! g` with
  `DerivedCategory.Qh.map g = qM.inv ≫ f ≫ qN.hom`. Lean's `≫` is composition in
  traversal order, so this is precisely q_N h q_M inverse in the node's notation.
- The following universal implication gives the representative formula for every
  lift satisfying that equation, independently of the uniqueness assertion. Its
  left side is `c_M.inv ≫ RU.map f ≫ c_N.hom`; its right side is
  `DerivedCategory.Qh.map ((U.mapHomotopyCategory (.up ℤ)).map g)`.
  This is exactly c_N RU(h) c_M inverse = Q_B(U_K(g)). In particular uniqueness
  concerns the lift equation itself, not a conjunction with the conclusion.
- No additive, linear or functorial choice of resolutions is supplied. `enough` is
  just the source's existence hypothesis. No boundedness is imposed.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`: the induced linear structures
  on the derived category and the instances for Q, Qh and shifts.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `rightDerivedFunctorOfQuasiIsoResolutions`, its `Unit`, its `_universal` and
  `_unique` specifications, and `rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso`.
  The existing `ObjIso` takes an actual complex resolution map, whereas the current
  node specifies arbitrary isomorphisms from derived objects. The auxiliary
  representative comparison therefore uses the same unit directly.
- Proof dependency `lem-weil-pbc-kinjective-hom-derived` is imported from
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, with declaration
  `CochainComplex.IsKInjective.Qh_map_bijective`. Its signature and the definition
  of `IsKInjective` in `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` were read.

Edge cases checked mathematically and by inspecting the statement: the zero ring,
zero objects and zero maps, zero original functor, identity representatives, arbitrary
nonidentity representative isomorphisms, and unbounded complexes are all included.
Independent object, Hom, scalar, and derived-localization universes remain independent.
No nonempty index hypothesis, injective-terms hypothesis, monomorphic resolution map,
or exactness of U has been inserted. There is no statement dispute.

Searches actually run with `msearch.py` for this group and item:

- LeanFinder: "An additive R-linear functor between abelian categories has an R-linear
  total right derived functor computed by K-injective resolutions". Eight results,
  including `Functor.instLinearDerivedCategoryMapDerivedCategory`, Q/Qh linearity,
  ordinary `rightDerived`, and `mapDerivedCategory`. None states this theorem.
  The source `DerivedCategory/ExactFunctor.lean` confirms that the induced
  `mapDerivedCategory` instance assumes exactness of the original functor; it cannot
  replace this result for arbitrary additive U.
- Loogle: `CategoryTheory.Functor.Linear, CategoryTheory.Functor.totalRightDerived`.
  Zero hits.
- Grep: `Linear|linear|map_smul`, subdirectory `CategoryTheory/Functor/Derived`.
  Zero hits.
- Local `rg` over both `lean/WeilConjectures` and `lean/Sheaf`:
  `kinjective-total-derived-linear|rightDerived.*[Ll]inear|[Ll]inear.*rightDerived|totalRightDerived`.
  Results include specialized sheaf direct-image linearity and general derived
  constructions, but no theorem combining the generic linearity and arbitrary
  representative formula. `RingedDerivedPushforwardLinear.lean` was read: it is
  specialized to ringed topoi and scalar sections. `KInjectiveDerivedMapComputation.lean`
  was read: its formula requires complexes and actual resolution maps, and it does
  not assert scalar linearity. Neither is an exact match for this node.
- `grep -rn 'lem-weil-kinjective-total-derived-linear' lean/WeilConjectures`: no hits.
- `rg` for both proposed declaration names over Mathlib, `WeilConjectures`, and
  `Sheaf`: no hits before creating the sandbox module.

Validation: the prescribed `scompile.py` compiled both the sandbox presentation and
library module on the live server, cleanly, in 4.5 s and 7.0 s respectively. No warning
was emitted. All universes and variables are explicitly bound; the only theorem in
this delivery has `sorry` as its entire proof. No proofs were added.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
