## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ExactTensorFunctorBraiding` states
`CategoryTheory.Functor.exactTensorFunctor_derived_braiding`, with its proof `sorry`.
There are no new definitions, dependency modules, or statement corrections.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-symmetric-monoidal-cat-complexes` (Tag 0FPQ), lines 12935 onwards, and
`lemma-symmetric-monoidal-derived` (Tag 0FPT), lines 13135 onwards. As the node
explicitly says, these supply the native signed symmetry constructions; the
cross-functor assertion is the agent-written calculation in the node, not a
verbatim Stacks assertion. All four proof steps are retained in the theorem docstring.

Hypothesis and clause correspondence:

- The two categories are `C : Type uC` and `D : Type uD`, with independent
  morphism universes `vC`, `vD` and derived localization universes `wC`, `wD`.
  Each has `Abelian`, `IsGrothendieckAbelian`, `MonoidalCategory`,
  `SymmetricCategory`, `MonoidalPreadditive`, `MonoidalClosed`, and
  `Abelian.HasFunctorialFlatResolution`, exactly the abelian, Grothendieck,
  symmetric, additive tensor, closed, and functorial flat-resolution hypotheses.
- Ordinary unbounded derived categories are `DerivedCategory C` and
  `DerivedCategory D`, under the two `HasDerivedCategory` binders. The native
  derived monoidal instances are supplied by `DerivedCategory.hasDerivedMonoidalCategory`;
  no transported or newly chosen tensor product is used.
- Flatness is the existing two-sided `ObjectProperty.flat`, used by
  `F.PreservesFlat`: the defining pair of `exactFunctor` properties says that
  tensoring on either side preserves finite limits and finite colimits, equivalent
  to short-exact-sequence preservation in this abelian additive setting.
- `F : C ⥤ D`, `F.Additive`, `PreservesFiniteLimits F`,
  `PreservesFiniteColimits F`, and `F.IsLeftAdjoint` express the additive exact
  left adjoint. `M : F.CoreMonoidal` is its specified strong monoidal structure,
  without including any braiding hypothesis in that structure.
- `F.PreservesFlat` expresses preservation of flat objects. `hKFlat` expresses
  preservation of every two-sided K-flat complex using the dependency's
  `CochainComplex.IsKFlatForTotalTensor`, not preservation of just bounded or flat-term
  complexes, and not preservation of just K-flat quasi-isomorphisms.
- The termwise functor is `F.mapHomologicalComplex (.up ℤ)`. The natural
  isomorphism `τ` has components from its image of the complex tensor to the
  tensor of the two images. The equation `hτ` specifies its value after each
  image of `HomologicalComplex.ιTensorObj`, for every `p + q = n`, as
  `(M.μIso (P.X p) (Q.X q)).inv` followed by the target summand inclusion.
  Thus it is precisely the comparison induced by the inverse ordinary tensorator,
  rather than an arbitrary tensor comparison. The complex tensor is the existing
  signed direct-sum total tensor; `hτ` does not replace its sign convention.
- `F.mapDerivedCategory` is E; `DerivedCategory.Q` is each complex localization;
  `F.mapDerivedCategoryFactors.hom.app P` is the canonical κ component, with
  the direction E(QP) → Q(FP) prescribed by the node.
- `t` is a Mathlib natural transformation between the two curried tensor
  bifunctors. Its type includes naturality in both variables. This is the
  natural comparison discussed in `lem-pur-derived-tensor-comparison`, quantified
  here with the exact K-flat normalization required by this node. No invertibility
  or derived monoidal structure on E is assumed.
- `hnormalized` quantifies only over K-flat P,Q. Write μC and μD for the native
  localization lax tensorators, so that mC = μC⁻¹ and mD = μD⁻¹ on K-flat pairs.
  It reads `E(μC) ≫ κ(P⊗Q) ≫ Q(τ) = t(QP,QQ) ≫ (κP ⊗ₘ κQ) ≫ μD`.
  Starting from the node's displayed normalization, precompose with E(μC) and
  postcompose with μD; this is exactly the written equation, with no stronger
  all-complex condition. Both μ maps are invertible on these pairs, since the
  images of K-flat complexes are K-flat by `hKFlat`, so this change of form is
  reversible. The model isomorphisms are their canonical inverses, not extra data.
- `hbraided` is precisely the ordinary symmetry square, in Lean's left-to-right
  composition notation: `F.map β.hom ≫ c(B,A) = c(A,B) ≫ β.hom`.
- The conclusion uses the explicitly specified `DerivedMonoidal.braiding'` at
  the two `DerivedCategory.Qh` localizations. These are the native braidings
  constructed from the homotopy Koszul braidings, with the native tensor counit
  normalization (`DerivedMonoidal.braiding_hom_μ`). Thus the two native-braiding
  normalizations in the node are fixed by existing constructions, rather than
  added as assumptions on arbitrary braidings.
- For arbitrary `K L : DerivedCategory C`, the conclusion is
  `E.map βC.hom ≫ t(L,K) = t(K,L) ≫ βD.hom`, exactly the final displayed equation.
  There is no boundedness hypothesis on K or L.

Dependency declarations and sources inspected:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`:
  `DerivedCategory.hasDerivedMonoidalCategory`, full enclosing assumptions and docstring.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor` and the recorded preservation declarations.
- `Mathlib.CategoryTheory.Monoidal.Functor`: `CategoryTheory.Functor.CoreMonoidal`,
  full unit/tensorator/naturality/coherence fields, lines 620–651.
- `Sheaf.CategoryTheory.DerivedTensorComparison`:
  `AlgebraicGeometry.ProEtale.SupportedTensorDerivation.ComplexCondition`,
  `ComplexComparison`, `ComparisonHom`, `ComparisonFamilyCondition`,
  `ComparisonCondition`, and `exists_unique_comparison`, including all signatures
  and proof/docstrings. The node supplies t, so no choice of the existence witness
  is needed. Its natural-transformation type uses Mathlib directly: the recorded
  `ComparisonCondition` imposes normalization on all complexes and shares successor
  universes, whereas this item explicitly assumes only K-flat normalization and
  allows independent category/localization universes. No duplicate definition is made.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactors`.
- `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided`:
  `DerivedMonoidal.braiding'`, `braiding_hom_μ`, and `braidedCategory'`.
  Its explicit construction is used, rather than choosing a witness of
  `DerivedCategory.nonempty_braidedCategory`.
- Proof imports retain the recorded declarations in
  `Sheaf.CategoryTheory.DerivedCategory.KFlatDerivability` and
  `Sheaf.CategoryTheory.MultivariableDerivedCalculus`, and the Mathlib colimit
  and adjunction modules for the remaining proof dependencies.

Edge cases checked before and during drafting: zero complexes and zero derived
objects remain allowed; a summand index can be negative, zero, or positive with
no finite-support restriction on the complex; the direct sum is over all integer
pairs of the prescribed total degree. No division by 2 or characteristic
restriction occurs in the Koszul sign. The identity functor with its identity
strong monoidal structure gives the native braiding equation. K and L may be
unbounded in both directions. Naturality and model normalization are retained
for the prescribed t; it is not replaced by an arbitrary monoidal structure.
All six category/localization universe parameters remain independent.

Searches actually run:

- `msearch.py ... leanfinder` with query “An exact symmetric monoidal functor
  preserves native derived braidings with a K-flat normalized tensor comparison”:
  eight hits, including `Functor.map_braiding`, `Functor.Braided.braided`, and
  `Localization.Monoidal.braidingNatIso_hom_app`. None proves the cross-functor
  result: the first two assume an already braided functor; the last concerns
  a single monoidal localization rather than the derived tensor comparison.
- `msearch.py ... loogle 'CategoryTheory.Functor.map_braiding'`: one hit,
  requiring `[F.Braided]`; not the present statement.
- `msearch.py ... grep '(derived.*[Bb]raid|[Bb]raid.*[Dd]erived|braidingNatIso_hom_app)'
  CategoryTheory`: five hits in Mathlib's localization braided module, with
  `braidingNatIso_hom_app` at line 57; no exact match.
- `rg` on `lean/WeilConjectures` for the node id: no hit. Searches there for
  derived/braiding and `map_braiding` locate the native braiding constructions
  and the special étale pullback result in `UpperStarMonoidal/Braided.lean`.
  The latter is a special sheaf pullback theorem, not this general exact-functor
  result. Corresponding `rg` searches in `lean/Sheaf` find specialized derived
  pullback/tensor symmetry modules and no exact match for this statement.

No statement dispute or node fault was found. The sole postponed theorem is
`CategoryTheory.Functor.exactTensorFunctor_derived_braiding`.

## Second reading by NM

I reread the node and the final signature directly (a second self-reading; this
worker's dispatcher brief forbids starting another agent, and the maintainer
performs the independent delivery review). The checks were the direction of
κ, the inverse ordinary tensorator in every bidegree, preservation of all
K-flat complexes, the exact placement of t(L,K), and using the two independently
fixed native braidings. The counit-normalized equation was checked by composing
the node's formula on both sides as described above; it does not assume the
stronger all-complex normalization of the dependency interface. No mathematical
mismatch was found. The initial compile found a namespace projection issue on
`(F.mapHomologicalComplex _).obj P`; the final signature spells the predicate
`CochainComplex.IsKFlatForTotalTensor` explicitly there. No hypothesis or clause
changed in that repair.
