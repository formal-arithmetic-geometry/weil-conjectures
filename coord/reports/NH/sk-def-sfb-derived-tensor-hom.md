## Worker report

This delivery records an existing, multi-module interface for
`sk-def-sfb-derived-tensor-hom`. No module or definition is added. Only the item's
`lean` field changes. The source is the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/_section.md`,
read in full, including its list of existing Lean declarations. That list already names
both layers, their monoidal structures, and both tensor–Hom adjunctions. The record also
names existing lax-localization and K-flat comparison interfaces to cover every clause.

The main declaration is `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`. Its recorded signature
is verbatim up to the defining `:=`. The declarations list contains its exported Layer B
and generic interfaces; the note explicitly records the existing Layer A components
and their owning modules. This unit is a convention combining existing components.
A consumer needing everything imports both `WeilConjectures.SixFunctors.ProEtale.Derived.Hom`
and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`.

Hypotheses, each matched to the existing source context:

- Scheme: `(X : Scheme.{u})`, with no separatedness, finiteness, nonemptiness or base-field
  assumptions.
- Coefficient category: `(A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]`.
- Closed symmetric tensor: `[MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]`.
- Additive tensor: `[MonoidalPreadditive A]`.
- Functorial flat resolutions: `[Abelian.HasFunctorialFlatResolution A]`.
- Commutative condensed ring: `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`
  with `[MonObj Λ] [IsCommMonObj Λ]`. This is the ring-object presentation of the
  dependency's sheaf of commutative rings, rather than a constant discrete ring.
- Pulled-back coefficient: `AlgebraicGeometry.ProEtale.condensedRingObj Λ X` is
  `(upperStarFromPoint X).obj Λ`, with its transported commutative ring structure.
- Ambient derived categories: the ordinary unbounded `DerivedCategory` applied to
  `Sheaf (Scheme.ProEt.topology X) A` and to
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  There is no constructibility, boundedness or finite Tor-amplitude restriction.

Clauses and their declarations:

1. Layer A tensor is `ProEtale.derivedTensor A X := curriedTensor _`. The monoidal
   structure is the existing K-flat one supplied by `DerivedCategory.hasDerivedMonoidalCategory`
   in `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, and
   `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` in
   `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
2. Its two-variable universal property is
   `ProEtale.isLeftDerivedFunctor₂_derivedTensor A X`, for quasi-isomorphisms in both
   variables and the specific comparison `Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh`.
   The tensor of complexes descends to the homotopy category; `Qh` then localizes it.
   This is the same homotopy-localization interface already recorded for
   `lem-sfb-derived-tensor-sheaves-derived`, not a different tensor bifunctor.
3. Computation by replacing either argument uses `DerivedCategory.exists_kFlat_iso`,
   `tensorLeftCounit`, `tensorRightCounit`, `isIso_tensorLeftCounit` and
   `isIso_tensorRightCounit`, all in
   `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`. At a K-flat `P`,
   these are the isomorphisms from `Qh(P) ⊗ᴸ Qh(Z)` to `Qh(P ⊗ Z)`, or with `P` on
   the right. Composing with the localization of a quasi-isomorphic replacement gives
   precisely the computation claimed. No requirement that both arguments be K-flat.
4. The complexes localization is lax monoidal by `ProEtale.laxMonoidal_Q A X`,
   explicitly for `DerivedCategory.Q`; the statement is not limited to `Qh`.
5. Layer B tensor is `ProEtale.CondensedRing.derivedTensor Λ X := curriedTensor _`,
   in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`.
   `CategoryTheory.Mod.derivedMonoidalCategory` in
   `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory` supplies its monoidality.
   That module also supplies `Mod.isLeftDerivedFunctor₂_curriedTensor`;
   `CondensedRing.isLeftDerivedFunctor₂_derivedTensor Λ X` is its specialization.
6. The underived module tensor is exactly `CategoryTheory.Mod.monoidalCategory` from
   `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`. Its `tensorObj_X` is the
   balancing coequalizer of the right action through the braiding and the left action;
   `tensorObjπ` and `isColimitTensorπ` exhibit this coequalizer. Thus the derived
   bifunctor already derives relative tensor. It is not tensor over the integers and
   a subsequent quotient. The K-flat comparisons in clause 3 apply to this module
   category and this very tensor. `CondensedRing.laxMonoidal_Q` is available as well.
7. Closedness of both derived monoidal categories is `DerivedCategory.monoidalClosed`,
   in `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed` (and its exported
   flat-resolution specialization in `Monoidal.Instances.DerivedCategory`).
8. Layer A internal Hom is `ProEtale.derivedHom A X` in
   `WeilConjectures.SixFunctors.ProEtale.Derived.Hom`; Layer B is
   `ProEtale.CondensedRing.derivedHom Λ X` in the corresponding
   `ModuleObject.Derived.Hom`. Both definitions are literally
   `MonoidalClosed.internalHom`. Each has domain `Dᵒᵖ ⥤ D ⥤ D`, giving the required
   contravariance, covariance and codomain.
9. In each of these Hom modules, `derivedTensorHomAdjunction₂` is the parameterized
   adjunction `derivedTensor ⊣₂ derivedHom`, literally
   `MonoidalClosed.internalHomAdjunction₂`. The unary `derivedTensorHomAdjunction`
   takes an arbitrary `K` and evaluates `.adj K`. This gives the displayed adjunction
   for every object, with naturality in `K`, not just separate unrelated adjunctions.

Dependency declarations read and used:

- `sk-def-sfb-condensed-ring`: audited upstream `Profinite.continuousMapRingSheaf`,
  `continuousMapRingObj`, `continuousMapRingSheafMap` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`, and the four
  padic coefficient definitions in its `EllAdic` companion. Their docstrings and
  signatures were read. The item uses arbitrary commutative condensed rings.
- `sk-def-sfb-pulled-back-coefficients`: `ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, `isCommMonObj_condensedRingObj`, in the published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `sk-def-sfb-derived-categories`: Mathlib `DerivedCategory` for the ambient categories;
  the recorded `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` concerns
  another convention in that multi-clause unit and is not needed by this tensor definition.
- `sk-def-sfb-sheaf-tensor`: `CategoryTheory.sfbSheafTensor_properties` in
  `Sheaf.CategoryTheory.SheafTensor` and its `sfbSheafTensorStructure` dependency were
  read. The construction sheafifies objectwise tensor, using the same localized sheaf
  tensor as the existing pro-etale framework; no private tensor is substituted.
- `sk-def-sfb-module-objects`: audited Mathlib `CategoryTheory.ModObj`, `Mod`,
  `Mod.forget`, `Mod.regular` in `Mathlib.CategoryTheory.Monoidal.Mod`. Their action,
  module morphism, forgetful and regular-module definitions were read in source.
- `def-sfb-modobj-relative-tensor`: `CategoryTheory.Mod.monoidalCategory` and its
  coequalizer descriptions, in `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`.
- `def-sfb-derived-tensor-sheaves` and `def-sfb-derived-tensor-modules`: exactly the
  existing Layer A and Layer B tensor definitions above.
- `def-sfb-derived-hom-sheaves`: exactly `ProEtale.derivedHom` above.
- `def-sfb-derived-hom-modules`: its Mathlib match `CategoryTheory.MonoidalClosed.internalHom`
  (`Mathlib.CategoryTheory.Monoidal.Closed.Basic`, lines 292–294) is precisely the body
  of `CondensedRing.derivedHom`; no specialization repair is required.
- The proof's adjunction nodes likewise use the same upstream parameter adjunctions
  and Mathlib `MonoidalClosed.internalHomAdjunction₂` (lines 305–307).

Edge cases checked: the empty scheme is allowed; zero objects and the zero coefficient
ring are allowed; the derived categories are unbounded; neither tensor argument needs
boundedness or flatness. For a K-flat argument the named counit is invertible, including
when that argument is zero. The unit is the coefficient tensor unit, respectively the
regular module, rather than a cartesian tensor unit. No assumptions on characteristic
or primes are introduced. The small site retains object universe `u+1` and morphism
universe `u`; the coefficient Hom universe is `u+1`, as in the published convention.
The coefficient object universe `u'` is independent. These are the dependency interfaces'
size convention, not an imposed equality of site object and morphism universes.

Searches (all made before recording the match):

- `msearch.py ... leanfinder "derived tensor product and derived internal Hom for sheaves
  and modules over a condensed ring on the pro etale site"`: eight hits on underived
  light-condensed monoidal structures; none is the full derived convention.
- `msearch.py ... loogle "MonoidalClosed.internalHom, internalHomAdjunction₂,
  IsLeftDerivedFunctor₂"`: zero hits, unknown identifier `MonoidalClosed.internalHom`.
  Direct source reading confirms the fully qualified declaration exists.
- `msearch.py ... grep "internalHomAdjunction₂|def internalHom|IsLeftDerivedFunctor₂"
  CategoryTheory`: seven hits, including the exact Mathlib internal-Hom definitions.
- `rg` in the slopmaster2 `WeilConjectures/SixFunctors/ProEtale` tree for derived tensor,
  Hom, derivation and adjunction names found Layer A. Searching the item id found no
  literal blueprint tag, which does not invalidate the exact declaration matches.
- `rg` in `lean/Sheaf/Paper` for derived tensor/Hom found existing consumers and unrelated
  scheme constructions, not a missing replacement definition for this unit.
- Read the precise Layer B sources under the shared `lean/WeilConjectures` overlay and
  `coord/pefw-upstream-framework.md`. Used `scompile.py --source` to confirm current
  published Layer A Tensor/Hom and Layer B Tensor/Hom, rather than relying on the older
  checkout's availability.

Validation: a sandbox-only `scratch/Consumer.lean` publicly imported both Hom modules,
explicitly bound all universes and hypotheses with `autoImplicit false`, and checked
both tensors, derivation instances, lax localizations, Homs, parameter/unary adjunctions
and both K-flat counit theorems. `scompile.py NH sk-def-sfb-derived-tensor-hom ...` passed
both sandbox and library checks with no errors or warnings (3.0 s and 2.1 s). The scratch
probe is not delivered. No new proof is supplied and no upstream sorry is claimed closed.
No statement correction, dependency replacement, new node or dispute is needed.

## Second reading by NH

This is a self-check, not an independent worker review: the dispatcher explicitly
forbids starting other agents, and the maintainer supplies the independent reading.
Re-read the current node alongside all four existing component sources and the generic
monoidal/K-flat interfaces. Every scheme/category/condensed-ring hypothesis is accounted
for above. Layer A and B are different derived categories, and the record documents both, with
Layer A in the note and Layer B in the primary declaration and exported declarations.
Relative tensor is balanced before derivation. The K-flat counits cover replacement in
one argument; Q itself is lax monoidal. Both Hom definitions are for the selected tensor,
and both parameter adjunctions ensure naturality. The primary signature alone covers
Layer B Hom; the record note and ownership map document the full multi-module convention.
The initial dry run correctly exposed that Layer A declarations were not exported by
the primary Layer A Tensor module together with Layer B; the record was repaired to
use Layer B Hom with only its exported declarations in the list, and explicit Layer A
module/name bindings in the note. No mathematical statement change was needed.
