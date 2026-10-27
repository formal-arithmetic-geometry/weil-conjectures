## Worker report

The module `Sheaf.AlgebraicGeometry.OpenCoefficientSquareActionIdentification` states
`lem-sfb-open-coefficient-square-action-identification` without changing its TeX statement.
Every new theorem has the whole proof `sorry`; definitions contain actual functor and
natural-isomorphism data. Six statements and five constructions are recorded together.
The primary statement is `openCoefficientSquare_action_identification`.

Hypothesis and clause correspondence (all names below lie in
`AlgebraicGeometry.ProEtale.CondensedRing` unless qualified):

- Commutative condensed rings are `Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`
  with `[MonObj Λ] [IsCommMonObj Λ]` and the corresponding instances for Λ'. The
  coefficient morphism is `a : Λ ⟶ Λ'` with `[IsMonHom a]`. These are internal rings and
  ring morphisms in abelian sheaves, rather than ordinary external module categories.
- Schemes are `U X : Scheme.{u}`, the immersion is `j : U ⟶ X`, and each theorem has
  `[IsOpenImmersion j]`. The first two constructions work for any scheme morphism;
  the identity-comparison constructions use the open-instance inverse-square theorem.
  There is no flatness, invertibility, characteristic, nontriviality or boundedness
  hypothesis on `a`, Λ or the complexes.
- `A_T`, `B_T`, `a_T` are the existing `condensedRingObj Λ T`,
  `condensedRingObj Λ' T`, `coefficientMap a T`. The abelian pullback F is
  `ProEtale.upperStar Ab.{u + 1} j`; its monoidal structure is
  `Functor.LaxMonoidal.μ`, inherited from the published strong monoidal structure.
  The α's are `condensedPullbackHom Λ j` and `condensedPullbackHom Λ' j`, with
  their existing `IsIso` instances. `upperStar Λ j` and `upperStar Λ' j` are exactly
  mapMod followed by forward extension along α. Scalar restrictions are `Mod.comap`.
- `openCoefficientRestriction` writes mapMod followed by restriction along α⁻¹.
  `openCoefficientCollapse` is the published `Mod.extendScalarsIsoComapInv` whiskered
  by mapMod. `openCoefficientCollapse_quotient` specifies its composite with
  `Mod.extendπ` as α⁻¹ followed by the transported action, and its inverse as the
  left-unitor inverse, unit insertion, and quotient. Thus the balanced collapse and
  its inverse are fixed, not an unspecified isomorphism between the same objects.
  The declaration applies separately to both coefficient rings and every module.
- `openCoefficient_inverse_square` is exactly `a_U ≫ α_B⁻¹ = α_A⁻¹ ≫ F.map a_X`
  in Lean's diagrammatic composition order. Neither horizontal map is inverted.
- `openCoefficientSquare_actions_components`, first two clauses, identifies both
  inverse-restriction actions with `(a_U ≫ α_B⁻¹) ▷ FN ≫ μ ≫ F.map γ_N`.
  Together with the inverse-square equation this is precisely the two equal action
  formulas in the node. This normalization is on the actual sheaf FN.
- Clauses three and four of that theorem state both underlying components of the
  specified `comapUpperStarIso a j`, conjugated by the fixed collapses, equal `𝟙 FN`.
  The fifth and sixth clauses specify the two identity components of the explicit
  inverse-restriction comparison. All equalities are of internal sheaf morphisms.
- `openCoefficientIdentityRestrictionIso` is constructed from the identity-component
  `mapModComapIso`, `comapComp`, and `comapCongr` applied to the inverse square.
  `openCoefficientIdentityIso` conjugates it by the collapses. This is d⁰ with
  exactly the required orientation, from `Mod.comap a_X ⋙ upperStar Λ j` to
  `upperStar Λ' j ⋙ Mod.comap a_U`. Neither definition chooses an arbitrary iso.
- `openCoefficientSquare_maps` gives both actual composite functors' maps on h,
  conjugated by the collapses, equal `F.map h.hom`. Naturality in N is also built
  into every construction's natural-isomorphism type; this includes both directions.
- `comapUpperStarIso_symm_eq_openCoefficientIdentityIso` states `(c⁰).symm = d⁰`
  as natural isomorphisms of the actual module functors, not just an equality of
  isomorphism classes or underlying objects.
- `derivedOpenCoefficientIdentityIso` is degreewise localization of d⁰ using
  `Functor.mapDerivedCategoryNatIso` and the published
  `Functor.mapDerivedCategoryCompIso` on its two sides. These use ordinary unbounded
  `DerivedCategory` and preserve the composite factorization isomorphisms.
  `openCoefficientSquare_action_identification` states
  `(derivedComapUpperStarIso a j).symm = derivedOpenCoefficientIdentityIso j a`.
  This is c⁻¹=d as a natural isomorphism on the entire unbounded derived category.

Dependency interfaces read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `ProEtale.coefficientMap`, its identity/composition laws and coefficient-square law;
  `CondensedRing.comapUpperStarIso`, `derivedComapUpperStarIso`. Their definitions
  fix the precise scalar-square composite and its localization.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, `condensedPullbackHom`, `isIso_condensedPullbackHom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, the mapMod/Ext composite.
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` and `MapMod`:
  the transport interface, `Functor.mapMod`, `Functor.mapModComapIso`,
  `Mod.extendScalarsIsoComapInv`. `Mod.extendScalarsIsoComapInv` is adjoint uniqueness
  for the actual extension/restriction adjunction, and is not replaced here.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `Mod.extendπ`, the extension unit, and the adjunctions.
  `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `Mod.comap`, `Mod.forget` and actions.
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`:
  `Mod.extendScalarsComapIsoOfIsIso`, used by the actual published c⁰.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  derived-category convention module; the statements here use `DerivedCategory`
  and exact levelwise functors, rather than right-derived replacements.
- Proof-only modules are imported without public visibility:
  `Sheaf.CategoryTheory.SheafTensor`,
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`,
  `Sheaf.CategoryTheory.ExtensionIsoQuotientFormula`
  (`Mod.extensionIso_quotient_formula`), and
  `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
  (`CondensedRing.module_pullback_additive_exact`). The other recorded proof
  interfaces, `Functor.mapDerivedCategoryFactors`, `Localization.liftNatIso` and
  localization full faithfulness, are already in the public upstream import closure.

The docstrings give the node's proof in stages: normalized quotient formulas;
inverse square; transport action naturality; identical restricted actions; computation
of the specified scalar-square composite including its actual collapse factors;
naturality and cancellation; exactness; degreewise maps and differentials; descent
using localization full faithfulness. Each postponed theorem carries this node's
blueprint tag. The auxiliary definitions belong to this comparison itself, so do not
introduce a second independent notion or require additional DAG nodes.

Edge cases checked: `a = id` requires no additional identification or flatness;
`j = id` still uses the canonical α and does not assume it definitionally identity;
`U = ∅` and zero modules/complexes are allowed; zero coefficient rings are allowed;
a non-flat coefficient map such as constant Z/4 → Z/2 is not excluded. Nontrivial α
isomorphisms have the correct orientation: the common arrow is A_U → F(B_X).
The site has its published object/morphism universes, and abelian coefficients have
universe u+1. No extra universe equality was introduced.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder`: “The canonical scalar restriction pullback comparison
  has identity components after extension along coefficient isomorphisms is collapsed”.
  Eight hits, all ordinary `ModuleCat` restriction/composition identities; none
  states this internal pro-etale coefficient-square normalization.
- `msearch.py ... loogle`: `CategoryTheory.Mod.extendScalarsIsoComapInv,
  CategoryTheory.Functor.mapModComapIso`: zero hits, upstream identifier unknown to
  the Mathlib index. Direct upstream reads located the two existing constructions.
- `msearch.py ... grep`: `comapUpperStarIso|extendScalarsIsoComapInv`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures`: `comapUpperStarIso` locates the definitions in
  ChangeOfCoefficients and their Shriek users, but no normalized component statement.
  Search for this node's exact id returns no declaration.
- `rg` in `lean/Sheaf`: `comapUpperStarIso|extension_iso_quotient|balancedCollapse|
  collapse|extendScalarsIsoComapInv` locates ExtensionIsoQuotientFormula and ordinary
  users of collapse, but no theorem identifying this specified square with d⁰.
  A final name search in both roots and `dag/lean_names_upstream.json` found no
  collision with any new declaration.

No statement fault, disputed statement, dependency repair or new node is needed.
The server `scompile.py` compiles the file in both sandbox and library module mode
cleanly, with no errors and no non-sorry warnings. Earlier parser and overlapping
instance warnings were repaired in the sandbox; no library source was edited.

## Second reading by Q137

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
