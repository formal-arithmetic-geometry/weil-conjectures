## Worker report

Item: `lem-weil-pbc-proetale-closed-underived-projection`.
Module: `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`.
Primary declaration:
`AlgebraicGeometry.ProEtaleClosedProjection.closed_underived_projection`.

The module states the specified underived projection formula, joint naturality,
and the coefficient-linearity clause. Its main theorem has proof `sorry` and the
complete four-step natural-language proof in its docstring. The canonical-adjunct
clause also needs the named helper theorem `adjunction_exists`, with proof `sorry`
and its own complete proof docstring. It characterizes the adjunction uniquely by
the actual sectionwise unit. The other four declarations have real bodies: that
uniquely specified adjunction, the actual adjunct, the restriction of the regular
module, and the proposition spelling out the coefficient clause. The helper is
part of the item's specified canonical-map construction, as authorized for
missing canonical helpers; no independent DAG notion is introduced. Only the item's `lean` field is changed.
There is no statement correction or statement dispute.

Hypotheses and clauses, in the order of the node:

- Schemes X and Z: `{X Z : Scheme.{u}}`; the closed immersion is `(i : Z ⟶ X)
  with `[IsClosedImmersion i]`.
- The complementary open immersion j is `U.hom` for `(U : X.ProEt)` with
  `[IsOpenImmersion U.hom]`. Its domain is `U.left`. Every open immersion is
  weakly etale, so presenting this open in the small site does not restrict j.
  `[QuasiCompact U.hom]` is exactly the stated quasi-compactness, and
  `hU : Set.range U.hom = (Set.range i)ᶜ` is exactly complementarity.
- The small sites are Mathlib `Scheme.ProEt` and `ProEt.topology`, on the original
  scheme universe u. Site objects have universe u+1 and morphisms universe u;
  ring and module sections have universe u+1, as in the recorded dependencies.
  There is no imposed equality of the two site universes.
- Arbitrary commutative ring sheaf R is `(R : Rings X)`, where the dependency
  abbreviation is `Sheaf (ProEt.topology X) CommRingCat.{u+1}`.
  `inverseRing i R` is precisely the recorded inverse-image ring R_Z.
- Every module M on Z and F on X is quantified in the first conjunct as
  `(M : Modules (inverseRing i R)) (F : Modules R)`. These are the recorded
  `ringedSiteModules`/Mathlib `SheafOfModules`, not new categories.
- `tensor` is the dependency's actual sheafified sectionwise tensor, and
  `proEtaleRingedDirectImage i R` is direct-image evaluation with its ring-unit
  action. Thus `projection i R M F` has exactly source `(i_*M) tensor_R F` and
  target `i_*(M tensor_R_Z i^{-1}F)`.
- The canonical map is defined, not existentially asserted: `projection` applies
  `(adjunction i R).homEquiv` to `comparison i R (i_*M) F` followed by
  `tensorMap ((adjunction i R).counit.app M) (𝟙 _)`. This is literally the
  specified tensor-comparison/counit adjunct. `adjunction_exists` uniquely fixes
  the adjunction between those actual functors by requiring its unit on every
  F, V and section s to equal the dependency's constructed `inverseSection`.
  `adjunction` selects from this unique characterization, so the data are
  determined up to equality, as required by the no-hollow-definitions rule.
  This is not a choice from mere existence or a Nonempty adjunction. The helper's
  proof plan transports the concrete small-model module pullback adjunction back
  by explicit module equivalences; sectionwise identities give the normalized
  unit. Equality of units implies equality of adjunctions. The library's existing
  construction of this adjunction is private and cannot be referenced by a
  consumer name, even with `import all`; the final file does not use it, private
  internal names, or compatibility options. No adjunction hypothesis is added.
- The first conjunct states `IsIso (projection i R M F)` for every M and F.
- The second conjunct quantifies M, M', F, F' and maps a and b, and equates
  `(i_*a tensor b) ≫ projection M' F'` with
  `projection M F ≫ i_*(a tensor i^{-1}b)`. It is joint naturality of precisely
  the map in the first conjunct.
- The last conjunct quantifies every commutative ring sheaf B and morphism
  `a : R ⟶ B`, and asserts `CoefficientLinear i R M B a` for every M.
  `coefficientModule a` is B as an R-module, namely restriction of the
  existing regular module `SheafOfModules.unit`.
- In `CoefficientLinear`, eB identifies the inverse image of this regular
  module with the regular inverse-image ring, restricting scalars along
  `inverseRingMap i a`. Its displayed unit equation fixes this identification
  on the actual inverse-image sections using the ring adjunction unit.
- `S : Modules B` and `T : Modules (inverseRing i B)`, with eS and eT, express
  B-module structures on the actual source tensor and inverse-image target
  tensor. They are not arbitrary substitutes: eS and eT are isomorphisms of
  the restricted R-modules with those exact tensor objects. The two universally
  quantified pure-tensor identities prescribe the actions on the B factor:
  `c • (m tensor b) = m tensor (c*b)`; eB supplies the identical prescription
  on the inverse-image B factor. These equations determine the transported
  actions because sections of sheaf tensors are locally sums of pure tensors.
  The `@id` terms only expose the original S/T section types for scalar
  elaboration after restriction of scalars.
- `p : S ⟶ (proEtaleRingedDirectImage i B).obj T` is therefore B-linear by
  its type. This particular direct image uses the action through the actual
  ring adjunction unit `B ⟶ i_*i^{-1}B`. `IsIso p` includes a B-linear inverse.
  The final equation holds for every object V and every original tensor
  section x, and identifies p, through eS and eT, with the original
  `projection i R M (coefficientModule a)`. Hence this is B-linearity of the
  specified projection, not existence of an unrelated B-module isomorphism.
- No flatness, finite presentation, constructibility, nonzero-ring, finite-ring,
  compactness of X, or quasi-separatedness of X is assumed.

Dependency declarations read and used:

- Mathlib `AlgebraicGeometry.Scheme`: `Scheme`, and its morphisms.
- Mathlib `AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- Mathlib `AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- Mathlib `AlgebraicGeometry.Morphisms.QuasiCompact` (the quasi-compact notion
  recorded by `def-weil-finite-type-morphism`): `QuasiCompact`.
- Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleModuleInverseImage`, `proEtaleModelRingUnit`, and the explicit
  model transports used in the existing canonical module adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:
  `proEtaleModuleCoefficients`, `proEtaleRingedDirectImage`, and
  `proEtale_ringed_open_closed`. The last theorem supplies the open vanishing
  and localization sequence for the proof plan. Its private canonical
  `ringedInverseImageAdjunction` construction was read, including its complete
  signature and body, as evidence for the unit-normalized helper's proof plan;
  it is not referenced by the delivered file. No dependency repair is required.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`:
  `Rings`, `Modules`, `inverseRing`, `inverse`, `tensor`, `comparison`,
  `tensorMap`, `restrict`, `inverseRingMap`, `inverseSection`, `pure`, and
  `inverseImage_tensor_comparison`. The sigma used by the projection is the
  unique pure-tensor-normalized comparison in this dependency.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, the current
  recorded tensor node: imported directly; its public import
  `SiteTensorFunctoriality` retains the exact `siteSheafTensorRight` and
  `siteSheafTensorTmul` used by the comparison module. No new tensor is defined.
- Proof-only `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit`:
  `Scheme.proEtale_ringed_closed_counit` for the actual module counit.
- Mathlib `SheafOfModules.unit` and `SheafOfModules.restrictScalars` supply
  the regular coefficient module and its restriction.

Source reading: `literature/stacks-project/proetale.tex`,
`lemma-closed-immersion` (09AA) and `lemma-ses-associated-to-open` (09AH),
and `literature/stacks-project/sites-modules.tex`,
`lemma-tensor-product-pullback` (03EL) and Section 03EK. The node correctly
labels its projection consequence as agent-formulated. The source localization
lemma has precisely the quasi-compact open hypothesis retained here.

Edge cases checked before writing: empty X; empty Z (both tensors are zero);
Z = X with empty open complement (unit/counit reduce the projection to the
usual identity comparison); zero ring R or B; zero M or F; nilpotent/nonreduced
closed subschemes; non-flat coefficient extension, for example reduction
modulo a nonzero integer. No binder excludes any of these. In the coefficient
clause a = identity is retained, and B is not required to be a constant sheaf.
For a general open complement the ProEt presentation imposes no extra
restriction beyond its already assumed open immersion.

Searches performed with the prescribed msearch wrapper (recorded automatically
in searches.jsonl in the sandbox):

- LeanFinder: `Closed immersion pro etale arbitrary commutative ring sheaf
  underived direct image tensor projection formula`. Eight hits concerning
  formally etale/unramified rings and Kaehler differentials; no match.
- Loogle: `"SheafOfModules", "tensor"`. Ten hits on presheaf module tensors,
  tensor functoriality and preservation of colimits; no closed pro-etale formula.
- Grep: `(closedImmersion|ClosedImmersion).*(tensor|projection)|(tensor|projection).*(closedImmersion|ClosedImmersion)`.
  Zero Mathlib hits.
- LeanSearch: `Closed immersion direct image tensor projection formula for
  arbitrary sheaves of modules on a ringed site`. Eight closed-immersion
  geometry hits; none gives this module projection.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf`, and the required node-id
  grep in `lean/WeilConjectures`: no declaration for this item. Inspected
  `Sheaf.SixFunctors.ProEtaleClosedTensorProjection`: this is a derived
  statement, with derived tensor and pullback models, not this underived
  comparison with its coefficient clause. Upstream `ClosedStructureTensorProjection`
  concerns ordinary structure-sheaf modules on schemes, not arbitrary ring
  coefficients on the pro-etale site. None is an exact existing match.

Validation: the final file is checked with scompile.py against the published
library, without a global build. All universes and binders are explicit;
`autoImplicit` is disabled. The delivery dry run is run after compilation.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
