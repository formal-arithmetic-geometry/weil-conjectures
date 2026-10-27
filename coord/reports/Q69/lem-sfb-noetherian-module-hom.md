## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceNoetherianModuleHom` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_finitePresentation_moduleHom_of_noetherian`.
Its only theorem has proof `sorry`. No definition, helper theorem, dependency module,
or new DAG node is introduced. The natural-language statement is unchanged.

I read Stacks `quot.tex`, Situation 08JT (`situation-hom`) and all of Tag 08JY
(`lemma-noetherian-hom`), including its proof. The hypotheses and conclusion agree.
The proper closed-carrier convention is the one explicitly specified in the node,
following `spaces-perfect.tex` Tag 0CZI, rather than an additional properness hypothesis
on f or a choice of an arbitrary model for the support. The theorem docstring carries
all ten DAG proof steps and identifies their supporting nodes.

Hypothesis and clause correspondence:

- `S : Scheme.{u}` is the arbitrary base scheme. `X B : AlgebraicSpace S` and
  `f : X ⟶ B` are exactly the algebraic spaces and morphism of the node. `universe u`
  and `autoImplicit false` make the size convention explicit; sites and module section
  sizes are inherited from the existing algebraic-space interface. There is no derived
  category universe assumption in the theorem.
- `hf : MapIsLocally (@LocallyOfFiniteType) f` tests local finite type on every compatible
  pair of etale scheme charts. `hfqs` tests quasi-compactness of the relative diagonal
  on affine schemes using the existing `MapIsQuasiCompact`.
- `hBqc` supplies a scheme `U : Over S`, a representable etale surjective atlas map,
  and `CompactSpace U.left`, exactly the stated quasi-compactness convention.
- `hBqs : IsAbsolutelyQuasiSeparated B` is quasi-compactness of the absolute diagonal
  over Spec Z. Its existing definition uses the equivalent two-affine-test criterion
  of Stacks 0AHR, which does not assume the specified base S is quasi-separated.
- `hBnoeth` says every `V : B.EtaleSite` has locally Noetherian underlying scheme,
  using `IsLocallyNoetherian`. Together these are precisely the three Noetherian
  hypotheses in the node.
- `F G : X.QCoh` uses the existing full subcategory of quasi-coherent small-etale
  module sheaves. `hF` and `hG` are `IsFiniteType`, the existing predicate for finitely
  many local generators. Neither module is assumed globally generated or locally free.
- `hGflat : ModuleIsFlatOver f G.obj` uses all compatible etale chart pairs and the
  recorded scheme `Scheme.Modules.IsFlatOver`. On quasi-coherent modules this is the
  affine-local equivalent of the stated ordinary-stalk flatness. No flatness of f or
  of any test morphism is imposed.
- `hGsupport` supplies `Z`, a representable closed immersion `i : Z ⟶ X`,
  `MapIsProper (i ≫ f)`, and `N : Z.Modules` with `N.IsQuasicoherent`, `N.IsFiniteType`,
  and an isomorphism `(moduleDirectImage i).obj N ≅ G.obj`. This is the precise
  closed-carrier condition in the node, using its existing direct image. Properness
  has the recorded separated/finite-type/universally-closed meaning.
- The conclusion supplies `H : AlgebraicSpace S` and `h : H ⟶ B`.
  `MapIsAffine h` says every affine scheme test has affine scheme source.
  `ProperQuotFinitePresentation h` is the already defined conjunction of chartwise
  local finite presentation, quasi-compactness, and quasi-compact relative diagonal.
- Every scheme `T → B` is an object of `ProperQuotTest B`, the existing category
  `CostructuredArrow yoneda B.obj.obj`. `properQuotFibre f T` is the actual sheaf
  fibre product, and `properQuotFst f T` is its projection to X.
- For every such T, `e T` is a bijection from scheme maps to H over B (written as
  natural transformations with the commuting-triangle subtype) to the Hom set between
  the ordinary `moduleTensorPullback` of F and G. No quotient of module maps, restriction
  to etale tests, or derived replacement of either module appears.
- The final universal equation is naturality for every map `k : T' ⟶ T` of scheme tests.
  `a'.val = yoneda.map k.left ≫ a.val` is pullback of the represented point. On the
  other side, `properQuotFibreMap f k` pulls back the module map; the inverse source
  comparison and forward target comparison `properQuotSourceIso` identify the iterated
  pullbacks with F_T' and G_T'. Quantifying over both a and a' and the equality avoids
  inserting any separately postulated comparison or choosing a noncanonical map.
  For every a and k the composed map is again over B by the commuting triangle, so this
  equation covers every transition, including identities and composites. Bijections
  and this equation are precisely representation of the entire contravariant functor.

Statement dependencies read and used (namespace `AlgebraicGeometry` unless specified):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `EtaleSite`,
  `etaleForget`, and `Modules`.
- `def-weil-size-convention` has a convention record, not a declaration; the explicit
  universe binder and the dependency interfaces implement it.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally`, `MapIsProper`, and its chartwise/topological constituents.
  `MapIsQuasiCompact`, used by that interface, is defined in
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` as compactness on affine pullback tests.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`,
  the full subcategory for Mathlib `SheafOfModules.IsQuasicoherent`.
  `SheafOfModules.IsFiniteType` is Mathlib's local-generators predicate in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, reused through the chartwise predicate below.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `AlgebraicSpace.ProperQuotTest`,
  `properQuotFibre`, `properQuotFst`, `properQuotTestMap`, `properQuotFibreMap`,
  `properQuotSourceIso`, and `ProperQuotFinitePresentation`. These constructions do not
  assume finite presentation of f; that assumption belongs to the Quot functor only.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, used by `properQuotFibre`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicSpace.ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`.
  I read the normalized compatible-chart-section limit interface and its adjunction;
  these are the existing canonical operations, not arbitrary functors.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`:
  `AlgebraicSpace.ModuleIsFlatOver`. Added the already-landed definition node
  `def-sfb-space-flat-proper-coefficient` to stmt_deps to cite its owning interface.
  The separate annihilator-support predicate from that module is not substituted for
  the node's carrier hypothesis.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`. Added its already-landed owning node
  `def-sfb-space-absolute-quasi-separated` to stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`:
  `AlgebraicSpace.MapIsAffine`. Added its already-landed owning node
  `def-sfb-space-affine-quasifinite-properties` to stmt_deps.

Every recorded module of the stated proof dependencies is included as a plain import;
statement dependencies are public imports. Proof dependencies with no recorded Lean
module cannot be imported yet. The scheme local-Noetherian finite-type permanence
input is already supplied by Mathlib's Noetherian module. No import cycle was found.

Edge cases checked before writing and again against the compiled statement:

- Empty B and empty X are allowed. No atlas index or scheme test is required to be
  nonempty, and the empty scheme is a permitted quasi-compact atlas of the empty space.
- If F or G is zero, the Hom functor is the singleton functor on schemes over B and
  is represented by B with its identity map, which is affine and finitely presented.
  The support condition permits the empty carrier for G = 0.
- f can be nonproper, nonflat, and non-quasi-compact. Only local finite type and
  quasi-separatedness are assumed; the proof first restricts around the proper carrier.
- No characteristic, reducedness, separatedness of S, or field assumption is present.
- Arbitrary nonflat maps T' → T are admitted in naturality. Tensor pullback of Hom
  uses both composition comparisons with the correct orientation; it makes no claim
  that tensoring induces a bijection between the two Hom sets.
- For f = identity and finite free F,G, the usual affine space of matrices is the
  expected representative. For general F the statement does not demand it be a vector
  bundle; e.g. torsion in F may impose equations on the representative.

Searches actually run with `msearch.py Q69 lem-sfb-noetherian-module-hom`:

- LeanFinder: `Relative Hom of finite type quasi coherent modules with flat proper
  support over a Noetherian algebraic space is affine of finite presentation`.
  Eight hits, concerning scheme finite morphisms, finite-presentation chart maps, and
  affine spaces. None states this relative module Hom theorem for algebraic spaces.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, SheafOfModules.IsFiniteType`.
  The service reports unknown identifier `AlgebraicGeometry.AlgebraicSpace`, zero hits;
  it does not index this project's algebraic-space interface.
- Mathlib grep: `noetherian.*[Hh]om|[Hh]om.*noetherian|hom.*representab`,
  subdirectory `AlgebraicGeometry`. Two hits: a scheme homeomorphism used in Noetherian
  topology and the order-of-vanishing documentation. Neither is a match.
- LeanSearch: `Hom functor of finite type quasi coherent modules flat proper support
  Noetherian algebraic space affine finite presentation`. Eight hits, led by
  `AlgebraicGeometry.Scheme.Modules.Hom` and scheme/ring flatness declarations;
  none is a representation theorem for this functor.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for module Hom, Noetherian Hom,
  Hom representability, and candidate declaration names; node-id grep of
  `lean/WeilConjectures`; and the candidate-name search of `dag/lean_names_upstream.json`.
  No existing theorem matched. Related derived Hom constructions concern complexes
  or fixed scheme/site objects. Targeted searches found the three existing owning
  definitions listed above, which are reused instead of redefined.

No statement correction, disputed statement, or dependency-interface repair is needed.
The only existing-node changes are the item's lean record and the three added existing
definition dependencies. The recorded signature is copied verbatim from the module.

Validation: `scompile.py` compiled this single module both as sandbox and at its intended
library path against the published live library (2.1 s and 3.2 s), with no errors or
unexpected warnings. Delivery preflight and compilation are run by `deliver2.py`.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
