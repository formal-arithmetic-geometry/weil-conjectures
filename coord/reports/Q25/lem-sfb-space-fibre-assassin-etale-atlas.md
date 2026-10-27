## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFibreAssassinEtaleAtlas` states
`AlgebraicGeometry.AlgebraicSpace.space_fibre_assassin_etale_atlas`, with `sorry` as its
entire proof. Four explicit helpers specialize existing constructions: the residue-field
spectrum as a scheme over S, its canonical map to Y, the existing sheaf fibre product
X_y, and its second projection. Their data are fully specified; no new independent
mathematical notion or arbitrary comparison map is introduced.

Hypothesis and clause correspondence:

- Work over Spec Z: `X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))` and
  `Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))`. The lift retains every scheme universe;
  the point set is the existing `Point`, in universe u+1. All universes and variables
  are explicitly bound, with `autoImplicit false`.
- Scheme base Y and space morphism f: `f : X ⟶ schemeSpace Y`.
- Finite type and quasi-separated: `_hf : MapIsFiniteType f` and
  `_hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. Neither noetherianity of
  Y nor finite presentation, separatedness, or flatness is assumed.
- Finite type quasi-coherent M: `M : X.QCoh` and
  `_hM : SheafOfModules.IsFiniteType M.obj`.
- Representable étale scheme atlas p: `T : X.EtaleSite`; the existing site's object
  contains the scheme `T.obj.left.left`, its map `T.obj.hom`, and proof of `IsEtale`
  (whose definition includes representability). `_hp : IsSurjective T.obj.hom` is
  exactly surjectivity, with no quasi-compactness assumption on the atlas.
- N = p^*M, read on the Zariski site as instructed: `(X.schemeRestriction T).obj M.obj`.
  On an étale chart the canonical tensor pullback is restriction; Zariski restriction
  reads this module on open subschemes. This is the already recorded construction,
  not an arbitrary module isomorphic to that pullback.
- Every y: `y : Y.left`. `assassinPointBase Y y` is Spec κ(y), with its actual map
  to the original base. `assassinPointBaseMap Y y` is induced by the actual residue
  morphism, and `assassinSchemeFibre Y f y` is
  `enlargedFibreProduct f (assassinPointBaseMap Y y)`.
- Form p_y:T_y→X_y by fibre products: `Ty : (assassinSchemeFibre Y f y).EtaleSite`,
  `i : Ty.obj.left ⟶ T.obj.left`, and `_hcart : IsPullback Ty.obj.hom (yoneda.map i)
  (pullback.fst ...).hom T.obj.hom`. This is the defining cartesian square for
  T×_X X_y = T×_Y Spec κ(y). The maps are therefore the specified projections of
  a scheme representing that fibre product. Quantification covers every such
  representation, without selecting a scheme from an unnormalized existence theorem.
  The étaleness in the type of Ty is automatic for this base change of T.
- N_y: `(Scheme.Modules.tensorPullback i.left).obj ((X.schemeRestriction T).obj M.obj)`.
  This is the actual scheme tensor pullback along T_y→T, so it retains N=p^*M and
  the fibre-module construction. Tensor composition and the recorded comparison
  identify it with the chart pullback of M_y, as required by proof step 2.
- M_y: `(moduleTensorPullback (enlargedFibreProductFst f
  (assassinPointBaseMap Y y))).obj M.obj`, using the specified first projection.
- Ass(X_y,M_y): the existing `relativeAssassin (assassinPointBase Y y)
  (assassinSchemeFibreToPoint Y f y) M_y`. Over the field spectrum this is precisely
  the absolute chartwise assassin (taking the fibre over the unique point changes
  neither chart nor module up to their canonical identification).
- For every t in T_y, equivalence of association: the first conjunct `∀ t, ... ↔ ...`
  uses `Scheme.Modules.associatedPoints N_y` and `schemePointMap Ty.obj.hom t` in
  the above space assassin. It covers every lift, rather than only an associated lift.
- Exact image equality: the second conjunct is `(schemePointMap Ty.obj.hom) ''
  Scheme.Modules.associatedPoints N_y = relativeAssassin ... M_y`, in the actual
  point set of the sheaf fibre X_y.

Dependency declarations read and used (module prefix `Sheaf.AlgebraicGeometry.` unless
otherwise written):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`,
  `IsSurjective`, `EtaleSite`, and `Modules`.
- `AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`; `ProperCurveModuli` supplies
  `MapIsQuasiCompact`, through that recorded dependency.
- `AlgebraicSpaceQuasiCoherentModule`: `QCoh`, the full subcategory for the existing
  Mathlib `SheafOfModules.IsQuasicoherent` predicate.
- `AlgebraicSpaceModuleOperations`: `moduleTensorPullback` and its adjunction-normalized
  construction, read in full at its declaration.
- `AlgebraicSpaceFibreProductsEtaleCovers`: `fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `AlgebraicSpacePointTopology`: `pointTopologicalSpace`; `AlgebraicSpacePointClasses`
  supplies `Point` and `schemePointMap`.
- `SpaceUniversalRelativePurity`: `relativeAssassin`, its union-of-chart-images formula.
- `RelativeAssassin`: `Scheme.Modules.associatedPoints`, `Scheme.Modules.relativeAssassin`.
- `SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`, including its
  canonical restriction, extension and pullback comparisons.
- Landed definition nodes `def-trf-space-module-scheme-restriction`,
  `def-trf-scheme-algebraic-space`, and `def-sfb-space-sheaf-fibre-product` are added
  to stmt_deps for their already available `schemeRestriction`, `schemeSpace`,
  `enlargedFibreProduct`, and `enlargedFibreProductFst`, all read at their definitions.
  The last two nodes have existing:true records in `EnlargedEtaleRingedSite`; that
  module remains imported, but its enlarged-site theorem is not a statement dependency.
- `def-weil-size-convention` is metatheoretic; its convention record requests explicit
  universe polymorphism, not an additional object or hypothesis.

The module also imports all currently recorded proof-dependency modules, including
scheme-test étale calculus, local Noetherian descent, quasi-coherent pullback, tensor
realization, point calculus, Mathlib finite-type base change, Noetherianity and finite
presentation. `lem-sfb-scheme-etale-assassin-invariance` has neither a Lean record nor
an upstream closed declaration in the read node, so it has no module to import yet;
its use is retained in the theorem's full five-step natural-language proof docstring.

Sources opened locally: `literature/stacks-project/spaces-divisors.tex`, lines 588 onward
(0CUY), 601 onward (0CUZ, all chart equivalences and the final associated-point clause),
and 857 onward (0CVV, its explicit fibre-atlas image equality). The source permits the
statement: finite type makes fibre charts locally Noetherian without a Noetherian base.
No statement correction or disputed assertion is needed.

Edge cases checked: empty Y has no y; an empty fibre has empty associated-point sets
on both sides; the zero module has no associated stalks; embedded associated points
are retained (not replaced by generic points); the étale atlas need not be affine or
quasi-compact; Y need not be Noetherian or reduced; no characteristic is excluded;
choice of a different representing T_y changes neither clause under the unique
projection-preserving isomorphism. The common-refinement proof supplies association
for every lift, including when the atlas has many points over one point.

Searches, all run through the prescribed launcher wrapper or read-only source searches:

- LeanFinder: `Associated points on a fibre of an algebraic space detected by a
  surjective etale scheme atlas` → eight unrelated scheme-fibre and étale-property
  hits; none states this result.
- Loogle: `AlgebraicGeometry.Scheme.Modules.associatedPoints,
  AlgebraicGeometry.AlgebraicSpace.relativeAssassin` → zero hits, with the first
  project-specific name unknown to the Mathlib service.
- LeanSearch: `Associated points of an algebraic space detected on an etale atlas`
  → eight hits on scheme étale topology and ring étale loci; no matching statement.
- Mathlib grep through msearch: `associatedPoints|relativeAssassin|assassin` in
  `AlgebraicGeometry` → zero hits.
- Read-only `rg -n 'fibre.*[Aa]ssassin|fiber.*[Aa]ssassin|associatedPoints|FibreAssassin'`
  on `lean/WeilConjectures` and `lean/Sheaf` → existing scheme/space definitions and
  scheme base-change/flat pullback statements, but no space-fibre atlas assertion.
- `rg -n 'lem-sfb-space-fibre-assassin-etale-atlas' lean/WeilConjectures` → no hit.
- `rg -n 'FibreAtlas|fibreAtlas|fibreAtSchemePoint|fiberAtSchemePoint'` on both Lean
  roots → no existing named helper interface. The four delivered definitions merely
  specialize the canonical constructions already supplied by the dependencies.

Validation: scompile.py compiled this file both as an isolated sandbox statement and
as its actual library module, without errors or warnings. The single theorem's only
proof is `sorry`; all four helper definitions contain their actual construction data.

## Second reading by Q25

A separate in-thread pass reopened the node, source passages, and final Lean signature;
no other agent was started, as required by the dispatcher's brief. The maintainer's
independent review remains separate from this worker self-check.

The pass checked the Spec Z base and universe binders, finite type and quasi-compact
diagonal separately, QCoh and finite generation separately, and representability/étaleness
in T's type versus the explicit surjectivity hypothesis. It checked the cartesian square
has corners T_y, X_y, T, X in the right order: the upper map is exactly p_y and the
left projection is the actual sheaf-fibre projection. Thus the square specifies the
object being formed, without an extra mathematical assumption on f or M. N_y is formed
from the original chart restriction N along i, not replaced by an arbitrary module;
M_y uses the canonical first projection. It checked the RHS relative assassin is over
Spec κ(y), so it is the absolute assassin of the fibre, and both clauses use the point
map to X_y rather than to X. The equivalence quantifies every t; the equality is an
image equality of sets, not merely an inclusion or a nonemptiness statement.

No mismatch or statement change was found. The direct imports of construction owners
and the three corresponding landed definition stmt_deps give explicit interface ownership.

## Repair of returned head 773ed5afa0e6

H2: replaced `lem-trf-space-enlarged-etale-ringed-site-model` in stmt_deps with
`def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product`, as requested.
Retained `def-trf-space-module-scheme-restriction`. Read both landed existing:true
definition records on the current shared main checkout and their actual definitions
in `EnlargedEtaleRingedSite.lean`: `schemeSpace` constructs the Yoneda scheme sheaf;
`enlargedFibreProduct` constructs the sheaf pullback and `enlargedFibreProductFst`
its first projection. These are precisely the constructions used by this signature.
Compared the retained sandbox packet with the returned-head dependency list and the
current main item's original dependency list: only the erroneous added theorem owner
was replaced by the two definition owners. The Lean file and its recorded verbatim
signature are unchanged. Updated the dependency discussion and second-reading sentence
above to name the three actual definition owners. No mathematical statement changed.
