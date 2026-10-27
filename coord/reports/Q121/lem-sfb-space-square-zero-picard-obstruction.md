## Worker report

Item: lem-sfb-space-square-zero-picard-obstruction. Group Q121. Stage 2 only.
The main module is Sheaf.AlgebraicGeometry.SpaceSquareZeroPicardObstruction,
with theorem AlgebraicGeometry.AlgebraicSpace.space_squareZero_picard_obstruction.
Its single proof is `sorry`. The additional definition module has real data and
no postponed theorem or `sorry`. The original item statement, proof and
proof_deps are unchanged. No statement correction or disputed statement is needed.

I read Stacks spaces-more-morphisms.tex, lemma-picard-group-first-order-thickening
(Tag 0DNM), both its statement and its complete proof. The source explicitly
uses the common etale site, the short exact units sequence with x mapped to
1+x, and Picard-H1 identification. I also read the item's six proof steps and
every statement dependency's statement, Lean record/mathlib_match, full relevant
signature and docstring. The inherited first-order-ringed-description proof node
has no recorded Lean statement, so there is no import for it. Its site-model
notion is already available from def-sfb-space-square-zero-extension-data; the
present theorem asserts the required model's existence itself rather than
assuming the unstated proof theorem or trying to re-state its unrelated converse.

Clause-by-clause correspondence:

- Arbitrary base scheme S: `{S : Scheme.{u}}`. Both spaces are
  `{Z Z' : AlgebraicSpace S}` and the morphism is `(j : Z ⟶ Z')`.
- Representable closed immersion, square-zero ideal, full point support:
  `(hj : IsSpaceFirstOrderThickening j)`. The recorded definition is
  IsRepresentableWith `(fun _ _ p ↦ IsFirstOrderThickening p.left)`.
  The existing scheme predicate is IsClosedImmersion together with ker^2=bottom.
  A square-zero ideal is nilpotent, so every prime contains it and the closed
  immersion is surjective on points, hence a homeomorphism. No extra
  homeomorphism hypothesis is needed or silently imposed on a different map.
- The actual ideal J and its quasi-coherence: the existential presentation P
  has `ideal : Z.QCoh`, `inclusion`, `injective`, and `kernel_eq`. Its thick ring
  is identified with the transported structure ring of Z' by
  `ringIdentification`; `quotient_normalization` fixes its quotient to the
  regular-function map of the actual reduction scheme charts. Thus P.ideal is
  the actual kernel, not a freely chosen module. Kernels with these inclusions
  are uniquely isomorphic, so expressing this kernel by a presentation adds
  no mathematical hypothesis and does not change its cohomology.
- Quotient O_Z action on J: `P.scalar` says i(p(a)m)=a i(m).
  `P.square_zero` says i(m)i(n)=0. `P.locally_surjective` records exactly local
  lifting along a covering sieve, not surjectivity on every object.
- Line modules: the existing `RingedSitePicard.Line` is the subtype of module
  sheaves satisfying the existing `SheafOfModules.IsInvertible` (local
  rank-one generators/local isomorphisms to O). It is applied on the existing
  small affine etale basis. `smallModuleEquivalence` transports this to the
  specified original small etale ringed site, preserving local trivializations.
- Picard group: the existing `RingedSitePicard.Pic` is the isomorphism quotient
  of those actual line modules; `lineClass` is its quotient map. The witnesses
  `c' : Comparison ...` and `c : Comparison ...` contain AddCommGroup structures
  normalized by the structure-module zero and tensor-product addition.
  Their H1 equivalences are normalized by the actual generator extension class.
  Thus the group operation is the node's tensor product, with additive notation.
- Tensor restriction: the homomorphism `r` is normalized on every actual line M
  by existence of a line N isomorphic to
  `Z.smallModuleRestriction.obj ((moduleTensorPullback j).obj
  (Z'.smallModuleEquivalence.inverse.obj M.val))`, with
  `r (lineClass M) = lineClass N`. This uses the canonical existing adjoint
  tensor pullback of the enlarged etale ringed construction, transported
  through the already recorded small-model equivalence. It is not an
  arbitrary map between Picard groups.
- H2 means module cohomology: `picardModuleCohomology Z J 2` is
  `Ext.{u} (SheafOfModules.unit Z.smallStructureRings) J 2` in the category of
  ALL small-model module sheaves. Hom(O,-) is exactly global sections, by
  SheafOfModules.unitHomEquiv. Mathlib's
  InjectiveResolution.extAddEquivCohomologyClass computes this Ext group using
  any injective module resolution, so it is exactly right derived global
  sections, not right derivation inside QCoh and not cohomology with coefficients
  in a replacement constant ring. There is no assumption that forgetting an
  injective module gives an injective abelian sheaf.
- Canonical homomorphism delta: the existential `δ` is explicitly an
  AddMonoidHom from the tensor Picard group to that module H2. Its displayed
  normalization is `P.moduleToAbelian 2 (δ L) = H.map ...
  (H.δSucc P.exact 1 (c.comparison L))`. The isomorphism
  `P.unitsIdentification` is fixed on sections by x mapped to 1+i(x).
  `P.moduleToAbelian` is constructed as forgetful pushforward of Ext classes
  followed by precomposition with the integer-to-structure map 1 mapped to 1.
  Its bijectivity is asserted as part of the theorem. Thus the equation
  uniquely fixes delta by the source's connecting map; exactness alone is
  not being used as a purported definition of a canonical obstruction.
- Exact at Pic(Z): `Function.Exact r δ` states precisely image(r)=kernel(delta).
- Vanishing consequence: `Subsingleton (picardModuleCohomology ... 2)` implies
  that every `L : Line Z.smallStructureSheaf` has an `L'` on Z' together with
  `Nonempty (restriction L'.val ≅ L.val)`. The isomorphism is part of the
  conclusion, not merely existence of an equal class or an arbitrary module lift.
- No Noetherianity, properness, flatness, finite presentation, dimension,
  nonemptiness, field, or characteristic hypotheses occur. The only implicit
  size choice is the existing u-small affine basis in the same section universe.

Dependency declarations reused:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion, through the recorded scheme thickening.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace,
  IsRepresentableWith, EtaleSite, structureSheaf, Modules, IsLineModule.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh, using
  Mathlib SheafOfModules.IsQuasicoherent and its local-presentation definition.
- Sheaf.AlgebraicGeometry.SpaceCotangentRingMap: the recorded
  cotangentRingMap and its publicly imported enlarged ringed-site construction.
- Sheaf.CategoryTheory.SiteCoveringAxioms: Precoverage.IsSiteForCoverings;
  cohomology remains Mathlib Sheaf.H, not a second site/cohomology definition.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules/SheafOfModules.
- def-weil-size-convention is a metatheoretic convention: explicit universe u
  and SmallEtaleModel realize it; no fictitious extra object is introduced.
- Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData:
  IsSpaceFirstOrderThickening, ThickeningSiteModel, its reduction, quotient and rings.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel:
  SmallEtaleModel, smallStructureSheaf, smallStructureRings,
  smallModuleRestriction, smallModuleEquivalence.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  moduleTensorPullback, fixed by its adjunction to the canonical chart-limit direct image.
- Sheaf.CategoryTheory.Sites.RingedSitePicardData: ring, units, integers,
  integerOne, Line, Pic, lineClass, Comparison and its normalization.
- Mathlib CategoryTheory.Abelian.Ext and Functor.mapExtAddHom, and the canonical
  Sheaf.H.δSucc and Sheaf.H.map from
  WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic.

Proof-only imports retain the DAG plan: RingedSitePicardH1Natural,
ModuleAbelianEvaluationComparison (including its general Grothendieck-site
interface), RightDerivedUniversalDeltaFunctor, RingedSiteGrothendieckAbelian,
and Mathlib Sites.EpiMono. The consumer retains its stated proof-dependency imports; the helper
does not need an explicit EnoughInjectives import. The unrecorded first-order-ringed-description has no module to import.
No cycle is introduced and no dependency node is repaired or copied.

Edge cases checked mathematically before drafting and again against the signatures:
J=0 and the identity thickening give a zero obstruction and surjective restriction;
the empty algebraic space is included (local triviality and the zero section rings
are permitted); zero rings retain their unit 1=0 and the normalized integer map;
k[epsilon]/epsilon^2 -> k satisfies the square-zero formulas in every characteristic,
including 2; general nonproper/non-Noetherian spaces need no added hypothesis.
The small scheme-object site need not have a terminal object: Ext from O computes
module global sections and the abelian comparison uses the enlarged model only
in the proof. No terminal object is added to the hypothesis.

Searches before writing:

- msearch leanfinder, `Picard obstruction exact sequence square zero thickening
  algebraic spaces`: eight hits, cotangent exactness and formal unramifiedness;
  no algebraic-space Picard obstruction theorem.
- msearch loogle, `"Pic", "Exact"`: three hits, the two ring Picard exactness
  results and path-homotopy exactness; none is this statement.
- msearch grep, `Pic.*(thicken|square|obstruct)|picard.*(thicken|obstruct)|thicken.*Pic`:
  only an unrelated matrix-block comment in Mathlib.
- rg/grep in lean/WeilConjectures and lean/Sheaf for the item id, Picard
  obstruction and square-zero units: no exact theorem. The existing
  SquareZeroPicardObstruction and SquareZeroUnitsBoundary are scheme/Zariski
  constructions, not algebraic-space small-etale constructions. Reused the
  general ringed-site Picard data and space site models instead.
- Searches for the added notion are recorded verbatim in its mathlib_searches:
  LeanSearch (eight unrelated normalization/group cohomology hits), LeanFinder
  (eight ring extension/cotangent hits), and Mathlib grep (zero hits). Project
  and DAG search located only the scheme-specific units boundary. The additional
  blueprint searches returned no existing normalized algebraic-space presentation.

Validation: scompile.py compiled each module separately in dependency order in
its private server directory, including the library-name pass for the consumer.
The initial elaboration errors were repaired by explicit underlying-ring casts,
explicit coefficient universes, and Functor.whiskerLeft; no implicit variables,
local notation, private definitions, or theorem proofs were introduced. A line
length warning was repaired. Final delivery preflight and compile results are
recorded below after the prescribed dry run.

## New nodes

`def-sfb-space-picard-units-presentation` defines the normalized common-site ring,
kernel and units presentation, its integer unit, the module-cohomology abbreviation,
and the concrete module-to-abelian Ext homomorphism. Source: Stacks 0DNM proof,
05ZS, 040E and 03FD. Its field equations fix the actual geometric quotient,
quotient action, x mapped to 1+x and 1 mapped to 1. The structure is only a notion:
it assumes neither existence nor a chosen inverse comparison. The item's theorem
asserts existence and the needed bijectivity. Its helpers reuse Mathlib kernels,
short complexes, Ext and exact-functor maps. The searches above show why the
existing scheme-specific boundary and general site-model nodes do not define
this combined normalized presentation. It is in the item's chapter and cites
each existing definition it uses. Its inherited null blueprint ancestor is
preserved, with the item's complete ancestry path and the item prepended to via.
The item also adds the already landed def-trf-space-etale-module-functors to
stmt_deps to cite the exact moduleTensorPullback it uses.

## Second reading by Q121

Separate rereading pass by this worker, with both files and the original node open;
no second agent was started, as explicitly required by the dispatcher. This is not
represented as an independent agent review; the maintainer's independent review
remains the delivery review specified in the brief.

I checked the base scheme and both spaces against the first line of the node;
`hj` unfolds to scheme-test closed immersions with square-zero kernel. The
presentation's geometric quotient identification excludes an unrelated ring
extension. Its QCoh field and injective kernel map encode exactly the stated
ideal; its scalar equation supplies the quotient action. I read Line's
IsInvertible definition (local rank-one generators) and Comparison.normalized's
unit/tensor/generator-extension clauses. Thus neither tensor invertibility of an
unrelated derived object nor H1 merely renamed Picard is used. I checked the
restriction expression uses moduleTensorPullback of this j and both existing
small-module equivalences in the correct directions. The boundary normalization
and bijectivity of moduleToAbelian force the canonical delta. Function.Exact
has the correct orientation from Pic(Z') to Pic(Z) to H2, and the last
Nonempty contains the actual restriction isomorphism in the direction required
for an extension. Ext is in all module sheaves, not the quasi-coherent subcategory.

This pass found and repaired a missing explicit local-surjectivity field in the
presentation and one overlong line. It also moved the module-operations import
to the consumer that uses tensor pullback. No statement change, omitted case,
extra geometric hypothesis, or hollow definition remains.

The current blueprint source was read from literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md, rather than an old snapshot.
The item is a supporting Stacks lemma, not the blueprint unit statement.

## Validation completed (retry, 2026-10-24)

The retained packet was inspected first and the prescribed dry run was retried.
Three dry runs and an explicit scompile.py invocation reproduced the private-overlay
error `resource exhausted (error code: 28, no space left on device)`.
No launcher script or live repository file was edited.

The helper's unused public import of
Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives was removed.
The helper then compiled under both its sandbox and library names in 16.8 and
17.9 seconds. A subsequent scompile.py invocation compiled both delivered modules
separately in dependency order, including the consumer under both names (12.6 and
12.7 seconds), with no errors or warnings. The theorem and all definition
signatures are unchanged; the helper has no sorry and the consumer has exactly
its named theorem's expected sorry.

The required deliver2.py --no-push passed server preflight and compilation:
`OK (dry run): commit f2471a9de7a passes the preflight and compiles; nothing pushed`.
A final self-check confirmed both lean.statement fields match their source
signatures verbatim, canonical JSON formatting, maximum Lean line lengths 90 and
93, and changes to the existing item limited to lean and added stmt_deps. The
retained clause-by-clause correspondence and edge-case analysis above still apply.
The push wrapper repeats preflight and compilation for the updated report.
