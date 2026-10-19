## Worker report

Second-reader status: the following worker account is preserved as history. The
final two-module packet and current published dependencies are described in
"Second reading by Q33" below; its findings supersede earlier interface claims.

Current worker validation (2026-10-16): retained the prior implementation and
independent second-reading record. Refreshed the two stale dependency node copies
from the shared repository, preserving only their delivery-owned `lean` fields;
in particular the existing scalar-exactness statement correction is retained.
Re-read the live pro-etale module-derived-category and internal-Hom signatures,
the completed coefficient sheaf and its quotient levels, and the live rational
coefficient source through `scompile.py --source`. The latter still requires a
finite-field datum, so the unrestricted dependency interface remains necessary.
Repeated LeanFinder for "Locally bounded complexes of finite projective sheaves
on a ringed site" returned finite-type/presentation APIs, Loogle
`"IsLocallyPerfect"` returned zero hits, and Mathlib Algebra grep
`IsPerfectOnRingedSite|IsLocallyPerfect|PerfectComplex` returned zero hits.
Upstream/project searches found no declaration of this four-stage notion.
Checked all fifteen delivered modules for explicit auto-implicit disabling and
100-character lines, and checked their primary recorded signatures against the
files, including named arguments occurring inside theorem signatures.
The scalar-extension core is now retained verbatim from the published interface,
including independent scheme/coefficient universes and both comparison names.
The new ordinary finite-free helpers are appended in a separate namespace section,
so they do not narrow the core or remove a published declaration. The unrestricted
constructibility and composition repairs now use separate sf module paths; their
previously published datum-parameterized modules remain available. The unrestricted
constructibility theorem is named `sfIntegralScalarExtension_constructible`.

The item is stated in `lean/Sheaf/Paper/SitePerfectComplex.lean`. It defines four
predicates, one for each coefficient stage, and two local rational-model helpers.
All definitions contain real data. The delivered dependency theorems retain `sorry`;
this is a stage-2 delivery, not a proof delivery.

Repairs on resumption: named the canonical small coefficient-field structures to
avoid repeated unfolding during elaboration; restored the complete recorded
signatures of `integralOperationsWellDefined` and
`commonStage_verdier_existsUnique` (including nested named arguments); and put the
two finite-tensor zero-map `by sorry` proofs on their declaration lines so that the
stage-2 parser reads them correctly. The maintainer's static statement-module
checks now pass for all delivered modules, and the overlaid dependency graph has
no cycle reachable from this item. These repairs do not change the item's statement.
The common-stage inclusion is applied with its implicit `l`, `Ω`, and `Y` parameters
named explicitly, matching its declared signature.

Resumption verification (2026-10-16): read the item and all direct dependency
records, the general-site perfectness repair, and the four defining predicates.
Repeated `msearch.py leanfinder` for locally bounded finite-projective sheaf
complexes returned K-projective and finite-presentation declarations. Loogle
`"IsLocallyPerfect"` and Mathlib grep
`IsLocallyPerfect|IsPerfectOnRingedSite|StrictlyPerfect|PerfectComplex` under
`Algebra` returned no hits. The upstream source search finds the constant-ring
`AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect`; its full signature
was checked and it does not cover the completed or rational stages. The current
server `Sheaf.Paper.RationalizationKaroubi` source still requires `D` and `l ≠ D.p`,
so the unrestricted dependency repair remains needed. Refreshed each existing
sandbox node from the shared record while preserving only this delivery's `lean`
and the item's added statement dependencies; this retains newly added review data.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. A finite coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `Y : AlgebraicGeometry.Scheme` is arbitrary; no Noetherian, properness,
  finite-type, connectedness, or geometric-stalk condition is introduced.
- The small pro-etale site is `Y.ProEt` with `Scheme.ProEt.topology Y`, from the
  recorded `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` interface. Its object
  universe is `t + 1` and its morphism universe is `t`; these are not identified.
- Finite coefficients are `integralCoefficientSheaf l E Y n` from
  `Sheaf.Paper.CompletedIntegralCoefficients`. This is exponent `n + 1`, so `n : ℕ`
  parametrizes exactly all positive exponents in the node, including exponent one.
  `IsFiniteCoefficientSitePerfect` takes an object of the actual derived category
  of modules over this sheaf, with the standard derived-category localization.
- A cover and bounded finite-projective local models are expressed by
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`. Unfolding its definitions gives
  `∀ V, ∃ S : Sieve V, S ∈ J V ∧ ...`. For every arrow in this covering sieve,
  the restricted complex admits a quasi-isomorphism from a complex `F` with
  `∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (F.X n)`.
  Thus bounds can depend on the covering member. The existential representative
  of the derived object is connected to `K` by `Nonempty (K ≅ Q.obj P)`.
- Each finite-projective term has chosen maps `i n`, `p n` to/from the product of
  `Fin (N n)` copies of `SheafOfModules.unit`, with `i n ≫ p n = 𝟙 _`.
  Finite products are finite sums in this abelian category. The ranks can vary by
  degree and cover member, and may be zero. The maps are degreewise splittings,
  with no extra chain-map condition.
- `IsIntegralCoefficientSitePerfect` uses exactly the same local predicate with
  `completedIntegralCommRingSheafUnrestricted l E Y`. Forgetting commutativity is
  the recorded `completedIntegralCoefficientSheafUnrestricted`. These are the
  actual completed sheaves from the dependency, not a constant discrete valuation
  ring sheaf. The unrestricted spelling avoids an irrelevant finite-field datum;
  the dependency's datum-parameterized spelling is definitionally the same sheaf.
- The rational input is the raw category `rationalConstructibleCategory l E Y`
  from `Sheaf.Paper.RationalConstructibleCoefficients`, namely the recorded
  integral constructible category with Hom modules tensored with the fraction
  field, without a Karoubi envelope. `sitePerfectRationalAmbient` uses this same
  raw scalar-localization construction on the ambient completed derived category
  to compare local models. Its scalar action is the canonical constant-section
  action `integralCoefficientLinear` from `Sheaf.Paper.IntegralConstructibleLinear`,
  reused by `Sheaf.Paper.SfIntegralConstructibleLinear`.
- `IsRationalCoefficientSitePerfect` again requires an actual covering sieve.
  On a cover member `U`, the restricted integral representative is
  `(integralDerivedPullback l E U.hom).obj K.obj.obj`. This is precisely the
  completed pullback specified by `def-pur-integral-derived-operations`; for a
  member of the pro-etale site it computes restriction of the complete object.
  There is a bounded cochain complex `F` of completed module sheaves, and an
  isomorphism, **after scalar localization**, between that restriction and
  `Q.obj F`.
- Rational finite projectivity is `IsRationalFiniteProjectiveTerm`: the degree-zero
  image of `F.X n` is a retract of the degree-zero image of a finite sum of the
  completed unit in `sitePerfectRationalAmbient`. Both splitting maps and the
  splitting equation belong to the localized category. They need not exist
  integrally. This is the rational clause, not the stronger demand for an
  integral-perfect model.
- The bounded-model presentation retains the source's actual bounded complexes.
  In the degree-zero fully faithful embedding, localized Hom maps are exactly
  module maps with uniformizer denominators. A bounded complex has finitely many
  relevant differentials and relations. Choose a common denominator, multiply
  degrees successively by powers of the uniformizer, and multiply further to kill
  the finitely many torsion differential-composite relations. This produces an
  integral complex with the same bounded rational complex. Conversely localizing
  any displayed integral complex gives a bounded rational complex. Term splittings
  are only asserted after localization in both directions. This explains the
  presentation without substituting a finite tower of distinguished triangles.
- `IsAlgebraicallyClosedCoefficientSitePerfect` says `∃ E, ∃ P, ... ∧
  Nonempty (K ≅ inclusion.obj P)`, with `E` an actual finite intermediate field in
  the fixed algebraic closure, `P : Stage l Ω Y E`, and rational site-perfectness
  over its canonical algebra-equivalent small model `Coefficient l Ω E`.
  The inclusion is the recorded common-stage inclusion. The algebraic closure
  universe and the scheme universe are independent. This is an isomorphism in
  the actual pair category, not equality of chosen representatives and not a
  formal retract closure.
- The final sentence of the node is enforced by the cover quantifiers in all
  three local predicates. No geometric-stalk test is used as a substitute.

Dependency declarations used directly: the completed/finite coefficient sheaves and
CommRing enhancements in `Sheaf.Paper.CompletedIntegralCoefficients`; the generalized
`SheafOfModules` local-perfectness predicates in
`Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`;
`WeilConjectures.integralDerivedPullback` in `Sheaf.Paper.IntegralDerivedOperations`;
`WeilConjectures.integralCoefficientLinear` in `Sheaf.Paper.IntegralConstructibleLinear`,
reused through `Sheaf.Paper.SfIntegralConstructibleLinear`;
`WeilConjectures.rationalConstructibleCategory` in
`Sheaf.Paper.RationalConstructibleCoefficients`; and `Stage`, `Coefficient`, `Index`,
`inclusion`, and `algebraicallyClosedConstructibleCategory` in the coefficient
stage-system and algebraically-closed-coefficient modules. The full four-stage
pullback/tensor/Hom node has no record, but no new copy of its operations is needed:
the exact pullback operation used here is its already-recorded integral-operation
dependency, and site restriction at finite/integral level is Mathlib's `overFunctor`.

Edge cases checked: rank zero is allowed (`Fin 0`); the zero complex is bounded;
bounds and ranks are not uniform across the cover; exponent one is included;
all positive exponents occur; empty schemes and empty covering sieves are interpreted
by the topology rather than a nonemptiness assumption; a rationally split term is
not required to split integrally; identity coefficient extensions and repeated stages
use the normalized scalar units/associators; algebraic closure and site universes
are independent, and finite/integral coefficient universes are independent of the
site universe. No special hypothesis is imposed on stalks. No statement correction
or counterexample was needed.

Searches: `msearch.py leanfinder` for locally bounded finite-projective sheaf models
returned derived representatives/K-projective declarations, not this four-stage
notion. Loogle `CochainComplex.IsStrictlyGE, Retract` returned no result (unknown
`Retract`), and `"IsPerfect"` returned unrelated perfect pairings/graphs. Mathlib grep
`IsPerfect|StrictlyPerfect|PerfectComplex|IsLocallyPerfect` returned unrelated results.
LeanSearch for local perfectness was unavailable (Internal Server Error), so no
mathematical verdict is inferred from it. Upstream/project `rg` found the landed
strict-perfect package; it is reused and generalized only in its universes.
The upstream node-id search found no declaration of this item. Blueprint search
`site-perfect` found uses of the notion, not a second full definition. Current server
source and delivery-branch inspection confirmed that rational/common-stage dependency
records were absent. Candidate canonical coefficient modules from the read-only Q36
sandbox were inspected and included, with their prerequisite statements, rather than
waiting for their landing. All modified files are in this sandbox.

## Earlier proposed new nodes (superseded)

The resumed worker also read the blueprint definition and its enclosing unit directly
on the server. The unit is a projection-formula reduction statement; this auxiliary
definition is not the unit statement. The DAG's already clarified common-stage clause
matches the source's finite-field representative condition up to isomorphism.
Repeated searches used LeanFinder's query "A complex of sheaves on a ringed site is
perfect if locally isomorphic to a bounded complex of finite projective sheaves",
Loogle `"IsPerfect"`, and Mathlib grep
`IsPerfect|StrictlyPerfect|PerfectComplex|IsLocallyPerfect`. LeanFinder returned
K-projective and finite-presentation declarations; Loogle and grep returned unrelated
perfect-pairing, field, group and graph notions. The upstream source search also found
`AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` in
`WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean:428`: it is a predicate
on derived sheaves valued in modules over a constant ring. It does not supply
the completed coefficient sheaf or the raw rational/common-stage categories here.
The existing general ringed-site predicate is therefore specialized, using its
independent-universe repair, rather than replacing the completed coefficient sheaf
by constant coefficients. Upstream `DerivedCategory.IsPerfect` concerns ordinary
modules at a point, not local models on this coefficient site.

`def-sf-rational-coefficient-stage-system` defines the actual rational stage categories,
canonical small coefficient-field models, normalized scalar transitions and associators,
and their directed stage system. Source: the finite-stage construction in blueprint
order 1462. It is needed by the common-stage clause. Search of the DAG, blueprint,
Mathlib, upstream Lean, and `lean/Sheaf` found no such specialization. LeanFinder returned
field-embedding filtrations and generic direct-limit declarations, not this datum;
LeanSearch was unavailable. The existing upstream `StageSystem` is used. The stage
system is assembled directly from the specified functors and associators, with only
the cocycle proof postponed; it is not selected from an unspecified existence theorem.
`Coefficient` is a named definition of the same canonical `Shrink` model, with
explicit transported `coefficientField` and `coefficientAlgebra` instances. This keeps
typeclass inference from repeatedly expanding the field transfer through `Shrink`;
it changes neither the coefficient field nor the transition maps.

## Earlier dependency modules (superseded)

`def-weil-pbc-strict-perfect-coefficient-package`: the original interface equates site
object, morphism, and coefficient universes and cannot accept the small pro-etale site.
The new module imports that interface and supplies the identical splitting, local
perfectness, perfect derived object, and localized representation definitions with
independent universes. The original coefficient-ring and constant-sheaf APIs remain
available through its import. Only this dependency's `lean` record changes.

`def-pur-integral-derived-operations`: import repair, using only the owning
`IntegralOperationsWellDefined` and `DerivedInternalHomOfUniverses` modules,
which provide the declarations used, instead of broad and retired duplicate imports. The actual normalized pullback, completed tensor, internal Hom, and their
representative comparisons are retained.

`lem-pur-integral-operations-well-defined`: repair the retired duplicate K-flat import
and specialize the independent-coefficient monoidal/zero-map interface in
this owning module. The source and published KFlat artifacts expose different names
for that general interface; the specialized proof obligations are named theorems
with complete proof docstrings. The
finite-level tensor models, transitions, signed Roos construction, derived-limit
property and unique normalized descents are unchanged.

`lem-weil-integral-constructible-triangulated`: the recorded finite-field-datum interface
cannot supply the unrestricted integral categories required here. State triangulated
and isomorphism closure for the already-recorded `sfIntegralConstructible` predicate.

`lem-weil-integral-constructible-linear`: likewise use that unrestricted full category.
The new module preserves the original datum-parameterized module and declarations.
The scalar action is the actual constant-section action descended through the standard
derived localization, with ring laws, and is inherited by the full subcategory.

`lem-weil-integral-scalar-extension-well-defined`: reused from the published library.
It supplies the canonical quotient maps, strict scalar tower and Roos model, plus
the normalized unique descent and actual constant-section scalar compatibility.
The final preflight found that this module had landed unchanged. A fresh
`scompile.py --source Sheaf.Paper.IntegralScalarExtensionWellDefined` check confirmed
that its published text is identical to the sandbox copy, so both its redundant
module and redundant node copy were removed from the delivery.

`def-weil-integral-scalar-extension`: there was no recorded declaration. Supply the
canonical Roos descent and its comparison, actual completed coefficient inclusion,
ordinary finite-free tensor model and its exact derived functor.

`lem-weil-integral-scalar-extension-constructible`: there was no recorded declaration.
State preservation of the recorded unrestricted integral condition, including the
ordinary finite-free model; restrict that actual functor to the full subcategories.
Its comparison to the Roos model is stated without choosing an arbitrary isomorphism.

`def-weil-rationalization-karoubi`: there was no recorded declaration. Supply the raw
scalar localization of the recorded integral category, its canonical Hom tensor-field
coordinates, inherited triangulation and actual scalar-extension tensor Hom map.
No idempotents are adjoined.
The resumed branch check found the delivered Q04 `RationalizationKaroubi` interface
and read its full `rationalizedIntegralCategory` signature. That interface requires
an auxiliary `FiniteFieldDatum D`, a proof `l ≠ D.p`, and the corresponding
datum-parameterized integral category. It cannot be instantiated in this item's
arbitrary-scheme, unrestricted-coefficient setting. The present dependency repair
uses the existing `sfIntegralConstructibleCategory` and the same raw scalar
localization construction; it does not introduce an auxiliary characteristic choice.

`lem-weil-scalar-extension-composition`: there was no recorded declaration. Supply the
scalar associators and units fixed on ordinary sheaf tensor generators, their derived
and full-subcategory restrictions, their raw rationalizations, and their coherence.

`lem-weil-scalar-extension-exact-triangulated`: there was no recorded declaration.
Supply the shift comparison normalized by the actual integral derived comparison,
and state exactness and additivity of the rational scalar-extension functor.

`def-weil-algebraically-closed-coefficients`: there was no recorded declaration. Supply
the actual upstream pair category of the specified coefficient stage system, its Hom
colimit coordinates, canonical inclusions, common-stage triangles and triangulation.
The closure universe is independent of the scheme universe. No Karoubi envelope is
used. Every existing dependency copy changes only its `lean` field.

`def-weil-pbc-common-stage-cones` and `thm-weil-pbc-verdier-axioms`:
the current server could not supply StageSystemVerdier or its common-stage-cone
module. Include their canonical generic interfaces on the existing upstream
StageSystem pair category. The cone is the actual pair at its chosen finite stage;
the final arrow includes the prescribed signed shift comparison. Distinguishedness
is the isomorphic finite-stage image criterion. The Verdier theorem states the
unique pretriangulation with that set, TR4, exact stage inclusions, and the assumed
shift compatibility of the canonical transition identifications. Its proof docstring
spells out finite-diagram lifting for all four axioms. No new independent notion
is introduced.


## Earlier second reading (a previous round; superseded)

Independent second reading, 2026-10-16. I opened the delivered node, all fifteen
modules and their owning node statements, all five original statement dependencies,
and the relevant recorded dependency declarations. The source blueprint is not
materialized in the local read-only mirror, so I read the actual source on the
server over SSH: order 1881 and its enclosing `_section.md`, plus the rational
and algebraically closed coefficient definitions at orders 1460 and 1462.
I also read Stacks `sites-cohomology.tex`, `definition-strictly-perfect`,
`definition-perfect` (08G5), and the following independent-representative lemma.
That lemma explains why the covering-of-the-final-object formulation and the
all-site-objects covering-sieve formulation agree here. The enclosing unit is
projection-formula compatibility, and this node is an auxiliary definition.
The sandbox statement equals the current reviewed node statement; there is no
stage-2 `statement_change` to audit and no unit statement is altered.

My object/hypothesis/clause list and the corresponding Lean are:

1. A scheme Y and its small pro-etale site: the finite/integral definitions bind
   `Y : Scheme.{t}` and use `Y.ProEt` / `Scheme.ProEt.topology Y` through the
   recorded coefficient sheaves. I opened `ProEtaleDerivedCategory` and the
   finite constant CommRingCat construction: these are the prescribed site and
   coefficient-module categories. Verdict: same objects.
2. A prime ell, a finite extension E/Q_ell and each positive exponent:
   `(l : ℕ) [Fact l.Prime]`, the field/algebra/finite-dimensional instances on E,
   and `n : ℕ` with `integralCoefficientSheaf ... n` meaning exponent n+1.
   The coefficient extension is not restricted to Q_ell itself or to an
   unramified extension. No hypothesis on the characteristic of Y, or on its
   finiteness, separation, nonemptiness or stalks, is introduced. The ancillary
   finite-field datum in older dependency interfaces is absent from these
   constructions; it does not enter the actual completed sheaf. Verdict: exact.
3. A finite-coefficient complex K in the ambient derived category:
   `IsFiniteCoefficientSitePerfect` binds the standard derived localization of
   `SheafOfModules (integralCoefficientSheaf ... n)`. Its body specializes
   `IsPerfectOnRingedSiteOfUniverses`. Unfolding gives a representative P and
   `Nonempty (K ≅ DerivedCategory.Q.obj P)`, then for every V a sieve
   `S ∈ J V`, and a local quasi-isomorphism from a model F into the restriction
   of P on each arrow of S. This is derived local isomorphism on a genuine
   covering, not a condition on separate geometric stalks. Verdict: exact.
4. Each local F is bounded with finite-projective terms:
   `∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (F.X n)` and
   the existing `StrictPerfectCoefficientPackageOnSite` give, degree by degree,
   `N n : ℕ`, maps to/from the finite product of copies of
   `SheafOfModules.unit`, and `i n ≫ p n = 𝟙 _`. In an abelian module-sheaf
   category finite products are the stated finite sums. These are degreewise
   splittings, not maps of complexes into a fixed free complex. Both ranks and
   bounds can depend on the covering member. Verdict: every clause present.
5. Integral coefficients are the completed coefficient sheaf:
   `IsIntegralCoefficientSitePerfect` specializes the same local predicate to
   `completedIntegralCommRingSheafUnrestricted`. I opened its definition and
   the forgetful presentation: the underlying ring sheaf is the actual limit
   of the finite constant quotient sheaves, definitionally the same completion
   as the datum-parameterized dependency spelling. It is not a discrete
   constant O_E sheaf. Verdict: exact.
6. Rational coefficients use the raw scalar localization:
   `IsRationalCoefficientSitePerfect` takes `K : rationalConstructibleCategory`.
   I opened `sfIntegralConstructible`, `integralTowerModules`, the raw
   `ScalarLocalization`, and the delivered rational dependency. Its objects
   are integral constructible representatives and its Hom groups are the
   stated tensor-field modules; no Karoubi envelope is taken. A covering sieve
   precedes the local model quantifier. `integralDerivedPullback ... U.hom`
   is the recorded completed pullback of the integral representative to the
   cover member. For a complete input this computes the required restriction.
   Verdict: correct coefficient category and restriction.
7. The rational local model is bounded with finite-projective terms after
   localization: the model F is an actual bounded integral cochain complex,
   its image represents the restricted object in `sitePerfectRationalAmbient`,
   and `IsRationalFiniteProjectiveTerm` asks for the two splitting arrows and
   their identity in that localized category. The splitting arrows need not
   lift integrally. The degree-zero derived embedding is fully faithful;
   scalar localization therefore has the ordinary localized module maps in
   degree zero. For a bounded complex, finitely many differential denominators
   and differential-composite relations can be cleared: rescale consecutive
   degrees by uniformizer powers, then multiply differentials by a further
   common power killing the finitely many torsion composites. Degree rescaling
   identifies the rational complexes. Conversely the displayed F localizes to
   such a bounded rational complex. This presentation retains the source's
   bounded-complex meaning and does not replace it by a triangle tower.
   Verdict: equivalent presentation of exactly the rational clause.
8. The algebraically closed category is the common-stage pair category, and
   perfectness is descent up to isomorphism from some finite coefficient field:
   `IsAlgebraicallyClosedCoefficientSitePerfect` quantifies over an actual
   `Index l Ω`, then `P : Stage ... E`, requires rational perfectness over its
   algebra-equivalent `Coefficient`, and requires
   `Nonempty (K ≅ inclusion.obj P)`. `Pair` is the upstream
   `StageSystem.PairCategory` of the specified rational system. Verdict: exact;
   neither literal equality of representatives nor retract closure is imposed.
9. Covers, not individual-stalk tests, are required: all three local predicates
   quantify over covering sieves before their local model choices. The
   common-stage clause calls the rational predicate. Verdict: final sentence
   retained without adding a stalk criterion.

Edge cases: `Fin 0` allows zero-rank summands; the zero complex admits any finite
support interval; n=0 is exponent one, and every allowed positive exponent occurs.
Bounds are local rather than globally uniform. An empty scheme or an empty covering
sieve is governed by its Grothendieck topology; there is no Nonempty hypothesis.
Identity extensions and repeated coefficient stages retain the normalized units
and associators. The finite/integral definitions have independent site and coefficient
universes, with site objects in t+1 and morphisms in t. Rational stages use the
recorded common coefficient/site size convention. The finite coefficient fields
admit the explicit finite-basis `Small` witness and `Shrink.algEquiv` transport;
the algebraic closure universe v is independent of the scheme universe u. No extra
equality between site object and morphism universes has been imposed.

Independent H4 searches used different wording: `msearch.py leanfinder` for a site
complex locally having a finite resolution of finite-rank projective sheaves returned
K-projective/resolution and finite-presentation declarations; these are not the local
four-stage predicate. Loogle `"IsLocallyPerfect"` returned zero hits. Direct rg of
Mathlib Algebra returned no local-perfect-complex definition. Upstream and side-project
rg found `AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` and the existing
strict-perfect coefficient package. I opened both: the upstream predicate concerns
sheaves valued in modules over a constant ring, whereas the present integral and
rational stages require the completed sheaf and raw scalar localization. The current recorded
`StrictPerfectCoefficientPackageOnSite` already provides the independent-universe
degreewise package. I removed the worker's duplicate package and reused that exact
structure; only its missing local-perfectness and derived-representation wrappers
are generalized from the old same-universe interface. There is no existing exact
four-stage declaration to record in place of this module.

New-node reading (H12): `def-sf-rational-coefficient-stage-system` is the finite-stage
transition datum actually described in blueprint order 1462. Its objects, inclusions,
normalized associator/unit and cocycle match that source. I read its complete node,
including source, dependencies, empty proof lists, creation/blueprint/lean-audit fields,
and its module. `stageSystem` has explicit T and assoc fields; only the cocycle proof
is postponed. `coefficientSmall` uses finite-basis coordinates, and `Coefficient` is
an actual Shrink construction, with transported field/algebra structures. A second
LeanFinder query for constructible categories indexed by finite extensions returned
field-embedding and normal-closure declarations; Loogle `"StageSystem"` returned no
hits. Blueprint search `coefficient stage system` returned no nodes. DAG/upstream/side
rg found the generic pair-category infrastructure and the enclosing common-stage
category node, but no separate specialized normalized rational transition datum.
The generic upstream StageSystem is reused, including its actual quotient category.

Dependency-module reading (H13): I matched each delivered dependency to its own node,
not merely to the name used by the item. The general strict-perfect interface retains
the original ring-module and constant-sheaf constructions through its public import;
the canonical OnSite structure supplies the ranks, maps and splitting. Only its
local boundedness/perfectness and derived-representation wrappers are added at
independent universes. IntegralOperationsWellDefined builds
finite reductions, actual pure-tensor transitions and the signed mapping cocone,
then states quasi-isomorphism invariance and descent with unique compatible
representative comparison. IntegralDerivedOperations selects that normalized descent.
SfIntegralConstructibleTriangulated retains completeness and constructible reductions
in one interval; SfIntegralConstructibleLinear imports the existing canonical ambient
constant-section action and shift linearity, and restricts them to the unrestricted
full subcategory. IntegralScalarExtension uses its
published normalized Roos descent, and its ordinary completed-coefficient map is fixed
by all finite projections. Its constructibility module restricts actual finite-free
ordinary tensor and states comparison with the Roos construction. The rational module
uses the raw Hom tensor localization and gives its scalar map on pure tensors.
ScalarExtensionComposition fixes associators/units on sheaf tensor generators before
deriving, restricting and rationalizing; ScalarExtensionExact fixes the shift comparison
by that integral comparison and states preservation of distinguished triangles.
StageSystemCommonStageCones gives the actual finite-stage cone pair, including the
shift comparison in its third arrow, and the isomorphic-stage-image criterion.
StageSystemVerdier states the unique pretriangulation with exactly that criterion,
TR4 and exact inclusions. AlgebraicallyClosedCoefficients specializes that actual pair
category, constructs its Hom-colimit coordinates and bilinear composition, and fixes
its stagewise shift, inclusions, common-stage cones and distinguished triangles.
These interfaces do not select arbitrary functors or arbitrary comparison maps.
The normalized existential data are fixed by universal properties or explicit
component formulas. The scalar-localization triangulation theorem also fixes its
shift-by-one functor and identity localization comparison; its witness is not an
unconstrained choice of triangulation. All theorem proofs remain `sorry`, all other
data are real constructions, and the docstrings give their sources, blueprint ids
and proof plans. I checked all fifteen lean.statement strings against the corresponding
full source signatures and checked the 100-column limit: all match.

Mismatches and changes: refreshing the actual dependency declarations uncovered an
H4 duplication in the worker's final sandbox. The newly recorded
`SheafOfModules.StrictPerfectCoefficientPackageOnSite` already has precisely the
independent-universe degreewise splitting data. I removed the duplicate
`StrictPerfectCoefficientPackageOfUniverses` structure, changed the dependency import
to `StrictPerfectPackageOnSite`, used the recorded OnSite structure in both remaining
local-model definitions, and removed the deleted declaration from lean.declarations.
The local-perfectness, derived-perfectness and representation wrappers are still
needed: their old imported versions equate site object and morphism universes.
The item's four predicates and mathematical statement are unchanged.

Seven dependency lean.note records still described older absent or same-universe
interfaces. I corrected the notes for the strict-perfect package, integral scalar
extension, rationalization, scalar-extension constructibility, composition and
exactness, plus integral linearity, against their actual current records. The completed scalar functor itself
is retained; its owning module additionally supplies the canonical completed map and
ordinary finite-free model needed by the normalized associators. The other full-subcategory recorded
interfaces still use the finite-field datum and l ≠ D.p, and hence the unrestricted
repairs remain necessary. I opened their actual modules, including the current
server RationalizationKaroubi source. The independent reading above records the final
repaired delivery, including the rational bounded-model presentation and full
new-node/dependency audit. All signature records remain exact; no source statement
correction is needed.

A second reuse repair concerns `lem-weil-integral-constructible-linear`: its current
recorded module already has the unrestricted ambient canonical action
`integralCoefficientLinear`, together with `integralCoefficientShift_linear`.
The worker's separate ring-laws/center construction duplicated that action. I removed
it, imported the recorded module, and reused its canonical action and shift theorem.
Only the sf full-subcategory wrappers remain. I gave them distinct sf-prefixed names,
so the datum-parameterized `integralConstructibleLinear`, triangulated and shift APIs
remain available through the import. Updated lean.declaration, lean.declarations and
lean.statement accordingly. No choice of a second scalar action remains.

I also supplied the missing main-declaration lists in the module docstrings, as
required by brief-stage2 section 3. Existing source citations, declaration docstrings
and mathematical content were retained. The unmodified operations-well-defined
module already had its main-definition and main-statement lists.

## Earlier second reading (a previous round; superseded)

I independently read the item, its source at blueprint order 1881, the enclosing
projection-formula unit, the five source dependency statements and their actual
interfaces, and Stacks `sites-cohomology.tex`, `definition-strictly-perfect`,
`definition-perfect` (08G5), and `lemma-perfect-independent-representative`.
The item is an auxiliary definition. Its statement and the unit statement are
unchanged; it has no proof steps to translate and needs no statement_change.

Object, hypothesis and conclusion checklist, in the order of the source:

1. Scheme and coefficient site. `Y : AlgebraicGeometry.Scheme.{t}`,
   `Y.ProEt`, and `Scheme.ProEt.topology Y` use the recorded small pro-etale
   site, whose objects live in t+1 and morphisms in t. I opened the exact
   ProEtaleDerivedCategory interface and the upstream framework. No finite-type,
   Noetherian, properness, separation, connectedness, or nonemptiness assumption
   is introduced. Verdict: the same site and arbitrary scheme as the node.
2. Coefficient field. `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E]
   [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` give precisely a finite
   extension of Q_ell. The rational/common-stage predicates use the dependency's
   `(D : FiniteFieldDatum.{d})` and `(hl : l ≠ D.p)` explicitly. Source orders
   1460 and 1462 fix these conventions throughout; no characteristic assumption
   on Y or additional finiteness hypothesis is added. Finite/integral coefficient
   sheaves themselves do not require D. Verdict: exact inherited conventions.
3. Finite coefficient object. `IsFiniteCoefficientSitePerfect` takes a derived
   object of modules over `integralCoefficientSheaf l E Y n`. I opened that
   definition: it is the constant quotient coefficient sheaf at exponent n+1,
   so n=0 includes exponent one and all positive levels occur. The derived
   category is `HasDerivedCategory.standard`, rather than a second chosen
   abelian structure. Verdict: correct object and exact positive reindexing.
4. Local bounded models. `IsPerfectOnRingedSiteOfUniverses` asks for a complex
   representative P and `Nonempty (K ≅ DerivedCategory.Q.obj P)`. Its local
   predicate is `∀ V, ∃ S : Sieve V, S ∈ J V ∧ ∀ U f, S f → ...`.
   Each cover member has a bounded F and a quasi-isomorphism from F to P
   restricted by `SheafOfModules.overFunctor`. Stacks' independence-of-
   representative lemma identifies this formulation with local derived
   isomorphisms over a cover of Y. Bounds precede neither the cover nor its
   members. Verdict: exactly local bounded models, not a uniform global bound.
5. Finite-projective terms. The existing
   `SheafOfModules.StrictPerfectCoefficientPackageOnSite` supplies `N r : ℕ`
   and degreewise maps i, p with `i r ≫ p r = 𝟙 _`, to/from the finite product
   of unit sheaves. In this abelian category finite products are finite sums.
   Boundedness is `∃ a b : ℤ, ∀ r, r < a ∨ b < r → IsZero (F.X r)`.
   No chain-map splitting into a preselected free complex is required.
   Verdict: exactly the source's bounded finite-free direct summands.
6. Integral stage. `IsIntegralCoefficientSitePerfect` uses the same local
   predicate with `completedIntegralCommRingSheafUnrestricted`. Its underlying
   sheaf is `completedIntegralCoefficientSheafUnrestricted`, the actual inverse
   limit of the finite quotient constant sheaves, not the discrete constant
   valuation-ring sheaf. I checked the limit and commutative-ring enhancement.
   Verdict: precisely the prescribed completed coefficient object.
7. Rational category and restriction. The input is the published
   `rationalConstructibleCategory D l hl E Y`, from RationalizationKaroubi.
   Its definition is the raw `ScalarLocalization` of the recorded bounded
   constructible derived-complete integral category. Its objects are unchanged;
   no Karoubi envelope is used. On U the local object is the raw localization
   of `(integralDerivedPullback l E U.hom).obj K.obj.obj`. I read the normalized
   finite-level Roos construction and representative comparison; on these
   complete inputs it computes the specified restriction. Verdict: the actual
   dependency category and pullback, not a private substitute.
8. Rational bounded models and splittings. The rational predicate asks for an
   actual covering sieve and a bounded F, then an isomorphism after localization
   to `DerivedCategory.Q.obj F`. `IsRationalFiniteProjectiveTerm` asks for the
   degree-zero image of each term to split from finitely many copies of the
   unit in `sitePerfectRationalAmbient`. Both maps and the splitting identity
   live after localization; integral splittings are not demanded. Degree-zero
   module maps embed fully faithfully. To present a bounded localized complex
   in the displayed integral form, clear its finitely many differential
   denominators, kill the finitely many torsion d-squared relations with one
   additional uniformizer power, and rescale successive degrees. Conversely
   localizing any displayed F gives a bounded localized complex. This keeps
   the source's bounded-complex clause, rather than replacing it by a triangle
   tower or dualizability criterion. Verdict: equivalent presentation of exactly
   the rational direct-summand clause.
9. Algebraically closed stage. The input is the published
   `algebraicallyClosedConstructibleCategory D l hl Ω Y`. The definition asks
   for `E : AlgebraicallyClosedCoefficients.Index l Ω`,
   `P : AlgebraicallyClosedCoefficients.Stage D l hl Ω Y E`, rational
   site-perfectness of P over `Coefficient.{u} l Ω E`, and
   `Nonempty (K ≅ inclusion.obj P)`. I opened Index, its Small instance,
   Coefficient, Stage, stageSystem, Pair and inclusion in the current module.
   Index consists of actual finite intermediate fields; Coefficient transports
   them by `Shrink.algEquiv`; Stage is exactly the published rational category;
   inclusion is the actual common-stage functor. Verdict: existence of an
   isomorphic finite-extension representative, not equality of representatives
   or formal retract closure.
10. Cover requirement. The finite/integral wrapper and rational predicate all
    quantify over an actual covering sieve; the last predicate invokes the
    rational one. No stalkwise hypothesis substitutes for a cover. Verdict:
    the node's final qualification is retained.

Edge cases: `Fin 0` permits rank zero, and zero complexes admit a bounded support
interval. Empty schemes and empty covering sieves are interpreted by the actual
site topology, with no nonemptiness assumption. Local bounds and ranks vary by
cover member and degree. The finite exponent starts at one through n+1. Rational
splittings need not lift integrally. Identity extensions and repeated stages use
the published normalized scalar units and associators. The datum characteristic
convention is inherited only where the recorded category needs it. Finite/integral
coefficient universe u and scheme universe t remain independent, with coefficients
in max u (t+1). Rational coefficients use the recorded scheme-universe model; every
finite-dimensional Q_ell field has such a model via finite-basis coordinates.
The published `coefficientSmall` and `Shrink.algEquiv` implement this in the common-
stage category, allowing the closure universe v to remain independent. No site
object/morphism universe equality or new universe equality hypothesis is imposed.

Independent duplicate searches: LeanFinder for "A sheaf complex on a ringed site
locally has bounded finite free summand resolutions" returned finite-type and
finite-presentation APIs, not perfect complexes. Loogle `"IsStrictlyPerfect"`
returned zero hits. Mathlib Algebra grep
`StrictlyPerfect|IsLocallyPerfect|IsPerfectOnRingedSite|PerfectComplex` returned
zero hits. Direct project/upstream searches found the constant-ring
`AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect`; I opened it in both
slopmaster2 and the exact current 51-module framework checkout. It is restricted
to constant ModuleCat coefficients and does not give completed or raw-rational
stages. `Scheme.IsPerfect` concerns structure sheaves on Zariski opens. Neither
is the four-stage predicate here. The existing general degreewise strict-perfect
package is reused. LeanSearch was unavailable, as recorded in the worker's search
history, and that service failure is not treated as evidence of mathematical absence.

H12/H13 review and repairs: the first packet attempted to supply missing rational
and common-stage infrastructure in fifteen modules and a new specialized stage-
system node. I read those dependency statements, source places and interfaces.
A current-source check before delivery found that Q24 has now published the needed
rational, scalar-extension and algebraically closed/common-stage interfaces. The
specialized stage datum is part of that published AlgebraicallyClosedCoefficients
module, so the proposed new node would duplicate it. I removed it and all thirteen
redundant prerequisite modules/node records from the delivery, and changed both
rational consumers to the exact recorded D/ell/hl-parameterized categories. This
also removes the earlier unrestricted API-name collisions. Source orders 1460 and
1462 explicitly supply D and ell different from p; their binders are retained.
The old worker and earlier reading sections are historical, not a claim that those
superseded modules are in the final packet.

The only dependency module retained is the strict-perfect universe generalization.
I checked its node against blueprint order 1263 and Stacks 08G5 and read the latest
StrictPerfectPackageOnSite signatures. Its degreewise package already permits
independent universes and is imported unchanged. Its small-site local-perfectness
and representation wrappers fix coefficient size at the site-object universe u+1;
this fails for independently larger coefficient fields. The delivered wrapper
retains the exact same covering quantifiers, boundedness, package and
quasi-isomorphism clauses at coefficient size max uC vC r, with object and morphism
universes separate. All sheafification/locally-bijective instances used by the
item are constructed from essential smallness, not imposed as new hypotheses.
The dependency lean.note explains this precise limitation of the latest API.
The existing global ring-module and constant-sheaf package constructions remain
available through the public import. No new mathematical definition node is needed.

Final packet: SitePerfectComplex.lean and
StrictPerfectCoefficientPackageOfUniverses.lean, with exactly their two owning node
records. Existing metadata was refreshed from the shared node records, preserving
only the delivery lean fields and the item's two added recorded dependencies.
Every primary lean.statement is the verbatim signature from its file. All binders
and universe names were checked with autoImplicit false. The definitions contain
real data; these two files introduce no sorry, theorem proof, hollow choice, or
arbitrary canonical-map substitute. Source/blueprint docstrings are present.

## Dependency modules

`def-weil-pbc-strict-perfect-coefficient-package`:
Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses imports and reuses the
recorded StrictPerfectPackageOnSite degreewise package. It generalizes only its
local-perfectness/derived-representation wrappers to coefficient size max uC vC r,
so that independent site object, site morphism and coefficient universes are allowed.
The latest small-site wrapper fixes coefficient size at u+1 and cannot accept
max u (t+1) when u is larger. Its mathematical statement is unchanged; only lean
is repaired under brief-stage2 section 1(B). All other node fields are preserved.

Verification of the final two-module packet: scompile.py returned exit 0 with
no errors or warnings. Both modules passed their separate sandbox and library
checks; the universe wrapper also passed the preliminary dependency check.
Static checks confirmed no sorry, no line over 100 characters, exact primary
lean.statement signatures, and only lean changes to the dependency node.

## Second reading by Q33

I reread the source node `sec-smooth-purity/sk-prop-sf-pf-reduction/def-weil-site-perfect-complex.md`,
its five recorded dependencies, and the delivered declarations. The item-by-item check is:

- The small pro-etale site of `Y` is represented by `Y.ProEt` with its recorded topology;
  the module introduces no extra scheme hypotheses. Verdict: matches.
- Finite coefficients `A_{E,n}` are represented by `integralCoefficientSheaf l E Y n`
  (`n + 1` gives every positive exponent), with `K` in its actual derived category.
  Verdict: matches the finite clause and includes the zero/rank-zero case.
- Finite local models use an actual covering sieve and bounded complexes whose terms are
  degreewise retracts of finite sums of the unit, via
  `IsPerfectOnRingedSiteOfUniverses`. Verdict: matches the finite-projective definition;
  bounds and ranks may vary on cover members.
- The integral clause uses the completed coefficient sheaf and the same covering/local
  bounded-retract predicate. Verdict: matches `\widehat{\mathcal O}_{E,U}` and adds no
  finiteness, Noetherian, or stalk hypothesis.
- The rational clause uses the raw scalar-localized category and bounded complexes whose
  terms split from finite sums of the unit after localization (`IsRationalFiniteProjectiveTerm`).
  Verdict: matches the source's localized direct-summand wording; integral splittings are
  not incorrectly required.
- The common-stage clause existentially chooses a finite coefficient extension and a
  site-perfect stage object, then gives an isomorphism in the actual common-stage pair
  category through the recorded `inclusion`. Verdict: matches the source's finite-field
  representative clause up to the necessary categorical isomorphism.
- The final cover requirement is present in all local predicates. Verdict: stalkwise
  perfectness is not substituted for site perfectness.

The earlier worker's unsupported triangle-tower replacement had already been removed in the
sandbox; no further statement mismatch was found and no node statement was changed. The
final packet contains exactly two modules: SitePerfectComplex and the generalized-universe
dependency interface. The completed, integral-operation, rationalization, and common-stage
interfaces are published dependencies, not additional files in this delivery. This reading
changed the report only; the two Lean modules and their node signatures were retained.

Edge cases checked: `Fin 0` permits zero finite rank; the zero complex is bounded; local
bounds and ranks need not be uniform; `n = 0` denotes exponent one; empty schemes and
covering sieves are governed by the topology; rational retracts need not lift integrally;
identity extensions and repeated stages use the recorded normalized maps; site, coefficient,
and algebraic-closure universes remain independent. The rational/common-stage binders
`D` and `hl : l ≠ D.p` are inherited from the recorded coefficient categories (orders
1460 and 1462), rather than an extra geometric hypothesis. The rational coefficient model
and scheme share `u` as in that category; every finite extension has a canonical small
model, as witnessed by `Coefficient`. No properness, Noetherian, connectedness, or
geometric-stalk assumption is added.

Searches were rerun with `msearch.py`/LeanFinder for locally bounded finite-projective
sheaf complexes, Loogle for `IsLocallyPerfect`/`IsPerfect`, and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`. Mathlib results were K-projective and finite-presentation declarations; the Loogle query
`"IsLocallyPerfect"` returned zero hits. Upstream
`AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` was opened at
`WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean:428`: it uses constant-coefficient
`Sheaf ... (ModuleCat Λ)` and does not supply the completed or localized/common-stage
clauses. Project `IsProEtaleSitePerfect` is reused through the dependency whose
coefficient-universe specialization is generalized here. No exact full four-stage
notion was found. LeanSearch was unavailable, as recorded by the worker.

Compilation with `scompile.py` succeeded for both the generalized dependency and
`Sheaf/Paper/SitePerfectComplex.lean`; no Lean errors or unbound variables remain.
