## Worker report

The module states `WeilConjectures.etaleLisseHomReduction`; its only postponed proof is
that named theorem. Definitions have real data. The coordinate helpers and local predicates are listed in the corresponding
definition nodes' `lean.declarations`; the theorem supplies the actual canonical arrows.
No source statement was changed. Four definition nodes supply the canonical finite-free evaluation coordinates,
the local model and restriction predicates, and existing upstream owners for
bounded-flat complexes and small-etale site-perfectness.

Hypotheses and clauses, in order:

- `D : FiniteFieldDatum` fixes p, q, the finite field and its algebraic closure k.
  `[Fact l.Prime]` and `_hl : l ≠ D.p` are the prime and invertibility convention.
- `E`, `[Field E]`, `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`
  give the finite coefficient field extension. `Padic.coefficientExtensionRing l E (n+1)`
  is the recorded valuation-ring quotient. The canonical ULift changes only size.
  Natural indices n,m encode all positive exponents; `hmn : m ≤ n` is exactly n≥m≥1
  for those exponents. `finiteHomQuotient` is the published quotient factor map.
- `X.Over (Spec (.of D.k))`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`
  state precisely that X is separated and of finite type over k. There is no
  nonemptiness, smoothness, reducedness or properness hypothesis.
- `g : Z ⟶ X`, `[IsClosedImmersion g]`, `j : S ⟶ Z`, `[IsOpenImmersion j]` encode
  the locally closed stratum. The input object is M on X, and L is a module sheaf
  on S. `_hL` is an etale cover, a finite projective scalar module on each member,
  and its constant-sheaf identification. No free-module assumption is substituted
  for the projective-module hypothesis.
- `_hM` is the recorded finite-value bounded constructibility predicate and `_hTor`
  is the recorded Tor-amplitude predicate testing every degree-zero module sheaf.
  The integers a,b are unrestricted, so zero objects with empty Tor intervals remain
  included. There is no added a≤b hypothesis.
- Natural dX,dS supply nonnegative integer bounds; `_hdX`, `_hdS` compare them with
  `topologicalKrullDim`. In particular dimension bound zero is allowed for empty schemes.
- The first conclusion gives a finite-free etale cover; its rank `t : ℕ` can be zero.
  The next conclusions are `Etale.DerivedCategory.IsSitePerfect (single L)` and
  `hasTorAmplitudeIn ... 0 0 (single L)`. Together with that degree-zero sheaf
  trivialization this is site-perfectness in degree zero.
- `lisseHomStratumExceptional` is the actual right adjoint of closed derived direct
  image followed by exact derived open pullback: N=j*Rg!M. Its finiteness instance
  comes directly from `Padic.finite_coefficientExtensionRing`; it is not a new axiom.
  The next two conclusions give N bounded constructible and Tor interval
  `[a,b+2*dX+1]` exactly.
- The following two conclusions give Q=RHom_A(single L,N) bounded constructible
  and Tor interval `[a-2*dS,b+2*dX+1+2*dS]` exactly.
- The next four conjuncts state bounded constructibility and finite Tor amplitude
  separately for F(Q) and RHom_B(F(single L),F(N)). This places both endpoints in
  the full D^b_ctf subcategory before invertibility is asserted.
- `IsIso (etaleFiniteHomCanonical ... (single L) N)` concerns the existing, canonical
  evaluation transpose, not an arbitrary morphism or an unconnected isomorphism.
  Since the endpoints satisfy the two finiteness properties and the subcategory is
  full, this is the asserted isomorphism in D^b_ctf.
- The local-model clause applies `LisseHomRestrictedLocalFreeCalculation`, which applies
  `LisseHomLocalFreeCalculation` to the canonical derived restrictions, on every small-etale
  object U, hence on every covering object and every further etale restriction.
  It quantifies over every finite-free trivialization of the restricted single L,
  every bounded flat model P of restricted N and every representing isomorphism.
  The first coordinate map identifies Q with the finite product of Q(P); in an
  additive category this is the finite direct sum. The source and target coordinates
  identify both sides with the finite product of Q(P tensor_A B). They are required
  to be isomorphisms. Their displayed commuting equation makes u the identity in
  those specified evaluation coordinates. These maps are morphisms in B-module
  derived categories, so retain the B action. Evaluation, the standard basis, the
  scalar unit and the scalar representative counit determine the maps; no arbitrary
  coordinate isomorphism is chosen. Rank zero uses the empty product, the zero object.
- The last clause `LisseHomRestrictionCompatibility` states the explicit canonical
  restriction square. `lisseHomRestrictionGeneral` in the new local-calculation module is the tensorator mate for derived
  upperStar. The square transports the reduced inputs by `Etale.scalarPullbackIso`;
  it equates restriction of the actual global u with the actual local u. Both Hom
  restriction comparisons are isomorphisms. Thus the local coordinates describe
  restrictions of the global arrow, not merely unrelated local isomorphisms.
  Local restriction uses L(upperStar); upperStar is exact, so this is the same exact
  restriction as its mapDerivedCategory presentation used for the open j.

Dependency declarations read and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`; `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: convention node; the Mathlib scheme classes listed above.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`; `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`; `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`; `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`; `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`; `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`; `AlgebraicGeometry.IsOpenImmersion`.
- `lem-exc-closed-ambient`: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`; `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`; `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-weil-site-perfect-complex`: `Sheaf.Paper.SitePerfectComplex`; `WeilConjectures.IsFiniteCoefficientSitePerfect`.
- `def-sf-etale-finite-coefficient-hom-arrow`: `Sheaf.Paper.EtaleFiniteCoefficientHomArrow`; `WeilConjectures.etaleFiniteHomCanonical`.
- `def-sf-finite-free-hom-local-calculation`: `Sheaf.Paper.FiniteFreeHomLocalCalculation`; `WeilConjectures.LisseHomLocalFreeCalculationRing`, `WeilConjectures.LisseHomRestrictionCompatibilityRing` and their listed canonical maps.
- `def-sf-finite-free-hom-evaluation-coordinates`: `Sheaf.Paper.FiniteFreeHomEvaluationCoordinates`; `WeilConjectures.lisseHomCoordinatesRing` and its listed standard-basis helpers.
- `def-pur-etale-scalar-pullback-iso`: `Sheaf.Paper.PurEtaleScalarMateProjection`; `AlgebraicGeometry.Etale.scalarPullbackIso`.
- `def-sf-etale-bounded-flat-complex`: `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`; `AlgebraicGeometry.Etale.IsBoundedFlatComplex`.
- `def-sf-etale-site-perfect-complex`: `WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`; `AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect`.
- `lem-sf-flat-model` is a proof dependency only: `Sheaf.Paper.FiniteCoefficientFlatModel`; its flat-model existence theorem supplies the proof plan, not a definition used to state the item.

The scheme-property collection is a convention node: the module uses the standard
Mathlib `IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`, `LocallyOfFiniteType`
and `QuasiCompact` classes it specifies. The general-site Hom and change-of-rings
modules are imported; on the small etale site the exposed published fixed-coefficient
presentations are used, as in their existing dependency records. The pro-etale
site-perfect module remains imported as originally recorded; the existing upstream
small-etale `Etale.DerivedCategory.IsSitePerfect` is used through its new owning
definition node `def-sf-etale-site-perfect-complex` for this entirely etale statement.
No private copy of either notion is made. Proof-dependency modules are plain imports.
The unstated proof dependency `lem-coef-finite-hom-domain-calculus` is not imported:
this statement does not require its theorem, and no downstream result is assumed.

Edge cases checked mathematically: n=m gives identity coefficient reduction; m=0
in the Lean indices gives actual exponent one; all ranks include zero; X,Z,S and
covering members may be empty; dX=dS=0 remains permitted; zero M and reversed
input intervals cause no excluded case. No object/hom universe equality is added:
the schemes live in u and their etale coefficient categories in u+1.

Searches (also recorded verbatim by msearch in searches.jsonl):

- leanfinder, “Derived internal Hom from locally constant finite projective etale
  sheaf commutes with coefficient reduction”: eight light-condensed/module results,
  none with exceptional Tor bounds or this etale lisse comparison.
- loogle, “SheafOfModules.homObj, Module.Projective”: no hits, with unknown identifier
  diagnostic for homObj. This search is recorded as returned, not as mathematical evidence.
- msearch grep, “locally.*[Ff]ree|[Ll]ocally.*[Pp]rojective”, in
  Algebra/Category/ModuleCat/Sheaf: ordinary locally free sheaf definitions only.
- rg in WeilConjectures and Sheaf for the node id, lisse Hom/reduction names and local
  projectivity: no exact theorem. Existing EtaleFiniteCoefficientHomArrow, SitePerfect,
  EtaleSitePerfectConstructibleHom, finite flat models and finite constructible Hom
  were read and reused. The general theorem FiniteCoefficientHomChange describes the
  stratum argument in its proof plan but does not state these exceptional Tor bounds
  and canonical local-model coordinates as a separate declaration.

No STATEMENT-DISPUTED flag and no statement correction.

## Second reading by Q143

The dispatcher explicitly prohibits starting another agent and assigns the independent
review to the maintainer. This section records the worker's second pass, not a claim of
an independent reviewer. Reopened the JSON statement and Lean together, checked the
hypotheses and conclusions against the correspondence above, including both ctf
endpoints, both different dimension bounds, n=m, rank zero and every bounded flat
representative. During drafting, replaced a bare local isomorphism claim with actual
standard-basis evaluation coordinates and their identity equation. Kept the ordinary
small-etale derived categories throughout and used the published canonical comparison.

## New nodes

`def-sf-finite-free-hom-evaluation-coordinates`, in
`Sheaf.Paper.FiniteFreeHomEvaluationCoordinates`, defines evaluation on supplied
vectors, its standard-basis specialization on the small etale derived category,
and vectors transported through trivializations. The reduction of vectors is supplied by the
local-calculation definition node, built using the canonical scalar unit. All data is constructed;
there are no postponed proofs. It uses the existing internal Hom, constant-sheaf
functor, unit identification, and derived scalar extension. The main theorem imports
these definitions and states their isomorphism and identity properties separately.
Source: thm-coef-finite-hom proof paragraphs 2–3. Generic and ring-level interfaces
share the canonical category and sheafification data to keep elaboration within the per-file limit.

Searches for this definition: leanfinder “Canonical finite free derived internal Hom
coordinates evaluation at standard basis” returned eight ordinary module coevaluation
and free-module Hom results; loogle “ihom.unitIsoSelf, Pi.lift, LinearMap.single”
returned no hits with an unknown-identifier diagnostic; Mathlib grep for evaluation
coordinates and standard-basis Hom returned zero hits. The source-repository and
Sheaf rg searches returned only rationalization coordinates. DAG rg and
blueprint_refs.py search found `lem-sf-ringed-finite-free-hom-coordinates`, whose
statement and record were read: it assumes the scalar extension itself finite free,
rather than taking a finite-free first argument of Hom. It does not give these maps.
LeanSearch returned eight results, including `CategoryTheory.ihom.ev`, which is
used directly; ordinary free-sheaf section equivalences do not give this derived map.
The general evaluation and product primitives are reused, not redefined. Rank zero
is retained, and coefficient reduction uses the actual quotient map in the theorem module.

`def-sf-finite-free-hom-local-calculation`, in
`Sheaf.Paper.FiniteFreeHomLocalCalculation`, defines the bounded-flat representative
maps, source and target evaluation coordinates, their identity predicate for a
specified arrow, and the canonical restriction square predicate. It uses arbitrary
commutative rings of the existing etale size. The theorem's small wrappers
instantiate these predicates on the published finite coefficient quotient and the
actual `etaleFiniteHomCanonical`, globally and locally. No hypothesis about an
arbitrary replacement arrow is added to the theorem. The generic Hom restriction
helper requests preservation of flatness; the published ModuleCat upperStar instance
supplies it, so it adds no hypothesis to the node statement. Its source is the same
finite-free calculation and restriction paragraph of thm-coef-finite-hom.

For this node LeanSearch “Bounded flat finite free derived Hom scalar reduction
identity in evaluation coordinates compatible with restriction” and LeanFinder
“Finite free internal Hom models scalar extension coordinates identity restriction
square” each returned eight ordinary module extension/restriction results. Mathlib
grep “scalar.*[Hh]om|[Hh]om.*scalar|[Hh]om.*[Cc]oordinates” under ModuleCat/Sheaf
returned four ordinary scalar restriction implementation lines. DAG and blueprint
searches found the original theorem item and the finite-free scalar-extension nodes
already distinguished above. Source/Sheaf rg found only unrelated affine source
coordinates and geometric restriction modules. The model counit, scalar unit,
Hom restriction mate and scalar/pullback iso are all reused from the library.
Both new nodes have complete data definitions and no sorry.

The two theorem-module predicates use existential arrows with `HEq` to the actual
published canonical arrows. The equality witnesses fix those arrows themselves:
this is a transport between definitionally equal closed-instance presentations,
not a choice of any comparison or coordinate isomorphism. It avoids normalizing
large derived monoidal instance terms merely while checking the statement. The
local property and restriction square still concern exactly the specified u.
`lisseHomRestrictionFunctorRing` is definitionally the published L(upperStar), with
its instance fixed before specializing the coefficient quotient or etale object.

A final second pass includes both new definition nodes: their formulas use the
same degree-zero constant unit and standard vectors; source coordinates apply the
actual scalar representative counit; target coordinates use the canonical scalar
unit. The restriction square's contravariant input uses the inverse scalar/pullback
iso and its covariant input uses the forward iso. No map data comes from sorry.

Validation of the original packet (before this return repair): `scompile.py` compiled all three delivered files, separately in dependency
order, with no errors or warnings (the expected sorry is the main theorem only).
The final run reported 6.4 s for the coordinate module, 8.2 s for the model module,
and 6.2 s for the theorem module. `deliver2.py --no-push` printed OK: the three-node
packet passed maintainer preflight and its per-file compiles (dry-run commit
8d94a059dbc). No statement correction or dependency-module repair was needed.


`def-sf-etale-bounded-flat-complex` records the existing upstream
`AlgebraicGeometry.Etale.IsBoundedFlatComplex` in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`, with
`existing: true` and no new module. The full source signature and body were read:
for arbitrary integers a,b it requires `IsZero (P.X q)` when `q<a` or `b<q`,
and `ObjectProperty.flat (P.X q)` in every degree. The latter requires exactness
of both tensor functors; they agree in this symmetric sheaf tensor category.
This is the bounded-flat hypothesis of the local calculation, with no a<=b
hypothesis. Reversed intervals require all terms zero. No constructibility,
Noetherianity, coefficient finiteness or existence theorem is part of the predicate.
The ring is in universe u+1 and the scheme in universe u. Its source is the
upstream definition at FlatModel.lean:47 and the bounded-flat representative in
thm-coef-finite-hom proof paragraphs 2–3. LeanSearch for bounded flat etale sheaf
complexes returned eight general sheaf/module results; LeanFinder returned eight
complex-support and t-structure results; Mathlib grep returned zero hits. Source
rg found this exact definition and its Sheaf consumers. DAG rg and blueprint search
found the flat-model theorem but no owning definition. The search returns are
recorded in the new node, including the actual msearch JSON responses.

`def-sf-etale-site-perfect-complex` records the existing upstream
`AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect` in
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`, with
`existing: true` and no new module. Read its ambient binders, docstring, signature
and body: an arbitrary commutative ring in u+1, a scheme in u, and an etale cover
with, on each member, a complex bounded strictly below and above and an isomorphism
from the actual derived restriction of K to Q of that complex. Each term is a
retract of a constant finite power of the coefficient ring. Bounds can vary by
covering member and ranks by degree; no uniform bound or positive rank is added.
This is exactly the small-etale site-perfect clause of the theorem. Zero objects,
empty schemes and rank zero remain allowed, with no invertibility or geometric
hypothesis. Source: SitePerfect.lean:68 and the local finite-projective model of
thm-coef-finite-hom proof paragraphs 2–3. LeanSearch and LeanFinder each returned
eight general sheaf/site/projectivity results; Mathlib grep returned zero hits.
Source rg found this exact definition. DAG rg and blueprint search found the
small-etale dualizability theorem and pro-etale definition nodes; neither owns
this small-etale predicate. The new node records these searches and reuses the
existing declaration without duplicating it.

## Returned-delivery repair

The retained packet was first inspected and dry-run against the current live base.
It passed the mechanical preflight and all three file compiles, producing dry-run
commit f4e303fdec5; that unchanged packet was not pushed. The independent return
concerns definition ownership that those checks did not reject. All three points
are repaired in this packet:

1. In both the item and `def-sf-finite-free-hom-local-calculation`, replaced the
   statement-dependency citation `lem-pur-etale-scalar-mate-projection` by the
   already existing definition owner `def-pur-etale-scalar-pullback-iso`.
   The local-calculation node's bracket citation now names that owner too. Its
   imported module and actual normalized `Etale.scalarPullbackIso` stay the same.
2. In those same two nodes replaced the statement-dependency citation
   `lem-sf-flat-model` by `def-sf-etale-bounded-flat-complex`. The local-calculation
   node's bracket citation now names the new existing definition owner. Its module
   explicitly publicly imports the upstream FlatModel module where the predicate
   is defined. The flat-model theorem stays only in the item's proof dependencies
   and ordinary proof import, since stage 3 uses existence of the representative.
3. Added `def-sf-etale-site-perfect-complex` to the item's statement dependencies.
   The pro-etale `def-weil-site-perfect-complex` remains an original base dependency,
   but it is not offered as ownership of the small-etale predicate. No dependency
   theorem is used as a substitute for the new definition owner.

Second reading of the repair: opened the retained node and theorem alongside the
two source definitions and the local-calculation predicate. The theorem's signature
and all three original modules' definitions are unchanged; only an explicit import
was added. In particular the original positive exponent shift, projective input L,
exceptional and Hom Tor intervals, both ctf endpoints, canonical arrow, evaluation
identity for every flat model including rank zero, and scalarPullbackIso restriction
square all retain the independently accepted formulas. No mathematical statement
correction, new proof hole, private definition, or pro-etale replacement was made.
The new nodes are definition records for exact existing declarations, not dependency
modules. The delivery wrapper refreshes and builds on the live main branch.

Resumed validation: the retained packet failed preflight only because the two
existing upstream ownership records used `lean.branch: sheaf-dag`. Corrected both
to `slopmaster2`, as required for `WeilConjectures` declarations. The definition
statements, declaration names and all Lean signatures remain unchanged.
