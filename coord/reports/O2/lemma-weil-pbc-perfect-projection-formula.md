## Worker report

This delivery states `lemma-weil-pbc-perfect-projection-formula` in
`Sheaf.Paper.PerfectProjectionFormula`. The primary declaration is
`AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula`;
the other clauses are the separately named statements listed in `lean.declarations`.
Every theorem has proof `sorry`. Definitions contain actual data; selections of
isomorphisms use uniqueness characterizations or the two inverse identities.

Sources read: the complete node and every statement dependency, with their recorded
Lean signatures and docstrings; the master blueprint unit
`sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-perfect-projection-formula.md`
(first statement, both proofs, and Detailed form); the detailed blueprint
`proper_base_change.tex`, lines 5558–5618 (ordered compactification composite and
identity compactification). The blueprint sources absent in the local mirror were
read from the server. The current server source of
`Sheaf.Paper.AdicCoefficientDatumCompleted` and
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange` was checked through
`scompile.py --source`; the latter is the actual exchange used in the square.

Hypothesis and clause matching (names below are in
`AlgebraicGeometry.Scheme.PerfectProjection` unless qualified):

| Node text | Lean rendering |
| --- | --- |
| Schemes X,Y and any morphism f | `{X Y : Scheme.{u}} (f : X ⟶ Y)`; no properness assumption except in the final identity-compactification clause |
| Adic datum (A,I), commutative Noetherian, finite and perfect positive quotients | `{A : Type (u+1)} [CommRing A] (d : AdicCoefficientDatum A)`; inherited fields `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`, and `quotientFinite` are exactly the recorded datum |
| A_T is the inverse limit of finite quotient coefficient sheaves | `ring d T := adicLisseCompletedRing T d.ideal`; the recorded `finite_coefficient_identification` identifies this constant finite-quotient presentation with the function-sheaf presentation, naturally in the entire system |
| Ordinary uncompleted categories | `modules`, `derived`, using existing `proEtaleRingModules` and its standard `HasDerivedCategory`; no completeness predicate on objects |
| Canonical inverse-image coefficient identification | `coefficientMap` is the actual limit lift of inverse-image quotient projections followed by `proEtaleConstantComparison`; `coefficientCone_naturality` supplies its cone law; `coefficientMap_isIso` and `coefficients` retain this precise map |
| Ordinary derived operations and K-flat tensor | `pullback`, `directImage` specialize `proEtaleRingDerivedPullback` and `proEtaleRingDerivedDirectImage`; `aY`, `aX : ProEtaleTensorModel ...` specify signed total tensor on all flat K-flat representatives |
| Arbitrary K | `(K : derived d X)` with no boundedness, constructibility, torsion or completeness condition |
| The exact canonical projection map | `projection` specializes the already-landed `proEtaleProjectionFormulaMate`; its underlying `derivedProjectionFormulaMate` is the adjunct of the canonical tensor comparison followed by counit tensor identity |
| Full isomorphism locus | `locus := fun P ↦ IsIso (projection ... P)` is an `ObjectProperty`; its associated subcategory is full |
| Thick triangulated | First two conjuncts of `perfect_projection_formula`: `locus.IsTriangulated` and `locus.IsStableUnderRetracts` |
| Every finite free A_Y^m, including m=0 | Third conjunct quantifies over all `m : ℕ`, using degree-zero finite products of `SheafOfModules.unit`; in this additive category finite products are finite sums |
| Every site-perfect complex, local bounds allowed | Fourth conjunct uses `IsPerfectOnSmallRingedSite`; its defining covering-sieve quantifier chooses the bounded complex and both bounds separately for every cover member |
| Every positive n | All quotient declarations use `n : ℕ` to denote exponent `n+1`; this includes exponent one and excludes exactly exponent zero |
| Canonical Lf*(P_n)_Y ≅ (P_n)_X | `quotientPullback_existsUnique` fixes the module comparison by its constant-section adjunct, `quotientPullback` retains that characterization, and `quotientDerivedPullback` is exact degree-zero descent of it |
| K_n = K tensor^L (P_n)_X | `reduction d aX K n` |
| pi_n : (Rf_*K) tensor^L (P_n)_Y ≅ Rf_*K_n | `reductionMap` composes the original projection mate with direct image of the canonical quotient comparison; `reductionMap_isIso`, `reductionIso` |
| rho_n is its inverse | `inverse := reductionIso.inv`; no arbitrary inverse map is supplied as a hypothesis |
| Agrees with signed-totalization inverse on a finite-projective resolution | `Resolution` records a K-injective model and a bounded finite-free retract coefficient model representing the fixed quotient; `resolution_exists` prevents a vacuous model quantifier; `Resolution.totalInverse` directly applies the recorded `tensorAdjunctionTotalInverse`, whose summand theorem fixes the splitting formula and signs; `totalization_compatibility` identifies both localized arrows using the canonical source/target representative comparisons |
| Independent of resolution and splittings | `reductionMap` and `inverse` contain no resolution argument; `totalization_compatibility` quantifies over every `Resolution`, including any choice of degreewise splitting; `mixed_existsUnique` specifies its representative comparisons on every flat K-flat resolution |
| Quotient tower maps | `quotientModuleMap_existsUnique` fixes the sectionwise quotient formula; `quotientMap` localizes it; `quotientDerivedPullback_naturality` and both equations of `tower_compatibility` cover every n≤m, including identity and nonadjacent tower maps |
| Compatible coefficient operators | Both equations of `operator_compatibility`, for every linear map `q : K ⟶ K'`; taking K'=K gives every endomorphism, and the preceding tower equations give compatible families |
| Base change in the specified projection-formula square | `coefficients_square` gives canonical coefficient coherence; `exchange` is the recorded ambient exchange, `baseChangeSource` and `baseChangeTarget` are its actual tensor/quotient transports; both equations of `baseChange_compatibility` use them with no base-change-isomorphism assumption |
| Proper f and identity compactification | `identityCompactification_compatibility [IsProper f]` identifies the forward and reverse arrows with the normalized identity-compactification composites after the same quotient comparison |

Dependency declarations used:

- `Sheaf.Paper.AdicCoefficientDatum` reexports `AdicCoefficientDatum` from
  `CompletedAdicCoefficientDatum` and the finite-function ring construction.
  `Sheaf.Paper.CompleteCoefficientDatum` uses the recorded
  `DerivedCategory.IsPerfectRingComplex` from
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtaleConstantComparison`, `proEtale_profinite_coefficient_inverse_image`.
- The arbitrary identified-coefficient operations reexported by
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`:
  `proEtaleRingModules`, `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModuleAdjunction`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, `proEtaleRingDerivedPullbackFactors`,
  `proEtaleRingDerivedDirectImage_kInjective`.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: `ProEtaleTensorModel`,
  `proEtaleOrdinaryTensorPullback`, its naturality, and the canonical derived tensor
  comparison; this is the recorded tensor-pullback dependency specialization.
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`:
  `proEtaleProjectionFormulaMate`, `proEtaleProjectionFormula_baseChange`;
  its publicly imported `ProEtaleAmbientRingedExchange` supplies
  `proEtaleAmbientRingedExchange` and the normalized square comparison.
- `Sheaf.Paper.ProjectionFormulaArrows`: `tensorAdjunctionTotal`,
  `tensorAdjunctionTotalInverse`, its summand characterization. The mixed comparison
  here supplies the same representative characterization on the required unequal
  site universes; it does not supply an arbitrary comparison isomorphism.
- Proof imports retain `ringedProjectionMateExact`,
  `ringedProjectionFormula_totalization`, `ringedProjectionRestriction`,
  `completed_constant_sheaf_reduction`, and the degreewise-split distinguished-triangle
  and triangle-morphism isomorphism interfaces. The generic ringed formulas whose
  site universes coincide are used through their abstract-category constructions;
  the small pro-etale site's universes are never equated.
- The repaired strict-perfect and identity-compactification modules are described
  below. The missing generic compactified and open-piece modules are not imported:
  the identity lemma uses their normalized identity-open formulas directly, as in
  its source proof. Their non-identity cases are not needed to state this dependency.

Edge cases checked: rank zero, zero complexes, the empty scheme and empty covering
sieves, identity morphisms and identity base-change squares, n=1 (index zero), all
nonadjacent quotient transitions and n=m, zero ring and I=A, I=0 when the datum's
finite-quotient condition holds, arbitrary unbounded K, and site-perfect complexes
with no common bound across their covering objects. No quotient-flatness assumption
is introduced: Z/p over Z is perfect but not flat and is still included. The
coefficient universe is u+1 with site objects u+1 and site morphisms u throughout.

Searches actually run:

- `msearch.py leanfinder`: “Perfect projection formula for finite adic reductions on
  pro-etale ringed sites, thick isomorphism locus”. Eight unrelated hits on standard
  etale rings and BDeRham; none states this projection formula.
- `msearch.py loogle`: `"projectionFormula"`. Zero hits.
- `msearch.py grep`: `perfect.*projection|projection.*perfect`. Zero Mathlib hits.
- `msearch.py leansearch`: “The isomorphism locus of the derived projection formula
  contains every perfect complex”. Service unavailable, Internal Server Error;
  this was not treated as evidence of absence.
- `rg` for `lemma-weil-pbc-perfect-projection-formula|perfect.*projection|projection.*perfect`
  in upstream `WeilConjectures` and the project's `lean/Sheaf`: related etale pairing
  and projection modules, no theorem with this completed-coefficient statement.
- Exact upstream node-id `grep -rn`: no match.
- `rg` for the proposed namespace and helper names: no previous `PerfectProjection`,
  `IdentityProjectionCompactification`, or unequal-universe strict-perfect declarations;
  the canonical tensor model and projection mate already existed and are reused.
- Current-server `--source` checked the ambient exchange and adic interface; an
  attempted `--source Sheaf.Paper.ProjectionFormulaIdentityCompactification` reported
  that the module was unavailable, so that dependency is supplied here.

No statement correction, new DAG node, or mathematical dispute is claimed.
Compilation status is recorded in the validation section below.

## Dependency modules

`def-weil-pbc-strict-perfect-coefficient-package`:
`Sheaf.Paper.StrictPerfectPackageOnSite`. Its published independent-universe
`StrictPerfectCoefficientPackageOnSite` is retained verbatim and used directly
by the local perfectness predicate and the main resolution package. The imported
older `IsPerfectOnRingedSite` still requires equal site object and morphism
universes. This §1(B) repair extends the recorded module with
`IsLocallyStrictPerfectComplexOnSite`, `IsPerfectOnSmallRingedSite`, and
`SiteStrictPerfectCoefficientRepresentation` at the actual small-site universes.
Their definitions retain the covering-sieve quantifier, separately bounded local
representatives, and finite-free retract condition. The ordinary-ring packages
and associated constant sheaf construction remain reexported.

`def-weil-pbc-projection-formula-map`: attached with `existing: true` to
`AlgebraicGeometry.Scheme.proEtaleProjectionFormulaMate` in
`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`. The declaration specializes to
exactly the completed coefficient ring sheaves, canonical coefficient identification,
K-flat tensor and derived adjunction of this node. Its body uses the canonical mate,
which is the prescribed unit followed by direct image of tensor(counit,identity).
There is no newly invented projection morphism or postponed assertion of invertibility
inside the definition.

`lemma-weil-pbc-projection-formula-identity-compactification`:
`Sheaf.Paper.ProjectionFormulaIdentityCompactification`. There was no recorded
statement. The module states the dependency in the identity-open normalized
presentation specified verbatim by its source: extension by zero and pullback for
j=1_X have identity functors and identity constraints. Accordingly `directImage`
is identity followed by the actual Rf_*, `theta` is identity, and `forward` and
`backward` are the actual ordered composites. The arbitrary E, site-perfect Q and
proper f context is retained. The canonical mate's inverse is determined by its
inverse identities; no free inverse or arbitrary natural isomorphism is assumed.

## Validation

The prescribed `scompile.py` accepted all three repaired modules locally, each
as a separate file at both its sandbox and library path, with no errors or warnings.
The dependency also passed its preliminary check. The wrapper retained its default
60-second compiler limit and performed no global build. The node copies change
only `lean`, their primary signatures are copied verbatim, and every Lean line
is at most 100 characters. The final prescribed dry delivery follows this check.

## Repair of returned immutable head 3431f587f57d

The returned immutable compile could not resolve `SheafOfModules.IsPerfectOnSmallRingedSite` in the identity-compactification module (four occurrences). The currently published dependency record names `Sheaf.Paper.StrictPerfectPackageOnSite`, whose generalized splitting package is available but whose imported local-perfectness predicates remain restricted to equal site object and morphism universes. This repair keeps that published structure and extends its owning module with the missing local-perfectness predicates and localized representative. Both consumers import the recorded module explicitly. The old separate `StrictPerfectCoefficientPackageSmallSite` module and its duplicate splitting structure are removed. The main resolution data uses the published `StrictPerfectCoefficientPackageOnSite` directly. No mathematical hypothesis, conclusion, coefficient universe, or local-bound quantifier changes.

The previous second reading is archived in `scratchpad/previous-second-reading.md`; a fresh second reader must verify this repair. Fresh wrapper compilation and dry-run results are recorded below after validation.

Repair searches: `scompile.py --source Sheaf.Paper.StrictPerfectPackageOnSite`
returned the published independent-universe splitting structure; the old
`StrictPerfectCoefficientPackageSmallSite` module was unavailable. `rg` on both
strict-perfect modules confirmed that the published module did not yet define
`IsPerfectOnSmallRingedSite`, and upstream `WeilConjectures` had no declaration
with that name. The new predicates use the published structure directly.

## Second reading by N2

This is a fresh independent reading of the repaired delivery, including all three
modules. I read the item's complete statement and six proof steps, all statement
dependency records and their declaration signatures, and the bodies that determine
the coefficient rings, operations, tensor comparison and projection mate. I read
on the server the master order-1275 blueprint (both statements and both proofs),
the detailed blueprint's ordered compactification composites at lines 5558–5618,
Stacks sites-cohomology lemma-projection-formula (0944), its following base-change
remark, sites-cohomology definition-perfect (08G5), more-algebra definition-perfect
(0657), and the source definition of the strict-perfect package. There is no
statement_change and there are no new definition nodes in this delivery.

The following is my object/hypothesis/conclusion inventory and Lean comparison.
Names in the middle column are in Scheme.PerfectProjection unless qualified.
Every row passes; the remaining paragraphs explain the dependency repairs and checks.

| Source requirement | Actual Lean rendering and verdict |
| --- | --- |
| Schemes X,Y, arbitrary morphism f | `{X Y : Scheme.{u}} (f : X ⟶ Y)`; no quasi-compactness, properness, separatedness or finite-type assumption. Pass. |
| Commutative Noetherian adic datum (A,I), finite perfect positive quotients | `{A : Type (u+1)} [CommRing A] (d : AdicCoefficientDatum A)`; I is `d.ideal`. I opened `CompletedAdicCoefficientDatum` and `CompleteCoefficientDatum`: `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect` and `quotientFinite` are the recorded datum, not extra hypotheses on the theorem. `adicQuotientPerfect` uses `IsPerfectRingComplex`, whose signature allows a separate localization universe and whose body requires bounded finite projective terms. Pass. |
| A_T is the inverse limit of finite quotient sheaves | `ring d T = adicLisseCompletedRing T d.ideal`; I opened `adicLisseRingSystem`: its objects are constant sheaves of A/I^(n+1), its transitions are the quotient ring maps, and its completed ring is their actual limit. `CompletedConstantReduction.finite_coefficient_identification` relates this presentation and the function-sheaf coefficients naturally. Pass. |
| Canonical identification f^{-1}A_Y ≅ A_X | `coefficientMap` is the limit lift of inverse images of the quotient projections followed by the recorded `proEtaleConstantComparison`. Thus its projections are exactly the unique comparison of `proEtale_profinite_coefficient_inverse_image`, not an arbitrary isomorphism. `coefficients` is `asIso` on that map using `coefficientMap_isIso`. Pass. |
| Ordinary uncompleted module derived categories and operations | `modules` is the existing `proEtaleRingModules` over this ring; `derived` is its ordinary `DerivedCategory`. `pullback`, `directImage` use the actual identified-coefficient operations `proEtaleRingDerivedPullback` and `proEtaleRingDerivedDirectImage`. I opened their module-level pullback/direct-image and normalized adjunction interfaces. These are all module sheaves, with no completeness condition on objects. Pass. |
| K-flat derived tensor and arbitrary K | `aY`, `aX : ProEtaleTensorModel` identify tensor naturally with signed total tensor on all flat K-flat representatives. I opened that structure and its canonical comparison characterization. `K : derived d X` has no boundedness, constructibility or Tor-amplitude hypothesis. These model parameters present the prescribed tensor operation. Pass. |
| The specified projection map pi_(f,K,P) | `projection` specializes the existing `proEtaleProjectionFormulaMate`; I opened the current server declaration, `derivedProjectionFormulaMate`, and the upstream adjunction projection map it calls. Its construction is the tensor comparison followed by counit tensor identity, transposed under the normalized derived adjunction. It makes no invertibility assumption. Pass. |
| Full isomorphism locus is thick triangulated | `locus : ObjectProperty (derived d Y)` is exactly `IsIso (projection ... P)`; its object-property subcategory is full. The first two conjuncts of `perfect_projection_formula` assert `IsTriangulated` and `IsStableUnderRetracts`. Pass. |
| Every finite free coefficient sheaf, rank zero included | The third conjunct quantifies over every `m : ℕ` and uses `singleFunctor ... 0` of the finite product of the actual completed-ring unit sheaf over `Fin m`. Finite products equal finite sums in this additive category. This is A_Y^m, not the discrete constant sheaf of A. Pass. |
| Every site-perfect complex, with bounds depending on cover member | Fourth conjunct: every `P : derived d Y` satisfying `IsPerfectOnSmallRingedSite (ring d Y) P` lies in the locus. I unfolded the repaired predicates: for every site object V, a covering sieve is chosen; for each arrow in it a bounded complex F, finite-free splittings and a quasi-isomorphism F → restricted K are chosen. The two bounds occur inside the arrow quantifier. This is precisely the node and Stacks 08G5. Pass. |
| Every n≥1, canonical Lf*(P_n)_Y ≅ (P_n)_X | `n : ℕ` uniformly denotes exponent n+1. `quotient` is the recorded residue module in degree zero, with the completed action through the nth limit projection. `quotientPullback_existsUnique` fixes the adjunct on every quotient section; `quotientDerivedPullback` uses exact degree-zero pullback of that same map. Pass. |
| K_n and the displayed isomorphism pi_n | `reduction` is `aX.tensor.obj (K, quotient d X n)`. `reductionMap` composes the original mate with direct image of tensor of the canonical quotient comparison. `reductionMap_isIso` asserts invertibility (and quotient site-perfectness), and `reductionIso.hom` is this fixed map. Pass. |
| rho_n is its inverse and agrees with the signed finite-total inverse | `inverse` is `reductionIso.inv`. `Resolution` fixes representatives of K and of the same quotient, a bounded coefficient complex and degreewise splittings. `resolution_exists` prevents vacuity. `Resolution.totalInverse` calls the existing `tensorAdjunctionTotalInverse` with the actual ordinary adjunction, canonical ordinary tensor comparison, normalized unit and splitting data. `totalization_compatibility` equates both localized arrows with the fixed maps using the specified mixed and K-injective model identifications. Pass. |
| Independence of resolution and degreewise splitting | `reductionMap` and `inverse` have no resolution parameter. `totalization_compatibility` quantifies over every `Resolution`, including its arbitrary splitting package. `mixed_existsUnique` fixes the mixed model comparison by its square for every flat K-flat resolution, rather than by bare existence of an isomorphism. Pass. |
| Compatibility with quotient tower maps | `quotientModuleMap_existsUnique` fixes the underlying section function to the actual quotient transition; `quotientMap` localizes it. `quotientDerivedPullback_naturality` and the two equations of `tower_compatibility` cover every n≤m, including identities and nonadjacent transitions. Pass. |
| Compatible coefficient-linear endomorphisms | Both equations in `operator_compatibility` hold for every `q : K ⟶ K'`; K'=K gives all linear endomorphisms, and the preceding tower equations give compatibility on reductions. This agrees with the coefficient-operator variable of the cited naturality dependency. Pass. |
| Base change in the specified square, forward and inverse | `coefficients_square` expresses coherence of the canonical completed coefficient comparisons. `exchange` uses the actual recorded `proEtaleAmbientRingedExchange`; `baseChangeSource` and `baseChangeTarget` insert precisely its tensor/quotient comparisons. `baseChange_compatibility` states both squares, without requiring the exchange to be invertible. I compared these with the current `proEtaleProjectionFormula_baseChange` signature and Stacks' following projection-formula remark. Pass. |
| For proper f, identity compactification agrees | Only `identityCompactification_compatibility` adds `[IsProper f]`. Its two equations transport the normalized identity compactification's ordered forward and reverse composites by the same quotient pullback comparison and its inverse. Pass. |

Dependency-module reading (H12/H13): there are no new nodes. The strict-perfect
repair retains the already-published `StrictPerfectCoefficientPackageOnSite`
structure verbatim, including independent object, Hom and ring universes. The
old imported local-perfectness predicate fixes equal site universes, so it cannot
serve the small pro-etale site; the added two predicates and localized
representation use exactly the existing splitting structure at objects u+1,
Homs u, coefficients u+1. Their data are bounded complexes, quasi-isomorphisms,
and finite-free retractions, exactly the dependency node's notion. The original
ordinary-ring and constant-sheaf package declarations remain reexported. The
four delivered declaration names are all in its lean.declarations record.

For the identity dependency I checked the normalized identity-open presentation
against the detailed source before checking the theorem: j_! and Lj^* and their
unit constraints are identities there. Thus `directImage = identity ⋙ Rf_*`,
`theta = identity`, and `forward`/`backward` are the ordered composites in that
presentation. This does retain the direct-image, theta, forward and reverse
clauses of the node. Its inverse is determined by the canonical mate's inverse
identities; it is not a new map chosen from a bare existence statement. `mate_isIso`
uses proper f and the same local-perfectness condition as the cited compactified
formula. Generic nonidentity compactifications are not asserted by this module.
The canonical projection-map dependency uses the exact existing declaration,
with its current body and actual completed-coefficient specialization checked.

Edge cases checked independently: Fin 0, zero K, zero representatives, empty
schemes and any empty covering sieves permitted by the topology; n=0 is exponent
one, and the full positive range is covered. No n=0 exponent statement is added.
Tower maps include n=m and arbitrary gaps. There is no characteristic, field,
nonzero-ring, nonempty-scheme or quotient-flatness assumption. I=A and I=0 remain
allowed whenever the datum holds. In particular, perfect nonflat quotients are
not excluded. Cover-dependent amplitude is genuinely local. The small site has
object universe u+1 and Hom universe u throughout; no equality between them is
imposed. The coefficient size u+1 is the recorded sheafification convention,
which includes smaller finite coefficients by their usual lift.

Independent searches, actually run in this reading and logged in searches.jsonl:
LeanFinder “Derived direct image tensored with a locally bounded complex of finite
projective sheaves is isomorphic to direct image of its pullback tensor” returned
ordinary sheaf pullback/pushforward comparisons, not this derived projection
statement. Loogle `"projection"` returned Lean metaprogramming projections.
Mathlib grep `projection.*(perfect|finite)|perfect.*projection|IsLocallyStrictPerfect`
returned finite-set/projection geometry hits, none about this theorem. LeanSearch
“For ringed sites the projection formula is an isomorphism for perfect complexes
with local bounded finite projective representatives” was available in this
reading and returned structure-sheaf and ordinary projective-resolution results,
not this theorem. I also ran rg with tensor/pushforward/directImage, projection,
StrictPerfect and locally-perfect words in upstream WeilConjectures and project
lean/Sheaf, and checked the exact node id in dag/lean_names_upstream.json.
The project's canonical mate and split-perfect package already exist and are
reused. Upstream etale pairing/constructible projection results are different
coefficient categories and restricted objects. I read
coord/pefw-upstream-framework.md and the shared framework's
CategoryTheory.ModuleObjects.ProjectionFormula: it is a coherent projection
formula interface on internal module objects, not this theorem for ordinary
completed-ring module sheaves and arbitrary unbounded K.

Mismatches and changes in this fresh reading: no mathematical mismatch remains
in the repaired Lean modules. The existing projection-map dependency's recorded
signature was flattened and omitted its `noncomputable` modifier. I copied its
signature verbatim from the current server source, preserving the declaration,
body and all mathematical content. All three nonexisting primary signatures
already match their files byte for byte and were retained. The fresh report
supersedes the archived second reading; its dependency inventory correctly lists
four declarations in the extended strict-perfect module. No statement correction,
new node, universe restriction, extra hypothesis or Lean theorem proof was added.

H5/H6/H8/H9: definitions have actual data. The chosen comparison data are fixed
by unique section formulas or universal properties, and inverses by inverse laws;
none is a bare arbitrary object selected from unproved existence. Named helper
theorems carry the corresponding source and item/dependency blueprint tags and
natural-language proofs, and every theorem body is still sorry. The main
docstring follows all six node proof steps across its separately named clauses:
coefficient comparison; unit and finite sums; shifts, triangles and retracts;
local stupid truncations and detection; reduction representatives; totalization
and naturality. Explicit binders and universes were checked; no local notation,
private definitions or file-local instances were introduced. The maximum Lean
line length is 95. All 53 main and seven identity declarations, and all four
extended strict-perfect declarations, are recorded by their owning nodes.

Fresh second-reader validation: deliver2.py --no-push completed successfully and
printed `OK (dry run): commit 4ab44a3167 passes the preflight and compiles; nothing
pushed`. Its prescribed scompile.py invocation checked all three sibling modules
separately in dependency order, at sandbox and library paths, plus a real probe of
the existing projection-mate declaration. There were no Lean errors or disallowed
warnings and no server compile fallback in this dry run. The current server
preflight passed. The complete dry-run output is retained in the sandbox at
scratchpad/second-reader-dryrun.log. All limits stayed at the wrapper defaults;
no live source, global build, or direct Git mutation was used by the reader.
