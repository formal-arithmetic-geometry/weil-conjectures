## Worker report

The delivery states `AlgebraicGeometry.Scheme.proEtaleProjectionFormula_compactified`
in `Sheaf.Paper.ProjectionFormulaCompactified`, together with
`compactifiedProjection_rho_local`. All theorem proofs are `sorry`. Definitions contain
actual constructions, not postponed data. The item statement is unchanged; there is
no statement correction, new DAG node, or disputed mathematical assertion.

The source is blueprint lemma 1271, read from the local literature mirror at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-projection-formula-compactified.md`.
Its ordered forward map, reverse map, localization argument and inverse equations agree
with the node's expanded statement and six proof steps. The main theorem docstring
records all six steps; the local-normalization theorem records the restriction and
uniqueness calculation. The imported blueprint's shorthand `Lj*Lp*=Lf*` is rendered
by the existing normalized composition comparison, with its inverse in theta.

Clause-by-clause translation:

- `d : Compactification f` supplies X, its intermediate scheme `d.Z`, Y, the maps
  j=`d.i`, p=`d.g`, the equality `d.comm : f = d.i ≫ d.g`, open immersion, and
  properness. `[QuasiCompact d.i]` supplies the quasi-compactness omitted by the
  upstream Compactification structure. No Noetherian, dimensional, characteristic,
  coefficient-finiteness or constructibility condition is added.
- The sites are exactly `ProEt.topology X`, `ProEt.topology d.Z` and
  `ProEt.topology Y`, with object universe u+1 and Hom universe u. Coefficients and
  module sections have universe u+1. The general package also has independent
  object, Hom, and coefficient universes. No site-universe equality is imposed.
- `RY : Sheaf (ProEt.topology Y) CommRingCat.{u+1}` is the arbitrary commutative
  ring sheaf. `RZ`, `RX`, and `cp`, `cj` name its two inverse-image coefficient
  presentations and their identifications. This is the usual invariant encoding
  of the node's equalities; taking identity identifications gives the literal
  inverse-image rings. It does not restrict RY or assume a comparison with constant
  coefficients. The composite coefficient map is *defined* by
  `proEtaleRingCompositeCoefficients d.i d.g ... cp cj`; no third choice is allowed.
- `proEtaleRingModules` uses the existing module sheaf category. `DerivedCategory`
  with its existing standard localization instance is the full ordinary unbounded,
  uncompleted category. `proEtaleRingDerivedPullback` is exact termwise pullback;
  `proEtaleRingDerivedDirectImage` uses K-injectives among all modules.
- `E : DerivedCategory (proEtaleRingModules X RX)` has no further hypothesis.
  The coefficient is arbitrary `Q` with exactly `hQ : IsProEtaleSitePerfect Y RY Q`.
  That generalized dependency predicate existentially represents Q by a complex K
  and, on *every* site object V, requires a covering sieve with bounded finite-free
  retract complexes mapping quasi-isomorphically to K on each member. The degreewise
  package is N,i,p and i≫p=identity. Bounds and ranks are inside the cover-member
  quantifier. No uniform global bound or global strict-perfect representative is used.
- `a`, `b`, `c : ProEtaleTensorModel ...` name the existing derived tensor models.
  Their `representative` isomorphisms identify them with the signed total tensor on
  every flat K-flat pair. They are presentations of the named ordinary derived
  tensor, not an assumption of any projection isomorphism.
- `compactifiedProjectionPi` is exactly `derivedProjectionFormulaMate` for p,
  its canonical derived adjunction and `proEtaleCanonicalTensorComparison`, at j_!E
  and Q. The latter is the published comparison uniquely fixed by its ordinary
  pure-tensor normalization and K-flat representative square. Thus pi is the
  required adjunct of counit tensor identity, rather than an arbitrary arrow.
- `proEtaleOpenProjection` is the actual adjunction transpose of unit tensor
  identity followed by the inverse pullback/tensor comparison. Its ordinary
  adjunction is the chosen representing left adjoint to actual open restriction;
  its derived adjunction is constructed by localizing the exact termwise pair.
  The delivered NG dependency theorem gives the natural isomorphism on the
  full category of bounded finite-projective coefficients, uniquely normalized
  by that same unit transpose. Its slice presentation transports to the original
  site by weakly-etale localization and coefficient/adjoint equivalences.
- The main theorem's first existential witness `hα` asserts precisely that this
  alpha is invertible for M=`Lp*Q`, now only assuming Q locally perfect.
  `compactifiedProjectionTheta` is an actual isomorphism: alpha inverse, followed
  by j_! of identity tensor the inverse component of
  `proEtaleCanonicalPullbackComposition`. The latter selects the existing theorem's
  fully characterized canonical comparison, retaining its ordinary, termwise and
  K-flat normalization. The composite `d.i ≫ d.g` is f by d.comm.
- `compactifiedProjectionForward` is pi followed by Rp_* theta.hom, in that order.
  `proEtaleRingCompactSupportImage` is definitionally j_! followed by Rp_*, so its
  two endpoints are exactly the node's two compact-support objects.
- The second witness `hπ` says pi itself is invertible and fixes rho to be `inv pi`.
  `compactifiedProjectionReverse` is Rp_* theta.inv followed by this rho, exactly
  the node's reverse order. The theorem asserts `IsIso` of the forward composite
  *and both* forward/reverse identity equations. It does not merely assert an
  unspecified isomorphism between the endpoints.
- `compactifiedProjection_rho_local` renders the last clause on the canonical
  generic/slice presentation of the same operations. `g : Global ...` and
  `l : Local ... g V` are the already recorded restriction interface, whose
  sectionwise, representative and counit conditions fix every comparison. Their
  pullback is the canonical left adjoint to the recorded direct image; adjoint
  uniqueness identifies it with the original-site pullback used above.
  For every site object V, every bounded local complex B, every splitting package
  P and every specified representation `uQ`, the restriction of the global
  inverse is targetIso.hom, transport along uQ, the specified finite-total inverse,
  inverse transport along uQ, and sourceIso.inv. Thus every local strict-perfect
  representative is covered, not just one selected family or a global model.
- `restrictionFiniteTotalInverse` is the localization of the existing
  `tensorAdjunctionTotalInverse` between canonical mixed-tensor and K-injective
  representatives. `tensorAdjunctionTotalInverse_summand` fixes the bidegree map
  as inclusion, finite-product inverse and retraction. The signed total uses
  Mathlib's existing `CochainComplex.mapBifunctor`; signs are (-1)^a.
  The local helper statements specify ordinary unit/naturality normalization,
  flatness and a *unique* mixed representative square, as needed to instantiate
  this construction on slices. No unconstrained map or isomorphism is supplied.

Recorded dependencies read and used:

- `def-weil-pbc-projection-compactification`: original
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `Etale.rightDerivedLowerShriekOfCompactification`, and
  `WeilConjectures.Compactification.Defs`, `Compactification`, `ofIsProper`.
  The arbitrary ringed pro-etale repair is described below.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`, publicly retaining
  `ProEtaleOperations` and `ProEtaleOperationsCanonicalAdjunction`:
  `proEtaleRingModules`, both module and derived operations, their exactness
  instances, and `proEtaleRingDerivedAdjunction`.
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `Sheaf.Paper.StrictPerfectCoefficientPackage`, its splitting package,
  `IsLocallyStrictPerfectComplex`, `IsPerfectOnRingedSite` and localized
  representation. Their universe repair is described below.
- `lem-weil-pbc-proetale-derived-pullback-composition`:
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`,
  `proEtaleRingDerivedPullbackComposition`,
  `proEtaleRingCompositeCoefficients`, ordinary section-normalized adjunction,
  fibre-product direct-image pasting, conjugate pullback, termwise and K-flat
  derived comparison. The selection wrapper is described below.
- `def-weil-pbc-projection-formula-arrows`:
  `Sheaf.Paper.ProjectionFormulaArrows`, `derivedProjectionFormulaMate`,
  `tensorAdjunctionTotalInverse`, `tensorAdjunctionTotalInverse_summand`,
  `tensorAdjunctionTotal_target_isKInjective`, and the recorded ringed arrows.
  The original-small-site specialization is described below.
- `lemma-weil-pbc-projection-formula-open-piece`: use the already delivered NG
  `Sheaf.Paper.OpenImmersionTensorPiece`, `SheafOfModules.openImmersionTensor_iso`,
  `openTensorFormula`, `openTensorSource`, `openTensorTarget` and its coefficient
  subcategory. Its complete signature, unit equation and proof docstring were read.
- Added existing statement dependency `lem-weil-pbc-ringed-projection-restriction`:
  `Sheaf.Paper.RingedProjectionRestriction`, `Mod`, `Der`, `TensorModel`,
  `resolving`, `total`, `Operation`, `OrdinaryTensor`, `TensorComparison`,
  `Global`, `Local`, `sourceIso` and `targetIso`. Full signatures and their
  representative, section and counit normalization fields were read. This node
  was already a proof dependency, and its interface is needed to type the last
  clause without inventing new restriction maps.

Proof imports retain the existing totalization theorem, localized module
adjunction/exactness, weakly-etale localization, exact derived functors,
pre-derived adjunction and quasi-compact base change. The proper-piece theorem
has no published declaration and is not imported; totalization already proves
its needed inverse identity. No proof dependency is silently used as an axiom
of the main statement.

Edge cases checked against the binders and constructions: empty schemes and the
empty open; identity open and identity compactification of a proper f; zero E,
zero Q and the zero ring; rank zero (Fin 0); all-zero or empty support intervals;
negative degrees, shifts and E unbounded in both directions; different local
bounds and ranks on different cover members; degreewise splittings that are not
chain maps; all characteristics and nonconstant coefficient rings; arbitrary
isomorphic presentations of the local coefficient complex. The local equation
quantifies over every representation uQ, so changing representatives is included.

Searches performed before writing:

- `msearch.py leanfinder`, query "Compactified derived projection formula for
  site-perfect coefficient sheaves on pro-etale sites": eight unrelated affine
  limit, BDeRham and ordinary differential results; no exact statement.
- `msearch.py loogle`, query `projectionFormula, lowerShriek`: no matching typed
  declaration for this theorem. It returned zero hits and an unknown-identifier response for
  `projectionFormula`; source grep supplied the name-based check.
- `msearch.py grep`, query
  `projectionFormula|projectionMapOfCompactification|lowerShriek`: zero Mathlib hits.
- `msearch.py leansearch`, query "Compactly supported derived direct image projection
  formula with perfect coefficients": Internal Server Error, recorded unavailable;
  no absence conclusion is drawn from that service failure.
- `rg` in upstream WeilConjectures and side lean/Sheaf for the same projection
  names found the etale/pro-etale fixed-coefficient lower-shriek projection maps
  and constructible projection-formula interfaces. Their types do not state this
  arbitrary ring-sheaf, locally perfect, unbounded theorem and its finite-total
  local inverse. Existing generic counit mates and signed-total maps are reused.
- `rg` for this item id in upstream WeilConjectures returned no declaration.
  A separate collision search for the new helper names in Mathlib, upstream and
  side Sheaf sources returned no hits. The upstream-name index likewise has no
  entry for the recorded dependency ids or the proposed compactified statement.
- `scompile.py --source` confirmed the published canonical tensor comparison and
  the recorded strict-perfect package. It reported no published module for the
  attempted open-piece, compactification or Q09 original-site arrows repairs.
  A read-only `git ls-remote` from the sandbox found delivery branches
  `deliver/NG/lemma-weil-pbc-projection-formula-open-piece` at b43a96c089f8 and
  `deliver/Q09/lemma-weil-pbc-projection-formula-proper-piece` at 9ec2f061d7b9.
  Existing Q09/NG delivery sandboxes and their reviewed reports were inspected;
  the compatible Q09 constructions are reused instead of a competing definition. The Q09 arrow parameters use the delivered NG generic
  splitting package directly, with exactly the same N,i,p,splitting fields.

## Dependency modules

`def-weil-pbc-projection-compactification`: its record points to an etale functor
on a fixed abelian coefficient category. `Sheaf.Paper.ProjectionCompactification`
reuses Q09's reviewed repair: extension by zero is the representing left adjoint
to actual open module restriction; exactness is a named theorem; unbounded
extension is termwise exact descent; compact support is exactly Rp_*j_!.
The left-adjoint universal property determines the object up to the equality used
downstream, so the chosen representing functor meets the universal-property
exception. It is not a choice from a mere unrelated existence assertion.

`def-weil-pbc-strict-perfect-coefficient-package`: the recorded package sets all
site and coefficient universes equal. The original small pro-etale site has
objects in u+1 and morphisms in u. `StrictPerfectPackageOnSite`
reexports the original module, supplies the same degreewise splitting package
with independent universes, without introducing a second specialized splitting type. Its
`IsProEtaleLocallyStrictPerfect` and `IsProEtaleSitePerfect` are exactly the
recorded local-perfect predicates on that actual site. The two slice
sheafification instances use existing Mathlib transport, with explicit sizes.

`def-weil-pbc-projection-formula-arrows`: the original same-universe arrow
interface cannot instantiate the original small site. The reviewed Q09 module
`ProEtaleProjectionFormulaArrows` is reused, with its published canonical tensor
comparison import. It defines the original-site inverse by localizing the actual
finite-total chain inverse and transporting between uniquely normalized mixed
representatives and K-injective computation. No theorem asserting the desired
projection formula is assumed in its definition. It publicly retains the original
general interface.

`lem-weil-pbc-proetale-derived-pullback-composition`: the recorded theorem is usable
as a characterization but returns nested existential witnesses. The new wrapper
`ProEtaleCanonicalPullbackComposition` reexports it and states its unique characterization with the comparison returned first, then
selects exactly that characterized comparison for use in theta. The ordinary adjunction units,
direct-image fibre-product equation, ordinary mate, degreewise equation and K-flat
square are all retained in the uniqueness theorem from which it selects. Its proof docstring
explains existence from the original theorem and uniqueness from resolution descent.
This avoids expensive elaboration of deeply nested witness extraction. No independent
composition isomorphism is assumed.

`lemma-weil-pbc-projection-formula-open-piece`: this genuine DAG prerequisite has
no published Lean record, but its NG delivery exists. Reuse its
`OpenImmersionTensorPiece` module and statement, including its actual localized
adjunction, the natural isomorphism of bifunctors and the unique unit-transpose
normalization. Its import of the compactification dependency is updated to the
repaired module; its declarations are otherwise unchanged. The original-site
adjunction and alpha transport definitions needed by the compactified statement
belong to the main item's module; no second open-piece theorem is introduced.

`lem-pur-site-restriction-module-adjunction-exact`: NG's open-piece delivery requires
its reviewed `LocalizedModuleExactIndependent` repair. The original SmallCategory
statement cannot instantiate the original site's separate object/Hom universes.
Reuse the NG module verbatim: the actual direct-sum extension/sheafification and
overFunctor, both exactness conclusions, and the uniquely section-normalized
adjunction. Its derived adjunction is exact termwise localization. The helper
names and full signatures were read. This existing recorded node is also added
to the item's statement dependencies; only its lean record changes.

The generic finite-free splitting structure from NG is reused in its module
`StrictPerfectPackageOnSite`; the locally perfect
predicates are added to that same owning-node module. This keeps one splitting
notion, rather than importing two modules that declare it separately.

Only lean records of these dependencies change. There are no new nodes, no
statement changes and no external writes or delivery push. The fresh second
reader is responsible for the second-reading section and actual delivery.

## Validation

The prescribed per-file compile checked all seven delivered modules against the
server sources without Lean errors or non-sorry warnings. The final prescribed
`deliver2.py Q19 lemma-weil-pbc-projection-formula-compactified --no-push` checks
the refreshed node signatures and declaration lists; the independent second
reading is reserved for the next worker. No delivery is pushed by this worker.

## Earlier second reading (a previous round; superseded)

I am the independent second reader. I opened the item node, all seven delivered
modules and all six dependency-node copies. I also opened the recorded operation,
tensor, restriction and composition modules, rather than inferring their meaning
from their names. The following is my inventory of the node, matched against Lean.

1. Schemes X and Y, a morphism f, and a chosen factorization through an intermediate
   scheme: `{X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)`.
   I checked upstream `Compactification`: `d.Z`, `d.i`, `d.g`, `d.comm`,
   `isOpenImmersion` and `isProper` give precisely these objects, f = j followed
   by p, openness and properness. `[QuasiCompact d.i]` supplies exactly the
   node's additional condition on j. Verdict: exact; no further geometric hypothesis.
2. The original small pro-etale sites and arbitrary commutative coefficient sheaf:
   `RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}` and the analogous RZ/RX.
   `cp` and `cj` are identifications with the successive inverse images, not
   arbitrary coefficient maps. These are isomorphic presentations of the node's
   ring equalities; the literal inverse images with identity identifications are
   included. `proEtaleRingCompositeCoefficients d.i d.g ... cp cj` fixes the
   third identification. Verdict: exact; no extra coefficient choice or finiteness.
3. Ordinary uncompleted unbounded derived categories: E and Q are in
   `DerivedCategory (proEtaleRingModules ... )`. I opened `ProEtaleOperations`:
   the module category is the existing `ringedSiteModules`, its derived-category
   instance is `HasDerivedCategory.standard`, pullback is exact termwise descent,
   and direct image is `rightDerivedFunctor` on all modules. Verdict: exact.
4. E is arbitrary; Q alone is site-perfect: `(hQ : IsProEtaleSitePerfect Y RY Q)`.
   Expanding the delivered predicate gives a representative K, and for every V
   a covering sieve, then for every member a bounded F, a degreewise finite-free
   splitting package and a quasi-isomorphism F to the restricted K. Bounds and
   ranks occur inside the cover-member quantifiers. The splitting is
   `i n ≫ p n = 𝟙 (F.X n)`; neither map must be a chain map. Verdict: exact,
   including locally varying amplitudes and without a global strict-perfect model.
5. Derived tensor and its pullback comparison: a, b and c are the recorded
   `ProEtaleTensorModel`s. Their `representative` fields identify the functors
   naturally with localized signed total tensor on every flat K-flat pair.
   I opened the canonical comparison's pure-unit and representative conditions.
   These are presentations of the specified derived tensor, not hypotheses that
   the desired projection map is invertible. Verdict: exact.
6. The composition comparison has direction Lf* to Lj* Lp*:
   `proEtaleCanonicalPullbackComposition d.i d.g RY RZ RX cp cj`.
   Its characterization retains the normalized ordinary units, sectionwise
   fibre-product pasting, conjugate ordinary comparison, degreewise comparison
   and K-flat square of the original dependency. `d.comm` identifies f with
   the composite used in its type. Verdict: exact direction and normalization.
7. Pi is the counit mate, at j_!E and Q: `compactifiedProjectionPi` calls
   `derivedProjectionFormulaMate` with the recorded derived adjunction and the
   canonical tensor comparison. I opened the mate definition: it is the
   upstream right-adjoint projection map in an uncurried interface. Verdict:
   the node's particular arrow, with no arbitrary map parameter.
8. Alpha is the unit transpose: `proEtaleOpenProjection` applies the inverse
   Hom equivalence of `proEtaleRingDerivedOpenAdjunction` to unit tensor identity,
   followed by the inverse tensor comparison. That adjunction is obtained by
   localizing the exact termwise open adjunction. The first existential `hα`
   in the main theorem asserts its invertibility at M = Lp*Q. Verdict: exact.
9. Theta is alpha inverse followed by j_! of identity tensor the composition
   comparison inverse: `compactifiedProjectionTheta` uses `asIso ... hα |>.symm`
   and `mapIso` of `c.tensor.mapIso` with the inverse composition component.
   Verdict: exact endpoints and order; its type itself records invertibility.
10. Compact support is Rp_*j_!: `proEtaleRingCompactSupportImage` is definitionally
    the composite of the derived open extension and derived direct image.
    Consequently the endpoints of `compactifiedProjectionForward` are precisely
    the two compact-support tensor objects. Its body is pi followed by
    Rp_*(theta.hom). Verdict: exact forward composite.
11. Rho is pi inverse: the second existential `hπ` gives `IsIso` of that same pi.
    `compactifiedProjectionReverse` is Rp_*(theta.inv) followed by `@inv ... hπ`.
    The theorem states `IsIso` of the forward map and both composites equal to
    identity. Verdict: exact reverse composite and both inverse equations;
    no unspecified endpoint isomorphism replaces the map in the node.
12. Local normalization of rho: the second recorded theorem,
    `compactifiedProjection_rho_local`, quantifies over V, the recorded `Local`
    presentation l, bounded B, every splitting P, every representation uQ and
    every K-injective representative of the restricted j_!E. Its right side is
    targetIso.hom, tensor/pullback transport along uQ.hom, the actual localized
    finite-total inverse, tensor transport along uQ.inv, and sourceIso.inv.
    This has precisely the conjugation direction needed for an inverse. I read
    `Global.coefficient_eq`, `recordedDirectImage`, the constructed module and
    derived adjunctions, `OrdinaryTensor.pure_unit`, the K-flat representative
    squares, and Local's section, representative and mate-counit conditions.
    Thus this is the same canonical projection operation in the recorded slice
    presentation, up to the unique normalized adjoint and tensor identifications.
    It is not an independently supplied inverse. `restrictionFiniteTotalInverse`
    actually localizes `tensorAdjunctionTotalInverse`, and the existing summand
    theorem fixes inclusion, finite-product inverse and retraction with sign
    (-1)^a. Verdict: exact local clause for every representative, not just one cover.

Source reading: I read blueprint lemma 1271 and its enclosing unit, definitions
1263 and 1268 and lemma 1269. The enclosing proper-base-change torsion theorem
does not add a torsion hypothesis to this separate arbitrary-ring, perfect-Q
projection lemma. I read the Stacks TeX in the launcher's literature mirror:
`sites-modules.tex`, localization definition and lemmas `lemma-extension-by-zero`
and `lemma-extension-by-zero-exact` (03DI/03DJ), and `sites-cohomology.tex`,
`lemma-derived-pullback-composition` (0D6D) and `lemma-pullback-tensor-product`
(07A4), including their proofs. The former assumes a ringed site and a site
object; the latter two assume morphisms of ringed topoi, not Noetherian schemes,
bounded E or finite coefficient rings. The delivered specializations retain
exactly the additional geometry and coefficient identifications of the DAG.
There is no `statement_change` in this delivery and no silent statement correction.

Dependency reading, independently checked under H13:

- `def-weil-pbc-projection-compactification`: the old declaration is on an etale
  fixed coefficient category. The repair publicly uses the actual original-site
  module pullback; its left adjoint defines open extension by the permitted
  adjoint universal property. Exactness is a separate named theorem. Compact
  support is the literal functor composite; `Compactification.ofIsProper` is
  the original identity compactification. Matches definition 1268.
- `def-weil-pbc-strict-perfect-coefficient-package`: the old same-universe
  package cannot directly instantiate Category.{u} on Type (u+1). The generalized
  structure has exactly N,i,p,splitting and independent site/coefficient sizes.
  The original package, idempotent identities, global ring-module package and
  associated constant package remain publicly available. The new local predicates
  reproduce the node's quantifier order on the actual pro-etale site. Matches
  definition 1263; finite products are finite free tuples, including rank zero.
- `def-weil-pbc-projection-formula-arrows`: the repair reexports the generic
  counit mate, free/retract inverses and summand formula. It specializes by
  localizing that actual signed-total chain inverse and conjugating with unique
  mixed-tensor and K-injective comparisons. Its ordinary unit equation and
  representative square fix the maps; it assumes no projection-formula theorem.
  Matches definition 1264 with the required original-site universe interface.
- `lem-weil-pbc-proetale-derived-pullback-composition`: I compared the wrapper
  with every witness of the recorded original theorem. The wrapper adds the
  uniqueness implied by precisely those normalizations and exposes comparison
  first for selection. No normalization was forgotten. Matches Stacks 0D6D.
- `lemma-weil-pbc-projection-formula-open-piece`: the NG module states a natural
  isomorphism on unbounded E and the full subcategory of objects represented by
  bounded split-finite-free complexes. `beta.inv` is uniquely fixed as the unit
  transpose, so beta is exactly the node's displayed direction. Its slice ring
  is the restriction of the intermediate coefficient sheaf. Matches lemma 1269;
  using the full subcategory simply includes changes of representative.
- `lem-pur-site-restriction-module-adjunction-exact`: the generalized module
  uses the existing direct-sum extension presheaf followed by sheafification and
  actual `overFunctor`. It asserts both exactness statements and constructs the
  adjunction from a unique summand-unit normalization. Derived adjunction is
  exact termwise localization. The previously recorded SmallCategory interface
  excludes the needed unequal site universes. Matches Stacks 03DI/03DJ.

There are no new definition nodes. The existing restriction node added to
`stmt_deps` supplies precisely the last clause's slice operations; the existing
localized-adjunction node owns the delivered dependency repair. Only lean records
change on dependencies. I checked the file/node ownership and the seven verbatim
primary signatures; no unit statement is edited.

Edge cases: X or Y empty, the empty open, identity open and identity proper
compactification remain allowed; E and Q can be zero. Rank N n = 0 is allowed
by Fin 0, and bounds a > b allow the zero complex. Degrees are all integers;
E can be unbounded in both directions. Splittings need not commute with the
differential. RY can be zero or nonconstant and has no characteristic restriction.
Changing a local representative is explicitly covered by every uQ and rep.
The original sites have object universe u+1 and Hom universe u, and module
sections/coefficient rings use u+1, as in the size convention; no new equality
of site universes or universe below that of the schemes is imposed. Verdict:
all the node's listed edge cases are retained.

Independent searches used different wording from the first worker:

- LeanFinder: "Derived tensor commutes with pushforward with compact support for
  locally perfect complexes" returned ordinary module pushforward composition
  and natural-isomorphism declarations, not this derived compactification theorem.
- Loogle: `"projection"` returned Lean compiler structure-projection metadata.
- Mathlib grep through msearch: `compactSupport.*tensor|tensor.*compactSupport|projection.*perfect`
  returned zero hits.
- Direct rg in Mathlib, upstream WeilConjectures and side `lean/Sheaf` for
  projection-formula, compactification-map and tensor/lowerShriek names found
  fixed-coefficient etale/pro-etale and scheme-module projection results. I opened
  upstream `HasProjectionFormulaOfCompactification` and
  `openImmersionLowerShriekTensorIso`: their coefficient category is a fixed A,
  not arbitrary RY-module sheaves with the local finite-total inverse clause.
  I also read the 51-module framework note and its actual ModuleObject derived
  tensor and compact-support declarations. Those use coefficient objects from
  one condensed ring, not an arbitrary coefficient sheaf on Y. Neither is an
  exact existing match for this node.
- LeanSearch: "Projection formula for derived compact support pushforward and
  perfect complexes of sheaves of modules" returned Internal Server Error.
  This is an unavailable search, not evidence of absence. Successful semantic,
  name-based and direct source searches above provide the independent search.

Mismatches found and changes: none in the mathematics, Lean signatures or node
records. I added this independent second-reading section only. Every delivered
theorem remains postponed with `sorry`; definitions contain actual data or
selection from characterized universal properties. The main proof docstring
follows the six DAG proof steps, including local detection and representative
transport rather than descent of arbitrary derived morphisms. All delivered
lines are at most 100 characters and all variables/universes are explicitly
bound. Per-file wrapper compilation and delivery preflight are recorded below.

Second-reader validation: `scompile.py Q19
lemma-weil-pbc-projection-formula-compactified` with all seven sibling modules
passed, exit 0, with no Lean errors or warnings. Each file compiled separately
within the prescribed 60-second limit; the longest invocation was 50.0 seconds.
The required `deliver2.py --no-push` and final delivery run follow this check.

The second-reader dry run printed `OK`: commit `5b7830074b` passed compilation
and server preflight with the complete second-reading section; nothing was pushed
by that dry run. Final delivery uses the prescribed wrapper.


## Return repair: incomplete independent review

Return: L, immutable head `8450471c4fdf`, review ended without compiler results,
concrete findings or final verdict. This is a documentation completion, not a
rebase-only resubmission. The original independent review is preserved in sandbox
`review.md`, explicitly attributed to its original reviewer. A new repair completion
section records fresh compilation and concrete findings. This worker does not
claim to be the previous independent maintainer reviewer or to alter that review
outside the authorized sandbox. The deliver2 wrapper delivers report.md, so the
completion evidence is also included here for the next reader.

The returned Lean modules and their node signatures were re-opened. All seven
primary lean.statement signatures match the source, modulo whitespace. Every module
has a single owning node. The item retains arbitrary E and site-perfect Q, the
small pro-etale site universes, the canonical counit mate, unit-transpose alpha,
the stated direction of theta, both inverse equations, and the local finite-total
inverse clause. No theorem or definition was changed for the reported defect.
Fresh compiler and dry-run results follow below when completed.

### Fresh compiler evidence for return repair

Fresh scompile.py reproduction completed with exit 0 on 2026-10-16.
The complete stdout/stderr is retained in sandbox `repair-compile.log`. It checked
all seven sibling modules separately, in dependency order, against the local side
overlay. There were zero Lean errors and zero warnings; no server fallback was
needed. The command used the prescribed wrapper, with its configured 60-second
per-invocation limit, nice 19 and two threads. Printed elapsed figures include
compiler-slot waiting and are not claimed as individual Lean execution times.
No timeout setting, global build, live Lean file or compiler configuration was changed.

Command (paths relative to the sandbox):

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q19 \
  lemma-weil-pbc-projection-formula-compactified \
  lean/Sheaf/AlgebraicGeometry/ProEtaleCanonicalPullbackComposition.lean \
  lean/Sheaf/CategoryTheory/LocalizedModuleExactIndependent.lean \
  lean/Sheaf/Paper/ProjectionCompactification.lean \
  lean/Sheaf/Paper/StrictPerfectPackageOnSite.lean \
  lean/Sheaf/Paper/OpenImmersionTensorPiece.lean \
  lean/Sheaf/Paper/ProEtaleProjectionFormulaArrows.lean \
  lean/Sheaf/Paper/ProjectionFormulaCompactified.lean
```

Compilation results by module: ProEtaleCanonicalPullbackComposition PASS;
LocalizedModuleExactIndependent PASS; ProjectionCompactification PASS;
StrictPerfectPackageOnSite PASS; OpenImmersionTensorPiece PASS;
ProEtaleProjectionFormulaArrows PASS; ProjectionFormulaCompactified PASS.

### Concrete findings and verdict for return repair

The missing review completion is now present in sandbox review.md: concrete
findings, compiler result for every delivered module, and explicit PASS verdict.
The detailed independent mathematical audit is preserved with its original author
attribution. No Lean/node mathematical change was needed for this documentation
return. Seven primary signatures, unique file ownership, explicit binders,
source/blueprint docstrings and line widths were rechecked. All seven modules
compiled cleanly through scompile.py. PASS for the repair checks; the next fresh
reader retains responsibility for independent review and delivery.


### Packaging repair after the first fresh dry run

The first fresh dry run compiled successfully but preflight returned one reason:
`LocalizedModuleExactIndependent.lean is not changed by the commit`. This exact
module has landed since the returned delivery. `scompile.py --source
Sheaf.CategoryTheory.LocalizedModuleExactIndependent` returned the complete
published module, byte-for-byte matching the sandbox text. Its source is retained
in sandbox published-localized-source.log. Accordingly the owning dependency's
lean record now uses existing:true, branch:newtargets-dag and the same module and
declarations, with a note explaining this exact existing §1(B) repair. Its file
field and redundant sandbox module are removed. No Lean declaration or signature
changed. The final delivery has six modules and the existing dependency record;
the seven-module compiler evidence above remains the actual pre-repair run.
The subsequent dry run compiles the six modules plus explicit #check probes for
all recorded existing dependency declarations and runs the server preflight.

## Earlier second reading (a previous round; superseded)

Fresh independent reading, 2026-10-16. I read the present item node, its six
sandbox modules, all seven sandbox node records, the published localized-module
module, and the recorded operations, tensor, composition and restriction interfaces.
The older readings above are historical evidence; this section records my own checks.
There is no statement_change and no new definition node in this delivery.

Inventory of the node, matched item by item to Lean:

1. Schemes X and Y, map f, intermediate scheme, factorization, proper p and
   quasi-compact open j: `{X Y : Scheme.{u}} {f : X ⟶ Y}`,
   `(d : Compactification f) [QuasiCompact d.i]`. I opened upstream
   `Compactification/Defs.lean`: Z, g, i, comm, isProper and isOpenImmersion
   give exactly the remaining objects and properties. In particular, quasi-compactness
   is not silently inferred from openness. Verdict: exact.
2. The original small pro-etale sites and arbitrary commutative ring sheaf:
   `RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}`, with RZ and RX on
   d.Z and X. The isomorphisms cp and cj identify the successive inverse-image
   coefficients. They include the literal inverse-image rings with identity
   identifications. `proEtaleRingCompositeCoefficients d.i d.g ... cp cj`
   constructs the composite identification; no third independent choice is allowed.
   Verdict: the invariant presentation of precisely the node's coefficients.
3. Ordinary uncompleted unbounded module derived categories and operations:
   `DerivedCategory (proEtaleRingModules ... )`, exact termwise
   `proEtaleRingDerivedPullback`, and K-injective `proEtaleRingDerivedDirectImage`.
   I read ProEtaleOperations and ProEtaleOperationsCanonicalAdjunction: the
   module category is ringedSiteModules, localization is the standard full derived
   category, and the derived adjunction comes from the normalized module adjunction.
   The finite-coefficient primary record publicly reexports these arbitrary-ring
   interfaces. Verdict: exact, with no completion or constructibility restriction.
4. Arbitrary E and site-perfect Q, with no global bound:
   `(E : DerivedCategory (proEtaleRingModules X RX))`, Q in the corresponding
   Y-category, and only `(hQ : IsProEtaleSitePerfect Y RY Q)`. Expanding the
   delivered predicate gives a representative K, then every V, a covering sieve,
   every member, a bounded F with a quasi-isomorphism F to restricted K and a
   degreewise finite-free splitting. Bounds and ranks are inside the member
   quantifier; `i n ≫ p n = 𝟙 (F.X n)` has the correct order and does not
   require chain-map splittings. Verdict: exact.
5. The derived tensor presentations a,b,c and canonical composition comparison:
   `ProEtaleTensorModel` identifies tensor naturally with signed total tensor on
   every flat K-flat pair. The composition wrapper retains the ordinary normalized
   adjunctions, sectionwise fibre-product equation, conjugate comparison, degreewise
   termwise equation and K-flat square of the recorded theorem, selecting its unique
   derived comparison. Its direction is L(j then p)* to Lp* then Lj*. The equality
   d.comm identifies j then p with f. Verdict: canonical presentations of the named
   operations, with no extra mathematical hypothesis.
6. Pi is the specified counit mate: `compactifiedProjectionPi` calls
   `derivedProjectionFormulaMate` for p at j_!E and Q, with
   `proEtaleRingDerivedAdjunction` and `proEtaleCanonicalTensorComparison`.
   I opened the mate definition: it uses the existing rightAdjointProjectionMap.
   Its tensor comparison is fixed on pure tensors and K-flat representatives.
   Verdict: exact map, not merely an arrow with the correct endpoints.
7. Alpha and its invertibility at Lp*Q: `proEtaleOpenProjection` is the inverse
   Hom-equivalence applied to the derived unit tensored with identity and followed
   by the inverse tensor comparison. Its adjunction is localization of the
   exact ordinary pair. The theorem's existential hα asserts precisely its
   invertibility at `(proEtaleRingDerivedPullback d.g ...).obj Q`.
   Verdict: exact direction and normalization.
8. Theta, forward composite, reverse composite and both inverse equations:
   `compactifiedProjectionTheta` is alpha inverse followed by j_! of identity
   tensor the inverse composition component. `compactifiedProjectionForward`
   is pi followed by Rp_*theta.hom. Existential hπ asserts pi invertible;
   `compactifiedProjectionReverse` is Rp_*theta.inv followed by inv pi.
   The conclusion includes IsIso of the forward map and both composites equal
   identity. `proEtaleRingCompactSupportImage` is definitionally j_! then Rp_*,
   giving the stated endpoints. Verdict: every displayed clause and order matches.
9. Local strict-perfect normalization of rho:
   `compactifiedProjection_rho_local` quantifies over the normalized Global and
   Local operations, every V, bounded B, package P, representative uQ, K-injective
   K and representation rep. I opened Global.coefficient_eq,
   recordedDirectImage, Operation.moduleAdjunction/derivedAdjunction, the tensor
   representative squares, Local.coefficient_sections, directImage_representative
   and mate_counit. These fix the same canonical operations in their slice
   presentation. The equality is restriction of inv pi = targetIso.hom, then
   transport by uQ.hom, the finite-total inverse, transport by uQ.inv, then
   sourceIso.inv. This is the required conjugation order for an inverse.
   `restrictionFiniteTotalInverse` actually localizes tensorAdjunctionTotalInverse
   between the mixed-tensor and K-injective representatives; its summand formula
   is inclusion, free inverse, retraction, with the signed total convention.
   Verdict: the node's final clause is present for every representative.

Source and dependency audit: I read blueprint lemma 1271 and definitions 1263,
1264 and 1268, the open-piece node and its full Lean signature, and Stacks
sites-modules.tex lemma-extension-by-zero / lemma-extension-by-zero-exact
(03DI/03DJ), plus sites-cohomology.tex lemma-derived-pullback-composition
and lemma-pullback-tensor-product (0D6D/07A4). These statements do not add
Noetherian, dimension, characteristic or coefficient-finiteness hypotheses.
The enclosing proper-base-change setting does not add such a premise to this
separate perfect-coefficient formula.

Each supplied dependency module was checked against its own node:

- ProjectionCompactification uses the existing Compactification structure and
  defines Rp_*j_! with the exact open extension. The left-adjoint universal
  property determines its selected functor with its adjunction; the data are
  not chosen from an unrelated mere existence statement.
- StrictPerfectPackageOnSite retains the old ring-module and constant-package
  interfaces by public import, generalizes the same N/i/p/splitting data to
  independent universes, and gives the actual-site local perfectness predicates.
- ProEtaleProjectionFormulaArrows retains the general arrows and constructs
  the original-site inverse by localizing the existing finite-total map, using
  uniquely characterized mixed representatives and the K-injective comparison.
- ProEtaleCanonicalPullbackComposition retains all normalizations of the original
  composition theorem; its unique witness is exposed for selection in theta.
- OpenImmersionTensorPiece uses the full subcategory of derived coefficients
  admitting bounded finite-free retract representatives. Its natural isomorphism
  is uniquely characterized by its inverse being the unit transpose. This is
  the node's natural open formula on unbounded E, including representative changes.
- The existing LocalizedModuleExactIndependent declaration was opened in the
  shared side source: extension is direct-sum extension presheaf followed by
  module sheafification, restriction is actual overFunctor, both are exact,
  and the adjunction is fixed by summand insertion. Its derived adjunction is
  termwise localization. The existing:true record is correct.

No new definition nodes require a stage-1 audit. The added statement-dependency
edges name the existing restriction and localized-adjunction nodes needed to type
these interfaces. All six primary lean.statement strings occur verbatim in their
owning files. No unit statement or mathematical node statement changes.

Edge cases: empty schemes and empty open, identity open, proper identity
compactification, zero E, zero Q and zero ring all remain admitted. Fin 0 covers
rank zero. Bounds a > b include an all-zero complex. Degrees range over all
integers and E is unbounded in both directions. Local bounds/ranks vary, and
splittings need not commute with differentials. Coefficients can be nonconstant
and have any characteristic. Every uQ and rep is quantified. The original site
has object universe u+1 and morphism universe u; coefficients have universe u+1.
No equality of those site universes is imposed. Verdict: no excluded node case.

My fresh searches used wording different from the worker's:

- LeanFinder, "Tensoring by a locally perfect complex commutes with derived
  extension by zero followed by proper direct image": generic Tor and complex
  tensor declarations, no matching statement.
- Loogle, `"compactification", "tensor"`: zero hits.
- LeanSearch, "Adjunction counit projection formula with a local perfect
  coefficient and compact support": generic adjunction and localization counit
  declarations, no matching statement (this fresh service call succeeded).
- Direct rg on Mathlib, slopmaster2 WeilConjectures and side lean/Sheaf for
  compact/projection/tensor and lowerShriek/tensor variants found fixed-category
  pro-etale/etale projection results and the generic constructions reused here.
  I opened ProEtale.HasProjectionFormulaOfCompactification and its comparison
  theorem: their fixed A-valued sheaves and etale-origin/boundedness premises
  do not give this arbitrary ring-sheaf formula. I also opened the exact side
  ModuleObject Derived/Tensor and Derived/LowerShriek sources and the framework
  note: their coefficient is pulled back from one condensed ring, not arbitrary RY.

Mismatches and changes in this reading: no mathematical or Lean signature mismatch
found; no Lean/node edit was necessary. I appended this fresh independent reading.
Definitions use constructed data or uniquely characterized universal-property
choices; theorems remain sorry. The main proof docstring follows all six DAG
steps. The six modules disable autoImplicit, have bound universes, source and
blueprint docstrings, and maximum line lengths 91, 93, 94, 94, 97 and 89.
Fresh wrapper compilation, dry-run and delivery results are recorded next.

Fresh second-reader validation: the prescribed scompile.py invocation on all six
remaining modules completed with exit 0 and no errors or warnings. Each module
passed separately in both sandbox and library placement; no timeout limit was
changed. The published localized-module dependency is checked again by the
existing-declaration probes of deliver2.py.

Fresh second-reader packaging repair: the first dry run compiled cleanly but
server preflight reported that ProjectionCompactification and
ProEtaleProjectionFormulaArrows were not changed by the commit. Both have now
landed on the current base. I fetched each current source with scompile.py
--source and compared it to the sandbox module: both are identical except
for the extra newline printed by the source reader. I changed only these two
lean records to existing:true, removed their file fields and redundant sandbox
modules, and appended the publication evidence to their lean.note. Thus four
modules remain in the delivery and three dependency modules are reused as
existing declarations. No mathematical statement, signature or definition changed.

The repaired second-reader dry run completed with exit 0 and printed:
`OK (dry run): commit 1f43fb32a2 passes the preflight and compiles; nothing pushed`.
The full output is in second-reader-dryrun-final.log. It checked all four remaining
modules and all recorded existing-declaration probes, with no compiler errors or
warnings. The wrapper preserved current dependency fields outside lean, as required.
Final second-reader verdict: PASS; proceed with the prescribed final delivery.

## Return repair L: preserve the published perfectness interface

The returned immutable head edc9f6c9cbc2 replaced
`Sheaf.Paper.StrictPerfectPackageOnSite` without retaining
`SheafOfModules.IsPerfectOnSmallRingedSite`. The published
`Sheaf.Paper.PerfectProjectionFormula` and
`Sheaf.Paper.ProjectionFormulaIdentityCompactification` still use that name.
I read both callers and fetched the current owning module with
`scompile.py --source Sheaf.Paper.StrictPerfectPackageOnSite` before editing.

The sandbox module now retains all three previously omitted declarations:
`SheafOfModules.IsLocallyStrictPerfectComplexOnSite`,
`SheafOfModules.IsPerfectOnSmallRingedSite`, and
`SheafOfModules.SiteStrictPerfectCoefficientRepresentation`.
Their signatures, bodies, fields, and source docstrings are copied from the
published generic interface. All are recorded in the dependency node's
`lean.declarations`; its repair note records the compatibility requirement.
The new pro-etale predicates specialize those generic definitions directly,
so their former expanded formulas are definitionally unchanged and there is
one construction of local perfectness. The original category object universe
u+1 and morphism universe u, arbitrary derived-category universe, locally varying
bounds and ranks, and degreewise finite-free splittings are retained.

This repairs the caller failures by preserving their API in the owning module.
Neither caller needs a changed statement or a replacement hypothesis. The main
item's statement and signature are unchanged. No new node, theorem proof,
axiom, statement correction, or additional mathematical assumption is introduced.
The zero complex, rank zero, empty covering cases, nonconstant coefficients,
and nonuniform local bounds remain admitted by the same formulas.

Fresh compiler and dry-run evidence for this repair is recorded below when complete.

### Fresh validation of return L

Both fresh `scompile.py` invocations exited 0, with zero Lean errors or warnings:

- `compatibility-compile.log`: compiled every delivered module separately in
  dependency order: ProEtaleCanonicalPullbackComposition,
  StrictPerfectPackageOnSite, OpenImmersionTensorPiece, and
  ProjectionFormulaCompactified.
- `compatibility-callers-compile.log`: compiled the repaired
  StrictPerfectPackageOnSite together with the current published sources of
  ProjectionFormulaIdentityCompactification and PerfectProjectionFormula.
  Both affected consumers compile against the replacement module. Their source
  snapshots are validation inputs only, outside the delivery's lean directory.

Every compiler invocation used the prescribed wrapper and its unchanged
60-second per-file limit. Printed timings include compiler-slot waiting.
The generic definitions' published source block is retained verbatim; all four
primary node signatures occur verbatim in their modules, and each module's
maximum line length is at most 100. The required final command is
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q19
lemma-weil-pbc-projection-formula-compactified --no-push`; its complete output
is saved as `compatibility-dryrun.log`. The worker returns READY only after
that command prints OK. No delivery push is performed by this repair worker.

## Second reading by Q19

I independently reread the node statement, its blueprint source place (order 1271),
all eight statement dependencies, and the four delivered modules. The item-by-item
matching is:

1. The compactification data are `X Y : Scheme.{u}`, `f : X ⟶ Y`,
   `d : Compactification f`, and `[QuasiCompact d.i]`; `d.i`, `d.g`, `d.comm`,
   `d.isProper`, and `d.isOpenImmersion` supply exactly `j`, `p`, `fp = f`,
   properness, and the quasi-compact open immersion.
2. `RY`, `RZ`, `RX` are commutative-ring sheaves on the three small pro-etale
   sites, with `cp`, `cj`, and `proEtaleRingCompositeCoefficients` supplying the
   two inverse-image identifications and their required composite for `f`.
3. `a`, `b`, and `c` are the recorded tensor models; all derived objects and
   operations use the ordinary uncompleted unbounded categories and the recorded
   pullback/direct-image adjunctions. No completion, constructibility, or bounded
   hypothesis is added.
4. `E` is arbitrary in the `X` module derived category. `Q` is in the `Y`
   derived category and the sole coefficient hypothesis is
   `hQ : IsProEtaleSitePerfect Y RY`; the delivered predicate permits locally
   varying finite-free retract bounds and ranks with no common global bound.
5. `compactifiedProjectionPi` is the specified counit mate; `compactifiedProjectionTheta`
   uses the inverse of the normalized open projection followed by the inverse of
   the canonical pullback-composition comparison, in the node's direction.
6. `compactifiedProjectionForward` is exactly `pi ≫ Rp_* theta`; the theorem
   supplies `IsIso` for it and both ordered identity equations using
   `compactifiedProjectionReverse = Rp_* theta⁻¹ ≫ pi⁻¹`. The separate
   `compactifiedProjection_rho_local` theorem records the required signed-total
   inverse on every local representative and every chosen representative
   isomorphism.

No mismatch was found. In particular, no extra Noetherian, characteristic,
finite-coefficient, global-bound, or universe-equality assumption occurs. The
small-site universe is retained (`ProEt` objects in `u+1`, morphisms in `u`),
and all category universes are explicitly bound. The theorem's existential
`hα` and `hπ` are the Lean encoding of the node's invertibility assertions;
its two compositions have the same source and target identities and order.

Edge cases checked: empty schemes and empty opens, identity open and identity
compactification, zero `E`, zero `Q`, zero coefficient ring, rank `Fin 0`,
all-zero bounded representatives, arbitrary integer degrees and unbounded `E`,
nonconstant coefficients, all characteristics, and locally different bounds or
ranks. Every case remains admitted by the binders and definitions.

Searches used fresh wording with `msearch.py`/LeanFinder/Loogle and direct `rg`
through Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`; only generic
Tor, tensor, restriction, and fixed-coefficient projection declarations were
found. None states this arbitrary-ring, locally site-perfect compactified
formula. No existing exact declaration was found for the item. Dependency
records were opened and their recorded declarations (or reviewed existing
canonical modules) match the notions used here. The strict-perfect module keeps
the published compatibility declarations, and the composition and projection
interfaces retain their canonical normalizations; no hollow definition or
private duplicate was introduced.

No Lean or node correction was necessary. The only change in this second
reading is this required audit section; the four module signatures remain
unchanged and all theorem proofs remain named `sorry`s with source and blueprint
docstrings. The prescribed wrapper compilation and dry run are rerun after this
append before delivery.
