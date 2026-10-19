## Worker report

Q44 repairs returned delivery 5c4a0c297239 for
`lem-trf-proper-composition-site-transport`. This is now a stage-2 delivery:
`lean/Sheaf/AlgebraicGeometry/ProperCompositionSiteTransport.lean` states the
composition square, the mixed refinement square, and the identity-open proper
normalization. Each theorem has `:= by sorry`. Every definition has complete data.
The ten-step natural-language proof from the node is in the composition theorem's
docstring; the refinement and proper theorems also have their corresponding proof
arguments. The current repository node is the baseline: its `split_report` and
all fields other than `lean` and the permitted addition to `stmt_deps` are retained.
The added dependency is the already landed refinement-comparison definition.
No correction to the mathematical statement is needed.

Hypotheses and clauses, read against the node:

- A field k is `(k : Type u) [Field k]`. The prime and invertibility conditions
  are `(l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))`.
- A finite extension of Q_l is `(E : Type (u + 1)) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Positive level is
  `(n : ℕ+)`, allowing level one. `properTransportCoefficient l E n` is exactly
  `Padic.coefficientExtensionRing l E n`, not a newly chosen coefficient ring.
  Its finiteness instance invokes `Padic.finite_coefficientExtensionRing` with
  `n.property`. The common coefficient universe is the standard universe of
  fixed-module site sheaves; no equality between object and morphism universes
  of the pro-etale site is imposed.
- U,V,W are `Scheme.{u}` with `Over (Spec (.of k))` structures. Each structural
  morphism has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances.
  The last two together say finite type, not merely locally finite type.
- The maps are `(h : U ⟶ V) (f : V ⟶ W)` with `IsOver`, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` instances, exactly separated finite-type
  k-morphisms. Properness is the explicit disjunction
  `(_hproper : IsProper h ∨ IsProper f)`. It is not restricted to an inner proper
  factor. No finite-map, smoothness, constructibility or extra boundedness
  hypothesis appears.
- `ch`, `cf`, `chf` are arbitrary supplied `Compactification h`,
  `Compactification f`, and `Compactification (h ≫ f)`. The local instances used
  inside the compositor definitions express existence only; canonical pairwise
  candidate comparisons carry their globally chosen models to these supplied
  models. The argument does not mistake a Prop-valued existence instance for a
  prescribed choice.
- L is an arbitrary `DerivedCategory.Plus (Sheaf U.smallEtaleTopology
  (ModuleCat.{u + 1} (properTransportCoefficient l E n)))`. Its image under the
  comparison has the canonical bounded-below etale-origin witness; no witness
  existence is assumed as an extra condition.
- C is `(comparisonUpperStar ... T).mapDerivedCategory`, or its plus restriction
  in the proper-normalization clause. `properTransportComparison A c L` is the
  inverse of the recorded `compactSupportSiteComparison A c` at L. The inverse
  has exactly the node's direction `C F_e -> F_p C`. That recorded comparison
  is constructed from the counit mate b followed by the proper image of the
  normalized open comparison e, so c is not an arbitrary isomorphism.
- The actual ordinary compositor is `properTransportEtaleComposition`: the
  recorded canonical compactification changes, then
  `Etale.unboundedEtaleLowerShriekCompIso`, then change to `chf`. Its evaluation
  on L.obj represents the specified D-plus compositor using its recorded
  unbounded restriction compatibility. `properTransportComparisonAfterInner`
  inserts exactly those inclusion compatibilities to evaluate c_f at F_h^e L.
- The actual pro-etale compositor is `properTransportProEtaleComposition`:
  evaluate `originCompositionAmbient` on the canonical comparison image of L,
  with canonical changes from ch and cf and to chf. `properTransportCandidateChange`
  is the unique descent along the comparison equivalence of the recorded
  ordinary canonical change conjugated by the named site comparisons. It uses
  all ambient morphisms in the full origin subcategory, rather than an
  artificially smaller hom-set or an arbitrary chosen natural isomorphism.
- `properCompositionSiteTransport` asserts precisely, in Lean's left-to-right
  composition convention,
  `C(alpha_e) ≫ c_hf = c_f(F_h^e L) ≫ F_f^p(c_h) ≫ alpha_p`.
- `properCompositionSiteTransport_refinement` asserts
  `c_c ≫ theta_p(r) = C(theta_e(r)) ≫ c_d` for every actual refinement r.
  `properTransportRefinement` is the actual pro-etale refinement map, assembled
  from the inverse direct-image compositor and the proper image of the inverse
  normalized proper/open comparison. It is not defined by conjugating c, which
  would make the mixed square tautological. The equation gives the inverse
  comparison equation by cancellation, and gives finite chains/common-refinement
  comparisons by composition, as explained in its proof docstring. Thus the
  composition square is transported under the canonical refinement comparisons
  at all three candidates.
- `properCompositionSiteTransport_proper` uses `Compactification.ofIsProper f`.
  After the explicitly constructed ordinary and pro-etale identity-open
  identifications, it equates c to `fixedComparisonDirectImageMatePlus`, the
  specified counit mate b. Both identifications come from the identity-open
  adjunction, not from `Nonempty` of some isomorphism.

Dependency declarations used (module, name):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  The morphism-properties node is a convention; its finite-type condition is
  `LocallyOfFiniteType` together with `QuasiCompact`.
- `WeilConjectures.Compactification.Refinement`: `Compactification`,
  `Compactification.Refinement`, `Compactification.ofIsProper`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and its Plus API:
  `Etale.rightDerivedLowerShriekOfCompactification`, its Plus version and
  `rightDerivedLowerShriekOfCompactificationPlusCompatibility`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport`; the fixed-scalar realization of the
  intrinsic operations is the existing one used by the site-comparison and
  witness-realization interfaces, not another compact-support definition.
- `Sheaf.Paper.EtaleOriginDerivedCategory`: `EtaleOriginDerivedCategory`;
  its recorded witness category is retained through the existing realization
  adapter in the composition module. Its fixed-scalar full-image presentation is
  `DerivedCategory.plusEtaleOrigin` and
  `comparisonUpperStarPlusEtaleOrigin` (upstream finite-coefficient API).
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompactSupport`, `originCompositionAmbient`, `originComposition`, and
  the recorded witness adapter `originCompositionWitnessed`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `Etale.rightDerivedLowerShriekOfCompactificationIso`,
  `Etale.unboundedEtaleLowerShriekCompIso` and the bounded-below restriction
  compatibilities. `Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition`:
  `Etale.unboundedEtaleProperComposition_normalization` (inner-proper
  normalization only; the general ordinary compositor handles either proper
  factor).
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`; fixed-module `comparisonUpperStar` is its
  recorded coefficient realization. `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  gives the recorded derived categories.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, `proEtaleComparisonDirectImageCompIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparison_coherence`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`, `compactSupportSiteComparisonPlus`,
  `properOpenProEtaleIsoPlus`, with the recorded mate/open-unit normalization.
- The repaired proper-coincidence module supplies
  `Etale.properCoincidenceIdentityOpenPlus` and
  `ProEtale.properCoincidenceIdentityOpenPlus`.
- The repaired refinement module supplies `properTransportRefinementPlus` and
  `properTransportRefinement`; the direct-image composition module retains
  `finiteDirectImageComposition`. The existing statement modules of proof
  dependencies are imported as the stage-3 proof plan. The tower-normalization
  node has no current Lean record and is cited in the docstring instead of
  inventing a proof theorem in this delivery.

Edge cases checked mathematically and in the signatures: only h proper, only f
proper, both proper, either map the identity, arbitrary chosen nonidentity-open
models of a proper map, identity and noncartesian refinements, inverse refinement
comparisons and common-refinement chains, empty source scheme, L=0, n=1, and
arbitrary (not necessarily finite) base field. The definitions require neither
nonemptiness nor nonzero complexes. Properness is never replaced by finiteness.
There is no added cartesian condition on refinements.

Searches:

- `msearch.py ... leanfinder` with "The etale to pro-etale comparison respects
  compact support composition with a proper factor and refinement": eight
  ordinary morphism/composition results, none the mixed-site statement.
- `msearch.py ... loogle` with
  `Functor.isoWhiskerLeft, Functor.isoWhiskerRight, NatIso.ofComponents`:
  no match (the query parser reported an unknown identifier). The actual
  declarations were subsequently read in the project/Mathlib source.
- `msearch.py ... grep` with
  `compactSupportSiteComparison|originComposition`: no Mathlib match.
- `rg` in `WeilConjectures/` and `lean/Sheaf/` for compact-support comparison,
  origin composition, proper-open comparison, proper coincidence, and derived
  direct-image composition found the dependency constructions listed above,
  but no existing mixed composition/refinement/proper-normalization theorem.
- `grep -rn lem-trf-proper-composition-site-transport` in the upstream
  `WeilConjectures/` tree had no result. `rg` for the new full declaration names
  in Mathlib, upstream and the side library also had no result.
- `scompile.py --source` was used to inspect current server-only finite-coefficient
  modules and the transport-identifies-exchange source. In particular the current
  finite open-extension path is `FiniteCoefficient.LowerShriek.Open.Defs`.

No `STATEMENT-DISPUTED` issue remains. There are no new definition nodes: all added
helpers expose canonical maps of the existing owning nodes.

## Dependency modules

`cor-cbc-proper-coincidence`: the old `Nonempty` isomorphism record does not give
the source's canonical proper identification or equality of exchange maps.
`ProperCoincidenceNormalized.lean` constructs the identity-open isomorphisms from
adjunctions, transports ordinary candidates canonically, and states the actual
exchange equality and its invertibility. This is the requested section 1(B)
repair; its node changes only in `lean`.

`thm-sf-comp-composition`: the original module imported three retired ProEtale
paths, conflicting with the finite-coefficient operations imported by the site
comparison. The delivered module uses their finite-coefficient counterparts.
Every definition and theorem body is retained, including the full ambient origin
category, canonical compositor, witnessed adapter and all coherence statements.
Only the dependency node's `lean` record changes.

`def-sf-refinement-comparison-isomorphism`: the existing coefficient-realized
witness interface is retained in full. The needed pure comparison-input Plus and
ambient specializations are added to this owning module, using precisely its
part (b) formula. This avoids inventing a second notion of refinement. Its old
imports are migrated to the current finite-coefficient paths and the canonical
site comparison is imported. Only the dependency node's `lean` record changes.

`lem-weil-derived-direct-image-composition`: six stale operation imports collide
with the current finite-coefficient operations (the first reported duplicate was
`upperStarIsoLowerStarInv`). The imports are migrated to FiniteCoefficient;
`finiteDirectImageComposition` keeps its entire original universal-right-derived
construction and signature. Only the dependency node's `lean` record changes.

## Second reading by Q44

This is a separate second pass by the same dispatcher worker: the brief explicitly
forbids starting other agents. No independent worker review is claimed. The
maintainer's independent review can read the concrete statement delivery.

With the node and all modules open, the second pass checked every hypothesis and
each of the three conclusions. It confirmed that the properness hypothesis is a
disjunction and that the arbitrary compactification binders are genuine inputs.
It checked the orientations of c and both compositors, and followed the exact
bounded-below inclusion maps when c_f is evaluated on F_h L. It checked that the
pro-etale refinement map is independently built from the specified proper/open
arrow, rather than being defined to make the desired square true. It checked the
identity-open adjunction normalization on both sites, including the normalization
on the pullback candidate in the proper-coincidence exchange equality.

Mismatches found and repaired in this pass: the initial stale finite open-module
path used `OpenImmersion` instead of `Open`; the moved refinement specialization
needed an explicit coefficient-universe binder; and its direct-image dependency
still imported the retired `UpperLowerStar.Iso`, causing a duplicate declaration.
The compiler also found two field-access tokens split after the dot; these and the
same formatting pattern in the main module were joined before the final checks.
These were repaired in the delivered modules. The proper-normalization theorem
uses the actual named mate, not an arbitrary `Nonempty` proper isomorphism. No
mathematical node statement was weakened or corrected. All dependency modules
were read against their owning nodes, and their data definitions contain no
`sorry`. All postponed theorem declarations match the existing owning DAG node
and have source/blueprint and natural-language proof docstrings.

Validation (2026-10-17 UTC): the prescribed `deliver2.py ... --no-push` finished
with `OK (dry run): commit e7b557b363 passes the preflight and compiles; nothing
pushed`. All five delivered Lean files were compiled separately through the
`scompile.py` wrapper, including server confirmation, with no error or unexpected
warning. This repair retry retained the saved Lean packet after that successful
dry run. The final self-check confirmed all five primary signatures verbatim,
explicit universe/variable binders, the 100-character line limit, only the allowed
node-field deltas, and the unchanged baseline `split_report`. The original
stage-1 return is repaired by the concrete stage-2 modules and records above;
this is not an unchanged re-push of the returned stage-1 head.
