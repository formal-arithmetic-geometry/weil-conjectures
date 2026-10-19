## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` states the three
clauses of the node: exact module inverse image, abelian sheaf detection, and
unbounded derived zero-object/isomorphism detection. All three theorems have sorry
proofs, their source, and complete natural-language proof plans. Definitions contain
real data; exactness instances are projections of the named exactness theorem.

Hypothesis and clause correspondence:

- The scheme is `X : Scheme.{u}`. Noetherian is exactly
  `[IsLocallyNoetherian X] [CompactSpace X]`.
- `S : LocallyClosedStratification X` retains its finite indices `Fin S.n`,
  actual schemes `S.domain a`, immersion maps `S.immersion a`, immersion property,
  and disjoint locally closed covering of the underlying space.
- Every stratum has `V a : Scheme.Cover.{w} proetalePrecoverage (S.domain a)`.
  These are precisely fpqc weakly-etale covers. Their domains and arrows are
  `(V a).X j` and `(V a).f j`. The index universe `w` is arbitrary, with no
  finiteness restriction on covers.
- `F : Sheaf (ProEt.topology X) AddCommGrpCat.{u+1}` is an arbitrary abelian
  sheaf. `hF` asserts `IsZero` after canonical inverse image for EVERY `a,j`,
  and the conclusion is `IsZero F`. Restriction along the composite
  `(V a).f j ≫ S.immersion a` is canonically the successive inverse images
  by composition of the defining adjunctions; this is explained in the proof.
- `R : Sheaf (ProEt.topology X) RingCat.{u+1}` covers every ring sheaf,
  including noncommutative ones. No constant, finite or nonzero assumption is added.
- `proEtaleRingModuleInverseImage_exact` states additivity and preservation of
  finite limits and finite colimits for module inverse image over its ACTUAL
  inverse-image ring. The named instances use its three projections.
- Module categories are `ringedSiteModules.{u+1} R`, transparently the recorded
  Mathlib `SheafOfModules`. The helper localization instance uses exactly
  `HasDerivedCategory.standard`, the ordinary unbounded derived category.
  `proEtaleAllRingDerivedInverseImage` is precisely the exact canonical functor's
  `mapDerivedCategory`, so it is termwise inverse image and triangulated.
- The first conjunct of `proEtale_derived_stratum_cover_detection` quantifies over
  EVERY derived object `K` and asserts that zero on every chosen restriction
  implies `IsZero K`. The second quantifies over EVERY pair `K,L` and derived
  morphism `f`, and asserts that `IsIso` on every chosen restriction implies
  `IsIso f`. No representative, boundedness or constructibility restriction occurs.
  Converse preservation is automatic for additive functors and all functors,
  respectively, as described in the docstring.

Recorded dependencies read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through the former).
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.LocallyClosedStratification` and its fields.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the existing small site,
  coefficient and derived-localization convention (reexported by inverse image).
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleSheafAdjunction`, `proEtaleSiteModel`, `proEtaleModelTopology`,
  `proEtaleModelBaseChange`, `proEtaleModuleToModel`, `proEtaleModuleFromModel`
  (all in `AlgebraicGeometry.Scheme`).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory.standard`; `ExactFunctor`: `Functor.mapDerivedCategory`.
- Mathlib `proetalePrecoverage`, `Scheme.Cover`, `SheafOfModules.pullback`, and
  the actual ring-sheaf inverse-image adjunction unit are reused.

Stated proof dependencies are imported without public: site-pullback exactness,
weakly-etale localization, pullback stratification, and derived homology sequences.
The Mathlib closed-immersion, Noetherian-open, exact-derived-functor, and triangulated
Hom-exactness interfaces are in the import closure. The unstated
`lem-exc-open-closed-detection` is only a proof dependency, not required to TYPE this
statement. The full finite-stratum induction, cover detection, cohomology argument,
and distinguished-triangle argument are recorded in the theorem docstrings.

Edge cases checked: the empty scheme, zero strata, empty and nonreduced strata,
empty covers of empty strata, infinite cover indices, zero sheaf, zero ring,
arbitrary characteristic, noncommutative rings, unbounded complexes, and arbitrary
derived morphisms. Original site object universe u+1 and Hom universe u remain;
only the existing AsSmall transport equalizes sizes internally for the module API.
No hypothesis, clause, or node statement has been changed. No statement dispute.

Searches: msearch LeanFinder “Finite locally closed stratification detects zero
pro etale abelian sheaves and derived modules” returned eight unrelated etale,
formal-etale, and topology declarations. Loogle `Sheaf, IsConservative` returned
zero hits (unknown Sheaf). Mathlib grep
`stratif.*(detect|conserv)|proetale.*(detect|conserv)` returned zero hits. The same
regex in upstream WeilConjectures and project Sheaf returned only an unrelated
constructibility docstring; the item id upstream had no hits. Loogle
`SheafOfModules.pullback` returned the existing pullback, adjunction, and composition
interfaces, which are reused. LeanFinder for canonical module inverse image over a noncommutative pro-etale ring
sheaf returned eight scheme/module, differential, and slice-module candidates, none
a matching pro-etale RingCat inverse-image interface. Direct searches of every
new name in upstream, project, and dag/lean_names_upstream.json found no duplicates.
The existing `ProEtaleOperations` source and its node were inspected: its rings
are commutative and it uses a specified coefficient identification and extension
of scalars; it cannot state this node's noncommutative case. The previously recorded
wait on that node is resolved; the necessary RingCat interface is repaired here.

Validation: both delivered modules compiled separately through scompile.py in
canonical library positions and sandbox positions, with no errors or warnings.
The delivery dry run is performed after writing these records.

## Dependency modules

`def-weil-proetale-inverse-image`: its recorded module inverse image requires
CommRingCat, whereas the dependency explicitly allows noncommutative rings and
this item's conclusion quantifies over every ring sheaf. The repair module
`Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage` publicly reexports the entire
recorded module, adds `proEtaleRingModelUnit` from the ACTUAL RingCat adjunction
unit, and constructs `proEtaleRingModuleInverseImage` using the existing small-model
transport, Mathlib `SheafOfModules.pullback`, and transport back. Thus the inverse
image is the canonical sheafified module Kan extension over the inverse-image
ring, with real data and no new site or freely chosen functor. The two new helpers
carry the dependency's source and blueprint docstrings. The dependency changes
only in lean, with a note explaining the unusable specialization; its original
commutative declarations remain publicly imported. The lean.declarations list names
only the two additions owned by this module; original names stay in the imported source. No independent
new notion or new node is introduced.

## Second reading by NF

Independent reading of the node, both delivered modules, all seven statement-dependency
records, and their source signatures. The source places were read directly in
proetale.tex: lemma-ses-associated-to-open (09AH) requires a quasi-compact open
complement, and lemma-thickening (09AB) concerns integral universally injective
surjections. The finite-stratum argument is correctly identified as an agent consequence,
not the literal assertion of either tag. No reduced-stratum replacement is made.

Object/hypothesis/conclusion checklist, in the order of the informal statement:

1. Arbitrary scheme X: `X : Scheme.{u}`. Pass; no field, characteristic, separation,
   dimension or nonemptiness condition.
2. Noetherian = locally Noetherian and quasi-compact:
   `[IsLocallyNoetherian X] [CompactSpace X]`. Pass. Mathlib's `IsNoetherian`
   extends exactly these two classes; CompactSpace imposes no Hausdorff condition.
3. Finite stratification with actual immersed schemes: `S : LocallyClosedStratification X`,
   `Fin S.n`, `S.domain a`, `S.immersion a`. Read its structure fields: locally closed,
   pairwise disjoint, union all points, immersion property, and range equality. Pass.
   A nuance missed by the worker report: the CURRENT upstream `Topology.Stratification`
   also has `isConstructible_stratum`. I checked the live source with
   `scompile.py --source WeilConjectures.Topology.Stratification`. This does not add
   a hypothesis in THIS Noetherian statement: `IsNoetherian.noetherianSpace` and
   `IsLocallyClosed.isConstructible_of_noetherianSpace` supply that property for every
   locally closed stratum. `Topology.Stratification.ofNoetherianSpace` explicitly
   constructs the parent structure from just the node's partition data. The earlier
   dependency docstring's description is stale in general, but no cases here are lost.
4. A chosen pro-etale cover on every stratum:
   `V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a)`. Pass;
   arrows `(V a).f j` and indices `(V a).I₀` are the actual fpqc weakly-etale family.
   Arbitrary index universe w, no finite-cover assumption.
5. Every abelian sheaf: `F : Sheaf (ProEt.topology X) AddCommGrpCat.{u+1}`. Pass;
   this is the recorded small site and the standard larger coefficient universe.
6. Vanishing of every successive stratum/cover inverse image: `hF` quantifies
   `∀ a j` and uses `proEtaleSheafInverseImage ((V a).f j ≫ S.immersion a)`.
   Pass; composite and successive inverse images are canonically isomorphic by
   composition of the specified adjunctions. IsZero is invariant under that isomorphism.
7. Conclusion F = 0: `IsZero F`. Pass; zero-object property, not literal equality
   with a chosen zero sheaf.
8. Every ring sheaf: `R : Sheaf (ProEt.topology X) RingCat.{u+1}`. Pass, including
   noncommutative rings. The CommRingCat-only older module inverse image is unusable
   here, so I checked the delivered dependency repair against its full node.
9. Exact termwise inverse images over the actual inverse-image ring:
   `proEtaleRingModuleInverseImage_exact` gives Additive, PreservesFiniteLimits and
   PreservesFiniteColimits. Its three instances only project those properties.
   `proEtaleAllRingDerivedInverseImage` is its `mapDerivedCategory`, using the ordinary
   `HasDerivedCategory.standard` localization. Pass; no extra flatness, coefficient
   identification, or arbitrary map is assumed.
10. Joint zero detection in unbounded D(Mod(R)): the first conjunct of
    `proEtale_derived_stratum_cover_detection` quantifies every K in
    `DerivedCategory (ringedSiteModules.{u+1} R)` and concludes IsZero K from all
    restricted objects being zero. Pass; no boundedness or constructibility restriction.
11. Joint isomorphism detection: its second conjunct quantifies every K, L and
    `f : K ⟶ L`, and concludes IsIso f from IsIso of every restricted map. Pass.
    Converse preservation follows from the exact/additive functor and ordinary functor
    interfaces; no additional assertion is required to express joint detection.

Dependency repair reading: `proEtaleRingModelUnit` is the actual RingCat sheaf
adjunction unit whiskered by AsSmall.down, not a freely chosen ring morphism.
`proEtaleRingModuleInverseImage` is transport to the existing model, Mathlib
`SheafOfModules.pullback` along that unit, and transport back. I read Mathlib
PullbackContinuous: the pullback is the specified pushforward's left adjoint, with
`pullbackIso` identifying it with presheaf pullback followed by sheafification.
Presheaf.Pullback constructs its adjoint from free Yoneda modules and cokernels;
no existence-only sorry or unconstrained functor enters the data. This is the canonical
inverse image over f^{-1}R for arbitrary rings, consistent with Tags 03D2 and 04JC.
The repair publicly imports the complete old dependency interface. Its JSON changes
only lean, with an explanatory note. There are no new nodes to audit.

Edge cases: n=0 and empty cover indices remain allowed (then the covering and partition
axioms force the relevant schemes empty); zero objects and zero rings are allowed;
nonreduced/empty strata retain their actual immersion data; cover indices may be
infinite. All integer cohomological degrees and all derived morphisms are included.
Universe u is bound, cover-index universe w is bound, and coefficient size u+1 agrees
with the recorded site convention. AsSmall enlarges only the internal morphism universe;
it does not restrict the schemes or equate the original site universes.

Independent searches used different wording: msearch LeanFinder, "Joint conservativity
of restriction to finite locally closed pieces for unbounded derived sheaves", returned
8 results about derived t-structures and coherent sites, none the assertion. msearch
Loogle `SheafOfModules.pullback` returned 12 existing canonical pullback/adjunction/
composition interfaces, which the dependency repair reuses. Direct rg over Mathlib,
upstream WeilConjectures, and project lean/Sheaf searched
`stratif.*(vanish|zero|conserv)|((jointly|joint).*conserv)|proetale.*detect`.
I opened the relevant upstream hits: UpperLowerStar.Detection states section/morphism
vanishing for fixed-ring module-valued sheaves along finite quasi-compact surjective
families; OpenImmersion.Conservative states covering detection for localization
restrictions. Neither states this node's arbitrary abelian sheaf and arbitrary ring-sheaf
unbounded derived conclusions. Exact new-name searches in upstream, project and
lean_names_upstream.json had no matches. There is no exact existing declaration to
record in place of this delivery.

No mathematical mismatch requiring a Lean or node change was found. The only correction
is this report's clarification of inherited constructibility. All three theorem proofs
remain sorry; instances merely expose named theorem projections, and all definitions
have real data. Source/blueprint docstrings and the seven proof steps (composition,
covering detection, finite-stratum induction, open/closed detection, exactness, derived
zero detection, and triangles/Hom exactness) were checked against the node. Both modules
were compiled separately in one scompile.py invocation, including sibling overlay,
sandbox and canonical library positions: clean, no errors or warnings. The primary
lean.statement strings agree verbatim with the signatures in their respective files.
