## Worker report

Stage 2, N0, lem-trf-ringed-tor-amplitude-stalk-test. The resumed dispatch explicitly
assigns stage 2. The live stage-1 split is reviewed (2026-10-23, Q108), has no Lean
record and no released repair note. I preserved its statement, proof, dependencies
and review metadata. No interrupted compile or delivery remained active. The
launcher's WEIL_SANDBOX environment points to the stage-2 sandbox; the files are
there. Initially the sandbox had only launcher markers.

Files: the item node (only lean added), and
lean/Sheaf/Algebra/Homology/RingedTorAmplitudeStalkTest.lean. No new DAG nodes,
no dependency repairs, no statement correction, and no Mathlib leaves.

Three statements, all with sorry proofs, render all clauses of the item:

- AlgebraicGeometry.RingedSpace.torAmplitude_iff_stalks renders (1) iff (2).
  Z : RingedSpace is arbitrary; K : CochainComplex (Modules Z) integers is unbounded.
  The endpoints a,b and hab render ordered integer bounds. The left side tests
  every module sheaf F and every i outside [a,b], using the recorded
  CochainComplex.sheafDerivedTensorVanishes Z.sheaf K F i. The right side tests
  every point z, every module L over the actual stalk ring, and every such degree.
  It is IsZero of homology of Q of the actual termwise module stalk complex,
  derived-tensored with the derived single functor at degree zero applied to L.
  The HasDerivedCategory family is the choice of unbounded localizations needed
  to express the right side; these exist and are not geometric hypotheses. Its
  hom universe v is independent of u. No scheme, local-ring, boundedness,
  quasi-coherence or compactness assumption is imposed.
- AlgebraicGeometry.RingedSpace.locallyFiniteTorAmplitude_iff_uniform renders
  (3) iff (4). CompactSpace Z is precisely quasi-compactness without a separation
  axiom. Each point has an open W containing it and integers a<=b. On W the same
  vanishing predicate tests all module sheaves on the localized site, with ring
  Z.sheaf.over W and the actual termwise image of K under
  SheafOfModules.overFunctor (moduleRings Z) W. Opens of the subspace W are
  equivalent to the slice category of opens V -> W, so this is ordinary restriction
  to W. The right side asks for one ordered integer pair and all global test
  sheaves. This does not replace neighbourhood bounds by merely pointwise bounds.
- AlgebraicGeometry.RingedSpace.torAmplitude_zero_zero_of_isEmpty states the
  explicit final empty-space clause: every test sheaf has vanishing derived tensor
  with K outside [0,0]. IsEmpty Z is the only extra hypothesis in this statement;
  quasi-compactness is automatic and not needed as a binder.

Dependency declarations read:

- Sheaf.CategoryTheory.RingedSiteModules, CategoryTheory.ringedSiteModules:
  Modules Z from the recorded ModuleStalkFunctor module is the existing ringed-space
  specialization of this same SheafOfModules category, not a new definition.
- Mathlib.Algebra.Homology.DerivedCategory.Basic, DerivedCategory, Q and the
  existing singleFunctor supply the unbounded localization and degree-zero module.
  The published module-derived monoidal structure comes through
  WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory and
  WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution.
- Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes,
  CochainComplex.sheafDerivedTensorVanishes is used verbatim. It requires an actual
  quasi-isomorphism from a K-flat complex and vanishing of the total-tensor
  homology; it is not a conditional predicate on a hypothetically given resolution.
- WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat,
  CategoryTheory.MorphismProperty.kFlat is the existing module K-flat predicate
  in the imported derived tensor machinery. There is no new K-flat definition.
- WeilConjectures.Algebra.Homology.ModuleStalkFunctor,
  AlgebraicGeometry.RingedSpace.moduleStalkFunctor gives the actual termwise stalk
  and its zero-morphism-preservation instance.
- Proof-only modules are imported without public: KFlatResolutionIndependentCoefficients
  (CochainComplex.exists_isKFlatResolutionIndependentCoefficients), ModuleStalkExact
  (AlgebraicGeometry.RingedSpace.module_stalk_exact), StalkKFlatTensorHomology
  (stalk_kFlat_tensor_homology_iso), RingedModuleSkyscraper
  (SheafOfModules.ringedModuleSkyscraperFunctor), and SkyscraperComplexStalk
  (SheafOfModules.skyscraper_complex_stalk_recovery). Their statements and
  docstrings were read. The theorem docstrings carry all six accepted proof steps
  and their cited node ids. No additional comparison theorem has been postulated.

Sources read: Stacks cohomology.tex Tag 09U9, label lemma-tor-amplitude-stalk,
including its tensor and cohomology stalk comparisons; Tag 06YB, label
lemma-check-K-flat-stalks, including the skyscraper argument; the item's entire
accepted statement and proof; the chapter and unit records. The latest blueprint
is main-20261023-1620. This auxiliary input changes no chapter or unit route.

Edge cases checked in the signatures: empty space (no Nonempty assumption, with a
separate [0,0] clause); nonclosed points (arbitrary z); zero rings and zero sheaves
(no nontriviality assumptions); a=b; arbitrary unbounded complexes and arbitrary
coefficient modules; non-scheme ringed spaces; quasi-compact non-Hausdorff spaces.
The open encoding includes the top and empty opens. Only the second theorem uses
compactness. No local-ring or quasi-separatedness requirement is present anywhere.

Existing declaration searches: rg on lean/WeilConjectures and lean/Sheaf for the
blueprint id, all proposed names, torAmplitude, tor_amplitude and Tor/stalk phrases
found no exact arbitrary-ringed-space statement. The existing
AlgebraicGeometry.torAmplitude_of_open_neighbourhoods is scheme-only; etale and
pro-etale results concern different coefficient categories. I read the full
blueprint_refs.py search for “tor amplitude”. Mathlib searches actually run:

- `leanfinder`: A complex on an arbitrary ringed space has Tor amplitude in an interval if and only if all its stalk complexes have that Tor amplitude — 8 hits: DerivedCategory.isGE_Q_obj_iff, DerivedCategory.isLE_Q_obj_iff, DerivedCategory.isGE_iff, DerivedCategory.isLE_iff, DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, DerivedCategory.IsGE, DerivedCategory.instIsGEObjCochainComplexIntQOfIsGE, DerivedCategory.instIsLEObjCochainComplexIntQOfIsLE
- `loogle`: DerivedCategory, "torAmplitude" — 0 hits: 
- `leansearch`: Locally finite Tor amplitude on a quasi compact ringed space has uniform finite bounds — 8 hits: RingHom.QuasiFinite.propertyIsLocal, SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation, CategoryTheory.HasExt.instHasSmallLocalizedShiftedHomHomologicalComplexIntUpQuasiIsoOfIsGEOfIsLEOfNat, RingHom.QuasiFinite.of_finite, AlgebraicGeometry.instHasRingHomPropertyLocallyQuasiFiniteQuasiFinite, RingHom.QuasiFinite, SheafOfModules.IsFiniteType.mk, RingHom.QuasiFinite.holdsForLocalizationAway
- `grep`: torAmplitude|tor_amplitude|tor.amplitude — 0 hits: 

LeanFinder's results concern cohomological support of K rather than support after
tensoring with all modules. LeanSearch returned quasi-finite ring maps, local finite
presentation and Ext size bounds. Loogle and grep had no Tor-amplitude hits.
These do not give a matching existing statement. No search was fabricated.

Validation: scompile.py compiled the single file on the server in both sandbox and
library contexts, each under the 60-second limit, with no errors or warnings.
All three theorem bodies are exactly sorry. Every line is at most 100 characters.
The node's lean.statement quotes the first signature verbatim. The other two full
names are listed in lean.declarations. Delivery preflight follows.

## Review by N0

I reread all three Lean signatures against the accepted node after the clean
compilation. The first has exactly the two universally quantified tensor tests,
the correct interval endpoints, and the actual module stalk functor. The second
uses the actual restricted ring and complex; it requires z in W and ordered bounds
inside the appropriate existentials. CompactSpace supplies no separation axiom.
The third gives exactly [0,0] for the empty space. I checked the exactness and
K-flat tensor comparison statements in the proof imports for arbitrary ringed
spaces and no boundedness hypotheses. Skyscraper recovery applies at a point
without closedness. The docstrings retain the six proof arguments, including the
explicit germ identification and finite-subcover min/max argument. No mismatch
requiring correction was found; nothing in the accepted natural-language split
was changed. This is worker self-review; the maintainer's direct-delivery review
is the independent reading.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
