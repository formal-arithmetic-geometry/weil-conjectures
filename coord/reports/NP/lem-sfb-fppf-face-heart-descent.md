## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.fppf_face_heart_descent` in
`Sheaf.AlgebraicGeometry.FppfFaceHeartDescent`. All theorem proofs are `sorry`.
All structures, categories, comparisons and predicates have real data. The item's
natural-language statement and accepted six-step proof are unchanged.

The source read is Stacks, spaces-simplicial.tex, the full statement and proof of
`lemma-descent-qcoh-for-fppf-hypercovering` (Tag 0DHD), and the item's agent-supplied
six-step face-only reconstruction. The source's all-simplicial result is not
mistaken for the face-only result. In particular, degeneracies are available in
`U` for pulling back the triangle equation, but are not module transitions.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`, and the algebraic space over it is
  `{X : AlgebraicSpace S}`. There is no separation, Noetherian, quasi-compactness,
  finite-type or coefficient-finiteness assumption.
- The augmented simplicial algebraic space is `U : SimplicialObject (Over X)`.
  `hU : IsSpaceFppfHypercover U` is the existing matching-arrow predicate. It
  quantifies every natural-number degree, including zero. Its matching limits
  are proper-face limits in the slice, and its `SpaceMapIsFppf` is chartwise
  flatness, local finite presentation and singleton joint surjectivity on
  field-valued point classes. It does not assume representability of a cover.
- `spaceFaceDiagram U` is literally
  `SemiSimplexCategory.toSimplexCategory.op ⋙ U`. Thus precisely the injective
  order maps index its transitions. `SpaceFaceModuleSystem U` is the ordinary
  systems presentation of the enlarged ringed total category after the recorded
  scheme-restriction equivalence, with actual module tensor pullbacks and their
  tensor-normalized identity and composition isomorphisms. Compatible component
  maps are `SpaceFaceModuleHom`. This is the module-category presentation in the
  total-category dependency, not an arbitrary category or collection of objects.
- `P : SpaceFaceAugmentationModel U` denotes that canonical augmentation in this
  presentation. Its existence for EVERY U, with no extra hypothesis, is stated
  by `space_face_total_augmentation` appended to the original dependency module. Its pullback's
  components are the existing `moduleTensorPullback q_n`; `P.transition` fixes
  their transition to canonical composition. Its direct image has the actual
  equalizer object of the two canonical vertex arrows, and `adjunction_zero`
  fixes the Hom bijection by the degree-zero projection and component module
  adjunction. Thus neither an arbitrary adjunction nor a freely chosen map is
  substituted for the ordinary ringed augmentation. The theorem works for every
  such normalized presentation. No choice of an uncharacterized object is made.
- `spaceFaceQCohProperty U` defines the full subcategory A: its first conjunct
  is `(M.obj n).IsQuasicoherent` for EVERY degree, and its second conjunct is
  `IsIso (M.transition a)` for EVERY injection, with identity/composition already
  part of the ambient system. Quasi-coherence is Mathlib's existing local
  presentation predicate through the recorded algebraic-space module category.
- The first conclusion says pullback takes every `N : X.QCoh` into A.
- The second conclusion says ordinary direct image takes every object of A
  into quasi-coherent modules. This includes its value in the ambient category.
- The third conclusion is exactly `IsIso (P.adjunction.unit.app N.obj)` for
  every quasi-coherent N. The fourth is exactly invertibility of the ACTUAL
  counit on every M in A. These are not merely unrelated object isomorphisms.
- The last conclusion provides `X.QCoh ≌ (spaceFaceQCohProperty U).FullSubcategory`.
  Its functor, after full-subcategory inclusion, is naturally isomorphic to
  the restriction of `P.pullback`; its inverse is similarly identified with
  the restriction of `P.direct`. These are the claimed tensor-pullback
  equivalence and ordinary-direct-image quasi-inverse. The preceding clauses
  additionally retain precisely the restricted adjunction unit and counit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its actual `Modules` and `structureSheaf`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: publicly retains the
  enlarged-site model, including `EnlargedEtaleSite`, `enlargedBaseChange`,
  `enlargedStructuralMap`, `smallEnlargedModuleRestriction` and
  `smallEnlargedModuleEquivalence`; no new ring map is chosen in this delivery.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  `SheafOfModules.isQuasicoherent` / `IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.SpaceFppfHypercover`: `SpaceMapIsFppf`,
  `IsSpaceFppfHypercover`. This already-landed definition node is added to the
  item's `stmt_deps`; no new definition node is created.
- `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`: the original
  `CategoryTheory.SemisimplicialRingedTotal.semisimplicial_ringed_total_category`,
  `Presentation` and `AugmentationPresentation` remain in their original module,
  with their original signatures and bodies. The specialized ordinary interface
  is appended to that same module, as described below.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`.
  `SpaceFlatDirectImageBaseChange.moduleTensorComposition` and
  `SpaceDerivedPullback.moduleTensorPullbackId` provide the normalized ordinary
  comparisons, not a second tensor construction.
- Proof imports: `AlgebraicSpaceModulePullbackQuasiCoherent`
  (`isQuasicoherent_moduleTensorPullback`), `AlgebraicSpaceFppfCoveringCalculus`
  (`IsFppfCover`, `isFppfCover_pullback`, `isFppfCover_comp`), and
  `ModulePullbackPushforwardAdjunction` (`module_pullback_pushforward_adjunction`).
  The proof dependency `lem-sfb-space-fppf-qcoh-descent` currently has no Lean
  module record, so there is no module to import for that proof-only prerequisite.
  Its mathematical use remains explicitly documented in the theorem docstring.

Edge cases checked before writing: degree zero uses the terminal matching object
in the slice; identity injections are included and have the canonical identity
transition; higher degrees impose every injection rather than just elementary
faces. Empty spaces and zero modules are allowed, and no nonempty-chart hypothesis
is added. No boundedness or flat-degeneracy condition appears. Sites may have
larger object universes than their ring and module carriers: the supporting repair
keeps the recorded QCoh coefficients in u instead of imposing u = u+1 or silently
lifting all modules. The direct image is defined for arbitrary systems before its
quasi-coherence is asserted on A.

Searches actually run:

- `msearch.py ... leanfinder` with query `Effective quasi-coherent module descent
  on algebraic spaces for fppf hypercovers using only injective face maps`:
  eight hits, all generic quasi-coherent presentation constructors/predicates;
  none states descent on this hypercover or identifies the ordinary direct image.
- `msearch.py ... loogle` with `Functor.IsEquivalence, Adjunction.unit,
  Adjunction.counit`: unavailable identifiers in that unqualified query, not
  evidence of no match. Repeated with `CategoryTheory.Functor.IsEquivalence`:
  twelve generic categorical equivalence declarations, no geometric descent.
- `msearch.py ... grep` with
  `fppf.*hypercover|hypercover.*fppf|face_heart_descent` in CategoryTheory:
  zero hits.
- `msearch.py ... grep` with
  `Semisimplicial.*[Mm]odule|[Ff]ppf.*[Dd]escent|[Hh]ypercover.*[Mm]odule`:
  one hit: `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean:177`,
  the theorem that fpqc descent implies fppf descent. It does not state module
  descent on this algebraic-space face total category.
- `rg` in `lean/WeilConjectures` for the item id and proposed declaration names:
  no occurrence. Broader `fppf.*[Dd]escent` finds scheme/Hilbert material, not this
  algebraic-space face-only heart theorem.
- `rg` in `lean/Sheaf` finds `SpaceFppfHypercover`, `SpaceDerivedSystem`,
  `SpaceNegativeExtHyperdescent`, and `HypercoverAugmentationFaceProperty`.
  Their full relevant declarations were read: none states this heart theorem.
  The first is reused; derived hyperdescent is downstream and is not imported.

## Dependency modules

The return's H13 is repaired by appending the twelve `SpaceFace*` declarations
(including `space_face_total_augmentation`) to the sandbox copy of
`Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`. The original source
is retained verbatim, with three public imports added and the specialized
helper block appended after the original namespace ends. The abandoned
`SpaceFaceModuleSystems.lean` file is removed from this delivery.
`FppfFaceHeartDescent.lean` imports the original generic module directly.

The dependency node's entire live record is retained except for the expressly
permitted additions to `lean.declarations` and `lean.note`. In particular
`lean.module`, `lean.file`, `lean.declaration`, `lean.statement`, `by`, `date`,
`existing`, `branch` and `fixed_by` retain their live values. The main theorem is
still `CategoryTheory.SemisimplicialRingedTotal.semisimplicial_ringed_total_category`
with its generic coherent-site signature. The specialized existence theorem
`AlgebraicGeometry.AlgebraicSpace.space_face_total_augmentation` is an additional
recorded declaration of this same DAG node, with its existing source and complete
proof docstring; it does not replace the node's main declaration or statement.
The original generic theorem and all its consumers retain the same interface.
No changes are made to `reviewed_lean` or any of the fifteen citing nodes.

The small-coefficient presentation is needed because the generic `Site` has
one universe for site objects, rings and modules, whereas the enlarged
algebraic-space site has objects in u+1 and structure/module sections in u.
The appended ordinary systems presentation uses the existing normalized
`smallEnlargedModuleEquivalence`, actual `moduleTensorPullback`, and the
canonical tensor identity/composition comparisons. Its ordinary augmentation
is fixed by the actual degree-zero/degree-one equalizer and normalized Hom
bijection. The additional existence theorem is the ordinary augmentation
clause specialized to algebraic spaces, without a hypercover assumption.
Its DAG owner is `lem-sfb-semisimplicial-ringed-total-category` throughout.

## Returned delivery repair

Return at immutable head `a4f3d66573fb`, H13: the earlier delivery rebound the
generic dependency's main record to the algebraic-space specialization. That
was incorrect even though its old declarations remained imported. The repair
uses the return's explicit alternative of appending helpers to the original
module and changing only the declarations list and note. A structural comparison
with the live node verifies that every other `lean` key is identical; every
non-`lean` field is copied unchanged. Comparison with the returned sandbox
confirms that the substantive changes are the dependency record restoration,
helper relocation, removal of the old helper module and updated item import.
The item theorem's signature and mathematical statement are unchanged, matching
the review's clause-by-clause acceptance. All theorem proofs remain `sorry`;
all definition and structure data remain explicit. No new nodes or statement
corrections are introduced.

The latest blueprint unit direct-images proof was read during the original
work: the face-only descent node is an inherited supporting prerequisite, not
the unit statement, and the unit is unchanged. Compile and preflight results
for this repair are recorded below after the prescribed checks.

Repair validation: both delivered modules compiled cleanly, separately in
dependency order through `scompile.py`, including sandbox and library forms.
The modified generic module took 18.8 seconds and the item library form 2.9
seconds. A structural comparison confirms exactly `declarations` and `note`
changed in the dependency Lean record and no other node fields changed.
The original generic source remains verbatim apart from the added imports
and appended helper block.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
