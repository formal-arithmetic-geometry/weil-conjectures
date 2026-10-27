## Worker report

Stage 2, Q106: `Sheaf.AlgebraicGeometry.BlowupSequenceInsertion` states
`AlgebraicGeometry.ordinaryBlowupSequence_insertion`, with one `sorry`, and no proofs.
The prerequisite `BlowupSequenceInsertionData` has real structures/definitions only.
The accepted stage-1 split is preserved. The inherited BLOCKED ending concerned a
stage-1 re-split; brief-stage2 §0 expressly distinguishes that from this stage-2 task.
No statement correction, dependency-record repair, or disputed statement is required.

Source read: Temkin, https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf,
arXiv:0904.1592v2, §§2.2.3, 2.2.5, 2.2.8, 4.1.3, 4.2.1--4.2.4, Definition 4.2.2,
Lemmas 4.2.1, 4.2.3, 4.2.5, printed pp.28--29. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md`
was read; this item is a tool within its existing codimension-resolution branch.

Hypotheses and clauses, in order:

- Finite ordinary tower with ordered coherent ideals: `Input.old` uses the existing
  `OrdinaryBlowupTower`; `Input.noetherian` is `∀ i, IsNoetherian (old.level i)` and
  `Input.coherent` uses `RingedSpace.IsCoherent` on each ideal's existing `toModules`.
  Mathlib's `IsNoetherian` extends locally Noetherian and compact, exactly as the node.
- Position `0≤m≤n`: `Input.position : Fin (old.length+1)` includes both endpoints.
- Preserved open: `Input.preserved : X.Opens`.
- Closure hypothesis for every old suffix center: `Input.closure` quantifies over
  all indices with `position.val ≤ i.val`, equating the actual ideal to the kernel of
  the restricted center's map to its ambient scheme. This retains nilpotents.
- Inserted finite ordinary tower: `Input.inserted`, its Noetherian/coherence fields,
  and `Input.supported`, evaluated on every point of each center, express precisely
  support in the complement of the inverse image of U.
- Existence: `∃ D : Diagram P`. The new tower is encoded by its three consecutive
  segments: the original prefix through m, the specified inserted tower, and
  `D.suffix`. The first two are fixed input, so are literally kept. `D.length_eq`
  makes the suffix length n−m. This segmented representation requires no separate
  concatenation definition or theorem, and covers every stage of the whole tower.
- Successive closure prescription: `Diagram.center_eq` is the kernel of the actual
  map from the restricted old center, transported by `openIso`, into the new level.
  `Diagram.noetherian` and `.coherent` retain the ambient and center conditions.
- Restriction over U: `Diagram.openIso`, `.over`, `.oldOpenMap_fac` and `.naturality`
  compare every old suffix level and transition to the new ones over U. `oldOpenMap`
  is the canonical restriction, uniquely determined by its factorization through an
  open immersion. Inserted centers have empty restriction by `Input.supported`.
  During preparation an overly strong draft used global maps to old ambient levels;
  this was removed. The delivered statement compares them ONLY on the preserved open,
  as Temkin Definition 4.2.2 prescribes.
- Uniqueness up to canonical stagewise isomorphisms: for EVERY other diagram E,
  `Nonempty (SuffixIso D E) ∧ Subsingleton (SuffixIso D E)`; `.over`, `.naturality`
  and `.ideal` retain the fixed terminal base, all transitions and ordered ideals.
- First old center after insertion, only m<n: the guarded clause identifies
  `D.firstNew h` with `P.transform h (Fin.last P.inserted.length)` as ideal sheaves.
  `firstNew` transports through the suffix initial isomorphism; `transform` uses
  the recorded `strictTransformMap` and its kernel, so it is the closed image
  in the ambient scheme of the scheme-theoretic strict transform relative to U.
  By the original schematic-density assumption this equals the successive usual
  strict transforms through G (the node's step 4, documented in the theorem).
- If G blows up subschemes of the old center and successive transforms:
  `∀ i, P.transform h i.castSucc ≤ P.inserted.center i` expresses the closed
  inclusion (ideal order is reversed). The consequent produces `CenterTower P h`:
  its transitions blow up the pulled-back center, its embeddings have exactly the
  transform ideals, and its initial embedding is C_m. The terminal isomorphism
  identifies the first new center with this iterated blowup. The subsequent
  isomorphisms over the ambient levels identify the pulled-back centers with the
  given subschemes, so the theorem concerns the stated centers, not arbitrary ones.
- Reduced old centers: each `IsReduced oldCenter.subscheme` implies
  `IsReduced newCenter.subscheme`. It is stated centerwise and does not require
  reduced ambient schemes.
- Pure image codimension and generic schematic density: `PureImageCodimension`
  uses local `ringKrullDim` at each generic image point; `DenseAboveGenericImage`
  says a section whose germs at every point above those generic points vanish is
  zero, on every open. These are restrictions to the induced local schemes and
  keep nilpotent information. The consequent gives equality of the two actual
  ranges in X, the same codimension e, and the same schematic-density property.
- Flat base change between Noetherian schemes: for every Y, `[IsNoetherian Y]`,
  f and `[Flat f]`, a pulled-back input Q exists (`InputPullback`). For EVERY such
  comparison and EVERY diagram E on Q, `TowerPullback b.terminalMap D.suffix E.suffix`
  exists. Its cartesian squares, naturality and ideal equalities compare exactly
  the prescribed base-changed construction. The prefix and inserted comparisons
  are already in `InputPullback`. All lengths are equal and every stage is kept;
  there is no nonemptiness condition or contraction of empty centers.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `.blowupMap`;
  these are the blowups within `OrdinaryBlowupTower`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the recorded coherence
  interface; `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `.toModules`.
- `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`; `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.Hom.image`, `imageι`; Basic: `Scheme.Hom.ker`, `ker_apply`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, `Flat.iff_flat_stalkMap`.
- The landed `def-trf-ordinary-resolution-rule` module
  `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `OrdinaryBlowupTower`, `.toBase`.
  Added its node to stmt_deps under the landed-node rule; no duplicate tower notion.
- Proof imports expose the complement theorem (`WeilConjectures.Blowup.Complement`),
  properness (`WeilConjectures.Blowup.Proper`, Mathlib Proper), Noetherian finite-type
  permanence (Mathlib Noetherian, public via the data module), scheme-image flat
  base change (`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`:
  `Scheme.Hom.ker_pullback_snd`, `.image.pullbackIso`), blowup flat base change
  (`WeilConjectures.Blowup.FlatBaseChange`: `.blowupFlatBaseChangeIso`, read from
  the closed slopmaster2 audit although that node lacks a lean record), ambient
  strict transforms (`WeilConjectures.Compactification.StrictTransformBlowup`:
  `.exists_isClosedImmersion_blowup_comap`), density (`WeilConjectures.Blowup.Density`:
  `IsAdmissible.isSchemeTheoreticallyDominant_preimage_ι`), and reduced images
  (`Sheaf.TraceFormula.ReducedSchemeImage`: `schemeTheoreticImage_reduced`).

Edge cases checked before and while writing: n=0 and m=n leave an empty suffix;
no `Fin 0` center is accessed because the first-center clause requires m<n.
A length-zero insertion identifies the first new center with the original closure.
U=X forces all inserted centers empty and keeps every identity stage. U empty
forces old suffix centers empty by the kernel closure condition, but imposes no
restriction on inserted centers. Empty schemes, empty flat fibers, center equal
to an entire transform, nonreduced ambient schemes, and empty image generic sets
are included. A whole-center blowup can remove that transform; `CenterTower` allows
empty levels. Flat pullback is not asserted to preserve reducedness. No separation,
characteristic, regularity, nonempty-center, or nowhere-density hypothesis was added.
All scheme and index universes are explicitly bound and autoImplicit is disabled.

Searches: msearch.py LeanFinder query "Insert a finite ordinary blowup tower into
another by schematic closure of centers" returned finite-morphism/composition and
approximation hits, no insertion interface. LeanSearch query "Canonical insertion
of blowup sequences with schematic closure centers and flat base change" returned
flatness/regular-sequence results, no match. Loogle `"blowup"` returned zero hits;
msearch grep `blow.?up.*(tower|sequence|insert)|strictTransform` in AlgebraicGeometry
returned zero Mathlib hits. The authentic JSON responses are in the new definition
node. `rg` on project Sheaf and WeilConjectures located the ordinary tower definition
and strict-transform APIs above, no insertion theorem or data; exact item-id grep
in WeilConjectures had no hits. `blueprint_refs.py search 'blowup sequence insertion'`
returned zero blueprint nodes; DAG searches found no existing insertion-data node.

Validation: both delivered modules compiled individually in dependency order with
scompile.py under the default 60-second limit, no errors or warnings (the theorem's
expected sorry warning is permitted). No local/global build or repository writes.

## New nodes

`def-per-blowup-sequence-insertion-data` defines the missing insertion input, segmented
closure diagram, canonical stagewise isomorphism and uncontracted ideal-level
pullback comparisons, with the center-transform and image-density predicates needed
by this combined assertion. Source: Temkin §§2.2.3--2.2.8, 4.1.3 and 4.2.1--4.2.4.
The searches above found the underlying ordinary tower and single-blowup operations,
which are reused, but no insertion/comparison package. The new node lists all its
helper declarations, cites the existing notion nodes, and has no postponed theorem.

Dry-run repair: the live preflight requires `import_flags` on a new node although
the standing §5 field list omits it; supplied the empty list and expanded the grouped
source citations to individual `[id]` references. No mathematical field was altered.

Final notion search: Mathlib `Topology.Sober.genericPoints` already defines generic
points of a space. `genericImagePoints f` specializes that existing definition to
the subspace `Set.range f` and maps it into X; it does not redefine generic points.
The other codimension search hits concern regular immersions, a different condition.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
