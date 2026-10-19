## Worker report

The module `lean/Sheaf/CategoryTheory/FrameSourceKanFibration.lean` states
`CategoryTheory.frame_source_kan_fibration` with proof `sorry`.  It uses the landed
`CosimplicialFrame`, `frameHom`, `frameHomPre`, and `frameHomPost` interfaces.  The
small helper `constNat` is the canonical constant natural transformation induced by a
map of base objects, and `AugmentedFrameMap` records a map of frames commuting with
augmentations and with the specified degree-zero identifications.  No definition uses
` sorry ` data and no new DAG node or dependency repair was needed.

The theorem renders the node clause by clause as follows.

- `C : Type u` with `Category`, `HasLimits`, `HasColimits`, `ModelCategory`, and the two
  functorial factorization hypotheses is the arbitrary model category with functorial
  factorizations.  The binders `A B`, `FA`, and `FB` are cofibrant objects and their
  cosimplicial frames; cofibrancy, objectwise weak equivalence of the augmentations,
  latching cofibrations, and degree-zero identities are exactly the recorded
  `CosimplicialFrame` fields.
- `uFrame : FA.obj ⟶ FB.obj` and `uBase : A ⟶ B` are the cosimplicial map and its
  degree-zero map.  `hAug` is the commuting augmentation square, using `constNat`; `hZero`
  is the explicit equation identifying the degree-zero component with `uBase`.
- `hReedy` is `HomotopicalAlgebra.Reedy.leftClass
  (monomorphisms SimplexCategory) (cofibrations C) uFrame`, i.e. every relative
  latching map of the map of cosimplicial objects is a model cofibration, the stated
  Reedy-cofibration condition for the simplex Reedy structure.
- For every `Y : C` with `IsFibrant Y`, the conjunction states that both
  `frameHom FA.obj Y` and `frameHom FB.obj Y` are Kan complexes and that restriction
  `frameHomPre uFrame Y` has the Kan lifting property
  `SSet.modelCategoryQuillen.J.rlp`, exactly the claimed Kan fibration.
- The final universal clause quantifies a second augmented pair, maps `a` and `b` of
  frames, their base maps, the two `AugmentedFrameMap` compatibility records, and the
  commuting pair equation `hPair`.  For maps between fibrant targets `g : Y ⟶ Y'`, with
  both `hY` and `hY'`, it gives the pair-map square
  `frameHomPre uFrame' Y ≫ frameHomPre a Y =
  frameHomPre b Y ≫ frameHomPre uFrame Y` and the target-map square
  `frameHomPre uFrame Y ≫ frameHomPost FA.obj g =
  frameHomPost FB.obj g ≫ frameHomPre uFrame Y'`.  These are the asserted naturality in
  augmented-pair maps and in fibrant targets.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CosimplicialFrameMapping`: `CategoryTheory.CosimplicialFrame`,
  `CategoryTheory.frameHom`, `CategoryTheory.frameHomPre`, and
  `CategoryTheory.frameHomPost`; I read the complete declarations and docstrings,
  including the explicit latching and augmentation fields and the Kan mapping-space
  conventions.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.leftClass` and its `relativeLatching` construction; I read
  the full signature and the simplex Reedy structure declaration.  The dependency's
  `model_structure` theorem is not copied; its canonical Reedy left class is used.

Edge cases checked before writing: degree zero is retained by `hZero`; empty or
zero-dimensional simplices are included by the all-degree latching predicate; no
nonemptiness, properness, combinatorial, enrichment, or universe-equality hypothesis is
added; arbitrary maps between fibrant targets (including identities and zero maps where
present) satisfy the naturality quantifiers; and the Kan condition is stated through the
full horn lifting property rather than only vertices.

Searches for an existing declaration were run as required:

- `msearch.py N0 lem-coef-frame-source-kan-fibration leanfinder` with the plain-language
  mapping-complex/Reedy-cofibration query: hits were generic model-category and Kan
  declarations, with no matching restriction theorem.
- `msearch.py ... loogle "Reedy, Fibration"`: no matching declaration.
- `msearch.py ... grep "Reedy|cosimplicial.*frame|frame.*cosimplicial" AlgebraicTopology`:
  only Reedy indexing and TODO infrastructure, no frame-source Kan-fibration result.
- `rg` over `WeilConjectures/` and `lean/Sheaf` for the item id, frame-source names,
  and restriction/Kan patterns: no existing declaration of this statement.

No `STATEMENT-DISPUTED` issue, node correction, new node, or dependency module was
required.  The prescribed `scompile.py` check compiled the file as both sandbox and
library confirmation with no error or warning.

## Second reading by N0

I reread the node and the completed module line by line.  The model-category and
factorization hypotheses are all present; `CosimplicialFrame` supplies exactly the two
cofibrant augmented frames; `hAug`, `hZero`, and `hReedy` render the augmentation,
degree-zero, and Reedy-cofibration clauses; the first conclusion contains both Kan
complex assertions and the restriction RLP; and the second conclusion contains the
pair-map and fibrant-target naturality equations.  No hypothesis or conclusion clause
was added, dropped, weakened, or specialized, and all variables and universes are
explicitly bound.
