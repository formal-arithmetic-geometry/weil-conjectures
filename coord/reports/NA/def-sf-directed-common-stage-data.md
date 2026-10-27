## Worker report

Defined `CategoryTheory.StageSystem.ExactStagePairData` in
`Sheaf.CategoryTheory.ExactStagePairData`. This is a data structure, with no theorem,
proof, sorry, existence assertion or chosen replacement for a canonical construction.
The item node changes only in `lean`. No new nodes or dependency modules are needed.
The example CompactObject module is withdrawn in the current clone; its former layout
is replaced by the current standard module header, public import, exposed public section,
explicit universes, autoImplicit false and source/blueprint docstrings.

Clause-by-clause correspondence with the unchanged node:

- `I : Type w`, `[Preorder I]`, `[IsDirectedOrder I]`, `[Nonempty I]` give exactly
  a nonempty directed preorder in an arbitrary universe. `C : I → Type u` and
  `[∀ i : I, Category.{v} (C i)]` keep object, morphism and index universes independent.
- `system : StageSystem C` is the actual existing unnormalized stage system.
  `StageSystem.T` supplies each transition functor and `StageSystem.assoc` supplies
  `T hij ⋙ T hjk ≅ T (hij.trans hjk)`. `StageSystem.cocycle` is the node's displayed
  associator equation, in Lean's left-to-right composition convention. There is no
  reflexive transition normalization or unit comparison in this structure.
- `system.PairCategory` is reused from `WeilConjectures.CategoryTheory.StageSystem.Basic`.
  Its fields `stage` and `obj` are the pair `(i,x)`. `PairCategory.Rep` consists of a
  common upper stage, both inequalities and the stage arrow. `StageSystem.tr` is
  `assoc.inv.app x ≫ (T h).map u ≫ assoc.hom.app y`, exactly the displayed transport.
  `PairCategory.Rep.Rel` is equality after transport to a common stage, and its setoid
  and quotient category are already constructed in Basic. Composition uses `Rep.comp`,
  then the quotient. The category identity is represented by the stage identity of
  `(T le_rfl).obj x` (Basic:239-242), not the identity of x.
- The existing `StageSystem.ι` sends x to `(i,x)` and f to
  `mkHom i le_rfl le_rfl ((T le_rfl).map f)` (Basic:388-394).
  The existing `StageSystem.transIso` is theta. Its component is the inverse of
  `isoToStage`; Basic:416-422 gives the representative `assoc.hom.app x` at stage j.
  Thus the existing `isoToStage` is exactly delta, and is not a new arbitrary isomorphism.
- `stagePreadditive`, `stageZero`, `stageShift`, `stageShiftAdditive` and
  `stagePretriangulated` store precisely the stage pretriangulated structures of
  def-weil-triangulated-category. No `IsTriangulated (C i)` (TR4) is assumed.
- `pairPreadditive`, `pairZero`, `pairShift` and `pairShiftAdditive` store the fixed
  preadditive, zero-object and additive integer-shift structures on the actual pair
  category. In particular they are supplied, not restricted to the shift construction
  in StageSystem.Shift; that module is not imported.
- `inclusionAdditive` stores additivity of every j_i. `inclusionCommShift` stores
  beta as `(system.ι i).commShiftIso n`. `transitionCommShift` stores sigma as
  `(system.T h).commShiftIso n`. Mathlib's `Functor.CommShift` includes precisely the
  zero- and addition-compatibility laws (Shift/CommShift.lean:147-154).
- `transitionExact` stores `(system.T h).IsTriangulated`, i.e. it maps distinguished
  stage triangles to distinguished triangles with these supplied comparisons. In the
  pretriangulated setting additivity follows from this Mathlib class; we do not add
  an extra requirement of faithfulness, full faithfulness or equivalence.
- `identificationCommShift` stores `NatTrans.CommShift (system.transIso h).hom ℤ`.
  Expanding its `shift_comm` and the composite functor's shift comparison gives
  `theta.app (x[n]) ≫ beta_i = j_j.map sigma ≫ beta_j ≫ theta.app x[n]`, where
  the last term means `(shiftFunctor P n).map (theta.app x)`. This is exactly the
  node's displayed theta equation in Lean composition order. No associator-shift
  condition beyond this equation is added.
- There is no field of type `Pretriangulated system.PairCategory`.
- The triangle-image definition is already exactly
  `(system.ι i).mapTriangle.obj U` in Mathlib.CategoryTheory.Triangulated.Functor:42-45:
  the first two maps are j_i applied to the original maps, and the third is
  `(j_i).map U.mor₃ ≫ ((j_i).commShiftIso 1).hom.app U.obj₁`. This is the beta-composed
  connecting morphism in the node. No second definition of triangle image is written.
- Triangles, triangle morphisms and their isomorphisms are Mathlib's
  `Pretriangulated.Triangle`, `TriangleMorphism` and category isomorphisms (Basic:44,
  104,146,187,202), exactly the recorded Mathlib match of def-weil-pbc-triangles-with-shift.
- The common-stage predicate D_S is already
  `StageSystem.CommonStageDistinguished` from the public import
  Sheaf.CategoryTheory.StageSystemCommonStageCones:50-52. Its full definition is
  `∃ (i : I) (U : Triangle (C i)), U ∈ distTriang (C i) ∧
  Nonempty (T ≅ (S.ι i).mapTriangle.obj U)`.
  It does not require a pretriangulation on P, TR4, exact inclusions, or normalized
  transitions. It is reused with the package's stored stage and pair shift structures;
  nothing is hidden behind a replacement predicate. Consumers may install these
  stored structures as instances and use this existing declaration directly.

Dependency declarations read and used:

- def-weil-triangulated-category is a Mathlib leaf, so has no `lean` record to repair:
  `CategoryTheory.Pretriangulated`, Mathlib.CategoryTheory.Triangulated.Pretriangulated,
  especially lines 43,65-88; `CategoryTheory.Functor.IsTriangulated`,
  Mathlib.CategoryTheory.Triangulated.Functor:186-188, with its additivity instance:237.
- def-weil-pbc-triangles-with-shift is likewise a Mathlib leaf:
  `CategoryTheory.Pretriangulated.Triangle` and its morphism/category/iso declarations
  in Mathlib.CategoryTheory.Triangulated.Basic, read at lines 25-115 and 146-205.
- Canonical constructions are imported through
  Sheaf.CategoryTheory.StageSystemCommonStageCones, which publicly imports the exact
  Basic and Mathlib Functor modules used here. Read full StageSystem signature and
  docstring (Basic:58-80), transport/representatives/quotient (92-245), identity and
  category laws (316-350), inclusions and canonical identifications (388-452), and
  CommonStageDistinguished's signature and docstring (CommonStageCones:44-53).
- Also checked Shift/CommShift:147-154,199-217,346-348 and Functor.mapTriangle:35-53
  against the displayed beta, sigma and theta formulas. StageSystemVerdier:24-35
  gives exactly these supplied hypotheses, except its extra TR4 assumption is
  deliberately not part of this definition.

Searches actually made on 2026-10-27:

- msearch.py leanfinder: `A directed stage system with supplied pretriangulated stages
  and additive shift coherent inclusions in its pair category` — 8 hits, including
  SpectralObject, TStructure, Pretriangulated, IsTriangulated. None packages this datum.
- msearch.py loogle: `CategoryTheory.Functor.CommShift` — matches the individual
  coherent shift-comparison class and associated lemmas, not the whole pair datum.
- msearch.py grep: `StageSystem|ExactStagePairData|CommonStageDistinguished` in
  `CategoryTheory` — no Mathlib hits.
- msearch.py leansearch: `directed stage system pair category supplied exact shift
  structures` — 8 hits, including HasShift, hasShiftMk, ShiftMkCore.mk,
  DirectedSystem.mk and TwistShiftData.shiftMkCore; no exact-stage pair package.
- Direct rg in Mathlib/CategoryTheory, WeilConjectures and Sheaf for
  `ExactStagePairData|exact.stage.pair|directed.common.stage|structure .*Stage.*Data`
  found only unrelated Nagata stage data and scheme stage data.
- Direct rg by `StageSystem|PairCategory|CommonStageDistinguished|CommShift` in
  WeilConjectures/CategoryTheory/StageSystem and Sheaf/CategoryTheory/StageSystem*
  found the actual unnormalized construction and common-stage predicate reused here.
  No existing declaration packages all and only the supplied data.
- Direct node-id/name rg in WeilConjectures, Sheaf and dag/lean_names_upstream.json
  found no attachment or competing ExactStagePairData declaration.

Edge cases checked against definitions before writing: empty I is excluded explicitly;
empty stage categories are excluded only by the specified zero objects. Singleton I
and T=Id is admitted. Singleton I with zero transition is admitted as well, so no unitor,
faithfulness or inclusion equivalence can be assumed. Repeated indices use the same
associator data and do not force T_ii=Id. All integers, including zero and negatives,
are covered by CommShift ℤ. No relation among w, u and v is imposed. Stage TR4 and
pair pretriangulation are absent, as required. The current normalized blueprint model
was read as context, not substituted for the explicitly unnormalized source datum.

No statement correction, node fault or STATEMENT-DISPUTED finding.

Validation: prescribed scompile.py compiled the full module without warnings or errors
(10.7 s sandbox; 1.7 s library-name check). Final docstring spelling was then corrected;
the dry run compiles the final bytes again.

## Second reading by NA

Self-check of the unchanged node and the complete module, carried out separately after
compilation. No independent worker was started, in accordance with the dispatcher brief;
the maintainer's independent review remains the independent reading.

Rechecked every binder and every field against the two paragraphs of the node. The
three universes and Nonempty/Preorder/IsDirectedOrder binders match. The system field
reuses the literal existing nonunital pair category and its canonical delta and theta;
its representatives, identity and inclusion maps have the specified reflexive T_ii.
The five stage structure fields give only pretriangulations; the four pair structure
fields give precisely the supplied additive/zero/shift data. The inclusion and transition
comparison fields are coherent for all integers, transition exactness uses the recorded
Mathlib notion, and the final natural-transformation field expands to the stipulated
theta equation. No TR4, associator-shift coherence, normalized unit or pair triangulation
has slipped into the package. Checked the reused mapTriangle and CommonStageDistinguished
bodies against the last two displayed definitions. Found one docstring spelling mismatch
(`identification_commShift` rather than `identificationCommShift`) and corrected it.
No mathematical or signature mismatch was found.
