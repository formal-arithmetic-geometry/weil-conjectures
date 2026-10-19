## Worker report

The delivery states `CategoryTheory.all_cofibrant_mapping_detection` in
`Sheaf.AlgebraicTopology.AllCofibrantMappingDetection`, with `sorry` as its only proof.
It introduces no definitions, helper assertions, or new nodes. The current reviewed
Q54 stage-1 split is preserved. The earlier stale-assignment message concerned
resplitting; this delivery only supplies the stage-2 Lean statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The model category is `{M : Type u} [Category.{v} M] [ModelCategory M]`.
  Mathlib's model category supplies the three morphism classes, retract closure,
  two-out-of-three and the two weak factorization systems. The node adopts complete
  and cocomplete model categories with functorial factorizations through
  `lem-coef-simplicial-boundary-collapse-test`; these additional conventions are
  rendered by `[HasLimits M] [HasColimits M]` and the two
  `MorphismProperty.HasFunctorialFactorization` binders, for cofibrations/trivial
  fibrations and trivial cofibrations/fibrations respectively. They are not extra
  properness or presentability hypotheses.
- The compatible simplicial enrichment is `[SimplicialCategory M]`. Mathlib's
  `EnrichedOrdinaryCategory` supplies composition, identities, and the identification
  of ordinary arrows with vertices. Its mapping simplicial sets are `sHom` in
  `SSet.{v}`. Object and morphism universes `u` and `v` are independently bound.
- The chosen simplicial tensors and cotensors are
  `(_T : SimplicialTensorCotensor M)`, using the recorded dependency's objects,
  universal elements and enriched representing isomorphisms unchanged.
- The displayed SM7 hypothesis is `(_hSM7 : SatisfiesSM7 M)` from the existing
  `CategoryTheory.SimplicialModelLocalization` namespace. Unfolding it quantifies
  over all `i : A ⟶ B` and `p : E ⟶ D`, assumes `Cofibration i` and `Fibration p`,
  and asserts horn lifting for `cornerMap i p`, plus weak homotopy equivalence
  when `WeakEquivalence i ∨ WeakEquivalence p`. That corner is the actual
  `pullback.lift (eHomWhiskerRight SSet i E) (eHomWhiskerLeft SSet B p)` with
  compatibility `(eHom_whisker_exchange SSet i p).symm`; its codomain is precisely
  `Map(A,E) ×_{Map(A,D)} Map(B,D)`. The recorded Kan--Quillen theorem equates horn
  lifting with Kan fibration and Kan fibration plus the realization-based weak
  equivalence with boundary lifting. Thus both triviality alternatives, including
  dimension-zero boundary lifting, are retained.
- Every object is cofibrant: `(_hall : ∀ T : M, IsCofibrant T)`. This ranges over
  all model objects, including possible intermediate factorization objects.
- The arbitrary tested map is `{X Y : M} (f : X ⟶ Y)`. There is no fibrancy
  assumption on X or Y, and no assumption that f is a cofibration or fibration.
- The equivalence is the literal `WeakEquivalence f ↔ ...`, retaining both
  implications. The right side is `∀ Z : M, IsFibrant Z → ...`, exactly every
  fibrant target and no nonemptiness assumption on mapping spaces.
- The map f* is `eHomWhiskerRight SSet f Z : sHom Y Z ⟶ sHom X Z`.
  The conclusion `SSet.Enhanced.IsWeakHomotopyEquivalence` is the dependency's
  bijection on path components of realization and bijections on all positive
  based homotopy groups at every source basepoint. It is not merely a component
  bijection or an unspecified equivalence between the two spaces.
- Fixed containing universes are rendered by explicit `universe u v` and by
  Mathlib's compatible `Category.{v}`/`SimplicialCategory` interface. No equation
  between object and morphism universes, no smallness constraint on the object
  type, and no properness or combinatorial structure is imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`,
  `CategoryTheory.simplicial_boundary_collapse_test`: its full model conventions,
  rendered with Mathlib `ModelCategory` and the explicit completeness/functoriality
  binders; its theorem is available for the proof's tensor lifting calculations.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`,
  `CategoryTheory.SimplicialTensorCotensor` (including `tensorMap` and `parameterMap`):
  exactly the recorded enriched tensor/cotensor interface.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.IsWeakHomotopyEquivalence`: realization-based weak equivalence.
  `componentsMap` and `homotopyGroupMap` were inspected as well.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen`: horn/boundary lifting, Kan objects,
  and compatibility of the realization-based weak equivalences with the model.
- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`,
  `CategoryTheory.SimplicialModelLocalization.cornerMap` and `SatisfiesSM7`:
  already landed canonical SM7 definitions. Its owning existing node
  `lem-coef-simplicial-model-nerve-localization` is added to `stmt_deps`, as the
  stage-2 rules permit for landed interfaces. The localization theorem itself
  is neither an assumption nor the proof route. This node has no dependency
  path to the item, so the added edge introduces no dependency cycle.
- Proof-only import `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`,
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak`, and proof-only import
  `Sheaf.AlgebraicTopology.FixedCylinderFibrantTargetDetection`,
  `HomotopicalAlgebra.fixedCylinder_fibrantTarget_detection`: full signatures
  and proof docstrings were read; the latter supplies the required converse.
- The Mathlib leaf `lem-coef-localized-good-homotopy-test` is represented by
  `Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma`:
  `LeftHomotopyRel.iff_map_eq` and `RightHomotopyRel.iff_map_eq`, together with
  `LeftHomotopyRel.leftHomotopy` and `RightHomotopyRel.rightHomotopy` in
  `Mathlib.AlgebraicTopology.ModelCategory.Homotopy`. Both modules are imported
  for the proof only. Its `mathlib_match` needs no replacement record.

The theorem docstring carries all seven proof steps of the current split:
transposition and endpoint lifting; the good simplicial cylinder; weak-map
factorization and a lifted homotopy; the forward weak mapping equivalence;
components of realization; comparison with the chosen very good cylinders via
ordinary localization; and the converse from fixed-cylinder detection. The
blueprint proof paragraph 2 for `prop-coef-integral-exceptional-adjoint` was
opened as the stated ancestry. The node explicitly records the general lemma
as an agent extraction and HTT A.3.1 as archival source WANTED; the delivery does
not claim to transcribe an unavailable HTT passage.

Edge cases checked before writing: identity f gives identity precomposition;
empty mapping spaces remain permitted and yield empty component quotients with
no chosen basepoint; the initial object is cofibrant by the all-object hypothesis;
the terminal object is a legitimate fibrant test; the one-object trivial model
has point mapping spaces and satisfies the assertion. Sources X and Y may be
nonfibrant. SM7 retains both independently trivial input cases and every horn,
but never imposes a dimension-zero horn/nonemptiness condition. Boundary-zero
lifting only occurs for the stipulated trivial Kan fibrations. No statement
fault or STATEMENT-DISPUTED flag was found.

Searches for an existing statement:

- `msearch.py leanfinder`, query "In an all cofibrant simplicial model category
  weak equivalences are detected by mapping into every fibrant object": eight
  results, chiefly `CofibrantObject.weakEquivalence_toHoCat_map_iff`, bifibrant
  wrappers and `RightHomotopyClass.precomp_bijective_of_weakEquivalence`.
  These concern an ordinary homotopy category or homotopy-class sets and do not
  assert the enriched weak-homotopy-equivalence criterion. Candidate source
  signatures in `CofibrantObjectHomotopy.lean` and `Homotopy.lean` were read.
- `msearch.py loogle`, quoted
  `HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_weakEquivalence`:
  one result. Its full signature gives only the forward bijectivity on ordinary
  right-homotopy classes, not this statement.
- `msearch.py grep`, query `mapping.*[Ww]eak|[Ww]eak.*mapping|SimplicialModel`
  in Mathlib `AlgebraicTopology`: zero results.
- Direct `rg` in upstream `WeilConjectures/` and `dag/lean_names_upstream.json`,
  searching for the proposed name, `SimplicialModel`, `SatisfiesSM7`, and
  mapping/weak patterns: no upstream match. Direct item-id search in upstream
  `WeilConjectures/` and project `lean/Sheaf/`: no existing item declaration.
- Direct `rg` in `lean/Sheaf/` for SM7 and mapping-model criteria found the
  existing `cornerMap` and `SatisfiesSM7` definitions, which are reused, and
  all-cofibrant recognition, which concludes SM7 from tensor conditions but
  does not state mapping-space detection. No private definition was made.
  The actual msearch output is preserved in sandbox `searches.jsonl`.

Validation: prescribed `scompile.py` compiled the delivery module in both
sandbox and library positions, with no errors or warnings (about 3.5 seconds
per file). It also compiled the current fixed-cylinder dependency in its private
overlay. All universes and variables are bound, with `autoImplicit false`.
Only the item's `lean` record and the added landed-interface `stmt_deps` edge
change in the node; the statement and Q54 proof remain unchanged.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
