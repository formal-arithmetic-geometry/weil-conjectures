## Worker report

The delivery states `SSet.FreeBar.free_bar_cell_filtration` in
`Sheaf.AlgebraicTopology.FreeBarCellFiltration`. Its conclusion is `Nonempty
(CellFiltration C)`, where the structure spells out the complete normalized
construction and all conclusions of the node. This is an existence statement
about the specified canonical construction: every stage, operator, quotient
injection, cell, augmentation and extra degeneracy is pinned by its formulas.
There is no definition selecting data from this postponed existence theorem.
All helper definitions have real data. The sole postponed theorem is the item
itself, and its docstring contains all five proof steps with their dependencies.
No mathematical statement was corrected and no dependency record was changed.

The preceding attempt's claim that Q37 already completed this stage was wrong:
Q37's reviewed PASS is the stage-1 split, with no Lean binding. At entry this
sandbox contained only four brief markers, no module, node copy, or report.
This delivery supplies the missing stage-2 work, leaving the accepted stage-1
statement, proof and review intact.

### Hypotheses and clauses

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial sets and the cited universe conventions | Explicit `universe u`; `SSet.{u}`, `C : Type u`, `[SmallCategory C]`. There is no equality imposed on independent large-category universes. |
| Any small ordinary category C | The theorem binds `(C : Type u) [SmallCategory C]`. |
| Any diagram Z, with no additional property | Every construction field quantifies over all `Z : C ⥤ SSet.{u}`, or is a functor on that entire diagram category. |
| The free covariant diagram F_c K(d) = Hom_C(c,d) × K | `free c K` transports `ProjectivePresheaf.representable (op c)` by `opOp C` and tensors it objectwise with the constant K. A degreewise element is `(a.op,z)` for `a : c ⟶ d`. `freeMap` is its induced coefficient map. |
| P_k(d) is the coproduct over c_0 → ... → c_k → d of Z(c_0) | `stageIso` identifies the stage of `P` with `∐ (fun c : ComposableArrows (Over d) k ↦ Z.obj (c.obj 0).left)`. A chain in `Over d` encodes exactly this chain: all its earlier structure maps to d are forced by the last arrow. The isomorphism is normalized on every summand by the next three fields. |
| First face applies Z to the first arrow; other faces compose arrows; degeneracies insert identities | `stage_operator` specifies restriction along EVERY `a : ⦋m⦌ ⟶ ⦋k⦌` using the existing nerve restriction. Its coefficient map is `Z.map ((c.map (homOfLE (Fin.zero_le (a.toOrderHom 0)))).left)`. Taking a face or degeneracy gives precisely the stated formulas, including the last face composing the final arrow to d. |
| The C-diagram action postcomposes the last arrow | `stage_postcompose`, using `Over.map a`. |
| QZ is the quotient/coend of P_k × Δ^k by all simplex relations | `realizationShape` indexes every simplex operator; `realizationIndex` has common source `P_n × Δ^m` and arrows `P(a) × id` and `id × Δ(a)`. `realization` is its actual `multicoequalizer`. `coendIso` and `ι_coend` identify Q and every summand map with that quotient. |
| Equivalently QZ(d)_r = P_r(d)_r | `diagonal` is the degreewise equivalence; `diagonal_ι` is exactly `[x,a] ↦ P(a)x`. This also forces compatibility with simplicial operators because it fixes the value on every quotient generator. |
| Natural filtration starting with the empty diagram | `filtration` is functorial in Z and has values `ℕ ⥤ (C ⥤ SSet)`. Index zero denotes Q_{-1}; index k+1 denotes Q_k. `initial_stage` asserts that index zero is initial. |
| Q_k is the image of outer simplices of dimension ≤ k | `inclusion`, `inclusion_mono`, and the exact image equivalence `filtration_image`. The image condition quantifies over every outer dimension m ≤ k, every inner-r simplex x, and every parameter a : [r] → [m]. |
| The filtration has colimit QZ | `filtration_colimit : IsColimit (Cocone.mk (Q.obj Z) (inclusion Z))` fixes both the apex and its specified inclusions. |
| Cells indexed by strings whose internal arrows are all nonidentity | `c : (nerve C).nonDegenerate k`. For a categorical nerve this is exactly the absence of identity adjacent arrows: nerve degeneracies insert identities, and an identity adjacent arrow can be deleted. It places no restriction on the last arrow to d or on coefficient degeneracy. |
| Source and target of each cell are F_ck(Z(c_0) × ∂Δ^k) and F_ck(Z(c_0) × Δ^k) | `boundaryFamily`, `diskFamily`, and `cellMap`. The latter is the actual coproduct map formed by `freeMap` on the coefficient-weighted boundary inclusion. |
| The specified free-cell pushout is in C-diagrams | `attaching`, `disk`, and `cell_pushout : IsPushout (cellMap Z k) (attaching Z k) (disk Z k) ...`. Its fourth leg is exactly the successor map of the filtration. |
| Attaching maps are induced by the stated faces | `cell_formula` fixes the entire cell map into Q on `(a,z,α)` as the corresponding coend representative of `overChain c.val a`. `disk_inclusion` fixes its factorization through Q_k. The pushout square's commutation fixes the boundary's factorization through Q_{k-1}; since `inclusion_mono` holds, this factorization is unique. The coend relations and `stage_operator` therefore prescribe precisely the face attaching maps, including overlaps. No arbitrary attaching map is substituted. |
| QZ is projectively cofibrant | `projectively_cofibrant` states that `initial.to (Q.obj Z)` belongs to `((modelCategoryQuillen.I.rlp).functorCategory C).llp`. This is exactly the recorded dependency's projective cofibration class, in covariant variance, and does not assume a model structure on the diagram category. |
| Composition gives an augmentation of the outer simplicial object to const Z | `augmentation` is a natural transformation `P.obj Z ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Z`. `augmentation_formula` fixes its value on each summand as `Z.map (c.obj 0).hom`, i.e. the composite to d. It is thus also natural in d and commutes with every outer operator. |
| h_{-1}(z) is the identity chain at d | `hMinus_formula` is the summand inclusion at `ComposableArrows.mk₀ (Over.mk (𝟙 d))`. |
| h_k appends d and 1_d, leaving the coefficient unchanged | `h_formula` specifies the appended chain c': its last face is exactly the original chain c, its last object in `Over d` is `Over.mk (𝟙 d)`, and its coefficient is the old coefficient transported along the forced equality of first objects. These conditions uniquely specify the appended chain, since `id_d` is terminal in `Over d`. |
| ε h_{-1} = 1 | `epsilon_hMinus` (categorical composition is written left to right). |
| d_{k+1} h_k = 1 | `last_face_h`, with `Fin.last (k+1)`. |
| d_0 h_0 = h_{-1} ε | `first_face_h_zero`. |
| d_i h_k = h_{k-1} d_i for k ≥ 1 and i ≤ k | `face_h` writes k = k'+1 and binds `i : Fin (k'+2)`; `i.castSucc` is the same index in the larger simplex. Every index in the node is covered. |
| s_i h_k = h_{k+1} s_i for i ≤ k | `degeneracy_h`, with `i : Fin (k+1)`, and the corresponding cast in the larger degree. |
| All operations commute with inner simplicial operators | All summand maps, augmentation components, hMinus and h are actual morphisms in `SSet`, not degreewise unstructured functions. P is a simplicial object of diagrams of simplicial sets. |
| All data, including augmentation, natural in Z | `P` and `Q` are functors with `stage_map`, `ι_map`; the filtration is a functor with `inclusion_map`; `augmentation_map`, `hMinus_map`, and `h_map` give the specified naturality. Cells and their stage factorizations are pinned by their generator formulas and monic stage inclusions, so their naturality follows too. |
| No fibrancy or nonemptiness assumed | There is no Kan, inhabited, nonempty, finiteness, or cofibrant-value binder anywhere in the theorem or `CellFiltration`. |

### Dependency declarations and source inspection

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the recorded
  `SSet.Enhanced.coneCategory` signature and docstring, together with its
  simplicial primitives and convention header. This item only needs its
  small-simplicial-set convention, not a cone or quasicategory assumption.
  The module is publicly imported as the node requires; existing Mathlib
  `SSet`, `stdSimplex`, Cartesian tensor and `nerve` supply those objects.
- `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`: read the whole
  module and `SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`.
  Use its `representable` in `free`, and exactly its projective cofibration
  class, the LLP against the objectwise boundary-RLP maps. The variance is
  D = C^op, with the double-opposite equivalence used for the representable.
- Proof input `lem-coef-kan-quillen-right-proper`: read the source and full
  signature of `SSet.KanQuillen.right_proper_kan_quillen`; import its module
  without `public` for the proof plan. It identifies boundary-RLP maps as
  trivial fibrations, and monomorphisms as Kan cofibrations.
- Proof input `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`: its
  `mathlib_match`, not a missing Lean record, supplies
  `SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_dim`,
  `SSet.unique_nonDegenerate_simplex`, `SSet.unique_nonDegenerate_map` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`. Read their full
  signatures/docstrings (existence near line 114, uniqueness near 217–233).
  The module is publicly imported because the cell index also uses
  `SSet.nonDegenerate`.
- Read `nerve` and `ComposableArrows` sources, the actual `Over.mk`,
  `Over.homMk`, and `Over.map` interfaces, the boundary definition, and
  `MultispanShape`, `MultispanIndex`, `multicoequalizer` and
  `Multicoequalizer.π` before writing their uses.

The already landed `SimplicialBarProjectiveResolution` was also inspected in
full. It does NOT state this node's complete assertion: its existential bar
claim does not retain the skeletal pushouts or these explicit contraction
equations. Its `barStage` is the generic coproduct notation for our stage,
but importing that theorem's module as a new DAG dependency would close the
cycle through extra-degeneracy realization, model localization, Rezk completion,
space geometric descent, and this item. Consequently the stage signature uses
Mathlib's coproduct inline; it introduces no second named `barStage` definition
and does not use the downstream theorem. The simplex-coend helper here is the
coend of an arbitrary supplied simplicial object of simplicial sets, while that
module's `barRealization` takes a general enriched category, tensor interface,
and coefficient diagram. No second definition of a recorded dependency is made.

### Edge cases checked before writing

- Empty C: no chains or cells. The diagram category has its unique object;
  the P, Q, filtration and naturality clauses are vacuous componentwise.
  The initial stage and colimit are still specified by universal properties.
- Empty-valued Z: every chain coefficient, stage and coend is empty, and the
  normalized augmentation/contraction maps and all image equations still type.
- k = 0: all zero-chains are nondegenerate and `boundary 0 = ⊥`; the first
  attachment is exactly the coproduct of free diagrams on Z(c). No terminal
  arrow is mistakenly excluded from its free factor.
- Discrete C: only degree-zero chains survive as outer nondegenerate cells,
  so QZ is objectwise Z. Higher cells have an empty index set.
- C = [1] and constant-point Z: QZ(0) is a point and QZ(1) is Δ^1;
  the degree-zero stage contains its two vertices and the next attachment
  inserts its one nonidentity edge. This checks covariant orientation and
  the last-face formula.
- Nontrivial endomorphisms and invertible arrows: they remain valid cells
  unless an adjacent displayed arrow is an identity. Composite identities
  do not incorrectly exclude a chain.
- Degenerate inner coefficients: still allowed in every cell family; the
  outer-chain index is independent of the inner coefficient degree.
- For h_0 the last face returns the original arrow to d, while its first
  face applies Z to that arrow and gives the identity chain at d. For k≥1
  the i=k face composes the last old arrow with the old terminal arrow.
- Empty non-Kan simplicial sets and arbitrary non-Kan Z are included;
  projective cofibrancy uses that all simplicial sets are Kan-model
  cofibrant, not that they are Kan complexes.

### Existing-declaration searches

All required search calls used `msearch.py Q05 lem-coef-free-bar-cell-filtration`.

1. `leanfinder`, query `Free bar simplicial replacement of a category diagram
   with skeletal filtration by free boundary cells`: eight hits including
   Dold–Kan, `SimplicialObject.sk`, `nerve`, and `cechNerve`; none states
   this free-bar cell filtration or terminal contraction.
2. `loogle`, query `SimplicialObject, SSet.skeleton`: zero hits, with the
   service reporting unknown unqualified identifier `SimplicialObject`.
   This is recorded as an unsuccessful query, not evidence of a match.
3. `grep`, query `simplicialReplacement|barResolution|freeBar|ExtraDegeneracy`,
   subdirectory `AlgebraicTopology`: five hits, all the generic
   `ExtraDegeneracy.lean` structures/constructions. Read its structure and
   related declarations; it does not state the free C-diagram filtration.
4. `leansearch`, query `Skeletal filtration of the categorical free simplicial
   bar construction by representable boundary cells`: hits include
   `SSet.skeleton`, `SSet.boundary`, `SimplicialObject.IsCoskeletal`,
   `SimplicialObject.sk`, and `SimplexCategory.toCat`; none matches.
5. Direct `rg` over Mathlib, the source project's `WeilConjectures`, and
   this project's `lean/Sheaf` for bar-construction names found group
   representation resolutions, coherent two-sided bars, and the general
   simplicial bar projective resolution discussed above. No exact statement.
6. Direct identifier/blueprint-ID searches in the source project,
   `dag/lean_names_upstream.json`, and `lean/Sheaf`: no existing declaration
   for the item, and no `SSet.FreeBar` namespace or chosen declaration name.
   The node still had no `lean` record when this delivery was written.
7. Direct `rg` for `CellFiltration|realizationShape|overChain|def free ` in
   Mathlib's algebraic topology, the source project and the relevant project
   topic directories: no name collision. Checked generic skeletal and
   extra-degeneracy APIs rather than treating search names as exact matches.

### Source grounding and validation

Read the current ancestor blueprint paragraph 2 in the 2026-10-15 snapshot;
its derived-coefficient-adjunction route is the same provenance recorded in
this agent-expanded foundation node. Opened the actual Rezk PDF, §7 at
printed p.13, which gives the chain-indexed diagram replacement and its
augmentation, and HTT Remark A.3.3.5 at printed p.871, which gives free
projective cofibrations. The detailed skeletal filtration and contraction
formulas remain explicitly agent-expanded as the node's source says; they
are not misattributed as a quoted Rezk theorem. Read Stacks
`simplicial.tex`, Lemma `lemma-splitting-simplicial-sets` (Tag 017R), for the
outer nondegenerate decomposition used in the proof plan.

No new nodes, dependency modules, statement correction, or disputed statement.
Only the item's `lean` field is added to a copy of the accepted node. No
shared file or source-project file was edited and no global build was run.

Compilation and the required delivery dry run are recorded below after the
final file check. The independent second reading is intentionally left for
the next worker, as required by the delivery tool.

Final validation (2026-10-17 UTC): the prescribed `scompile.py` compiled both
the sandbox and library-path copies cleanly, with no warnings, in 5.1 and
6.5 seconds respectively. The JSON comparison changes exactly `lean`;
the main recorded signature is verbatim, the module has one `sorry`, and
its maximum line width is 94 characters. `deliver2.py --no-push` printed
`OK (dry run)`: the packet compiles and passes preflight except for the
independent second reading, which the next worker must write. Nothing
was pushed. The report is included in a final repeat of the same dry run.

## Second reading by Q05

Independent second reader, 2026-10-17. I opened the accepted node and every
field of `FreeBarCellFiltration.lean`, then read the dependency records and
source signatures rather than relying on the worker's table. The following
is my inventory of the node's objects, hypotheses and conclusions, matched
to the delivered Lean. Verdicts concern the final version.

| Node object, hypothesis or conclusion | Lean rendering and second-reader verdict |
| --- | --- |
| Small simplicial sets in the dependency's fixed small universe | `universe u`, `SSet.{u}` throughout. Read `EnhancedDiagramsCones`' convention and `SimplicialPresheafProjectiveModel`'s universe binders. PASS: the same simplicial sets; no quasicategory or Kan condition is inherited merely by importing the convention. |
| A small ordinary category C | `(C : Type u) [SmallCategory C]` in the theorem, structure and helpers. PASS: objects and arrows are small in the same universe as coefficient simplices; arbitrary small categories, including empty ones. |
| An arbitrary covariant input diagram Z | `CellFiltration.P`, `.Q`, `.filtration` are functors on all `C ⥤ SSet.{u}`; the other fields quantify over arbitrary Z. PASS: no finiteness, fibrancy, nonemptiness, or valuewise condition added. |
| Free diagram F_c K(d) = Hom(c,d) × K | `free c K` uses `opOp C ⋙ ProjectivePresheaf.representable (op c)` and the objectwise Cartesian tensor with constant K. PASS: reading the recorded `representable := yoneda.obj d ⋙ Functor.const ...` shows that a generator at d is exactly `(a.op,z)` with a : c ⟶ d. `freeMap` changes K alone. |
| P_k(d) is the chain coproduct ending at d | `P` and `stageIso` identify each stage with `∐ (fun c : ComposableArrows (Over d) k ↦ Z.obj (c.obj 0).left)`. PASS: an Over-chain is exactly the indicated forward string and terminal arrow; its other structure maps are forced by composition. |
| Faces and degeneracies have the stated formulas | `stage_operator` covers every monotone a : [m] ⟶ [k], restricting the chain with the actual nerve and applying Z to its first composite. PASS: the first face changes the coefficient, interior faces compose arrows, the last face composes with the terminal arrow, and degeneracies insert identities internally. |
| C-diagram action and dependence on Z | `stage_postcompose` uses `Over.map a`, and `stage_map` applies the transformation at the first coefficient. PASS: correct covariant variance and normalized functoriality. |
| QZ is the objectwise quotient/coend P_k × Δ^k | `realizationDiagram P` is P followed by `curriedTensor SSet` and precomposition with `stdSimplex`; `realization` now uses Mathlib `coend`. `coendIso`, `ι` and `ι_coend` specify Q and its quotient generators. PASS after H4 repair described below. The existing `multispanIndexCoend` has source P_n × Δ^m and arrows P(a) × id and id × Δ(a), exactly the two required relations. |
| Equivalent degreewise formula QZ(d)_r = P_r(d)_r | `diagonal` is an equivalence and `diagonal_ι` fixes `[x,a] ↦ P(a)x`. PASS: it covers every quotient generator. These formulas also force its operator compatibility by the simplicial identities and jointly epimorphic coend injections. |
| All quotient maps natural in d and Z | `ι_postcompose`, `ι_map`, and the actual functors P and Q. PASS: the specified generators determine the natural maps, so Q cannot be an unrelated replacement. |
| Filtration beginning with the empty diagram | `filtration`, `inclusion`, `initial_stage`, and `inclusion_mono`. PASS: index 0 is Q_{-1}, index k+1 is Q_k. IsInitial specifies the empty diagram without choosing a point. |
| Q_k is exactly the image of outer degree at most k | `filtration_image` quantifies over all inner r, points y, outer m ≤ k, x ∈ P_m(d)_r and a : [r] ⟶ [m]. PASS: image equality, with no restriction on the coefficient simplex or simplex parameter. |
| The inclusions have colimit QZ | `filtration_colimit : IsColimit (Cocone.mk (Q.obj Z) (inclusion Z))`. PASS: the actual inclusions and apex are fixed, not just an unspecified isomorphic colimit. |
| Cell indices are strings with no identity internal arrow | `(nerve C).nonDegenerate k` in both cell families. PASS: read nerve restriction and ordinary simplicial degeneracy definitions; inserting an identity gives degeneracy, and any identity internal arrow can be deleted. This imposes no condition on the last arrow to d, coefficient degeneracies, invertibility, or composites of several arrows. |
| The free boundary and disk cell families | `boundaryFamily`, `diskFamily` use F_{c_k}(Z(c_0) × boundary k) and F_{c_k}(Z(c_0) × stdSimplex[k]). PASS: exactly the node's two objects, with existing Mathlib boundary and Cartesian product. |
| The map attaching those cells is the stated coproduct boundary inclusion | `cellMap` is `Sigma.desc` of `freeMap` on the actual boundary inclusion, followed by each disk injection. PASS: no arbitrary map replaces the canonical generating family. |
| The attaching square is a pushout in C-diagrams | `attaching`, `disk`, `cell_pushout` use the successor map from filtration k to k+1. PASS: this is Q_{k-1} → Q_k for every k ≥ 0, in the requested diagram category. |
| Attaching maps are induced by the stated faces | `cell_formula` identifies each disk generator `(a,z,b)` with the chain `overChain c.val a` in the coend; `disk_inclusion` specifies its stage factorization. PASS: pushout commutation identifies the boundary composite into Q with these same generators. Monicity of the old-stage inclusion makes this factorization unique, and the coend relations plus `stage_operator` give precisely the face maps, including their intersections. |
| QZ is projectively cofibrant | `projectively_cofibrant` uses `((modelCategoryQuillen.I.rlp).functorCategory C).llp` at `initial.to (Q.obj Z)`. PASS: read the dependency theorem's cofibration and trivial-fibration equalities. This is its projective class in covariant form (D = Cᵒᵖ, transported across double opposite), with no model-structure assumption added. |
| Composition gives the outer augmentation | `augmentation : P.obj Z ⟶ const Z` and `augmentation_formula` give Z.map (c.obj 0).hom on each summand. PASS: a natural transformation of outer simplicial C-diagrams, hence all required outer and d compatibility. |
| h_{-1}(z) = (d,1_d,z) | `hMinus`, `hMinus_formula`, using `ComposableArrows.mk₀ (Over.mk (𝟙 d))`. PASS: exact identity summand. |
| h_k appends d and its identity, retaining the coefficient | `h` and `h_formula`: the last face of c' is c, its last object is `Over.mk (𝟙 d)`, and the summand map preserves the coefficient along the forced first-object equality. PASS: id_d is terminal in Over d, so the appended arrow is the original terminal arrow and this specifies the unique extension, not an arbitrary extra degeneracy. |
| ε h_{-1} = 1 | `epsilon_hMinus`. PASS; Lean's categorical composition is written in execution order. |
| d_{k+1} h_k = 1 | `last_face_h`, with `Fin.last (k+1)`. PASS: last face, for every k including 0. |
| d_0 h_0 = h_{-1} ε | `first_face_h_zero`. PASS: the exceptional first-face degree-zero equation is present separately. |
| d_i h_k = h_{k-1} d_i for k ≥ 1 and i ≤ k | `face_h` writes k = k'+1 and i : Fin (k'+2); `i.castSucc` keeps the same vertex number in the larger simplex. PASS: every allowed index, including the first and final old face, and no missing k = 1 case. |
| s_i h_k = h_{k+1} s_i for i ≤ k | `degeneracy_h`, i : Fin (k+1), again `i.castSucc`. PASS: exactly all specified indices, including i = k. |
| The operations commute with inner simplicial operators | P is an outer simplicial object of C-diagrams of SSet; the augmentation, hMinus and h are morphisms of SSet. PASS: these are natural maps of inner simplicial sets, stronger-looking syntax expressing exactly the requested inner operator equations. |
| All data, including augmentation, natural in Z | `stage_map`, `ι_map`, `inclusion_map`, `augmentation_map`, `hMinus_map`, `h_map`, plus functorial P, Q and filtration. PASS: cell maps are fixed on all generators; disk and attaching factorizations are unique through the monic inclusions, which also forces their naturality. |
| One theorem with the complete conclusion | `free_bar_cell_filtration : Nonempty (CellFiltration C)`. PASS: the structure packages all the normalized data just listed. No definition selects an object from this postponed existence, and no arbitrary chosen object replaces a canonical construction. |

Source reading: I opened Rezk's actual PDF at
https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, §7, printed p.13
(PDF page 13), and read the displayed replacement over chains ending at i,
its description as the diagonal over (I ↓ i), and its natural augmentation.
The small diagram is arbitrary there. The sharpness assumptions of the later
Theorem 7.1 do not belong to the preceding construction and are not added.
I also opened HTT at https://www.math.ias.edu/~lurie/papers/HTT.pdf,
read the assumptions at the beginning of A.3.3 and Remark A.3.3.5, printed
p.871 (PDF page 889): free diagrams of cofibrations generate projective
cofibrations. For the ordinary diagram of simplicial sets this is the
already recorded projective-model dependency, not a new hypothesis on Z.
I read Stacks `literature/stacks-project/simplicial.tex`,
`lemma-splitting-simplicial-sets` (017R), including its uniqueness proof
using surjections and sections: no assumption beyond a simplicial set.
The filtration and terminal identities are explicitly agent expansions in
the node; the delivery does not claim that Rezk states those formulas.
I also read the cited ancestor blueprint paragraph in the recorded snapshot.

Dependency checks: `EnhancedDiagramsCones` uses Mathlib SSet, standard
simplices and Cartesian operations directly; its `coneCategory` signature
is not being mistaken for a required cone hypothesis. I read the whole
`SimplicialPresheafProjectiveModel` module, especially `representable`,
`generatingCofibrations`, and the theorem's lifting-class equalities, and
the full `right_proper_kan_quillen` signature identifying monos and boundary
RLP maps. The decomposition node is a Mathlib leaf: I opened
`exists_nonDegenerate` and all three `unique_nonDegenerate_*` signatures
in `Degenerate.lean`; their object and epi-map quantifiers agree with the
proof's use for the outer simplicial set in each fixed inner degree.
There are no dependency modules or new definition nodes in this delivery.
No repair note exists for this item. No statement correction was made, so
there is no statement_change or correction-citer audit to verify.

Edge cases checked independently:

- Empty C: no chain or cell index, no chosen category object; all diagrams
  and equations remain meaningful and the initial/colimit conditions hold.
- Empty-valued Z: all coefficient summands are empty, with the coend and
  each image stage empty; h and augmentation are still the specified maps.
- k = 0: `boundary 0` is empty, all nerve vertices are nondegenerate, and
  filtration 0 → 1 is the free degree-zero attachment Q_{-1} → Q_0.
  Both `last_face_h` at 0 and `first_face_h_zero` have the correct endpoints.
- Discrete C: every positive-dimensional chain contains an identity, so
  positive cell families are empty and QZ is objectwise Z.
- C = [1], Z = point: at the target object, two degree-zero vertices and
  one nonidentity edge give Δ¹; at the source they give a point. This tests
  the covariant free representable and last-face orientation.
- Nontrivial endomorphisms and invertible nonidentity arrows are allowed.
  An identity composite of adjacent nonidentity arrows does not discard
  the cell. Degenerate inner coefficient simplices also remain allowed.
- Arbitrary non-Kan and empty simplicial sets are included. There is no
  characteristic or scheme parameter, so characteristic and empty-scheme
  checks are inapplicable rather than excluded mathematical cases.
- Universes: u is explicit and arbitrary; C and its Hom sets are u-small,
  SSet has u-small degree sets, chains/Over-chains are u-small, and the
  simplex relation index is small. There is no unbound universe or extra
  equality between independent universes. The structure quantifies over
  all Z simultaneously as required by naturality, not over chosen Z only.

Independent searches (queries differ from the first worker's):

- `msearch.py ... leanfinder`: "Split simplicial replacement of a covariant
  diagram with representable cells and contraction at the terminal object".
  Eight hits, principally `SimplicialObject.Split` and `.Splitting`; these
  describe abstract splittings, not this full free-bar filtration theorem.
- `msearch.py ... loogle`: `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`.
  Twelve hits. I opened its fields: they use first-face extra degeneracies
  (s_n followed by δ_0 is identity), whereas this node requires terminal
  extra degeneracies and their explicit chain formula. It does not give
  this statement or its prescribed filtration.
- `msearch.py ... leansearch`: "Cellular skeletal filtration of the
  simplicial replacement of a small category diagram". Eight hits, including
  `SimplicialObject.sk`, `SSet.skeletonOfMono`, coskeleta and simplicial nerves;
  no full categorical free-cell statement.
- Direct `rg` of Mathlib AlgebraicTopology and CategoryTheory, the source
  project's WeilConjectures, and this project's lean/Sheaf for
  `simplicial.?replacement|skelet.*bar|bar.*skelet|free.?bar|terminal.*degenerac`
  and coend/realization definitions. Also checked the item's id and proposed
  namespace in upstream names, project Lean and upstream source: no exact
  declaration or name collision.
- I opened `SimplicialBarProjectiveResolution`: its general bar theorem
  does not give the image filtration, cell pushouts or contraction
  equations; importing this downstream theorem would create the already
  documented DAG cycle. `BousfieldKanComparisonCalculus` supplies generic
  diagonal replacements, not these outer stages and free-cell pushouts.
  `BisimplicialDiagonalSpaceColimit`'s `CoendDegree` is a quotient in each
  degree, not a simplicial coend object; `coendInclusion` targets the
  diagonal. Neither replaces this full theorem. The general enriched
  tensor realization requires a supplied `SimplicialTensorCotensor`, not
  the unconditional Cartesian SSet construction used here.
- Broader `rg` found Mathlib `Limits.Shapes.End`. I read
  `multispanShapeCoend`, `multispanIndexCoend`, `coend`, and `coend.ι`,
  and confirmed them with `msearch.py ... grep 'coend|curriedTensor'
  CategoryTheory/Limits/Shapes/End.lean`. This IS a usable existing notion
  for the quotient machinery, so I repaired the duplication rather than
  treating every search as a negative result.

Mismatch and repair: H4, the custom `realizationShape` and `realizationIndex`
reimplemented Mathlib's existing coend relation shape and index. Removed
both. Added only `realizationDiagram`, the specialization of the existing
Cartesian tensor bifunctor to P and stdSimplex, then defined `realization`
by `Limits.coend` and `realizationι` by `coend.ι`. The public import is now
`Mathlib.CategoryTheory.Limits.Shapes.End`; the node's `lean.declarations`
and explanatory `lean.note` are synchronized. This is an interface reuse,
not a correction of the node's mathematics: the quotient and its generator
formulas impose the identical relations. The main theorem signature is
unchanged, verbatim equal to `lean.statement`. No other mathematical
mismatch was found and no correct clause was rewritten.

H5/H6/H8/H9 check: all helper data is constructed, including the functor
laws of `overChain`; no object is chosen from the existence theorem.
The sole postponed theorem is the item, with whole proof `sorry`. Its
source/blueprint docstring carries all five proof steps, including the
nondegenerate pushout argument and sequential lifting. Every public helper
has its own source and blueprint docstring. No private definition, local
notation/instance, extra axiom, hidden hypothesis, or proved theorem was
introduced. Lines are at most 100 characters and autoImplicit is false.

Final compilation: the prescribed `scompile.py Q05
lem-coef-free-bar-cell-filtration
lean/Sheaf/AlgebraicTopology/FreeBarCellFiltration.lean`, run from this
sandbox, passed both its sandbox and library-path checks with no errors
or warnings (4.9 seconds and 6.7 seconds). An initial invocation from the
read-only repository had a relative-path FileNotFoundError; rerunning
from the authorized sandbox resolved it. During the reuse edit the first
compile diagnosed a missing `Functor.` qualification on `whiskeringLeft`;
that was repaired before the clean compile. No global build was run.

Delivery preflight: `deliver2.py Q05 lem-coef-free-bar-cell-filtration
--no-push` exited 0 and printed `OK (dry run): commit 4939bdfebe passes the
preflight and compiles; nothing pushed`. The staged packet was exactly this
report, the item's node copy, and `FreeBarCellFiltration.lean`. The node-only
comparison confirms that `lean` is the only changed field, its main signature
matches verbatim, there is one `sorry`, and the maximum Lean line width is 94.
