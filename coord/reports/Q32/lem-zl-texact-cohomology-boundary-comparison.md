## Worker report

Item: lem-zl-texact-cohomology-boundary-comparison. The module
`Sheaf.CategoryTheory.Triangulated.TExactCohomologyBoundaryComparison` constructs
four helpers belonging to the comparisons explicitly introduced by this node,
and states its boundary compatibility and triangle naturality as two theorems.
Both theorem proofs are `sorry`; every definition has actual data. There are no
new nodes, dependency repairs, statement changes, or disputed statements.

All declaration names below have prefix
`CategoryTheory.Triangulated.TStructure.`.

### Hypotheses and objects

- The two triangulated categories are `{C : Type uC}` and `{D : Type uD}`,
  each with explicitly bound independent object and morphism universes, and
  `Category`, `Preadditive`, `HasZeroObject`, `HasShift ... ℤ`, additive shifts,
  `Pretriangulated`, and `IsTriangulated` instances. These are exactly the
  recorded Mathlib encoding of def-weil-triangulated-category; there is no
  equality between any of the four universes.
- The t-structures are `(tC : TStructure C)` and `(tD : TStructure D)`.
  `_hC : tC.bounded = ⊤` and `_hD : tD.bounded = ⊤` retain the stated
  boundedness hypotheses on both theorems. The helper constructions need no
  boundedness, but the asserted results retain it.
- The exact functor is `(P : C ⥤ D) [P.CommShift ℤ] [P.IsTriangulated]`.
  `CommShift` includes the natural shift comparisons, their zero normalization,
  and addition coherence. Its `P.commShiftIso r` has components
  `P(M[r]) ≅ (PM)[r]`, in the node's specified direction.
- Preservation of BOTH halves in EVERY integer degree is precisely the
  upstream `[P.IsTExact tC tD]`: its `isLE` and `isGE` fields quantify over
  every object and `n : ℤ`, not just degree zero.
- The hearts are the existing full subcategories `tC.heart.FullSubcategory`
  and `tD.heart.FullSubcategory`. `texactHeartRestriction tC tD P` is P♥:
  `ObjectProperty.lift` applies P to underlying objects and morphisms, and
  the two existing `Functor.IsTExact.isLE_obj`/`isGE_obj` results certify
  membership in the target heart. Nothing is chosen or assumed about its maps.
- Heart-valued H⁰ is the dependency's actual `tC.homology₀` (and `tD.homology₀`),
  not a second cohomology construction. Degree-r cohomology is written as
  `shiftFunctor C r ⋙ tC.homology₀`, exactly H⁰(M[r]).

### Every conclusion and its canonical maps

- `texactHomologyZeroComparison tC tD P` constructs the natural isomorphism e
  from `P.eTruncGEIso tC tD (0 : ℤ)` on `τ≤0`, followed by
  `τ≥0(P.eTruncLTIso tC tD (1 : ℤ))`. Since `truncLT 1 = truncLE 0`, these
  are exactly the canonical α⁺ and α⁻ at degree zero from the recorded
  truncation-comparison dependency. Functor associators only rebracket the
  composite. `Functor.fullyFaithfulCancelRight tD.heart.ι` lifts that specific
  natural isomorphism through the full heart inclusion. It uses the actual
  preimage of the specified morphism, not a bare existence choice.
- `texactCohomologyComparison tC tD P r` is a natural isomorphism
  `(shiftFunctor C r ⋙ tC.homology₀) ⋙ P♥ ≅
   P ⋙ (shiftFunctor D r ⋙ tD.homology₀)`.
  Its components are exactly e at M[r], then `tD.homology₀` applied to
  `P.commShiftIso r`. Thus it is the node's canonical c^r, with naturality
  in M and inverses contained in the NatIso itself. No comparison is a
  hypothesis, an arbitrary isomorphism, or an independently supplied map.
- `(T : Triangle C) (_hT : T ∈ distTriang C)` is the specified distinguished
  triangle, with objects A, B, C encoded by `T.obj₁`, `T.obj₂`, `T.obj₃`.
  `P.mapTriangle.obj T` is PT; Mathlib defines its last arrow literally as
  `P.map T.mor₃ ≫ (P.commShiftIso (1 : ℤ)).hom.app T.obj₁`.
  Exactness of P sends `_hT` to distinguishedness of this same triangle.
- `heartCohomologyBoundary t T r` specializes the existing
  `t.homology₀.homologySequenceδ T r (r + 1) rfl` to
  `Functor.ShiftSequence.tautological t.homology₀ ℤ`. Its source and target
  are H^r(C) and H^(r+1)(A). This forces the standard shift associator and
  has no rotation sign. The specialization supplies real existing data;
  it is not a new definition of long exact cohomology.
- `texact_cohomology_boundary_comparison` states, for arbitrary `r : ℤ`,
  `P♥.map δ_T ≫ c^(r+1)_A = c^r_C ≫ δ_PT`. Lean writes composition
  left to right, so this is verbatim the node's mathematical equation
  `c^(r+1)_A ∘ P♥(δ_T) = δ_PT ∘ c^r_C`.
- The node's final sentence is
  `texact_cohomology_boundary_comparison_naturality`. It binds TWO
  distinguished triangles and an arbitrary `(φ : T ⟶ T')`. Its four
  conjuncts give the two boundary faces and the two comparison faces:
  H^r(φ₃) then δ_T' equals δ_T then H^(r+1)(φ₁);
  the same equation after P; and naturality of c^(r+1) at φ₁ and c^r at φ₃.
  The third-arrow equation is part of Mathlib's triangle morphism type.
  Applying P♥ to the first face gives the source face in the target heart.
  These four faces together with the main theorem on T and T' express
  exactly naturality of the comparison squares.

### Dependency declarations read and used

- def-weil-triangulated-category: Mathlib
  `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `CategoryTheory.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Triangulated`, and
  `CategoryTheory.Functor.IsTriangulated`/`mapTriangle` in
  `Mathlib.CategoryTheory.Triangulated.Functor`. These enter through the
  public dependency imports, with their original structures and arrows.
- def-weil-t-structure: `CategoryTheory.Triangulated.TStructure` in
  `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`, its `bounded`
  property, and `heart`/`mem_heart_iff` in
  `Mathlib.CategoryTheory.Triangulated.TStructure.Heart`.
- lem-weil-heart-short-exact-triangles: directly publicly imported
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
  The actual `homology₀` is its heart lift of `truncGELE 0 0`, with
  `isHomological_homology₀` supplying the standard long exact sequence.
  Its public imports supply the recorded truncation/heart declarations.
- lem-pod-texact-truncation-comparison: directly publicly imported
  `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`, whose
  `texact_truncation_comparison` characterizes the actual comparisons used.
  Its public upstream import supplies `Functor.IsTExact`, `eTruncLTIso`,
  and `eTruncGEIso` in
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`.
  The full signature and canonical counit/unit characterizations were read.
- Other reused APIs: Mathlib `ObjectProperty.lift`,
  `Functor.fullyFaithfulCancelRight`, `Functor.ShiftSequence.tautological`,
  `Functor.homologySequenceδ`, and `homologySequenceδ_naturality`.

### Source and edge cases

Read the local BBD PDF at printed pp. 29–31 (1.3.3 and 1.3.6) and 36–37
(1.3.16–17). As the node itself records, the boundary compatibility is a
formal consequence, not a separately printed BBD theorem. The two theorem
docstrings carry all six proof steps: full-heart restriction, composite e,
its naturality, shifted c, coherence at the shifted third arrow, the boundary
calculation, and the four naturality faces. Nothing in that proof is promoted
to an extra premise.

Checked before formulation: arbitrary negative, zero, and positive r (all
indices are integers); the identity functor (identity normalized comparisons);
split triangles (third arrow zero, hence both boundaries zero); zero terms
(including the all-zero triangle); identity and zero triangle morphisms;
and distinct object/Hom universes. The construction never inverts a boundary
or divides by a sign. No edge case is removed.

### Searches for an existing statement

All prescribed wrapper searches used group Q32 and this item id.

- `msearch.py leanfinder`, query "A t exact triangulated functor commutes
  with heart valued cohomology and connecting morphisms of distinguished
  triangles": 8 hits, including `Functor.map_distinguished_exact`,
  `Functor.comp_homologySequenceδ`, and `Functor.homologySequenceδ_comp`.
  None constructs the t-exact heart comparison and asserts its boundary square.
- `msearch.py loogle`, query `"homologySequenceδ", "NatTrans"`: 0 hits.
- `msearch.py grep`, query `IsTExact|eTrunc.*Iso|homologySequenceδ`, restricted
  to `CategoryTheory/Triangulated`: 20 hits. They provide truncation
  comparisons and standard boundaries/naturality, but not this square.
- `msearch.py leansearch`, query "Canonical cohomology isomorphisms of a t
  exact triangulated functor preserve boundary maps and are natural in
  triangle morphisms": 8 hits, including
  `SpectralObject.mapTriangulatedFunctor_δ'` and `Functor.IsTriangulated.mk`.
  Spectral-object transitions and short-complex comparison isomorphisms
  have different objects and do not state this heart-boundary comparison.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for t-exactness,
  cohomology comparisons, heart functors, and the proposed declaration names;
  item-id search in `lean/WeilConjectures`; and the upstream-name index:
  no existing exact statement or proposed-name collision.
  The generic upstream `eTruncGELTIsoApp` is the AMBIENT component of e,
  not a natural heart comparison or its boundary compatibility; its two
  component comparisons are reused. The landed A1 restriction comparison
  is a different ambient cohomology convention, specialized to endofunctors,
  and has no boundary assertion. No existing notion is privately replaced.

### Validation

The prescribed `scompile.py` compiled the sandbox and intended library module
cleanly against the live published build. Auto-bound implicits are disabled
by `set_option autoImplicit false`; all universes and variables are explicitly
declared. The only postponed proofs are the two named theorems belonging to
this node. The prescribed delivery dry run and final delivery follow.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
