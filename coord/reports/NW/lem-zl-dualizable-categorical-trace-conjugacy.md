## Worker report

Existing declaration: `CategoryTheory.MonoidalCategory.trace_eq_of_iso`, in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`, lines 92–96.
The delivery attaches that exact existing theorem; it adds no Lean module,
definition, theorem, or postponed proof and changes only the item's `lean` field.

I read the item, every statement dependency, the proof-dependency Mathlib matches,
the complete signatures and surrounding variables, and the source blueprint proof
`sec-trace-formula/sk-c-proper-global/lem-trf-local-frobenius-conjugacy.proof.md`,
part (3). Its final paragraph invokes conjugacy invariance for the stalk complexes.
The abstract theorem is exactly the implementation cited by the item's source.
No repair note for this item was present.

Hypotheses and conclusion, clause by clause:

- The braided monoidal category is the ambient `{C : Type*} [Category C]
  [MonoidalCategory C] [BraidedCategory C]` preceding the theorem. Object and
  morphism universes are unrestricted and independent; no smallness, symmetry,
  closedness, additivity, or rigidity of the entire category is assumed.
- The two objects `P,Q` are `{X X' : C}`.
- Their chosen right duals are `[HasRightDual X] [HasRightDual X']`.
  Mathlib's class stores a right-dual object and an `ExactPairing`, whose
  evaluation, coevaluation, and triangle equalities are the node's duality data.
- The endomorphisms `u,v` are `(f : X ⟶ X)` and `(f' : X' ⟶ X')`.
- The isomorphism `a : P ≅ Q` is `(w : X ≅ X')`.
- The equality `a ∘ u = v ∘ a` is
  `(h : f ≫ w.hom = w.hom ≫ f')`, since Lean writes composition in diagram order.
- The conclusion is `trace f = trace f'`, using the dependency's exact
  `CategoryTheory.MonoidalCategory.trace`. Its codomain is `𝟙_ C ⟶ 𝟙_ C`,
  so this is equality in the endomorphisms of the monoidal unit.

The recorded signature is copied verbatim from the existing theorem, from
`theorem` through the conclusion before `:=`, preserving its inherited binders.

Dependency declarations read and used:

- `sk-d-trace`: `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`,
  `CategoryTheory.MonoidalCategory.trace` (line 78). Its real construction is
  `η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ`, exactly the node's
  coevaluation, endomorphism tensor identity, forward braiding, and evaluation.
- Proof leaf `lem-zl-right-dual-mate-identities`: `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`,
  `CategoryTheory.rightAdjointMate`, `CategoryTheory.coevaluation_comp_rightAdjointMate`,
  `CategoryTheory.rightAdjointMate_comp_evaluation`. These give the two naturality
  equations for the mate without a braiding assumption. The original mate
  docstring reverses the written arrow, but its actual signature correctly reads
  `Yᘁ ⟶ Xᘁ`, and the recorded dependency uses that signature.
- Proof leaf `lem-sfb-braiding-naturality`: `Mathlib.CategoryTheory.Monoidal.Braided.Basic`,
  `CategoryTheory.BraidedCategory.braiding_naturality`, the exact tensor naturality
  equation after reversing composition notation.

The existing proof uses `trace_comp_comm`, implemented immediately above from the
same mate identities and braiding naturality. It cancels the intertwining
isomorphism to express `f' = w.inv ≫ f ≫ w.hom`, then uses cyclicity and cancels
`w.hom ≫ w.inv`. Thus no extra proof dependency or alternate trace is needed.

Edge cases checked by reading the unrestricted signature and trace construction:
identity isomorphism and identity endomorphisms; zero endomorphisms or zero objects
when available (no zero structure is required); the monoidal unit; arbitrary
chosen right dualities, with no compatibility hypothesis on the isomorphism;
and genuinely braided, nonsymmetric categories. The theorem never uses symmetry.
There is no finite-dimensionality or field assumption. The empty category has
no pair of objects to instantiate, as also in the informal universal statement.
No statement correction or disputed statement is needed.

Searches (2026-10-21):

- `msearch.py leanfinder`: “Categorical trace is invariant under an intertwining
  isomorphism between right dualizable objects in a braided monoidal category”.
  Eight infrastructure hits (rightDualIso, exactPairingCongrRight/Left, and mate
  identities); no Mathlib trace theorem.
- `msearch.py loogle`: `CategoryTheory.MonoidalCategory.trace_eq_of_iso,
  CategoryTheory.HasRightDual`. No hits; the upstream project theorem is not
  indexed by the Mathlib service.
- `msearch.py grep`: `trace_eq_of_iso|trace_comp_comm|def trace` in
  `CategoryTheory/Monoidal`. No Mathlib hits.
- `msearch.py leansearch`: “Categorical trace invariant under conjugation of
  dualizable objects”. Eight hits about ordinary linear trace or bicategorical
  conjugation; no matching Mathlib categorical-trace declaration.
- `rg` in `lean/WeilConjectures` with
  `trace_eq_of_iso|trace_comp_comm|def trace|lem-zl-dualizable-categorical-trace-conjugacy`
  finds the exact trace definition and theorem at lines 78 and 92 in the recorded
  module, plus downstream applications. The separate search for the item id
  finds no tagged implementation; the source citation supplies the exact match.
- `rg` in `lean/Sheaf` with
  `trace_eq_of_iso|trace_comp_comm|categoricalTrace.*[Cc]onj|trace.*conjug`
  finds uses of the upstream theorem in TraceFormalLaws and ChainSupertrace,
  and specialized perfect-complex trace statements, rather than a new definition
  needed by this node.
- `rg trace_eq_of_iso dag/lean_names_upstream.json` returns no index entry;
  direct reading of the upstream module establishes the declaration and type.

Validation: the prescribed delivery dry run compiles an existing-declaration
`#check` probe on the server and runs the maintainer's preflight. No source module
is delivered, so no new-file compilation is necessary.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
