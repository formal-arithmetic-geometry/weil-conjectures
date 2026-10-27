## Worker report

The delivery states `AlgebraicGeometry.groupoid_cohenMacaulayLocus_descends` in
`Sheaf.AlgebraicGeometry.GroupoidCohenMacaulayLocusDescent`, with its sole theorem
proof `sorry`. It supplies the missing pointwise and global Cohen--Macaulay
predicates in `Sheaf.AlgebraicGeometry.CohenMacaulayMorphismAtPoint`. Both definitions
have their full propositional bodies and use the existing flatness, fibre, depth,
and dimension definitions. There are no dependency-interface repairs and no
statement correction. The item's original statement and proof remain verbatim;
its statement dependencies gain the new definition node.

Source checked: `more-groupoids.tex`, lemma-local-source (04LH), its proof including
both division squares and the identity-section argument, and
remark-local-source-apply (047W), item (5). Also checked `more-morphisms.tex`,
definition-CM (045R) and lemma-flat-finite-presentation-CM-open (045U). The latter
requires flatness before applying the fibre-locus openness result; the proof
docstring first restricts to the open flat locus. The Stacks definition assumes
locally Noetherian fibres throughout. The item's explicit definition instead
includes Noetherianity of the relevant fibre stalk in its pointwise predicate.
These agree in this application, because local finite presentation implies
locally Noetherian fibres. The new definition records this distinction explicitly.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes S,U,R,B in the stated universe | Explicit `universe u` and `{S U R B : Scheme.{u}}`; `set_option autoImplicit false`. No derived categories or sites occur, so the size-convention node requires no further structure here. |
| Groupoid structure s,t,e,i,c | Binders `(s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)` and `hG : IsGroupoidScheme s t e i c`, using the recorded groupoid definition. |
| All structure morphisms over S | `uS : U ⟶ S`, `rS : R ⟶ S`, `_hs`, `_ht`, `_he`, `_hi`, `_hc`. The composition equation uses the first projection; the two projections have the same composite to S by the pullback condition and the source/target equations. |
| Flatness of s and t | `[Flat s] [Flat t]`. |
| Local finite presentation of s,t,g | The three corresponding `[LocallyOfFinitePresentation ...]` binders. |
| A morphism g:B→U | `(g : B ⟶ U)`. The structure map of B over S is its composite with uS. |
| H=B×[g,U,t]R | `pullback g t`; no replacement of this scheme by a set of pairs. |
| p=pr_B and h=s∘pr_R | `pullback.fst g t` and `pullback.snd g t ≫ s`. They are written out, so no helper with an arbitrary choice of a map is needed. |
| Flatness at x | In `IsCohenMacaulayAtPoint`, `(f.stalkMap x).hom.Flat`. This is exactly flatness of the source local ring over the target local ring. |
| Fibre local ring at x | `(f.fiber (f x)).presheaf.stalk (f.asFiber x)`, using the canonical point from Mathlib's `fiberHomeo`. |
| The fibre local ring is Noetherian | `IsNoetherianRing` of that stalk. |
| Depth equals Krull dimension | `IsLocalRing.depth` of that stalk as its own module, coerced to `WithBot ℕ∞`, equals `ringKrullDim` of the same stalk. No dimension-at-a-point substitute is used. |
| Cohen--Macaulay at every point | `Scheme.Hom.IsCohenMacaulay f` is definitionally `∀ x : X, f.IsCohenMacaulayAtPoint x`. |
| There exists an open subscheme W⊆B | `∃ W : B.Opens`; its scheme and inclusion are `W.toScheme` and `W.ι`. |
| Its inverse image is exactly the CM locus, with open subscheme structure | The first conjunct is `∀ z, z ∈ (pullback.fst g t ⁻¹ᵁ W) ↔ Scheme.Hom.IsCohenMacaulayAtPoint (pullback.snd g t ≫ s) z`. The left side is an actual Mathlib open, not an arbitrary scheme with the same point set; thus the equality supplies the canonical open subscheme structure. |
| The restriction is CM | The second conjunct applies `Scheme.Hom.IsCohenMacaulay` to `(pullback.fst g t ⁻¹ᵁ W).ι ≫ (pullback.snd g t ≫ s)`. |
| The restriction is locally finitely presented | The third conjunct is `LocallyOfFinitePresentation` of exactly that composite. |
| CMness at (b,e(g(b))) implies b∈W | The last conjunct evaluates at the image of b under `pullback.lift (𝟙 B) (g ≫ e) ...`. The compatibility proof uses `hG.identity_target`. This is the canonical section point, rather than an arbitrary point with those two projections (which would not specify a point of a scheme fibre product). |

Recorded dependency declarations used, after reading their source signatures and
docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
  Its composition is ordered c(a,b)=a∘b, with s(a)=t(b), exactly as in the node.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` identifying the pointwise local-ring condition.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth` and `IsLocalRing.depth`.
  The self-module is finite, so no extra finiteness binder is necessary.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim : WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `pullback.lift`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  realized here by the canonical inclusion of an open subscheme.
- `def-weil-size-convention` is the recorded metatheoretic convention; explicit
  universe binders implement its role in this scheme-only statement.

The proof-only imports include finite-presentation and qcqs permanence, open
immersion etaleness, `isLocallyNoetherian_fibre_of_finite_presentation_restrict`,
`isOpen_fibre_depth_eq_ringKrullDim`, `scheme_etale_source_target_properties`,
`pointwise_flatness_base_change`, and
`stalk_depth_eq_ringKrullDim_iff_of_field_extension`. Fibre base change is in the
already public fibre module. `lem-sfb-relative-flat-affine-charts` has neither a
usable Lean record nor a mathlib match in the current DAG, and therefore has no
module to import; its mathematical role remains explicit in proof step 2. It is
a proof dependency only, not a missing notion needed to type this statement.

Edge cases checked mathematically before writing:

- If B is empty then H is empty and W can be empty. Every universal pointwise
  clause includes this case; no nonemptiness hypotheses occur.
- For the identity groupoid, H identifies with B, p is the identity, and the
  conclusion is precisely openness of the pointwise CM locus of the lfp map g.
- For g=id_U, H identifies with R and the claim expresses saturation of the CM
  locus of s along t. No surjectivity of g is imposed.
- A morphism can have CM fibre stalks without being flat at the point. Such
  a point is excluded by the first conjunct of `IsCohenMacaulayAtPoint`; no
  global flatness assumption on h was inserted.
- No Noetherian hypothesis on S,U,R, or B is inserted. Only the actual fibre
  stalk's Noetherianity is part of the predicate. This also permits positive
  characteristic and arbitrary residue fields.
- A stalk at an actual scheme point is a nonzero local ring, so the bottom
  value of `ringKrullDim` for the zero ring creates no unintended extra case;
  the definition nevertheless compares depth and dimension in their full
  common extended value type and imposes no dimension bound.

Searches made (the wrapper results are recorded verbatim in `searches.jsonl`
and the new node's `mathlib_searches`):

- LeanFinder: “For a flat locally finitely presented groupoid the Cohen Macaulay
  locus of B times U R descends to an open of B”. Eight hits concerning smooth,
  etale and unramified loci, flatness, and free loci; none states this theorem.
- Loogle: `"AlgebraicGeometry", "CohenMacaulay"`. Zero hits.
- LeanSearch: “A scheme morphism is Cohen Macaulay at a point if flat and its
  fibre local ring is Noetherian with depth equal to Krull dimension”. Eight
  hits concerning flatness and smoothness; none gives the combined predicate.
- LeanFinder: “Cohen Macaulay at a point of a scheme morphism means flat with
  Noetherian Cohen Macaulay fibre stalk”. Eight hits concerning flatness and
  smoothness; no pointwise CM definition.
- Mathlib grep, `Cohen.?Macaulay|cohenMacaulay|IsCohenMacaulay`, subdirectory
  AlgebraicGeometry: zero hits.
- Project rg of both `lean/WeilConjectures` and `lean/Sheaf`, by CM names and
  definition keywords: existing CM theorems use inline depth equalities.
  The existing groupoid double-restriction and maximal-slice theorems have
  different conclusions, and FlatRelationCMOpen assumes an equivalence relation
  and gives a different open. No matching predicate or theorem was found.
- `rg` for this item's id in `lean/WeilConjectures` and for the chosen names in
  `dag/lean_names_upstream.json`: no hits. The quasi-finite-locus descent sibling
  is about a different property; its relative-groupoid and identity-section
  encoding provides a compatible convention, not a duplicate assertion.
- DAG grep for Cohen--Macaulay at a point and CM morphism: no definition node;
  theorem nodes express it inline. `tools/blueprint_refs.py search 'Cohen
  Macaulay'` returns zero blueprint nodes. The ancestor query returns no id,
  consistently with the item's inherited null ancestor.

There is no STATEMENT-DISPUTED flag and no source or item fault requiring a
correction. The newly named predicates express exactly the definition already
present in the item's statement. The canonical pullback lift includes only an
elementary compatibility proof, not a postponed theorem or new hypothesis.

Validation: both delivered modules compiled individually through the prescribed
`scompile.py` wrapper against the live published library. There were no errors or
unexpected warnings. The definition module contains no `sorry`; the theorem has
one `sorry` with the complete seven-step proof in its docstring. The delivery
dry run and push are performed after this report is written.

## New nodes

`def-sfb-cohen-macaulay-morphism-at-point` owns
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAtPoint` and
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay`. It introduces no extra geometric
construction: the predicates are the conjunction of local flatness and the
Noetherian depth-equals-dimension condition at `f.asFiber x`, and its universal
quantification over source points. Its source is Stacks 045R (1),(2), using
exactly the explicit fibre-stalk Noetherian convention in the assigned item.
Under locally Noetherian fibres this is the Stacks definition. The searches
above found no existing definition node or declaration; in particular the
already landed CM theorems have only inline conditions. It cites the recorded
scheme, flatness, fibre, Noetherian, depth, and ring-dimension definitions. Its
chapter and unit match the assigned item, and the null blueprint ancestor is
inherited; the via list prefixes the assigned item's id. The assigned item's
statement dependencies now cite this node.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
