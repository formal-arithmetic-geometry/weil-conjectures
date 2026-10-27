## Worker report

The module `Sheaf.AlgebraicGeometry.MultisectionComponentOverlapNeighbourhood` states
`AlgebraicGeometry.multisection_component_overlap_neighbourhood` with `sorry` as its
entire proof. Four fully constructed definition helpers name the concrete objects of
this same statement: `multisectionComponentLocus`, `multisectionOverlapProjection`,
`multisectionOverlapMap`, and `multisectionOverlapSection`. They introduce no
independent notion, arbitrary map, chosen witness, or postponed construction proof.
The last two are respectively the existing canonical `baseChangeMap` and a
`pullback.lift` with compatibility composed from existing equalities.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 057I,
`lemma-descent-connected-fibres`, lines 13088–13193, especially the paragraphs from
`X_Z` through the equality over `W`. The node isolates exactly that portion of the
proof. The later shrinking downstairs and descent use finite local freeness; the
portion formalized here uses only openness of two loci and continuity of two sections.
Thus the item's explicit absence of assumptions on `p` is respected.

Hypotheses and objects, clause by clause:

- The three schemes and the two morphisms are `{X B Z : Scheme.{u}}`,
  `(f : X ⟶ B)` and `(p : Z ⟶ B)`. The map `σ` and the triangle equation are
  `(σ : Z ⟶ X)` and `(hσ : σ ≫ f = p)`.
- Flatness is `[Flat f]`. Finite presentation is exactly
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`, using the
  convention in `def-weil-pbc-scheme-conventions`, including quasi-separatedness.
- Geometric reducedness of every fibre is
  `hred : ∀ b : B, GeometricallyReduced (f.fiberToSpecResidueField b)`.
- `Y` is `pullback f p`, `g` is `pullback.snd f p`, and the section is exactly
  `pullback.lift σ (𝟙 Z) (hσ.trans (Category.id_comp p).symm)`. Its projections
  are `σ` and `id` by the pullback lift equations. This is not an arbitrary section.
- `C` is `multisectionComponentLocus f p σ hσ`. Its data is the set of `y` in the
  connected component of the section value over `g y`, inside `g ⁻¹' {g y}`.
  The homeomorphism `g.fiberHomeo` in the fibre dependency identifies this with
  the union of the components in the scheme-theoretic fibres. This is also exactly
  the encoding in both the recorded component-openness and cartesian-comparison lemmas.
- `R` is `pullback p p`. Its structure map `q` is `pullback.fst p p ≫ p`;
  `pullback.condition` identifies it with `pullback.snd p p ≫ p`.
  `multisectionOverlapProjection p i` is an actual morphism over `B`, with
  underlying map `fst` for `i = 0`, and `snd` for `i = 1` (`i : Fin 2`).
- `X ×_B R` is `pullback f (pullback.fst p p ≫ p)` and `h` is its second
  projection. `multisectionOverlapMap f p i` is the canonical `a_i`, implemented
  by `baseChangeMap` on the corresponding morphism over `B`.
  `multisectionOverlapSection f p σ hσ i` is the universal lift
  `(pr_i ≫ σ, id_R)`; it is precisely the induced section `s_i`.

Conclusion, clause by clause:

- The first conjunct `IsOpen (multisectionComponentLocus f p σ hσ)` is openness of `C`.
- The second conjunct quantifies `i : Fin 2` and equates `a_i ⁻¹' C` with the
  `connectedComponentIn` set of `s_i` inside each fibre of `h`, without restricting
  to a neighbourhood. Both indices are included.
- The final conjunct starts `∀ b₀ : B, GeometricallyConnected
  (f.fiberToSpecResidueField b₀) →`. This is the stated geometric connectedness
  over the actual residue field `B.residueField b₀`, including nonemptiness.
  Only this neighbourhood assertion depends on `b₀`; the preceding assertions
  remain available without any geometrically connected fibre.
- `∃ W : (pullback p p).Opens` is an open subset of `R`, with no compactness condition.
  `(pullback.fst p p ≫ p) ⁻¹' {b₀} ⊆ (W : Set ↥(pullback p p))` contains
  the entire fibre of `q` as a subset, including an infinite or empty fibre.
- The next two conjuncts are exactly `s₀ '' W ⊆ a₁ ⁻¹' C` and
  `s₁ '' W ⊆ a₀ ⁻¹' C`, in that order. Neither direction is omitted.
- The last conjunct is equality of the two intersections of `h ⁻¹' W` with
  `a₀ ⁻¹' C` and `a₁ ⁻¹' C`. It asserts equality of subsets, not just an
  implication on the two section images.
- There is no typeclass, hypothesis, or restriction on `p` beyond being the given
  scheme morphism. Every universe and variable is explicitly bound.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with its
  stalkwise interpretation and base-change instances (`Flat.isStableUnderBaseChange`).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` and its base-change instances.
- The conventions dependency has a convention-only record. Its finite-presentation
  clause is rendered by the three classes above. `QuasiCompact` and `QuasiSeparated`
  were read in their corresponding Mathlib morphism modules.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: the recorded classes
  `GeometricallyIntegral`, `GeometricallyIrreducible`, `GeometricallyReduced`.
  The node also covers connectedness, supplied by the separately imported
  `Mathlib.AlgebraicGeometry.Geometrically.Connected.GeometricallyConnected`.
  All four class signatures and docstrings were read; the present statement uses
  precisely the reduced and connected classes on the fibre-to-residue-field morphisms.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the module's recorded
  canonical pullback, induced-section and fibre conventions. Scheme base change is
  `CategoryTheory.Limits.pullback`, with its `fst`, `snd` and `lift`; morphism base
  change reuses `AlgebraicGeometry.baseChangeMap`, whose actual declaration and
  docstring were read in `WeilConjectures.AlgebraicGeometry.PicardFunctor`.
  This specializes the dependency's scheme-base-change clause, not its module clause.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponentIn`.
  `ConnectedSpace` is the Mathlib match for `def-weil-connected-scheme`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, and `fiberHomeo`. The full signatures and fibre
  homeomorphism docstring justify the underlying fibre-subspace encoding.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  openness of a subset is the ordinary `IsOpen`, with its associated open subscheme.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the geometric fibre hypotheses use the canonical
  morphisms into `Spec (B.residueField b)` from the fibre module.
- Proof imports are `Sheaf.AlgebraicGeometry.FlatReducedSectionComponentOpen`
  (`isOpen_section_component_of_flat_of_geometricallyReduced_fibers`) and
  `WeilConjectures.AlgebraicGeometry.SectionComponentPullback`
  (`section_component_preimage_of_isPullback`). Both signatures and full docstrings
  were read; these are exactly the two substantive component inputs of the proof.
  The other proof dependencies are available from the Mathlib and base-change
  statement imports. There is no unavailable proof import or import cycle to omit.

Edge cases checked before stating:

- If `Z` is empty, both pullbacks over `Z` are empty, `C` is empty and open,
  and the neighbourhood can be empty. There is no nonemptiness hypothesis on `Z`.
- If `X` is empty, the existence of `σ : Z → X` forces `Z` empty; this reduces
  to the preceding case. An empty `B` likewise excludes a point `b₀`.
- If `q⁻¹(b₀)` is empty while `R` is nonempty, `W = ∅` satisfies every
  neighbourhood clause. No witness point in that fibre is required.
- If `q⁻¹(b₀)` is infinite, the intersection of the two section preimages is
  still one open set containing all of it. No finite intersection over fibre
  points or finiteness of `p` is used.
- Other fibres of `f` may be disconnected. Equality of the component loci is
  asserted only after restriction to `h⁻¹(W)`, as in the source.
- An empty `X_b₀` does not satisfy geometric connectedness: `ConnectedSpace`
  includes `Nonempty`. This matches the connectedness dependency exactly.
- The index is `Fin 2`, so both projections exist with distinct indices even
  when their underlying maps happen to agree. Characteristic is unrestricted.

Searches for an existing statement or notion (2026-10-24):

- `msearch.py ... leanfinder` with “Connected components through two sections of
  a flat finitely presented scheme with geometrically reduced fibres agree over
  an open neighbourhood of a geometrically connected fibre”: eight hits, led by
  `AlgebraicGeometry.ExistsHomHomCompEqCompAux.exists_eq`, `Flat.generalizingMap`
  and spreading-out lemmas; none states this result.
- `msearch.py ... leansearch` with “Relative connected components through sections
  agree near a geometrically connected fibre”: eight hits, including
  `Topology.IsQuotientMap.preimage_connectedComponent`, `image_connectedComponent`
  and `preimage_connectedComponent_connected`; none is the scheme overlap result.
- `msearch.py ... loogle '"GeometricallyConnected", "connectedComponent"'`:
  zero hits.
- `msearch.py ... grep
  'section.*component.*(overlap|neighbou)|component.*multisection|multisectionOverlap'`:
  zero Mathlib hits.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
  `multisection`, `connectedComponentIn`, and component overlap/neighbourhood
  phrases found the recorded component-openness and pullback lemmas, slicing
  results, and unrelated overlap constructions; no declaration states this item.
  Direct search for the item ID in `lean/WeilConjectures` found no declaration.
  Search of `dag/lean_names_upstream.json` for the new helper/theorem stems had no match.
  No replacement definition of a Mathlib or recorded project notion was written.

Compilation: prescribed `scompile.py Q67 <item> <file>` passed for both its sandbox
probe and the actual module name, with no warnings or errors. The initial
elaboration error came from writing `Set (pullback ...)`, which allowed Lean to
infer a pullback in `Type`. Explicit point-type coercions `Set ↥(pullback ...)`
and `x : ↥(pullback ...)` repaired it without changing the mathematics.

No node fault, statement correction, new node or dependency repair is needed.
Only the item's `lean` field is changed.

## Second reading by Q67

A separate rereading by the assigned worker reopened the final module and the
node's statement against the Tag 057I source. No other agent was started, as the
dispatcher brief prohibits that; the maintainer supplies the independent review.

The three morphisms and triangle equation are present. The four assumptions on
`f` are exactly flatness, local finite presentation, quasi-compactness and
quasi-separatedness, and `hred` quantifies all base points. In the helper data,
index zero is `fst` and index one is `snd`; both lie over the same structure map
by `pullback.condition`. `baseChangeMap` preserves the `X` projection and applies
the specified `R → Z` projection, and each section is the canonical lift of
`pr_i ≫ σ` and `id`, so the construction has the required direction.

I reread each conclusion: openness is independent of `b₀`; the component comparison
has both indices; geometric connectedness is imposed on the correct fibre-to-
residue-field morphism; `W` contains all of `q⁻¹(b₀)`; the first image inclusion
uses section zero and component one, and the second swaps them; the last equality
restricts both loci by precisely the same `h⁻¹(W)`. There is no implicit condition
on `p`. All empty and infinite fibre cases listed above remain admitted.

The definition bodies contain only actual sets and canonical morphisms, with no
`Nonempty` choice or postponed data. The only postponed proof is the named main
theorem, whose docstring carries the complete five-step DAG proof and sources.
The explicit point-type coercions are the only compile-driven adjustment; no
hypothesis, conclusion or node text was changed. No remaining mismatch was found.
