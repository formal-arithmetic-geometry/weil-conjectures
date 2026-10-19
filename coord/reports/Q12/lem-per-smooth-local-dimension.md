## Worker report

Item: `lem-per-smooth-local-dimension`. The module
`Sheaf.AlgebraicGeometry.SmoothLocalDimension` states two theorems with `sorry` proofs:
`AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_smooth` and
`AlgebraicGeometry.topologicalKrullDimAt_asFiber_eq_of_smoothOfRelativeDimension`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` record changes.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-smoothness-dimension` (Tag 0AFF, lines 7565–7594), including the immediately
preceding warning that these are topological dimensions, and
`definition-smooth-relative-dimension` (Tag 02G2, lines 7236–7260).
The source agrees with the node.

Hypothesis and clause correspondence:

- Schemes P and Q: `(P Q : Scheme.{u})`, with arbitrary explicitly declared universe `u`.
- Both schemes locally Noetherian: `[IsLocallyNoetherian P] [IsLocallyNoetherian Q]`.
- The named morphism: `(g : P ⟶ Q)`.
- Smoothness: `[Smooth g]` in the main formula; the constant-dimension clause uses
  `[SmoothOfRelativeDimension d g]`, which itself entails smoothness (Mathlib's
  `SmoothOfRelativeDimension.smooth`). No extra smoothness assumption is required there.
- Any source point: `(p : P)` in both declarations, without closedness or rationality.
- Its image q: the expression `g p`, so no equality binder or choice of image is needed.
- The scheme-theoretic fibre and its corresponding point: `g.asFiber p` has type
  `g.fiber (g p)`; the latter is the pullback along `Q.fromSpecResidueField (g p)`.
  The definition of `asFiber` is the inverse of the fibre homeomorphism applied to
  `⟨p, rfl⟩`; its projection is exactly `p`.
- Local dimension of P: `topologicalKrullDimAt p`.
- Local dimension of Q at q: `topologicalKrullDimAt (g p)`.
- Local dimension of the fibre: `topologicalKrullDimAt (g.asFiber p)`.
- The formula is the equality of the first term with the sum of the latter two,
  using addition in `WithBot ℕ∞`.
- The definition used throughout is the recorded `topologicalKrullDimAt`, whose data
  is `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`. It is not ring Krull
  dimension of a stalk. Its codomain allows infinity; at an actual point it is nonnegative.
- The final clause “constant relative dimension d ≥ 0, last summand d” is the second
  theorem with `(d : ℕ) [SmoothOfRelativeDimension d g]`, concluding
  `topologicalKrullDimAt (g.asFiber p) = (d : WithBot ℕ∞)`.
  Together with the first equality this also gives `dim_p P = dim_q Q + d`.

Dependency declarations read and reused:

- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` (lines 62–66) and
  `AlgebraicGeometry.SmoothOfRelativeDimension` (lines 129–139), including their
  affine-local docstrings. The recorded Mathlib classes give both notions unchanged.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (lines 56–59). This is the recorded equivalent
  every-affine-open form of the affine-cover definition.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`
  (lines 37–48), `fiberHomeo` (lines 102–104), and `asFiber` (lines 115–117).
  Read the full pullback and point signatures and their docstrings.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`
  (lines 341–344), the neighbourhood infimum used in both conclusions.

Proof plan imports also retain the stated proof dependencies:
`Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`, declaration
`AlgebraicGeometry.smooth_differentials_free_rank_fibre_dimension`;
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`, declaration
`AlgebraicGeometry.Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`;
`WeilConjectures.Mathlib.Topology.KrullDimension`, declaration
`IsOpen.topologicalKrullDimAt_eq`; and the recorded Mathlib modules defining open
immersions, flatness, finite presentation and finite type. The smooth-flat and
finite-presentation-on-affines Mathlib leaves are supplied by
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` respectively.
`lem-per-flat-constant-relative-dimension` has neither a Lean record nor a Mathlib
match in the inspected base; it is used only by the postponed proof, not by the
statement, so there is no module to import for it. The docstring records all six
steps of the node, with the last step attached to the second theorem.

Edge cases checked before writing:

- Empty source: there is no `p`, so both assertions are vacuous. An empty target
  admitting such a morphism likewise supplies no source point.
- Identity or open immersion: fibre dimension zero, giving preservation of local
  dimension. No surjectivity is assumed.
- A positive-dimensional affine space over a field, including its generic point:
  local topological dimension is its dimension at every point, unlike stalk dimension.
  In particular the generic point of the affine line has topological local dimension
  one but its local ring has dimension zero; the Lean conclusion uses the correct one.
- Disjoint components of different smooth relative dimensions: the first formula uses
  the individual fibre at `p` and imposes no global constant relative dimension.
- `d = 0` is allowed by the natural-number binder; no characteristic assumptions occur.
- Infinite base local dimension is permitted by `WithBot ℕ∞` and its extended addition;
  no finite-dimensional or global Noetherian hypothesis has been inserted.
- No separatedness, quasi-compactness, rational-point, or global finite-type assumption
  occurs in either signature. Scheme and coefficient-field sizes have not been restricted.

Searches actually run (2026-10-17 UTC):

1. `msearch.py Q12 lem-per-smooth-local-dimension leanfinder` with query
   “For a smooth morphism of locally Noetherian schemes local topological dimension at a
   point equals local topological dimension of the base plus dimension of the fibre”.
   Eight results concern `IsSmoothOfRelativeDimension`, standard smooth charts,
   composition and smoothness; none states the sum formula.
2. `msearch.py ... loogle '"Smooth", "topologicalKrullDimAt"'`: zero hits.
3. `msearch.py ... grep
   '(smooth|Smooth).*(krullDim|KrullDim|localDim)|(krullDim|KrullDim|localDim).*(smooth|Smooth)'
   AlgebraicGeometry`: zero Mathlib hits.
4. `rg` in `WeilConjectures` and `lean/Sheaf` for the node id and
   `smooth.*(local.*dimension|topologicalKrullDimAt)|topologicalKrullDimAt.*smooth`:
   no exact formula. The upstream result
   `AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension` concerns a
   scheme smooth over a FIELD, not an arbitrary locally Noetherian target, so it cannot
   be attached to this node. Read its full signature and docstring (lines 448–461).
5. Broader `rg` for `topologicalKrullDimAt.*[+=]|topologicalKrullDimAt_eq` in the upstream
   and side AlgebraicGeometry directories found fibre comparisons and dimension results
   with additional field/quasi-finite/flat-composition hypotheses, not this statement.
6. The proposed new full names were searched in `dag/lean_names_upstream.json`, Mathlib,
   `WeilConjectures`, and `lean/Sheaf`: neither already occurs.

No statement dispute was found. Compilation uses only the prescribed `scompile.py` wrapper;
all theorems deliberately remain unproved at stage 2.

## Second reading by Q12

This is the author's self-check for direct delivery, not a claim of an independent
worker review; the maintainer supplies the independent review under the dispatch brief.
I reread the node, the source text, and the completed module. The two locally Noetherian
binders, the smoothness binder and arbitrary point reproduce exactly the main sentence.
`g p` binds the image without changing it; `g.asFiber p` uses the canonical fibre point,
not an arbitrary lift or an assumption that it exists. Both sides use the recorded
neighbourhood infimum. I checked that the second declaration states the final fibre
summand clause with `d : ℕ`, instead of silently omitting that clause. Its relative
smoothness class already contains smoothness; both locally Noetherian hypotheses are
retained. No mismatch, correction, extra notion, or dependency repair was needed.

Validation: `scompile.py Q12 lem-per-smooth-local-dimension` returned exit code 0;
both sandbox and library per-file compilation completed without errors or warnings.
