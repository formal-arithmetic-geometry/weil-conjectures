## Worker report

The module `Sheaf.TraceFormula.FlatLFPCMLocusFibreDense` states
`flat_lfp_cm_locus_fibre_dense`. It uses Mathlib's scheme morphisms, scheme-theoretic
fibres (`Scheme.Hom.fiber`), flatness (`AlgebraicGeometry.Flat`), and locally finite
presentation (`AlgebraicGeometry.LocallyOfFinitePresentation`). For a point `x` of the
fibre, the ring rendered by the statement is
`(f.fiber s).presheaf.stalk x`. The Cohen--Macaulay condition is rendered clause by
clause as `IsNoetherianRing` of that ring together with
`(IsLocalRing.depth (R := ...) ...) : WithBot ℕ∞ = ringKrullDim ...`.

The hypotheses are rendered as follows: `f : X ⟶ S` is a morphism of schemes;
`[Flat f]` is flatness; `[LocallyOfFinitePresentation f]` is locally finite
presentation; `s : S` is an arbitrary base point; and `O : Set (f.fiber s)` is an
arbitrary open subset, with explicit hypotheses `IsOpen O` and `O.Nonempty`.
The conclusion `∃ x : f.fiber s, x ∈ O ∧ ...` says exactly that every nonempty open
meets the fibrewise Cohen--Macaulay locus. No nonemptiness of the fibre is assumed,
so the assertion is vacuous for an empty fibre. The affine zero-ring and empty-open
cases remain allowed by the unrestricted scheme and set binders.

Dependency declarations used:

- `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme` (dependency `def-pc-scheme`).
- `AlgebraicGeometry.Flat` from `Mathlib.AlgebraicGeometry.Morphisms.Flat`
  (dependency `def-weil-flat-morphism`).
- `AlgebraicGeometry.LocallyOfFinitePresentation` from
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
  (dependency `def-sbc-locally-finite-presentation`).
- `AlgebraicGeometry.Scheme.Hom.fiber` from `Mathlib.AlgebraicGeometry.Fiber`
  (dependency `def-pc-scheme-fibre`).
- `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs`
  (dependency `def-weil-pbc-noetherian-ring`).
- `IsLocalRing.depth` from `Sheaf.RingTheory.Depth` (dependency
  `def-weil-pbc-depth`).
- `ringKrullDim` from `Mathlib.RingTheory.KrullDimension.Basic` (dependency
  `def-weil-pbc-krull-dimension-ring`).

Searches made before writing:

- `msearch.py ... leanfinder "A flat locally finitely presented morphism has a Cohen Macaulay closed point in every nonempty fibre"` returned eight semantic hits (flat stalk maps, going down, smooth loci, universal openness) and no Cohen--Macaulay density theorem.
- `msearch.py ... loogle '"CohenMacaulay", "Flat"'` returned zero hits.
- `msearch.py ... grep 'CohenMacaulay|Cohen.Macaulay'` returned zero hits.
- `msearch.py ... leansearch "Every nonempty fibre of a flat locally finitely presented scheme morphism contains a closed point with Cohen Macaulay fibre local ring"` returned eight unrelated scheme/flatness hits and no matching theorem.
- `msearch.py ... leanfinder "For flat morphisms of finite presentation the Cohen Macaulay locus is dense in each fibre"` returned flatness/going-down hits and no matching theorem.
- `rg` over `lean/Sheaf` and `WeilConjectures/` found no theorem naming this fibrewise Cohen--Macaulay density statement. Existing Cohen--Macaulay files concern different ring-theoretic results.

The source read was More on Morphisms, Tag 045U, label
`lemma-flat-finite-presentation-CM-open`, assertions (1) and (3). The statement is
unchanged from the DAG node; no statement correction or disputed clause was needed.
The module compiles cleanly with `scompile.py`.

## Second reading by NY

I reread the DAG statement and the generated Lean signature. The morphism, both
morphism-property hypotheses, arbitrary point `s`, arbitrary open `O`, openness and
nonemptiness hypotheses, witness point, membership clause, Noetherian clause, and
depth/Krull-dimension equality all occur in the same order. The fibre is exactly
`f.fiber s`, and its local ring is exactly the fibre presheaf stalk. The explicit
`WithBot ℕ∞` cast records the equality of the depth value (`ℕ∞`) with the Krull
dimension value (`WithBot ℕ∞`). Empty fibres and zero rings are not excluded.


## Independent maintainer reading (2026-10-18)

The statement and all seven statement-dependency interfaces were checked against
the immutable delivery and the cited Stacks sources. No mathematical signature
change is needed. The complete replacement module expands the proof docstring
into the three DAG steps, explicitly treating the nonempty open, the order of
affine choices, tensor symmetry and finite generation, and transport to the
fibre stalk, with the dependency ids. It also imports the already-stated proof
dependency `WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`. These
repair H8 and the proof-import convention of brief-stage2 section 3 (H9).

The original immutable module compiled with scompile.py, exit 0, with no errors
or warnings (sandbox 8.7 s; library 4.9 s). The complete replacement compiled
with the same wrapper, exit 0, with no errors or warnings (sandbox 2.2 s;
library 2.1 s; the basename-only fix is checked as Sheaf.Stage2.Check). The
wrapper currently runs the server side overlay with --wire-confirm; its output
reports private /dev/shm overlay compilation. No global build was run.

The original and replacement signatures are byte-for-byte equal to the node's
lean.statement. Empty schemes, empty fibres, empty opens, arbitrary residue
characteristics, and dimension zero remain covered. The universe u is arbitrary
and agrees with the Scheme.Hom and fibre API. No extra Noetherianity, finite
dimension, nonemptiness, separation, or quasi-compactness hypothesis is imposed.
Independent text searches for Cohen-Macaulay, cm_locus, and cmLocus in the side
project, pinned Mathlib and upstream project found related algebra and openness
results, but no duplicate fibre-density statement. No dependency is in the
route-pivot dropped list and no item-specific repair note exists there.
