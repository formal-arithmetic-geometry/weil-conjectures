## Worker report

`Sheaf.RingTheory.Depth` defines `Ideal.depth` and the local specialization
`IsLocalRing.depth`. The source is Stacks Project, Algebra, Definition 10.72.1
(Tag 00LI); the regular-sequence condition is Definition 10.68.1 (Tag 00LF).
The repository's `literature/stacks-project/algebra.tex` is absent on this
machine, so I read both definitions at their official Stacks tag pages.

- A commutative ring is `[CommRing R]`. An ideal is `(I : Ideal R)`.
- A finite `R`-module is `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. The universe `v` permits any module type.
- `IM` is `I • (⊤ : Submodule R M)`. The `if` branch tests equality to `⊤`,
  which is `IM = M`, and returns `⊤ : ℕ∞`.
- If `IM ≠ M`, `sSup {n : ℕ∞ | ...}` takes the supremum of the lengths
  `n = (rs.length : ℕ∞)` for finite sequences `rs : List R`.
- `RingTheory.Sequence.IsRegular M rs` renders both injective multiplication
  on each successive quotient and the nonzero final quotient. `∀ x ∈ rs,
  x ∈ I` puts every term in the ideal.
- The empty list is among the candidates when `IM ≠ M`: its generated
  submodule is zero, while `M ≠ 0` follows from `IM ≠ M`.
- `[IsLocalRing R]` supplies the unique maximal ideal. The local definition
  is `(maximalIdeal R).depth M`; `IsLocalRing.depth R` is the ring's depth as
  a module over itself.

Dependencies used: `RingTheory.Sequence.IsRegular` in
`Mathlib.RingTheory.Regular.RegularSequence`, with `IsWeaklyRegular` handling
the successive quotients and `top_ne_smul` handling the nonzero quotient;
`Module.Finite` in `Mathlib.RingTheory.Finiteness.Defs`, defined as finite
generation of the top submodule. `IsLocalRing.maximalIdeal` is in
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`.

Edge cases checked: `M = 0` gives `IM = M` and infinity; `I = ⊤` likewise;
`I = ⊥` and nonzero `M` allow the empty sequence and depth zero; the zero
ring has no `[IsLocalRing R]`, consistent with its having no maximal ideal.
Unbounded regular-sequence lengths have supremum infinity in `ℕ∞`.

Searches: `msearch leanfinder` query "depth of a finite module relative to an
ideal, supremum of lengths of module regular sequences, infinity when ideal
times module equals module" returned Krull-dimension and module-length
declarations, no depth. `msearch loogle` query
`Ideal.depth,IsLocalRing.depth,ModuleCat.depth` returned no hits.
`msearch grep` query `depth|Depth` under `RingTheory` found Rees's theorem,
two comments, and an unrelated recursion-depth mention, but no definition.
`rg` over `WeilConjectures` and `lean/Sheaf`, plus `grep -rn` for this node ID
in `WeilConjectures`, found no depth declaration. The pinned Mathlib also
has no ring-theoretic depth declaration. Its upstream Ext-based depth,
recorded in the node as a candidate, has a different defining convention.

The server single-file compile succeeded without warnings.

## Second reading by G1

I checked the node against Stacks Algebra, Definitions 10.72.1 (Tag 00LI) and
10.68.1 (Tag 00LF), and read both dependency declarations in the pinned Mathlib.
The node and the Lean agree item by item:

- The commutative ring and ideal are `{R : Type u} [CommRing R] (I : Ideal R)`.
  No Noetherian or characteristic assumption is added.
- The finite module is `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. `Module.Finite` means finite generation of `M`, as in
  dependency `def-weil-finitely-generated-module`; `u` and `v` are independent.
- The submodule `IM` is `I • (⊤ : Submodule R M)`, exactly the span of the
  products `am` with `a ∈ I` and `m ∈ M`.
- The case `IM = M` is the `if ... = ⊤ then ⊤` branch, returning infinity in
  `ℕ∞`. This includes `M = 0` and `I = ⊤`.
- The case `IM ≠ M` is `sSup {n : ℕ∞ | ∃ rs : List R, ... ∧
  n = (rs.length : ℕ∞)}`. Each witness is a finite sequence of elements of
  `R`; `∀ x ∈ rs, x ∈ I` puts every element in the ideal. The `sSup` allows
  unbounded lengths to have value infinity.
- `RingTheory.Sequence.IsRegular M rs` is the recorded declaration of
  `def-weil-pbc-regular-sequence`. Its `IsWeaklyRegular` field says each
  successive multiplication is injective, and `top_ne_smul` says the final
  quotient is nonzero. These are exactly clauses (1) and (2) of Tag 00LF.
- In the local case `[IsLocalRing R]`, `IsLocalRing.depth M` is
  `(maximalIdeal R).depth M`. The ring's depth is this same definition with
  `M := R`; no extra ring condition or separate notion is introduced.

Edge cases: if `IM ≠ M`, then `M ≠ 0`, so the empty list is regular and gives
length zero. The zero module and `I = ⊤` take the infinity branch. For
`I = ⊥` and nonzero `M`, the empty list is admitted and no nonempty regular
list can lie in `I`. The definition is independent of characteristic and
works for arbitrary ring and module universes. There is no scheme or numeric
parameter in this node.

Independent searches used `msearch leanfinder` with "grade of a module ideal
via regular sequence length" (dimension and regular-sequence lemmas, no depth
definition), `msearch loogle` with
`ModuleCat.depth,Ideal.depth,IsLocalRing.depth` (no hit), and `msearch grep`
with `grade|codimension|depth` (only unrelated or supporting results).
I also searched the source repository's `WeilConjectures/`, this project's
`lean/Sheaf/`, and the pinned Mathlib's `RingTheory/Depth/`: no existing
definition of this depth. The upstream Ext-based candidate is absent from
the pinned Mathlib and has a different definition outside proved agreement
conditions. No mismatch was found, so I made no Lean or node change.
