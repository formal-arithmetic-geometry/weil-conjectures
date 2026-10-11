## Worker report

The module defines `Algebra.IsGlobalCompleteIntersection` and
`Algebra.IsLocalCompleteIntersection`. Source: Stacks Project, Algebra,
Definition 10.135.1 (Tag 00S9), read in the locally available Stacks copy at
`/home/ubuntu/c1-stacks-review/algebra.tex:35817`. The repository's
`literature/stacks-project/` is absent on this machine.

Clause (1), global: `k : Type u` with `[Field k]` is the field; `T : Type v`
with `[CommRing T] [Algebra k T]` is any commutative `k`-algebra. `Subsingleton T`
is exactly the zero-ring convention. Otherwise `n c : ℕ` allows all
nonnegative numbers of variables and equations, and
`f : Fin c → MvPolynomial (Fin n) k` is the list of polynomials.
`Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] T)`
is the required `k`-algebra isomorphism from the quotient by those equations.
`topologicalKrullDim (PrimeSpectrum T) = (↑(n - c) : WithBot ℕ∞)` is the
Krull dimension equality. `c ≤ n` makes this natural-number subtraction
equal to the integer `n - c` in the source; without it, truncated subtraction
would incorrectly accept a nonzero zero-dimensional ring with `c > n`.
Finite generation is a consequence of the displayed presentation, not an
extra premise on `T`, as the node says.

Clause (2), local: `S : Type v` with `[CommRing S] [Algebra k S]` and
`[Algebra.FiniteType k S]` is a finitely generated `k`-algebra.
`s : Set S` represents a family of elements, with no restriction on its
index set. `(⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤` states exactly that
the principal opens cover `Spec S`; `PrimeSpectrum.basicOpen g` has carrier
`{p | g ∉ p.asIdeal}`. `∀ g ∈ s, IsGlobalCompleteIntersection k
(Localization.Away g)` says each localization `S_g` meets clause (1).

Dependencies used: `Localization.Away` from
`Mathlib.GroupTheory.MonoidLocalization.Away` (def-weil-ring-localization-away);
`topologicalKrullDim` from `Mathlib.Topology.KrullDimension`
(def-kun-topological-krull-dimension); `PrimeSpectrum` and its topology,
with `AlgebraicGeometry.Spec` from `Mathlib.AlgebraicGeometry.Scheme`
identifying the associated affine scheme (def-weil-affine-spectrum);
`MvPolynomial` from `Mathlib.Algebra.MvPolynomial.Basic`
(def-weil-pbc-mv-polynomial-ring). The corresponding source declarations
and docstrings were checked.

Edge cases: `n = 0` and `c = 0` are admitted by `Fin 0` and the empty
ideal-generating family. The zero ring satisfies the first disjunct regardless
of its dimension `⊥`; a nonzero ring cannot use that disjunct. An empty
cover is admitted exactly when `Spec S` is empty, as for the zero ring.
No characteristic restriction is imposed on `k`. Arbitrary universe levels
`u` and `v` cover all field and algebra types.

Searches for an existing notion: `msearch.py` leanfinder with query
"global complete intersection over field polynomial quotient dimension n
minus c; local complete intersection covered by localizations" returned
standard-smooth definitions, not a match. `msearch.py` loogle with
"IsGlobalCompleteIntersection, IsLocalCompleteIntersection,
CompleteIntersection" found no match. `msearch.py` grep with
"CompleteIntersection|complete intersection|IsLCI" in Mathlib/RingTheory
found only a comment in Extension/Presentation/Basic. Direct `rg` for
"complete intersection|CompleteIntersection|IsLCI|LocalCompleteIntersection"
over Mathlib/RingTheory, the source `WeilConjectures/`, and the project's
`lean/Sheaf/` found no declaration. Direct `rg` for the proposed full
names over `dag/lean_names_upstream.json` and `WeilConjectures/` found none;
`grep -rn` for this node ID in `WeilConjectures/` also found none.

Server compile: clean, exit code 0.

## Second reading by F1

The node introduces the following objects and clauses, matched to the Lean
definitions:

* A field `k` is rendered by the `[Field k]` instance in both definitions.
* The global predicate is on a commutative `k`-algebra `T`, rendered by
  `[CommRing T] [Algebra k T]` in `Algebra.IsGlobalCompleteIntersection`.
* The zero-ring convention is rendered by the first disjunct `Subsingleton T`.
* For a nonzero presentation, `n,c : ℕ` and the family of `c` polynomials in
  `n` variables are rendered by `∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)`.
* The quotient presentation and k-algebra isomorphism are rendered by
  `Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] T)`.
* The source equality `dim T = n - c` is rendered by
  `topologicalKrullDim (PrimeSpectrum T) = (↑(n - c) : WithBot ℕ∞)`.
  The added `c ≤ n` is necessary because Lean's `ℕ` subtraction truncates,
  and is equivalent to the source equality for a nonzero ring; it prevents a
  presentation with `c > n` from incorrectly using a zero right side.
* The local predicate has a finite type k-algebra `S`, rendered by
  `[Algebra.FiniteType k S]` in `Algebra.IsLocalCompleteIntersection`.
* Its family of principal opens is rendered by `s : Set S`; the cover
  `Spec S = ⋃ D(g)` is rendered by
  `(⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤`.
* Each localization is rendered by
  `∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)`.

No mismatch was found. `Localization.Away` is the ring localization at the
element required by the node, and `PrimeSpectrum.basicOpen` is the principal
open D(g). The empty family is allowed exactly when the spectrum is empty;
`n = 0` and `c = 0` are represented by `Fin 0`; no characteristic or universe
restriction is added. The zero ring is admitted by the global disjunct and can
also have an empty local cover.

Searches were independently checked with `msearch.py` (LeanFinder and
Loogle), direct `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`, and the
upstream-name search. They found no existing complete-intersection notion;
only standard-smooth declarations and the Mathlib presentation comment were
returned. The exact source definition was reread at Stacks Algebra
Definition 10.135.1 (Tag 00S9). No edits to the module or node were needed.
