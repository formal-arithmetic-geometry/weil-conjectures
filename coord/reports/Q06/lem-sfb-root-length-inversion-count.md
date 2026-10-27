## Worker report

The module `Sheaf.LinearAlgebra.RootLengthInversionCount` states
`RootPairing.simple_reflection_length_eq_inversion_count`, with its proof `sorry`.
The item's statement, dependencies and proof are unchanged. No definition nodes,
dependency repairs or statement corrections are required.

The length is expressed by its minimum property rather than a new length function:
`∃ n, IsLeast {m | ∃ word : List Δ, word.length = m ∧ ...} n ∧ n = ...`.
`IsLeast` includes existence of a word of length n and the lower bound on every word
length. Hence this is exactly the specified least length and its equality, including
existence of reduced expressions. It imposes no Coxeter presentation as a hypothesis.
All universes and variables are explicitly bound; `autoImplicit` is false.

Hypotheses and clauses, in order:

- V finite-dimensional real: `(V : Type u) [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]`, with unrestricted u (including the zero space).
- Symmetric bilinear form: `B : LinearMap.BilinForm ℝ V`, `hBsymm : B.IsSymm`.
  Positive definite: `hBpos : ∀ x, x ≠ 0 → 0 < B x x`.
- Finite root set avoiding zero: `Φ : Finset V`, `hΦzero : ∀ a ∈ Φ, a ≠ 0`.
- Spanning: `hΦspan : Submodule.span ℝ (Φ : Set V) = ⊤`.
- Reduced root lines: `hΦline` intersects Φ with the full real line
  `{x | ∃ r : ℝ, r • a = x}` and equates it with `{a, -a}` for every root a.
- Root reflection permutation: `hΦreflect` is `Set.BijOn` on Φ for the exact map
  `x ↦ x - (2 * B x a / B a a) • a`. Division equals the displayed inverse formula.
  Each denominator is positive by hBpos and hΦzero.
- Crystallographic integrality: `hΦintegral` quantifies both a and β in Φ and
  requires `∃ z : ℤ, 2 * B β a / B a a = (z : ℝ)`.
- Simple roots Δ contained in Φ: `Δ : Finset V`, `hΔ : Δ ⊆ Φ`.
  `b : Module.Basis Δ ℝ V` together with `hb : ∀ a : Δ, b a = a.val`
  says the actual vectors in Δ form the basis; b is not an unrelated basis.
- Every root has integer coordinates with one sign: `hcoords` gives each
  `b.repr β a` an integer lift, and requires all coordinates nonnegative or all
  nonpositive. Coordinates, not just their absolute values, are tested.
- W_Δ: `Subgroup.closure` in the group `V ≃ₗ[ℝ] V` of the set of maps s for which
  `∃ a ∈ Δ, ∀ x, s x = x - (2 * B x a / B a a) • a`.
  This defines the generating set extensionally by its precise action, without
  supplying arbitrary maps or assuming existence of additional data. Positive
  definiteness makes each displayed reflection an invertible involution, so this
  is exactly the generated subgroup in the node. `hw` says w belongs to it.
- Words: `List Δ` is exactly a word in simple roots; `foldr` of the same explicit
  reflection formula, starting at x, applies the rightmost factor first.
  Equality for every x states that its linear transformation is w.
- Positive roots: in the counted set, `β ∈ Φ ∧ ∀ a : Δ, 0 ≤ b.repr β a`.
- The image is a negative positive root: `-w β ∈ Φ` and every coordinate of
  `-w β` is nonnegative. Since negation is involutive, this is precisely
  `w β ∈ -Φ⁺`, not merely the condition that one coordinate is negative.
- Inversion count: `.ncard` of that set, which is finite because it is contained
  in Φ. The equality is `n = ...ncard` for the minimum word length n.
- Rank zero: the final implication `(∀ x : V, x = 0) → Φ = ∅ ∧ Δ = ∅ ∧
  w = 1 ∧ n = 0` explicitly gives empty roots and simple roots, the sole group
  element and zero length. The counted set is then empty, so its count is zero.

Dependency declarations used: the recorded `def-weil-vector-space-dimension`
module `Mathlib.LinearAlgebra.Dimension.Finrank` is publicly imported; its
`Module.finrank` docstring and signature were read, and finite dimensionality is
expressed with the corresponding Mathlib `FiniteDimensional ℝ V` class.
The statement has no numeric dimension parameter, so finrank need not appear
in its type. `Module.Basis`, `LinearMap.BilinForm.IsSymm`, `Subgroup.closure`,
`List.foldr`, `IsLeast` and `Set.ncard` are Mathlib's existing notions.
The proof dependency `lem-sfb-root-sign-word-deletion` has no Lean record or
Mathlib match in the current DAG; its statement and complete proof were read.
Its expected module was also checked with `scompile.py --source` and is absent.
There is consequently no stated proof-dependency module to import. The proof
plan cites that node explicitly and imports can be added when it is stated.

Sources: read Milne Appendix C.8--C.11, printed pp.609--610 (PDF pp.621--622),
including the reflection formula and definition of a base. Read Björner--Brenti
Lemma 4.4.3 and Proposition 4.4.4, printed pp.102--104 (PDF pp.110--112), at
https://sites.math.washington.edu/~billey/classes/reflection.groups/references/EntireBook.pdf .
The local Björner--Brenti PDF is absent, as already recorded in the item.
Also read the current blueprint unit `sk-thm-sf-ctf-stability` and its direct-image
proof (3), which is the inherited ancestor context rather than a separate statement
of this reflection-group lemma.

Edge cases checked before writing: in the zero space the root set must be empty,
there are no letters, and the empty fold is identity. For identity in every rank,
the empty word has length zero and no positive root has negative image. For a
simple reflection only its own simple root becomes negative. No nonempty-root,
positive-rank or irreducibility assumption is present. A separate exact-rational
breadth-first enumeration then checked every group element for A1 (2 elements),
A1×A1 (4), A2 (6), B2 (8), G2 (12), and rank zero (1). For each, every root reflection
preserves the full root set and the shortest word length equals the inversion count;
maximum lengths were respectively 1, 2, 3, 4, 6, 0. B2 and G2 check unequal root lengths.
This is only a check of cases; the Lean proof remains sorry as required.

Searches for existing declarations:

- msearch LeanSearch: `Minimum length of a word in root reflections equals the
  cardinality of positive roots taken negative`. Eight hits: CoxeterSystem length,
  reduced-word and simple-generator lemmas, and RootPairing.reflection_apply_self.
  No exact match: CoxeterSystem requires a specified Coxeter presentation.
- msearch LeanFinder: `The length in simple reflections of an element of a finite
  real root system equals the number of positive roots mapped to negative roots`.
  Eight hits mostly on RootPositiveForm.rootLength (the squared norm), plus
  CoxeterSystem.length_simple and Base.IsPos.reflectionPerm; no length-count theorem.
  Read the actual rootLength, Coxeter length/IsReduced and sign-preservation sources.
- msearch Loogle: `"wordLength", "reflection"`: no hits.
- msearch grep: `length.*card|card.*length|def reflection` in
  `LinearAlgebra/RootSystem`: only the two reflection definitions, no count result.
- rg on Mathlib GroupTheory and LinearAlgebra: Coxeter length is a Nat.find on
  Coxeter words; Module.reflection is a general normalized-functional construction,
  not the theorem here. Read its full definition and docstring.
- rg on project `lean/WeilConjectures` and `lean/Sheaf` for root/reflection lengths,
  wordLength, simpleReflection, signWord and this node id: no duplicate theorem.
  RationalReflectionSimpleBaseOrbits states existence/generation for rational data;
  AffineReflectionDominantDescent states different geometric/weight conclusions.
- The new full declaration name has no match in either project library or the
  upstream declaration-name index. Search outputs are preserved in searches.jsonl
  in the sandbox by msearch.

Validation: `scompile.py` compiled both the isolated statement and its proper module
successfully, with no errors or unexpected warnings. The only postponed declaration
is `RootPairing.simple_reflection_length_eq_inversion_count`.
No statement dispute was found.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
