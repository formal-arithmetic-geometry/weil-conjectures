## Worker report

The module `Sheaf.RingTheory.MonotonePrefixEssentialRestriction` states
`MonomialDiagram.monotone_prefix_essential_restriction`, with proof `sorry`.
It also supplies `MonomialDiagram.essentialVariablesLinearOrder`: the canonical
inherited subtype order on the already defined `EssentialVariables a`. This is
real instance data obtained by `inferInstanceAs` on its defining subtype, with
no postponed proof and no new notion. No node statement was changed.

Hypotheses and objects, read against the complete DAG statement:

- `n s : ℕ` give the number of variables and the finite vertex list length;
  `Fin n →₀ ℕ` is exactly the finite-coordinate exponent space ℕⁿ. `Fin n`
  numbers the variables from zero rather than one without changing their order.
- `D : Set (Fin n →₀ ℕ)` and `hD : IsMonotone D` assert addition by every
  nonnegative vector and every whole-coordinate move from an earlier variable
  to a later one. The recorded definition uses truncated coordinate subtraction,
  subtracting precisely the old coordinate, so it is the specified move.
- `a : Fin s → Fin n →₀ ℕ` and `ha : IsOrderedVertexFamily D a` assert that
  this list enumerates exactly the coordinatewise minimal elements and is strictly
  ascending for degree followed by lexicographic coordinate order. There is no
  extra antichain, nonemptiness, generation, or dimension hypothesis.
- `Finsupp.degree` is the sum of the coordinates, hence the node's dᵢ. The node's
  Δᵢ is the recorded `quotientSupport a i`, not a new definition.

Conclusion, clause by clause:

1. The first conjunct quantifies `u : ℕ`. `prefixVertices a u` has domain
   `{i : Fin s // (a i).degree ≤ u}`, the exact Iᵤ, with its inherited order.
   `generated (prefixVertices a u)` is the union of the retained orthants D≤ᵤ.
   Its `IsMonotone` conjunct states both additive and coordinate-move closure;
   `IsOrderedVertexFamily` states exactly the retained ordered minimal vertices;
   the equality of `quotientSupport` at every retained subtype index says that
   each quotient support is the original Δᵢ, with the original index `i.val`.
2. The middle conjunct first asserts the final-segment property explicitly:
   for `p < v`, occurrence of p in a vertex implies occurrence of v in a vertex.
   For natural coordinates, `≠ 0` is equivalent to the node's `> 0`.
   `EssentialVariables a` is exactly J; `essentialVertices a` is restriction of
   the same indexed family to J, and the helper instance is the inherited order.
   `IsMonotone (generated (essentialVertices a))` asserts both closures of D̄,
   and `IsOrderedVertexFamily` identifies its ordered minimal vertex list with
   the restricted list, retaining every original index. The next conjunct
   equates each restricted degree to the original degree.
   The quotient-support set equality is precisely Δ̄ᵢ = {β : ι(β) ∈ Δᵢ}.
   The complement equality is precisely ℕᴶ \\ D̄ = {γ : ι(γ) ∉ D}.
   Here `Finsupp.embDomain (Function.Embedding.subtype _)` extends by zero
   outside the subtype J; it is Mathlib's canonical construction.
3. The final conjunct quantifies u again and repeats all six restriction
   assertions for `prefixVertices a u` and its generated diagram. In particular,
   `EssentialVariables (prefixVertices a u)` is its OWN Jᵤ, rather than J, and
   the final complement uses `generated (prefixVertices a u)`, rather than D.
   The original and restricted prefix families share the identical subtype
   index, so no unsupported reindexing or degree assumption is introduced.

Dependency declarations used (their full signatures and docstrings were read):
all of `MonomialDiagram.IsMonotone`, `IsOrderedVertexFamily`, `generated`,
`quotientSupport`, `prefixVertices`, `EssentialVariables`, `essentialVertices`
from `Sheaf.RingTheory.SupportedHomogeneousDivision`, the recorded module for
`def-trf-supported-homogeneous-division`. This is the only statement/proof
node dependency. The module publicly imports it. Mathlib's `Finsupp.embDomain`
and `Function.Embedding.subtype` supply extension by zero; `Finsupp.DegLex`
and `Minimal` are used through the recorded dependency definitions.

Edge cases checked before drafting and on the completed signature:

- Empty retained index set: its generated diagram is empty and all vertex and
  quotient clauses are vacuous. Its essential-variable set is empty, and its
  restricted complement is the singleton zero exponent.
- D = ∅: take s = 0, so every prefix is this empty case.
- D = ℕⁿ: the sole minimal vertex is zero; its degree is zero and it belongs
  to every natural-number prefix. J and every Jᵤ are empty. Restricted diagram
  and quotient support are singleton; both complements in the middle equality
  are empty.
- n = 0: the exponent space is singleton, hence D is empty or full; these cases
  apply with no coordinate moves. Nothing assumes positive n or s.
- A move from a zero coordinate is allowed by `IsMonotone`; no positivity
  binder restricts its closure clause. The final-segment occurrence hypothesis
  alone asks a nonzero coordinate, exactly as the node does.

Searches made through the prescribed `msearch.py` wrapper and direct source searches:

- LeanFinder: "Degree prefixes and deleting unused variables preserve a monotone
  additive monomial diagram and its ordered minimal vertices and quotient supports".
  Eight hits, concerning Linarith elimination and polynomial leading monomials;
  none states these preservation claims.
- Loogle: "Finsupp.DegLex, Finsupp.embDomain, Set.IsUpperSet". No usable result;
  the service reported unknown identifier `Set.IsUpperSet`. The needed exponent
  order and embedding were independently read in Mathlib's source.
- LeanSearch: "Monotone additive monomial diagrams are preserved by degree prefixes
  and deleting unused variables". Eight hits about polynomial degree or monomial
  order monotonicity, none about this diagram preservation result.
- Mathlib grep via msearch: `prefixVertices|essentialVertices|quotientSupport|MonomialDiagram`:
  zero hits.
- Direct `rg` over `lean/Sheaf` and `lean/WeilConjectures` for
  `monotone.?[Pp]refix|essential.?[Rr]estriction|prefixVertices|essentialVertices`:
  the dependency definitions, uses in `InitialDiagramStabilization`, and uses
  in `GenericMonotoneDiagram`; no preservation theorem. The latter statements
  concern finite division tests and generic diagrams, respectively.
- Direct upstream grep for the item's blueprint id: no hit.
- Direct `rg` over Mathlib, both project source roots, and
  `dag/lean_names_upstream.json` for
  `monotonePrefix|prefix_essential|essential_restriction|monotone_prefix`: no hit.
- The helper name `essentialVariablesLinearOrder` was checked against Mathlib
  and both project source roots: no hit.

The named source was opened at the journal PDF URL in the node. Section 8,
printed pp.273--274, gives exactly the whole-coordinate monotonicity convention;
Theorem 9.6, printed p.282, applies the stabilization theorem to the degree
blocks. The seven elementary preservation steps themselves are the node's
explicit finite-coordinate proof, reproduced in the theorem docstring.
Source: https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf

Validation: the prescribed scompile.py compiled both the isolated statement and
its library module cleanly. The initial compile diagnosed the absent order
instance on the named essential-variable subtype; the canonical inherited-order
instance above repaired that interface without changing any mathematical assumption.
All binders are explicit (`set_option autoImplicit false`), and the only postponed
proof is the item's named theorem. No statement dispute or node correction.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
