## Worker report

The delivery states `RootPairing.exists_simple_base_reflection_orbits` in
`Sheaf.LinearAlgebra.RationalReflectionSimpleBaseOrbits`. Its sole theorem has proof
`by sorry`; no definition or additional theorem is introduced. Only the item's `lean`
field changes. There is no statement correction, new node, dependency repair, or disputed
statement. No repair note exists for this item in the read clone.

Source checked: Milne, *Algebraic Groups*, Appendix C.12--C.22, printed pp.610--612,
read from `literature/milne-algebraic-groups_iAG2017.pdf`. C.14 supplies precisely the
linear coroot formulation, C.18 the reduced root-line condition, C.21 the common-sign
integer-coordinate definition, and C.22 both base existence and `W · D = S` with the
simple-reflection generators. The module docstring gives all six proof steps and
identifies all three mathematical proof dependencies.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A finite-dimensional rational vector space V | `(V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]`; universe `u` is explicit and unrestricted. |
| S is finite | `(S : Finset V)`, an arbitrary finite subset with no chosen ordering. |
| S contains no zero vector | `hS0 : ∀ r ∈ S, r ≠ 0`. |
| S spans V | `hSspan : Submodule.span ℚ (S : Set V) = ⊤`. |
| A linear map c_r for each r in S | `c : S → V →ₗ[ℚ] ℚ`, indexed only by the root subtype. No extension outside S is required. |
| c_r(r) = 2 | `hc2 : ∀ r : S, c r r = 2`. |
| c_r(S) is integral | `hcint : ∀ r x : S, ∃ z : ℤ, c r x = z`, with integer cast into ℚ. |
| s_r permutes S | `hcreflect : ∀ r : S, Set.BijOn (fun x ↦ x - c r x • (r : V)) (S : Set V) (S : Set V)`. |
| S meets the rational root line in exactly r and -r | `hSline` equates the intersection with `{(r : V), -(r : V)}`; the line is the set `{x : V | ∃ q : ℚ, q • (r : V) = x}`, including zero. |
| There is D contained in S | `∃ (D : Finset V) ... , D ⊆ S ∧ ...`; finiteness adds no restriction because S is finite. |
| D is a rational basis, consisting of those same vectors | `b : Module.Basis (↥(D : Set V)) ℚ V` and `∀ i, b i = i.1`; the equation prevents substituting an unrelated indexed basis. |
| Each root has integer D-coordinates | For every `r ∈ S`, a function `z : (↥(D : Set V)) → ℤ` satisfies `(z i : ℚ) = (b.coord i) r` at every coordinate. |
| The coordinates are all nonnegative or all nonpositive | `((∀ i, 0 ≤ z i) ∨ (∀ i, z i ≤ 0))` on the same function `z` for each root. The disjunction is outside the coordinate quantifier. |
| Every root is a word in simple reflections applied to a simple root | For every `r ∈ S`, `∃ (k : ℕ) (ds : Fin k → S) (d : V)`, with `d ∈ D` and `∀ j, (ds j : V) ∈ D`, and the displayed `foldr` equation. |
| k may be zero and the rightmost reflection acts first | `List.ofFn ds` enumerates the factors in order and `foldr (fun a x ↦ x - c a x • (a : V)) d` gives `s_d1 (s_d2 (... d))`; at k=0 it is d. |
| If V=0 then S=D=empty, and the orbit clause is vacuous | `((∀ x : V, x = 0) → S = ∅ ∧ D = ∅)` uses the zero-vector-space condition without comparing a type to a numeral. The orbit clause quantifies only over roots of S. |

Dependencies read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`. The instance on `ℚ` is
  Mathlib's field; no field or rational arithmetic is redefined.
- `def-weil-vector-space-dimension`: `Module.finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finrank`, whose full signature and docstring were
  read. The node uses finite dimension and a rational basis rather than a numeric
  dimension formula, so the statement uses the corresponding `FiniteDimensional`
  instance and `Module.Basis`; `Module.finrank` is not needlessly inserted as a clause.
- `lem-sfb-spanning-reflections-root-pairing`: Mathlib matches `RootPairing.mk''` and
  `RootPairing.isRootSystem_mk''` in `Mathlib.LinearAlgebra.RootSystem.Basic`. Their
  complete section parameters, perfect-pairing assumption, root/coroot embeddings,
  normalization, stability, spanning, and integer-pairing inputs were read. This is
  a proof dependency, not an extra bundled-root-pairing hypothesis on the item.
- `lem-sfb-reduced-rational-root-pairing-base`: `RootPairing.nonempty_base` in
  `Mathlib.LinearAlgebra.RootSystem.BaseExists`, including its finite,
  crystallographic, reduced and root-system assumptions and the five Base fields.
- `lem-sfb-root-base-reflection-induction`: `RootPairing.Base.induction_reflect` in
  `Mathlib.LinearAlgebra.RootSystem.Base`. Its three predicate hypotheses were read:
  negation, base-support membership, and preservation under simple reflections.
  The plain proof import of `BaseExists` provides all three proof-dependency modules
  through its imports. Statement imports are public; proof imports are plain.

Searches (all through the prescribed `msearch.py`, logs in `searches.jsonl`):

- LeanFinder: "A finite spanning set of nonzero rational vectors stable under integral
  reduced reflections has an integer sign coherent basis and is generated from that
  basis by simple reflections". Eight hits, including `Base.induction_reflect`,
  `nonempty_base`, and `isRootSystem_mk''`. These are the bundled proof ingredients;
  none is this unbundled existence statement.
- Loogle: "RootPairing.Base, FiniteDimensional, Set.BijOn". Zero hits.
- Mathlib grep: "simple.*base|nonempty_base|induction_reflect|reflection.*orbit",
  restricted to `LinearAlgebra/RootSystem`. Six hits, the base-existence and
  reflection-induction results already assigned as proof dependencies.
- Additional msearch grep: "rationalReflectionSimpleBaseOrbits|simpleBaseOrbits|
  reflectionSimple|RootPairing.*simple", subdirectory `WeilConjectures`: zero hits.
- LeanSearch: "finite rational reflection set reduced spanning simple roots integral
  coordinates every root is a word in simple reflections". Eight hits, chiefly
  Weyl-group definitions and Coxeter reduced-word results; no unbundled statement.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for rational-reflection,
  simple-base and root-pairing/orbit phrases, plus the exact node id: no duplicate.
  Direct `rg` for `exists_simple_base_reflection_orbits` and the module name in
  those trees and `dag/lean_names_upstream.json`: no declaration collision.

Edge cases checked by reading the source and expanding the statement:

- V=0: S is empty by `hS0`, D is the empty basis, the integer and orbit clauses are
  vacuous. No nonempty root, base, or positive-dimension assumption appears.
- k=0: `foldr` is d, so each simple root belongs to its orbit with an empty word.
- Two factors: the expression is `s_(ds 0) (s_(ds 1) d)`, with the rightmost first.
- Rank one: roots {r,-r}; c_r(r)=2 sends r to -r, and D={r} works.
- Reducible systems such as A1 x A1: the theorem asks for an orbit of some d in D,
  not one common orbit for all simple roots. No irreducibility was added.
- Different root lengths (B2/G2) are allowed: no symmetry or equal-length condition
  is imposed on c. Nonreduced BC1 is excluded exactly by `hSline`.
- Every universe and variable is explicitly bound, with `autoImplicit false`.

Validation: `scompile.py` compiled the final sandbox and library module on the live
server with its default 60-second per-file bound and no warnings or errors. The
sole postponed proof is `RootPairing.exists_simple_base_reflection_orbits`.

## Second reading by Q74

This section records the dispatched worker's own separate rereading of the node,
Milne C.14/C.18/C.21/C.22, and the complete final module. It is not a claim that a
second agent reviewed it; the dispatch explicitly forbids starting other agents,
and the maintainer supplies the independent delivery review.

The rereading found and repaired an initial fold lambda that ignored its tail:
it is now a direct vector-valued right fold, so two factors compose in the stated
order. The coroot family was also changed to `c : S → V →ₗ[ℚ] ℚ` to request only
source-prescribed data, and the zero-space clause now says every vector is zero.
The basis type is explicitly `Module.Basis`, with its values constrained to the
selected vectors. The correspondence table above checks every hypothesis and
conclusion against the final signature: no absent normalization, integrality,
permutation, reducedness, coordinate sign, empty word or zero-space clause remains.
The corrected draft compiled cleanly. The DAG's mathematical statement is unchanged.
