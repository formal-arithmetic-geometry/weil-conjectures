## Worker report

Stated `RootPairing.exists_rank_two_root_coordinate_classification` in
`Sheaf.LinearAlgebra.RankTwoRootCoordinateClassification`. Its only theorem has
`sorry` as its whole proof; no definitions or helper theorems are introduced.
The node is unchanged except for `lean`.

Source read: Milne, *Algebraic Groups*, Appendix C.12 and C.14 (printed p.610)
for finite spanning rational reflection data and integral coroot evaluations;
C.17--C.18 (p.611) for rational root systems and reducedness; section g,
table (180) and the four diagrams (pp.621--622) for the four complete root lists.
Read these pages directly from the local PDF using pdftotext. The module docstring
carries the node's five-step argument: finite averaging, the simple-base/orbit
lemma, restrictions on the two Cartan integers, stability of the explicit lists,
and orbit exhaustion, with all coordinate image lists included.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Rational vector space V: `(V : Type u) [AddCommGroup V] [Module ℚ V]`.
  The universe `u` is explicit and unrestricted. The field is Mathlib's rational
  field, not a new field construction.
- Dimension two: `[FiniteDimensional ℚ V]` and
  `(hdim : Module.finrank ℚ V = 2)`. Finite-dimensionality is part of being
  two-dimensional, not an additional mathematical restriction.
- S finite: `(S : Finset V)`; this encodes precisely a finite subset, with no
  enumeration, ordering, or DecidableEq assumption on V in the signature.
- S excludes zero: `(hS0 : ∀ r ∈ S, r ≠ 0)`.
- S spans V: `(hSspan : Submodule.span ℚ (S : Set V) = ⊤)`.
- One rational linear functional for each root:
  `(c : S → V →ₗ[ℚ] ℚ)`. Here S in the index type coerces to its root subtype.
- Normalization: `(hc2 : ∀ r : S, c r r = 2)`.
- Integral values on S: `(hcint : ∀ r x : S, ∃ z : ℤ, c r x = z)`.
  This is inclusion in the integer image in ℚ, with the standard integer cast.
- Reflection formula and permutation of S: `hcreflect` is
  `∀ r : S, Set.BijOn (fun x : V ↦ x - c r x • (r : V))
    (S : Set V) (S : Set V)`. This records both preservation and bijectivity
  for the prescribed function, without choosing a replacement action.
- Reducedness: `hSline` equates the intersection of S and
  `{x : V | ∃ q : ℚ, q • (r : V) = x}` with `{(r : V), -(r : V)}`
  for every root r. The displayed set is exactly the full rational line ℚr.
- Ordered rational basis: `∃ b : Module.Basis (Fin 2) ℚ V`.
  Its first vector s is `b 0` and its second vector t is `b 1`.
- Both basis vectors are roots: `b 0 ∈ S ∧ b 1 ∈ S`.
- Exactly one of the four root sets: four disjuncts, each an equality of
  `(S : Set V)` with the corresponding explicit finite set. A1 × A1 lists
  s,-s,t,-t. A2 additionally lists s+t and its negative. B2 additionally lists
  2s+t and its negative. G2 additionally lists 3s+t and 3s+2t, and both negatives.
  Each coefficient 2 or 3 is explicitly a rational scalar. The four set equalities
  express the node's alternatives without weakening equality to inclusion or
  imposing extra conditions on the coroot functionals.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, full class signature and docstring in
  `Mathlib.Algebra.Field.Defs` (line 180). The rational field structure is reused.
- `def-weil-vector-space-dimension`: Mathlib `Module.finrank`, full definition and
  docstring in `Mathlib.LinearAlgebra.Dimension.Finrank` (line 63); available
  through the public import `Mathlib.LinearAlgebra.FiniteDimensional.Basic`.
  `Module.Basis` supplies an actual ordered basis in the conclusion.
- Proof-only dependency `lem-sfb-rational-reflection-simple-base-orbits`:
  `RootPairing.exists_simple_base_reflection_orbits`, full signature and proof
  docstring read in `Sheaf.LinearAlgebra.RationalReflectionSimpleBaseOrbits`.
  Imported without `public`. Its input data matches the current root data
  exactly, including the subtype-indexed coroots and the full-line reducedness
  condition. No restatement or private copy is needed.

Edge cases checked before writing:

- The empty root set cannot span a two-dimensional vector space. Zero V and a
  one-dimensional V fail `hdim`, as the source requires.
- Zero is excluded by `hS0`; reducedness is imposed for each root and includes
  the negative root. No ambient ordering or inner product is assumed.
- The decomposable A1 × A1 case is included as the first disjunct; irreducibility
  is not assumed. Equal lengths give A2; the basis can be swapped for B2 and G2,
  so the source's short-root-first orientation is available without an extra
  hypothesis or a restriction on the input ordering.
- Finiteness is encoded without fixing a cardinality; the conclusion allows
  exactly the four sets of sizes 4, 6, 8, 12. Since b is a basis over ℚ, all
  displayed roots are nonzero and there is no positive-characteristic collapse.
- No irredundancy assertion on the four alternatives, abstract type classification,
  chosen Euclidean normalization, or additional coroot formulas are demanded.

Searches actually run (all remote search services answered successfully):

- msearch LeanFinder: “A two dimensional rational vector space with a finite
  reduced crystallographic root set has a basis with root coordinates of types
  A1 A1 A2 B2 or G2”. Eight hits: `RootPairing.nonempty_base`,
  `RootPairing.EmbeddedG2.basis`, `RootPairing.Base.mk'`, and G2 predicates and
  consequences. None classifies the four root sets from the unbundled data.
- msearch Loogle: `RootPairing.IsReduced, Module.finrank`. Zero hits.
- msearch grep: `classification|finrank.*2|allRoots_eq` in
  `LinearAlgebra/RootSystem`. Six hits, including
  `RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs` (G2.lean:312), whose full
  signature and surrounding coefficient list were read. It needs an already
  embedded G2 structure and does not cover the other three alternatives.
- msearch LeanSearch: “finite reduced crystallographic root system rank two
  explicit coordinate classification A1 A2 B2 G2”. Eight hits: bounds on two
  Cartan integers, explicit Cartan matrices and G2 lists. These are partial
  ingredients, not the statement of this node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `rank.two|root.coordinate|simple.base.orbits`: related root-coordinate files,
  the proof dependency, and the Chevalley parity consumer, but no exact statement.
- `grep -rn` for the item id in `lean/WeilConjectures`: no hits.
- Exact proposed declaration search for
  `exists_rank_two_root_coordinate_classification|rank_two_root_coordinate_classification`
  in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no hits before writing the declaration.

Validation: prescribed scompile.py compiled the module as a sandbox and under its
library module name, with no errors or warnings. No statement correction,
new node, dependency repair, or STATEMENT-DISPUTED issue is needed.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
