## Worker report

The module `Sheaf.RepresentationTheory.InducedCharacterConjugacyFormula` states
`Representation.induced_character_conjugacy_formula`, with exactly the two equalities
in the node, as a conjunction. Its sole theorem proof is `sorry`; its docstring carries
all eight steps of the accepted quotient-basis and conjugation-fibre proof. No definitions,
new nodes, dependency repairs, or statement corrections are required.

Hypothesis and clause correspondence:

- A finite group G: `(G : Type u) [Group G] [Finite G]`, with arbitrary universe u.
- A subgroup H ≤ G: `(H : Subgroup G)`; its underlying type coerces to `H`.
- A finite-dimensional complex vector space W: `(W : Type v) [AddCommGroup W]
  [Module ℂ W] [FiniteDimensional ℂ W]`, with arbitrary independent universe v.
- A linear H-action: `(ρ : Representation ℂ H W)`. A representation is a monoid
  homomorphism to linear endomorphisms; inverses in H make each action invertible.
- The character of W at h is `LinearMap.trace ℂ W (ρ h)` throughout.
- The induced quotient is `Representation.IndV H.subtype ρ`, and the induced action
  is `Representation.ind H.subtype ρ`. This uses the actual Mathlib tensor product
  and submodule quotient, rather than an arbitrary model satisfying axioms.
  Mathlib uses diagonal H-coinvariants with right inverse G-translation. Identify the
  node's `[x,w]` with `IndV.mk H.subtype ρ x⁻¹ w`. Then `[xh,w]` is Mathlib's generator
  at `h⁻¹*x⁻¹` with coefficient w. Applying h to that tensor in the coinvariants gives
  the generator at x⁻¹ with coefficient `ρ h w`, namely `[x,hw]`.
  The inverse generator relabeling sends the generator at y to `[y⁻¹,w]`; diagonal
  coinvariant relations hold in the node's quotient by its stated balancing relation.
  By `ind_mk`, a sends the generator at x⁻¹ to that at x⁻¹*a⁻¹ = (a*x)⁻¹, exactly
  left translation. This is the same convention already documented in
  `Sheaf.RepresentationTheory.BrauerMonomialInduction`.
- For every g: `(g : G)` is an arbitrary theorem argument.
- The left-hand character is `LinearMap.trace ℂ (IndV H.subtype ρ) (ind H.subtype ρ g)`.
  The induced space is finite-dimensional: finite-dimensionality passes from the finite
  group algebra and W to their tensor product and then to its coinvariant quotient.
  No finite-dimensionality assumption on induction is added to the signature.
- The first sum ranges over precisely `{x : G // x⁻¹ * g * x ∈ H}`. Its summand
  applies ρ to the subgroup element `⟨x.val⁻¹ * g * x.val, x.property⟩`, then takes
  its trace. Multiplication by `1 / (Nat.card H : ℂ)` gives the first fraction.
- The centralizer is `Subgroup.centralizer ({g} : Set G)`. Its elements are exactly
  those commuting with g, as `mem_centralizer_singleton_iff` confirms.
- The conjugacy class is Mathlib's `conjugatesOf g`; `IsConj` on a group says
  `∃ c, c*g*c⁻¹ = h`. Substitute c=x⁻¹ to obtain the node's x⁻¹*g*x convention.
- The final sum ranges over `{h : H // (h : G) ∈ conjugatesOf g}`, exactly H ∩ g^G,
  with each element counted once, and has summand `LinearMap.trace ℂ W (ρ h.val)`.
- Its coefficient is `(Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) /
  (Nat.card H : ℂ)`. Both fractions are complex divisions, not natural divisions.
- The signature is A=B ∧ B=C for the node's displayed A=B=C. All `∑ᶠ` sums have
  finite subtype index sets, hence are ordinary finite sums. `Nat.card` and `finsum`
  avoid adding Fintype enumerations or decidability assumptions.

Dependency declarations read and used:

- `def-weil-finite-dimensional-subspace`: Mathlib `FiniteDimensional`, from
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, the abbreviation of `Module.Finite`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, used by `IndV`'s definition.
- `def-weil-pbc-quotient-module`: `Submodule.hasQuotient` and the quotient module
  structure in `Mathlib.LinearAlgebra.Quotient.Defs`, used by
  `Representation.Coinvariants` in `Mathlib.RepresentationTheory.Coinvariants`.
- `def-weil-endomorphism-trace`: `LinearMap.trace` in `Mathlib.LinearAlgebra.Trace`.
  Its finite-basis expression is `LinearMap.trace_eq_matrix_trace`.
- Proof dependency `lem-weil-pbc-vector-space-free`: `Module.Free.of_divisionRing`
  in `Mathlib.LinearAlgebra.Basis.VectorSpace`, imported as a proof dependency.
- Proof dependency `def-weil-pbc-direct-sum-modules`: `DirectSum`, `DirectSum.lof`,
  and its module structure, imported through `Mathlib.Algebra.DirectSum.Module` as
  a proof dependency. All four statement dependency nodes have status mathlib and
  correctly have no `lean` record; their recorded `mathlib_match` is used.

Edge cases checked before writing:

- W=0: an empty basis gives zero induced space and zero traces in both sums.
- H=G: a single coset gives χ_W(g), and conjugation invariance makes both formulas
  equal this value; the class size times centralizer size is |G|.
- H={1}: the sum is empty for g≠1. For g=1 it gives |G| dim W.
- The trivial group: |H|=|G|=|C_G(1)|=1 and both sums are the identity trace.
- A conjugacy class disjoint from H: both index sets are empty, giving zero.
- g=1: the first value is |G|/|H| times dim W; the second uses centralizer G
  and the singleton identity in H. Subgroup cardinality is always nonzero because
  H contains 1. No positive-dimension, proper-subgroup, or nontriviality condition occurs.
- As a nonabelian sign check, for G=S₃, H generated by a transposition, and its sign
  character, the values on identity, transpositions and 3-cycles are (3,-1,0):
  on a transposition the centralizer and subgroup both have order two and the
  intersection is one transposition. This checks the conjugation orientation and factor.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder "Character of induced representation equals average over
  conjugates in subgroup and centralizer conjugacy class formula"`: eight hits,
  including `FDRep.average_char_eq_finrank_invariants`, `FDRep.char_conj`,
  `Rep.coindToInd_apply`, and `Representation.ind_mk`. These are invariance,
  reciprocity, or construction facts; none states either induced-character formula.
- `msearch.py ... loogle "Representation.ind, LinearMap.trace"`: zero hits.
- `msearch.py ... grep "ind.*char|char.*ind|character.*induc" RepresentationTheory`:
  one hit, the comment about linear independence of characters in Hilbert90.lean.
- `msearch.py ... leansearch "Induced character finite group conjugacy centralizer sum"`:
  eight hits, including `Representation.IndV`, `Rep.ind`, `LinearMap.sumOfConjugates`,
  the class equation and a centralizer/stabilizer cardinal lemma. None states this theorem.
- `rg -n` with `ind.*char|char.*ind|character.*induc|inducedCharacter|induced_character`
  over both `lean/WeilConjectures` and `lean/Sheaf`: only unrelated matching comments,
  additive trace characters, or other representation inputs; no matching formula.
- `grep -rn "lem-per-induced-character-conjugacy-formula" lean/WeilConjectures`:
  no matches. Exact proposed theorem-name searches in Mathlib, both project roots,
  and `dag/lean_names_upstream.json` returned no matches.
- Read `Mathlib.RepresentationTheory.Induced`, the coinvariants construction,
  the conjugacy and centralizer definitions, and the current blueprint proof
  `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`.
  The blueprint does not contain this auxiliary calculation, as the node honestly
  records; no claim is made that ILO Proposition 1.2 proves the formula.

No statement dispute or node fault was found. The prescribed example CompactObject.lean
is withdrawn and has no declarations; the module uses the stage-2 brief's required module
header, public statement imports, exposed section, source docstrings, and line width.

## Second reading by Q86

A separate second pass by this worker compared the completed signature to the original
node; the maintainer supplies the independent review, as specified in the dispatcher brief.
No other agent was started. G and W retain independent universes; finiteness, subgroup,
complex scalar field, dimension and H-action are all represented without extra assumptions.
The generator relabeling was checked in both directions: Mathlib's diagonal coinvariant
relation gives exactly the balancing relation, and right inverse translation becomes left
translation. The first sum uses the subgroup membership proof for its conjugate, the second
uses subgroup elements satisfying conjugacy, and the cardinal factors both lie in ℂ.
The conjunction is the two adjacent equalities, rather than a missing equality or a mere
character invariance statement. Zero W and either extreme subgroup remain allowed. No
mismatch was found and no signature correction was needed in this second pass.
