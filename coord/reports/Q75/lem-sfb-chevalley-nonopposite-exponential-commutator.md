## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyNonoppositeExponentialCommutator` states
`LieAlgebra.chevalley_nonopposite_exponential_commutator` with `sorry` and defines the
actual finite lattice exponential `LieAlgebra.admissibleRootExponential`. Both declarations
belong to the assigned node and are listed in its lean.declarations. The helper is the
exponential explicitly introduced by this node, not a separate independent notion.
No dependency record or mathematical statement has been changed.

Source read: Milne, Algebraic Groups (2017), printed pp.508--511, especially the bracket
table and Theorem 23.71, the admissibility condition on p.510, and equation (153).
The integral two-root calculation is explicitly agent-written in the node; Milne supplies
the normalization and exponential, not this complete universal-ring assertion.
The current blueprint at literature/blueprint/latest was searched for Chevalley/exponential
occurrences; this is an auxiliary node rather than a blueprint unit's own statement.

Hypotheses and clauses, in node order:

- Finite-dimensional rational semisimple algebra: `L`, `LieRing L`, `LieAlgebra ℚ L`,
  `FiniteDimensional ℚ L`, `HasTrivialRadical ℚ L`. The last is the exact recorded
  semisimplicity predicate, not the different direct-sum definition of IsSemisimple.
- Split Cartan: `H : LieSubalgebra ℚ L`, `H.IsCartanSubalgebra`, and
  `LieModule.IsTriangularizable ℚ H L`. These are Mathlib's splitting-Cartan encoding.
  The supplied root eigenvectors and Chevalley basis give the actual eigen decomposition.
- Finite reduced crystallographic root system in H dual: finite root index `I`,
  `P : RootPairing I ℚ (Module.Dual ℚ H) H`, with IsRootSystem, IsCrystallographic,
  IsReduced. `heval` specifies that the perfect pairing is evaluation, so the abstract
  coroot data have precisely the required meaning in H. Indexing roots by an embedding
  retains each root exactly once, equivalently the subset R of the node.
- Simple coroots and root vectors give a basis: `Δ : P.Base`, `B` indexed by
  `Δ.support ⊕ I`, with `Bh` and `Be`. Consequently the Cartan and root lines give
  the stipulated internal direct sum; no extra root spaces or vectors are allowed.
  `he` states both nonvanishing and `[h,e_i] = root_i(h) e_i` for every h.
- Opposite-root normalization is `hopp`. `P.reflectionPerm i i` indexes minus root_i,
  and `P.coroot i` is its coroot under evaluation.
- Sum-root bracket constants are `hadd`, with integer sign epsilon equal to 1 or -1
  and magnitude `P.chainBotCoeff i j + 1`. Mathlib RootSystem/Chain.lean, definition
  chainBotCoeff and root_sub_nsmul_mem_range_iff_le_chainBotCoeff, identify this with
  the maximum p in the node for independent roots. A sum that is a root is independent
  in a reduced system. `hzero` gives zero bracket when the sum is neither root nor zero.
- `α β : I`, `hne`, `hnopp` render the two exclusions, without excluding orthogonal roots.
- The ordered finite set S is `s : List (ℕ × ℕ × I)`. `hs : s.Nodup` excludes repetitions;
  `hmem` is the exact iff: positive i,j and i alpha+j beta equal the indexed root.
  Since P.root is injective, attaching the third coordinate adds no choices or pairs.
  `horder : s.Pairwise ... ≤ ...` is precisely any total enumeration refining i+j;
  it permits either ordering of equal heights.
- `∃ c : ℕ × ℕ → ℤ` comes BEFORE W, its representation, lattice, ring and parameters.
  Values outside S have no role. Thus the integers depend only on the Chevalley data,
  the roots and specified order, even when the representation is zero or not faithful.
- Rational finite-dimensional W: the four binders for W, AddCommGroup, Module ℚ and
  FiniteDimensional. A representation is the standard `LieRingModule L W` and
  `LieModule ℚ L W`; its actual Lie hom is `LieModule.toEnd ℚ L W`.
  These encode exactly an arbitrary bracket-preserving rational linear representation.
- Full finite free integer lattice: `Λ : Submodule ℤ W`, `Submodule.IsLattice ℚ Λ`
  (finite generation and rational span all W), and `Module.Free ℤ Λ`. A subgroup of a
  rational vector space is torsion free; these are exactly finite freeness and fullness.
- Nilpotence is `hnil` for every root. Divided-power stability is `hstable`, for every
  root, natural exponent m including zero, and lattice member w.
- `admissibleRootExponential` first restricts the rational divided-power endomorphism
  to Λ using `LinearMap.restrictScalars` and `LinearMap.restrict` with hstable, then
  extends scalars using `LinearMap.baseChange A`, and takes the finite weighted sum.
  Its cutoff is finrank ℚ W. A nilpotent endomorphism of a d-dimensional vector space
  has d-th power zero, so this is exactly the node's entire finite exponential.
  `A ⊗[ℤ] Λ` is the canonical commuted form of `Λ ⊗[ℤ] A`, using A-linear base change.
  All data in this definition are constructed; no existential choice or sorry occurs.
- The final equality has the four factors in the precise order alpha(a), beta(b),
  alpha(-a), beta(-b). `List.map` followed by `.prod` preserves the supplied order;
  each argument is the cast of c_(i,j) times a^i times b^j, at its specified root.
- The quantifier `∀ (A : Type z) [CommRing A] (a b : A)` includes every commutative
  ring, rather than just fields. Taking the integer polynomial ring with its two
  generators is the polynomial matrix identity over ℤ[u,v]; all other choices are its
  evaluations. Universes u,v,w,z are explicitly independent; none restricts coefficient
  characteristic or forces the space and coefficient ring into the same universe.
- Empty product is `.prod` of the empty list, hence one. There is no assumption of
  representation faithfulness, weight generation, or any algebraic group structure.

Dependencies read and used:

- `def-wf-lie-algebra`: its Mathlib match, LieRing and LieAlgebra in
  Mathlib.Algebra.Lie.Basic and LieModule.toEnd in Mathlib.Algebra.Lie.OfAssociative.
  Read the signatures and docstrings; LieModule's identities give the commutator action.
- `def-wf-semisimple-lie-algebra`: its Mathlib match HasTrivialRadical in
  Mathlib.Algebra.Lie.Semisimple.Defs and hasTrivialRadical_iff_no_solvable_ideals
  in Mathlib.Algebra.Lie.Semisimple.Basic, read with its full signature.
- `lem-sfb-chevalley-admissible-representation`: public import of
  Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation; read the complete signature and
  docstring of LieAlgebra.exists_chevalley_admissible_representation. Its Chevalley and
  admissibility conventions are used, but its faithful full-weight representation is
  not substituted for the arbitrary representation quantified over by this item.
- Both other proof dependencies, lem-sfb-chevalley-string-central-parity and
  lem-sfb-formal-class-two-exponential, had no recorded Lean declarations at reading.
  Their natural-language statements were read; they are recorded in the six-step proof
  docstring, and no invented import or theorem standing in for them was added.

Edge cases checked mathematically before writing: W=0 gives finrank=0 and a zero lattice;
its endomorphism ring is subsingleton, so the empty exponential sum is also the identity.
For T=0 and positive-dimensional W, the m=0 term gives one and all other terms vanish.
For a=0 or b=0 the commutator and all right factors are one. Orthogonal roots with no
positive mixed root give s=[] and the identity. Equal-height factors are allowed in any
order. Torsion rings, rings with nilpotents and the zero ring are all included. The root
system may be empty, in which case the requested alpha,beta cannot be supplied; no
spurious nonemptiness hypothesis was imposed. The nilpotence cutoff includes d=1.

Searches actually run (msearch.py, group Q75, this item):

- leanfinder: "Integral Chevalley commutator formula for nilpotent root vector exponentials
  on an admissible lattice". Eight GeckConstruction bracket results, including
  lie_e_lie_f_apply, e_lie_v_ne, f_lie_v_ne; no integral exponential commutator formula.
- loogle: `"LieAlgebra", "commutator"`. Five hits, four CommutatorRing instances and
  matrix_trace_commutator_zero; no match for the required statement.
- grep: `Chevalley|divided.?power|exponential`, subdirectory Algebra/Lie. Fifteen hits,
  including nilpotent derivation exponentials and Basis/Basic's TODO to define Chevalley
  bases; none gives this statement or a lattice exponential construction.
- leansearch: "Chevalley commutator formula for root exponentials on integral admissible
  lattices over arbitrary rings". Eight hits, root-space brackets, analytic exponentials,
  adjoint-power expansion and ordinary commutators; no integral polynomial identity.
- rg of lean/WeilConjectures and lean/Sheaf for Chevalley, rootExponentials and divided
  powers: existing admissibility, rank-two divided-power straightening and integral
  model statements, but no integral nonopposite exponential commutator. Read the complete
  rank-two straightening signature; it is an enveloping-algebra degree-lowering statement,
  not this universal-ring exponential identity.
- grep -rn of the item id in lean/WeilConjectures: no result. Exact-name rg for both new
  declarations in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no result.

No STATEMENT-DISPUTED issue or statement correction was needed. Compilation uses only
scompile.py; initial errors were tensor notation scope and use of a bare LieHom into
endomorphisms without a global LieRing instance. The module now uses the canonical
LieModule interface and scoped TensorProduct notation. A line-width warning was repaired.

## Second reading by Q75

A separate pass reread the full statement against the final signature and helper body.
This is a worker rereading, not a claim that a second agent reviewed it; the dispatch
instructions prohibit starting other agents and specify the maintainer's independent
review. The review-sensitive points are the quantifier order for c, arbitrary rather than
faithful representations, m=0 and zero-dimensional exponential, exact enumeration of S,
and polynomial rather than field-point identity. The final quantifiers, list iff,
List.prod and coefficient-ring quantifier preserve each of these. The helper's scalar
extension uses the standard tensor commutation, not an arbitrary replacement map.
The second pass found and repaired the overlong final-factor line. No statement mismatch
was found. There are no added nodes or dependency repairs to review.
