## Worker report

The module `Sheaf.Paper.PolynomialBarCofaceRetractionIdentities` states
`RationalPolynomialBar.coface_retraction_identities`, with its proof `sorry`.
It defines only the full indexed coface and the explicitly prescribed grading helpers;
all their data are real constructions. The accepted node statement, proof, dependencies,
and source fields are unchanged. No statement correction or disputed assertion is needed.

### Objects and each hypothesis

- `B : Type u`, `[CommRing B]`, `[Algebra ℚ B]` render an arbitrary commutative
  rational algebra. There is no domain, nontriviality, reducedness, field, or
  finite-dimensional assumption. The explicitly declared universe `u` is arbitrary.
- `r : ℕ` renders the nonnegative integer rank. Natural degrees `n,q : ℕ` render
  the nonnegative part, and the existing integer complexes give extension by zero.
- The existing `RationalPolynomialBar.P B r n` is literally
  `MvPolynomial (Fin n × Fin r) B`. Zero-based coordinates just relabel the node's
  blocks 1,...,n and coordinates 1,...,r.
- `RationalPolynomialBar.differential` is exactly the displayed first omission,
  alternating sum of adjacent additions, and last omission. `coface` names all
  n+2 substitutions as algebra maps. Its a=0 case shifts all input blocks; the
  intermediate face a merges input block a-1; the a=n+1 case leaves input blocks
  unchanged and hence omits the last output block.
- The existing `ExteriorIndex r q` consists of `Finset (Fin r)` with cardinality q;
  `K B r q` is `ExteriorIndex r q →₀ B`, the free module on exactly these subsets.
  `exteriorComplexNat` has zero differentials.
- The existing `inclusion` is the linear combination map on the ordered products
  from `Finset.orderEmbOfFin`. At q=0 its empty product is 1.
- The existing `projectMonomial` sums over tuples `j : Fin q → Fin r`, retaining
  exactly injective tuples whose `coordinateExponent` equals the input exponent.
  These are precisely the monomials with one variable in each block and distinct
  coordinates. Its coefficient `sortingSign` is the product of -1 over inversions,
  equal to the sign of the sorting permutation (a permutation and its inverse have
  the same sign). The output is `Finsupp.single (coordinateSubset ...)` with that sign.
  `projection` extends this rule using `MvPolynomial.basisMonomials.constr`.
  At q=0 the unique empty tuple, exponent zero, empty subset and empty sign product
  give the coefficient-preserving identification P⁰=B=K⁰; this is p⁰=1_B.

### Each conclusion

1. The first conjunct is the coface identity. The typed indices are
   `a b : Fin (n+2)` with `a ≤ b`: the outer left coface is `b.succ` and the
   outer right one is `a.castSucc`. Setting the node's b to this b+1 changes
   a<b into a≤b and its b-1 into this b. All valid faces, including both outer
   faces, are included with no out-of-range natural-number subtraction.
2. The second conjunct identifies the existing displayed `differential` with
   the signed sum of these named cofaces. This records what “cofaces defining d”
   means; it is the displayed differential, not an additional hypothesis.
3. `differential B r 0 = 0` is d⁰=0.
4. `(differential B r (n+1)).comp (differential B r n) = 0` is dⁿ⁺¹dⁿ=0.
5. `(differential B r q).comp (inclusion B r q) = 0` is d^q i^q=0.
6. `(projection B r (q+1)).comp (differential B r q) = 0` is p^(q+1)d^q=0.
7. `(projection B r q).comp (inclusion B r q) = LinearMap.id` is p^q i^q=1.
8. `coordinateWeight r n (a,j) = Pi.single j 1` assigns the required coordinate
   unit vectors. `MvPolynomial.IsWeightedHomogeneous` from Mathlib then expresses
   total coordinate multidegree, summing exponents over all blocks. `subsetWeight`
   is the indicator of I and `ExteriorHomogeneous` requires every nonzero subset
   coefficient to have that indicator. Four separate conjuncts state preservation
   by every coface, by d, by i, and by p, for every multidegree and homogeneous input.
   These homogeneous-component statements say exactly that all maps preserve the
   grading; arbitrary polynomials/vectors have finite homogeneous expansions.
9. For each `z : ℤ` with z<0, the two `Limits.IsZero` clauses state that
   `polynomialComplex B r` and `exteriorComplex B r` have zero objects there.
   These are the existing `ComplexShape.embeddingUpNat` extensions, so no new
   convention for negative degrees is introduced. Maps incident with those
   zero terms are uniquely zero; the displayed identities therefore extend there.
10. `r < q → Subsingleton (K B r q)` states the required upper-degree vanishing
    of K: subsets with cardinality q>r do not exist. This does not require B nonzero.
11. The last conjunct states the r=0 parity for every n and every `f : P B 0 n`.
    The canonical coefficient identification is `MvPolynomial.coeff 0`; its inverse
    is `MvPolynomial.C`. Since the variable type `Fin n × Fin 0` is empty, every
    polynomial is this constant. Thus the formula is zero for `Even n` and the
    identity of B otherwise, exactly the node's zero/identity alternating parity.

### Dependencies and existing constructions

Read the only statement dependency `def-weil-pbc-mv-polynomial-ring` and its Lean
record, including the full signatures/docstrings of `MvPolynomial`,
`MvPolynomial.aeval` and `MvPolynomial.algHom_ext` in Mathlib Basic/Eval. The
module explicitly publicly imports its recorded module
`Mathlib.Algebra.MvPolynomial.Basic`. The polynomial universal property is used
through `MvPolynomial.aeval` to construct `coface`, and polynomial extensionality
is identified in the proof docstring. This same node is the sole proof dependency.

Search found the exact P, K, merge, differential, ordered inclusion, signed
projection, and zero extensions already owned by
`lem-sfb-rational-polynomial-bar-contraction`, in
`Sheaf.Paper.RationalPolynomialBarContraction`. Read its complete module and node,
and confirmed the current live server source with `scompile.py --source`.
These objects are reused directly; neither `contraction` nor
`differential_squared` is invoked to prove the new identities. The complex object
itself already uses the latter named proof for its structure, as in its existing
record. No new definition node or dependency-module repair is needed: the new
helpers name only the cofaces and weights explicitly specified by this item.

**Import-cycle notice:** the parent's reviewed stage-1 split now lists this item
as a proof dependency. The parent module currently defines the common construction
and does not import this module. When maintaining proof imports, omit the reverse
import `RationalPolynomialBarContraction → PolynomialBarCofaceRetractionIdentities`
under `stages/2-statements.md` §3.7, since it would close the two-module cycle.
The present module imports the parent only to reuse its already-published
construction; it makes no logical appeal to the contraction theorem. No DAG
back-edge to the parent has been added. A future extraction of the shared
construction would allow the proof import, but changing that other node is outside
this delivery's authorized field scope.

Mathlib's `MvPolynomial.IsWeightedHomogeneous` is reused from
`Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous`, not redefined. The K grading
helper is just the coefficient condition for this node's specified subset basis.
All new declarations have source/blueprint docstrings; the sole theorem has all
eight accepted natural-language proof steps. Auto-bound implicits are disabled.

### Edge cases checked before writing

- n=0: the two cofaces are identical maps on constants, so d⁰=0; the first
  coface identity still compares every valid deletion of two of three vertices.
- q=0: unique empty subset and tuple; ordered product and sorting sign are 1,
  so both i⁰ and p⁰ are the canonical identities on B.
- q>r: there is no injective q-tuple and no q-element subset; K is zero,
  p and i are zero maps with the required zero-module identity.
- r=0: there are no polynomial variables in any degree; the n+2 alternating
  coface signs sum to 0 for n even and 1 for n odd. K is B only in degree zero.
- Negative degrees: both existing integer extensions are zero there, including
  the transition from -1 to 0; no negative index was coerced to a natural index.
- Zero algebra: no `[Nontrivial B]` occurs. The support-based grading predicates
  allow the zero vector in every weight; all identities remain well typed and true.
- Repeated-coordinate monomials project to zero. Quadratic blocks with distinct
  coordinates give opposite sorting signs; squared coordinates give repeated
  indices, so no division or assumption excluding zero algebras is hidden.

### Searches

Prescribed `msearch.py Q72 <item>` searches, logged by the wrapper:

- leanfinder: “The additive polynomial bar differential squares to zero and
  ordered coordinate monomials and signed multilinear projection are retraction
  cochain maps”. Eight hits, including `Rep.standardComplex.d_comp_ε`,
  `inhomogeneousCochains.d_eq` and Dold–Kan projections; none states these fixed
  polynomial cofaces, ordered inclusion, signed projection and multigrading.
- loogle: `MvPolynomial.aeval, MvPolynomial.lsum, CochainComplex.of`. No hit;
  diagnostic “unknown identifier MvPolynomial.lsum”. The nonexistent tentative
  name was not used in the implementation.
- grep: `(MvPolynomial|polynomial).*(coface|cobar|barComplex)|` followed by
  `(coface|cobar|barComplex).*(MvPolynomial|polynomial)`. No Mathlib matches.
- leansearch: “Multivariate polynomial homogeneous for a weight in a commutative
  additive monoid”. Exact useful hit `MvPolynomial.IsWeightedHomogeneous` and
  the corresponding weighted homogeneous submodule; reused as described above.

Direct `rg` searches for `polynomialBar|polynomial_bar|PolynomialBar` and the item
id over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
found the parent module above, but no theorem with all the requested conclusions.
The specifically requested `grep -rn` of the item id over `lean/WeilConjectures`
also found nothing. Broader polynomial/coface/bar searches in both source roots
found no other exact match. Searched candidate declaration names in Mathlib and
both project roots; the new names do not already exist. Read the current
`literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3): it motivates the open-direct-image route but does not assert this
agent-formulated polynomial lemma; the node accurately identifies that limitation.

### Validation

The initial file compiled successfully through the prescribed `scompile.py`, in
module mode both as sandbox and library module, in approximately 2.5 seconds per
compile. No warnings other than the permitted postponed-proof warning occurred.
The final wrapper dry run and delivery recompile the final file after its explicit
Mathlib Basic import was added. Only the node's `lean` field changes; JSON retains
one-space indentation, Unicode and a final newline. No live source, tool, or Git
state was directly modified.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
