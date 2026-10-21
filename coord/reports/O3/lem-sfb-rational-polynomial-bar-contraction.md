## Worker report

Stage 2, O3: `lem-sfb-rational-polynomial-bar-contraction`.

The delivery states the current reviewed node in
`Sheaf.Paper.RationalPolynomialBarContraction`, namespace `RationalPolynomialBar`.
The only JSON change is its `lean` record. The current stage-1 statement, eight
proof steps, dependencies and Q15 review are preserved. The previous attempt left
only dispatcher briefs in the sandbox. Its reported rejection concerned a stage-1
split already reviewed; this delivery supplies the missing stage-2 Lean statement.

I read the current node and its polynomial-ring dependency; the full stage-2 brief,
stage document, delivery-errors H, worker role, SETUP, GOAL, STATE and tools README;
the withdrawn CompactObject example and its node; the current blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3); and Q15's existing
stage-1 report. The blueprint supplies the surrounding open-direct-image reduction,
not this polynomial algebra proof. The module faithfully attributes the lemma to
the agent-formulated algebraic obligation, as the node does. No statement correction,
statement dispute, dependency repair, new node, or downstream change is needed.

Every hypothesis and clause has the following rendering:

- A commutative rational algebra B: explicit `(B : Type u) [CommRing B] [Algebra ℚ B]`.
  There is no `Nontrivial` instance or domain hypothesis. The natural number r
  is the arbitrary rank, including zero. All universes and variables are bound;
  both auto-implicit options are false.
- P in degree n: `P B r n = MvPolynomial (Fin n × Fin r) B`. The Fin indices
  are the order-preserving zero-based encoding of the node's one-based indices.
  `polynomialComplexNat` uses exactly these terms and `differential`.
- The first coface substitutes `(b.succ,i)`; `merge B r n a` substitutes the same
  block before a, the sum of adjacent coordinates at a, and the next block after a.
  Its coefficient is `(-1 : B) ^ (a.val + 1)`. The last coface uses `b.castSucc`
  with coefficient `(-1 : B) ^ (n + 1)`. These are exactly the three displayed
  parts of df, without normalization or an omitted outer coface.
- Degree-zero cancellation is the first conjunct `differential B r 0 = 0`.
  `differential_squared` states d² = 0 separately as the construction obligation
  for `polynomialComplexNat`; contraction's second conjunct also includes it.
- Negative degrees of P are zero: `polynomialComplex` uses Mathlib's extension
  along `ComplexShape.embeddingUpNat`. Its definition is extension by zero on
  integers outside the image of ℕ, not a second polynomial-complex construction.
- K in degree q is `K B r q = ExteriorIndex r q →₀ B`, where
  `ExteriorIndex r q = {I : Finset (Fin r) // I.card = q}`. It is the free
  B-module with precisely the prescribed subset basis. Its differential is zero
  in `exteriorComplexNat`; `exteriorComplex` extends by zero in negative degrees.
  For q > r no subset index exists, so the module is zero, including the case
  of nonzero coefficients.
- Inclusion i is `inclusion`: a B-linear combination of products
  `∏ a : Fin q, MvPolynomial.X (a, I.val.orderEmbOfFin I.property a)`.
  `orderEmbOfFin` is the increasing enumeration of I. For q = 0 the empty product
  is 1, giving exactly i(e_empty) = 1.
- The monomial projection is `projectMonomial`. It sums over all coordinate
  tuples j, keeps only injective tuples, and tests that the monomial exponent
  is `coordinateExponent r q j = ∑ a, single (a,j a) 1`. This selects exactly
  total degree one in every block, with pairwise distinct coordinates. All
  other monomials are sent to zero.
- For a retained tuple, `coordinateSubset` is its image subset with the proof
  of cardinality q. `sortingSign` is the product of -1 over pairs a < b with
  j(b) < j(a), hence the sign of the permutation sorting the tuple. The image
  is precisely that sign times its subset basis vector. `projection` extends
  these values B-linearly using `MvPolynomial.basisMonomials.constr`.
- For q = 0 there is one empty tuple, one zero exponent, sign 1 and one empty
  subset. Polynomials in no variables are constants, so this is p⁰ = 1_B under
  the canonical identifications. There is no different augmentation map.
- di = 0 is `(differential B r q).comp (inclusion B r q) = 0`; pd = 0 is
  `(projection B r (q+1)).comp (differential B r q) = 0`; pi = 1 is
  `(projection B r q).comp (inclusion B r q) = LinearMap.id`.
- The existential h is a family of rational linear maps from degree n+1 to
  degree n. It precedes the universal quantifier over B, ensuring that the
  same rational monomial matrix is used over every rational algebra B.
  `extendHomotopy` sends each B-monomial to the coefficient-map image of its
  rational h-image and extends B-linearly using the monomial basis. Thus each
  column has finite support because its image is an actual polynomial.
- h⁰ has target the zero negative-degree term and is the zero map. In degree
  zero the equation is explicitly `h¹.comp d⁰ = id - i⁰.comp p⁰`. In positive
  degree n+1 the final conjunct is exactly `dⁿ.comp hⁿ⁺¹ + hⁿ⁺².comp dⁿ⁺¹ =
  id - iⁿ⁺¹.comp pⁿ⁺¹`. Negative-degree equations are zero by extension. These
  equations, with di = pd = 0, are the cochain homotopy equivalence asserted
  in the node, rather than only isomorphisms of cohomology groups.
- The zero algebra is included by the absence of any nontriviality assumption.
  For r = 0, `Fin n × Fin 0` is empty, so every P term is B, while K has only
  degree zero. The inclusion is precisely the degree-zero inclusion into the
  unnormalized constant complex; positive-degree P terms have not been deleted.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: Mathlib's `MvPolynomial`,
  `MvPolynomial.aeval`, and `MvPolynomial.algHom_ext`, in
  `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`. I read their full signatures
  and source docstrings. The polynomial ring and evaluation are reused directly;
  there is no private polynomial ring or replacement universal property.
- Further canonical construction tools are `MvPolynomial.basisMonomials`
  (`Mathlib.RingTheory.MvPolynomial.Basic`), `Finsupp.linearCombination`
  (`Mathlib.LinearAlgebra.Finsupp.LinearCombination`), `Finset.orderEmbOfFin`
  (`Mathlib.Data.Finset.Sort`), `CochainComplex.of`, and
  `HomologicalComplex.extend` / `ComplexShape.embeddingUpNat`
  (`Mathlib.Algebra.Homology.Embedding.Extend`). These implement the objects
  already explicitly specified by this node; no independent new notion is needed.
- Stated proof dependencies are ordinary, non-public imports:
  `CategoryTheory.SimplicialObject.Splitting.homotopyEquivNondegComplex` from
  `Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject`, and
  `Submodule.exists_isCompl` from `Mathlib.LinearAlgebra.Basis.VectorSpace`.
  Their actual source declarations were read. The proper-product-interval
  homology proof dependency has no Lean declaration yet, so no import is invented
  for it. Its cited mathematical input remains in the contraction docstring.

The helpers in this module implement only the specific objects already introduced
by the item: its terms, cofaces, i, p, scalar extension, and complexes. Every helper
is recorded in `lean.declarations` with a source/blueprint docstring. There are two
postponed theorems, both clauses of this very node: `differential_squared` (needed
to construct the complex) and `contraction` (the full assertion). Their docstrings
contain the complete mathematical proofs using the node's named inputs. No theorem
is proved in this stage; no definition's data is `sorry` or chosen from unproved
mere existence. The trivial zero-square field of the zero-differential K is filled
by simplification, rather than by an additional mathematical assumption.

Edge-case/sign audit:

- n = 0: the inner sum is empty and the two outer substitutions cancel.
- q = 0: the unique empty tuple has exponent zero, sign one, and empty subset;
  both i and p are the identity under identification with B.
- r = 0: dⁿ is zero for even n and identity for odd n. Taking hⁿ = identity
  for even n >= 2 and zero otherwise gives the displayed homotopy equations.
- q > r: there are no injective tuples, and no subsets of cardinality q, so
  the projection and K vanish; no finite-rank bound is added as a hypothesis.
- q = 2: increasing (j1,j2) has sign +1; decreasing has -1; repeated indices
  fail injectivity. This checks the prescribed unsymmetrized ordered inclusion,
  with no factorial factor and no antisymmetrized inclusion substituted for it.
- The zero algebra, zero polynomials and empty sums/products remain well typed.
  The rational h-images are genuine finite polynomials, so scalar extension
  uses finite sums, including over the zero algebra.

Searches executed with the prescribed msearch.py for O3 / this item:

- LeanFinder: "The rational polynomial additive bar cochain complex contracts onto
  ordered exterior coordinate monomials". Eight hits included
  `ExteriorAlgebra.ιMulti_family`, exterior-power presentations,
  `Rep.standardComplex.d`, and `Rep.barComplex.d_single`. They concern exterior
  products or the discrete group bar resolution, not this polynomial complex.
- Loogle: "MvPolynomial, Homotopy". No hits.
- Mathlib grep: "(polynomial|cobar).*(homotopy|contraction)|(homotopy|contraction).*(polynomial|cobar)".
  Seven hits were polynomial separable-contraction/expansion lemmas; none matches.
- LeanSearch: "The polynomial additive bar complex over a rational algebra has a
  homotopy contraction onto exterior coordinate generators". Eight hits included
  `Rep.barComplex`, `AlgebraicTopology.DoldKan.homotopyPToId`, and general
  HomotopyCategory lemmas; none supplies this polynomial contraction.
- Direct project rg searches in both `lean/WeilConjectures` and `lean/Sheaf`
  for polynomial/bar/contraction combinations found only unrelated ring-theory
  or coefficient constructions. The exact item-id search in WeilConjectures had
  no result. Fresh searches for `RationalPolynomialBar`, `ExteriorIndex`, and
  `coordinateExponent` found no existing definitions of these objects. DAG and
  source searches locate the current item and its stage-1 proof inputs, but no
  existing Lean statement of it. Existing searches and metadata are preserved.

Validation: the required server scompile.py compiled the sandbox and library
module paths cleanly (4.4 s and 4.3 s). The first compile exposed a module-instance
mismatch from using generic Finsupp.linearCombination on polynomials; replacing
that with Mathlib's actual monomial basis resolved it. All delivered definitions
have real data. The final comments/records are checked again by the prescribed
delivery dry run; no local Lean compiler or global build is used.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
