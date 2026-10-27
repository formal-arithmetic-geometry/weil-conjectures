## Worker report

The module `Sheaf.RingTheory.SplitNodeSectionDualPresentation` states
`RingTheory.SplitNodeSection.split_node_section_dual_presentation`. Its only theorem
has proof `sorry`, with the entire twelve-step node proof described in its docstring.
The node's natural-language statement and dependencies are unchanged.

The auxiliary declarations are helpers for this very calculation, not alternative
notions: `Ring` is the actual quotient of `MvPolynomial (Fin 2) A` by `(XY-ab)`;
`x`, `y` are its actual quotient classes; `sectionIdeal` is the span of `x-a,y-b`;
`u`, `v` are those generators as elements of that ideal. `Dual` abbreviates
Mathlib's `Module.Dual`, `inclusion` is the ideal subtype linear map, `multiplier`
is scalar multiplication on that inclusion, and `presentation` is the displayed
map from the product of two copies of the ring. `Presentation` is a Prop-valued
package of precisely the presentation and exact-sequence clauses below. Its
augmentation and quotient map are arguments, not unproved definitions of data.
The three named instances only expose the actual quotient's ring and coefficient
algebra structures, including restriction along a coefficient algebra map.
There are no chosen data from an undetermined existence theorem and no helper sorries.

Clause-by-clause correspondence:

- Any commutative ring A and any a,b: `{A : Type u} [CommRing A]` and `(a b : A)`;
  there is no field, domain, Noetherian, local or nontriviality assumption.
- R=A[x,y]/(xy-ab): `Ring a b` is exactly this quotient, with `Fin 2` indexing
  its two polynomial variables. The constant term is `MvPolynomial.C (a*b)`.
- The augmentation: the existential `ε : Ring a b →ₐ[A] A`, together with
  `ε (x a b) = a` and `ε (y a b) = b`, fixes evaluation uniquely on all polynomials.
- I=ker ε=(x-a,y-b): `sectionIdeal` is the latter actual span and the third
  `Presentation` clause is `RingHom.ker ε.toRingHom = sectionIdeal a b`.
- M=Hom_R(I,R): `Dual a b` is the existing `Module.Dual (Ring a b) (sectionIdeal a b)`.
- Both finite presentation conclusions: the two `Module.FinitePresentation`
  clauses refer to I and to this actual dual, respectively.
- Existence and uniqueness of e: the existential `e : Dual a b`, its two equations
  on `u` and `v`, and `∀ e', ... → e' = e`. The first value is the negative
  algebra image of a; the second is the residue class of y.
- The map R²→M: `presentation a b e` is the sum of the two scalar-multiplier maps
  composed with product projections. `Function.Surjective` asserts surjectivity;
  its `LinearMap.ker` is the `Submodule.span` of exactly `(a,u)` and `(-y,v)`.
- The map R→M is `multiplier a b`; its injectivity is explicit.
- The quotient map is `π : Dual a b →ₗ[A] A`, with
  `π (r • inclusion a b + s • e) = ε s`. The extra equation
  `π (r • m) = ε r * π m` expresses exactly R-linearity for the ε-induced
  R-action on A; it introduces no alternative or arbitrary R-module structure.
  `Function.Exact (multiplier a b) π` and `Function.Surjective π`, together
  with multiplier injectivity, render the full short exact sequence.
- Arbitrary ring map A→A': `∀ (A' : Type v) [CommRing A'] [Algebra A A']`.
  An algebra structure on a commutative target ring is exactly a ring map, so
  this includes every coefficient map, including nonflat maps. Universes u,v
  are independent. Primed a,b are the algebra images of a,b.
- The induced ring map ρ is an A-algebra homomorphism fixing x,y to the primed
  classes; these generator equations characterize the canonical ring map.
  `i` and `m` are linear equivalences from the actual tensors to the actual
  primed ideal and dual. The pure tensor formula for i is
  `(i (c⊗z)).val = c • ρ z.val`. The formula
  `m(c⊗φ)(i(d⊗z)) = (c*d) • ρ(φ z)` specifies the canonical dual comparison,
  on all functionals, not just the two generators.
- Primed counterparts and exact sequence: `Presentation a' b' ε' e' π'`;
  `m(c⊗inclusion)=c • inclusion'`, `m(c⊗e)=c • e'`, and
  `π'(m(c⊗φ))=c*image(π φ)` identify both generators and the quotient arrow.
  The first arrow is identified for every r by the inclusion equation and
  A'-linearity: m(c⊗r·inclusion)=c·ρ(r)·inclusion', using the canonical
  dual-evaluation formula. Thus the whole tensored sequence is the primed one.
- Every flat R-algebra C: independent `C : Type w`, `[CommRing C]`,
  `[Algebra (Ring a b) C]`, `[Module.Flat (Ring a b) C]`. The last is precisely
  flatness of the specified ring map, by `RingHom.flat_algebraMap_iff`.
- IC is the actual mapped ideal `(sectionIdeal a b).map (algebraMap _ C)`.
  The flat-case i and m are C-linear equivalences with this ideal and its
  actual `Module.Dual`. Their pure-tensor/evaluation formulas are respectively
  `c⊗z ↦ c*image(z)` and `m(c⊗φ)(i(d⊗z))=c*d*image(φ z)`.
- Generator compatibility over C: m carries the inclusion to the ideal's
  actual subtype map; evaluating the general formula with φ=e gives the
  induced e, with values `-image(a)` and `image(y)` on the induced generators.
  C-linearity extends those values from 1⊗e to c⊗e.
- The last sequence has middle term the actual `C ⊗[R] Dual a b` and last
  term the actual ideal quotient `C ⧸ IC`. The quotient map q satisfies
  `q(c⊗(r·inclusion+s·e)) = [c*image(s)]`; this is the tensor of π under
  the canonical identification C⊗_R A=C/IC. Its initial arrow is literally
  `c ↦ c • ((1 : C) ⊗ₜ inclusion)`, with injectivity and exactness explicit,
  and q is surjective. No abstract existence of an unspecified short exact
  sequence replaces the displayed arrows.

Dependencies read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.algHom_ext`
  in `Mathlib.Algebra.MvPolynomial.Basic`, and `MvPolynomial.aeval` in
  `Mathlib.Algebra.MvPolynomial.Eval`; their full signatures and docstrings
  were read. The Eval import exposes the polynomial construction and its API.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation` in
  `Mathlib.Algebra.Module.FinitePresentation`, its finite-generator/finite-relation
  definition and finite-free presentation equivalence.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat` and `Module.Flat`, via
  `Mathlib.RingTheory.RingHom.Flat`, with `RingHom.flat_algebraMap_iff` and the
  tensor-injectivity characterization read in `Mathlib.RingTheory.Flat.Basic`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk`
  (Defs), `TensorProduct.lift` and `TensorProduct.ext'` (Basic), and
  `LinearMap.rTensor` (Map), all read and exposed through the TensorProduct.Tower
  import. Tensor notation is Mathlib's global scoped notation.
- Proof-only `lem-weil-pbc-tensor-right-exact`: `LinearMap.lTensor_exact` and
  `LinearMap.rTensor_exact` in `Mathlib.LinearAlgebra.TensorProduct.RightExactness`,
  imported without public visibility; the signatures were read.
- Other construction APIs: Mathlib ideal quotient, ideal span, Module.Dual,
  LinearMap.smulRight, product linear maps and Function.Exact. No dependency
  needs a repaired interface or a second definition.

Source read: the primary author text at https://arxiv.org/html/1106.1588, Section 3
(matrix factorization, Proposition 3.1, Corollary 3.2) and Section 4. The inherited
node already supplies the arbitrary-ring split-coordinate argument; this delivery
preserves it. The current blueprint and upstream-name searches yielded no existing
formalization of this particular local calculation.

Edge cases checked mathematically against the signature and displayed relations:

- A the zero ring (all quotient rings and modules are zero); no Nontrivial binder.
- a=b=0: e has values (0,y); the relation module is generated by (0,x),(-y,y).
- a a unit: I is principal and the formula e(u)=-a is consistent with the relation
  y*u+a*v=0; the quotient M/R is still A, not zero.
- A=Z/4 and a=b=2: f=xy, no cancellation of 2 occurs in the presentation.
- Characteristic 2: the minus signs are ring negatives, with no use of 2 inverse.
- Nonflat coefficient maps such as Z→Z/2 are included; exactness is asserted
  for the primed presentation rather than inferred from preservation of injections.
- Identity coefficient map and arbitrary independent coefficient universes included.
- C the zero R-algebra: all flat-clause equivalences and the exact sequence are zero.
- For A a field and a=b=0, IC may be nonprincipal; the signature uses the actual
  ideal and dual, not a freeness hypothesis.

Searches made (wrapper outputs are in sandbox searches.jsonl):

- LeanFinder: "Explicit dual presentation of the section ideal (x-a,y-b) in
  A[x,y]/(xy-ab), with arbitrary base change". Eight hits on cotangent and
  submersive presentation constructions; none is this dual-section calculation.
- Loogle: `MvPolynomial, Module.Dual`. No hits.
- LeanSearch: "The dual of the section ideal of xy=ab has a two generator
  presentation compatible with base change". Hits on FractionalIdeal.dual and
  IsBaseChange.dual. The latter's full source was read: it requires finite free
  modules, and hence does not give this singular ideal theorem.
- Mathlib grep through msearch: `splitNode|split_node|nodal.*dual|dual.*nodal|sectionDual`:
  no hits. `matrix.?factori[sz]|splitNode|split_node|nodal.*dual|dual.*nodal`
  in RingTheory: no hits.
- Direct rg of the same concepts in lean/WeilConjectures and lean/Sheaf:
  unrelated nodal geometry and completion transport, and a proof docstring in
  SectionIdealProjExpansion citing this item; no declaration of this calculation.
- Direct rg of the exact item id upstream: no match. No upstream indexed name
  and no blueprint statement duplicates this local dual computation.

Validation: scompile.py compiles the module under both its sandbox and final
module paths in about 2.3 seconds each, with no warnings or errors. No local or
global Lake build was run. All variables/universes are bound explicitly and
both auto-implicit options are disabled. No statement correction, disputed
statement, new independent node or dependency module is needed.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
