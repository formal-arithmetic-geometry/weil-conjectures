## Worker report

The module `Sheaf.RingTheory.ResidueAlgebraFiniteTypeModel` states
`IsLocalRing.residue_algebra_finite_type_model`. Its only postponed proof is this theorem,
with the complete four-step proof from the node in the declaration docstring. There are no
new definitions, dependency repairs, new nodes, or statement corrections. Only the item's
`lean` field changes. The original statement and accepted split are retained.

Hypothesis and clause correspondence:

- A nonzero commutative local ring A: `(A : Type u) [CommRing A] [IsLocalRing A]`.
  Mathlib's `IsLocalRing` extends `Nontrivial A`; for commutative rings it is equivalent
  to the unique-maximal-ideal convention. `maximalIdeal A` is that maximal ideal.
- A commutative A-algebra C: `(C : Type v) [CommRing C] [Algebra A C]`.
  The universes u and v are independent, and C need not be nontrivial or flat.
- The specified finite generating family, including n=0: `(n : ℕ) (c : Fin n → C)` and
  `(hc : Function.Surjective (MvPolynomial.aeval (R := A) c))`.
  This says precisely that every element is a polynomial in this family with coefficients
  from A; it does not replace the chosen family by existentially selected generators.
- k=A/m is Mathlib's `IsLocalRing.ResidueField A`, whose definition is exactly
  `A ⧸ maximalIdeal A`. The coefficient quotient map is `IsLocalRing.residue A`.
- mC is `(maximalIdeal A).map (algebraMap A C)`. The definition of `Ideal.map` is the
  ideal span of the image, so it is exactly the extended ideal, even when it equals top.
  D is `C ⧸ (maximalIdeal A).map (algebraMap A C)`. Every displayed quotient map is
  `Ideal.Quotient.mk` of this same ideal.
- k is a field: `IsField (ResidueField A)`. This predicate states nontriviality,
  commutativity and inverses of all nonzero elements on the existing ring structure;
  it is the propositional version of the dependency's `Field`, via `Field.toIsField`.
  Mathlib already supplies the canonical `IsLocalRing.ResidueField.field` instance,
  constructed from the maximal-ideal quotient field.
- k is Noetherian: `IsNoetherianRing (ResidueField A)`.
- The induced k-algebra structure: the existential witness is a ring homomorphism
  `β : ResidueField A →+* D`. By `RingHom.toAlgebra` this is exactly a k-algebra
  structure on the fixed commutative ring D, as the algebra-definition dependency says.
  The first conjunct gives its value `β (residue A a) = q (algebraMap A C a)` for EVERY
  a in A. The next conjunct says EVERY ring homomorphism γ satisfying that formula
  equals β. Thus the action is characterized uniquely on all residue classes. This is
  a theorem asserting the uniquely determined action, not an assumed arbitrary action
  or a definition choosing data from a nonunique existence theorem. The construction in
  the proof is also Mathlib's `Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map`.
- The exact reduced family generates D over k: the next conjunct is surjectivity of
  `MvPolynomial.eval₂Hom β (fun i ↦ q (c i))`, the elementwise polynomial-generation
  condition over k. Its domain is `MvPolynomial (Fin n) (ResidueField A)`.
- Coefficient reduction for every polynomial expression: the next conjunct quantifies
  `P : MvPolynomial (Fin n) A` and states
  `q (MvPolynomial.aeval c P) = MvPolynomial.eval₂ β (fun i ↦ q (c i))
  (MvPolynomial.map (residue A) P)`.
  `MvPolynomial.map` reduces every coefficient modulo m, and the variable family on the
  right is exactly the image of the original c. This is equality of the evaluated
  expressions, not a claim that only some expression for each element is compatible.
- D is a finite type k-algebra: the final conjunct is `β.FiniteType`, exactly the
  recorded `RingHom.FiniteType` interface of the finite-type dependency. It unfolds to
  `Algebra.FiniteType` for the k-action `β.toAlgebra`.

Dependency declarations read and used:

- `def-weil-pbc-algebra-hom-quotient`: Mathlib's `Algebra`, `AlgHom`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, and ideal operations, from
  `Mathlib.Algebra.Algebra.Hom` and `Mathlib.RingTheory.Ideal.Quotient.Operations`.
  The statement uses their underlying ring maps and quotients directly.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType` in
  `Mathlib.RingTheory.FiniteType` (the node's recorded interface), with the same
  module's `Algebra.FiniteType`; the chosen family is expressed by polynomial evaluation.
- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, rendered as `IsField`
  on the fixed quotient ring, using `Mathlib.Algebra.Field.IsField`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, exactly the recorded declaration.
- Proof dependency `lem-weil-common-extension-fields-quotient-field`:
  `Ideal.Quotient.field` in `Mathlib.RingTheory.Ideal.Quotient.Basic`, imported without
  `public` for the proof plan. No project prerequisite needs repair.

Sources read: `literature/stacks-project/algebra.tex`, definition-finite-type (00F3),
section-Noetherian (00FM), and `literature/stacks-project/fields.tex` opening discussion
of the residue field of a local ring (09FB). The node's imported top-level source locator
still mentions section-examples, but its proof and split review already identify 09FB;
this delivery preserves the source field as required.

Edge cases checked before writing:

- n=0: `Fin 0` is allowed and the hypothesis says C is a quotient of A, while the
  conclusion uses the empty reduced family and constant polynomials over k.
- C=0 and mC=C: D is the zero ring. Maps from k to D exist as unital ring maps;
  neither injectivity nor nontriviality of C or D is required.
- A is a field: m=0, and the quotient coefficient action agrees with the original
  action after the canonical zero-ideal quotient identifications.
- A=Z/4 and C=A/(2): the reduced family may be empty and the result reduces to the
  residue field. No Noetherian hypothesis on A is imposed.
- C=A[x]/(p*x-1) over the local ring Z_(p): mC=C, so this also tests the zero closed
  fibre; no contraction-equality or lies-over assumption is introduced.

Searches for an existing whole statement (all on 2026-10-24):

- `msearch.py ... leanfinder "A finite algebra generating family reduces modulo the
  maximal ideal to generators over the residue field, with polynomial evaluation
  commuting with reduction of coefficients"`: eight hits, including
  `IsLocalRing.basisQuotient_repr`, `Algebra.Generators.naive`, and power-basis quotient
  formulas. These concern module bases or specialized algebra presentations; none is
  the theorem for a specified arbitrary finite algebra generating family.
- `msearch.py ... loogle "Algebra.adjoin, MvPolynomial.aeval"`: twelve hits, including
  `Algebra.adjoin_range_eq_range_aeval` and `MvPolynomial.aeval_range`. These justify
  the equivalent chosen-family polynomial-surjectivity encoding, but do not state
  the residue action and coefficient-reduction theorem.
- `msearch.py ... grep "quotientAlgebra|quotient.*algebra|algebra.*quotient|eval₂_map"
  RingTheory`: hits for existing quotient constructions and evaluation tools; none
  states all the clauses here.
- Direct `rg` searches of Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for residue finite-type/generating statements, the
  intended declaration name, `algebraQuotientOfLEComap`, and the item id found no
  existing equivalent whole statement. `grep -rn` of the item id in
  `lean/WeilConjectures` returned no matches. The general quotient-base action already
  exists in Mathlib, so it has not been defined again.

Validation: the prescribed `scompile.py` compiled the sandbox and intended library
module cleanly after making A explicit as the coefficient ring in the generating-family
hypothesis. The delivery dry run performs the final per-file compile and preflight.
No mathematical dispute or correction is needed.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
