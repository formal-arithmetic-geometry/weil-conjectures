## Worker report

The module `Sheaf.RingTheory.JacobianPresentationLift` defines the coefficientwise lifts,
lifted determinant, explicit polynomial quotient, and canonical reduction map of
`def-exc-etale-algebra-lift`. It uses the namespace
`Algebra.SquareJacobianPresentation.CoefficientLift`.

Clause-by-clause correspondence:
- The commutative ring A and ideal I are `{A : Type u} [CommRing A] (I : Ideal A)`.
- The specified algebra B over A/I is `{B : Type v} [CommRing B]
  [Algebra (A ⧸ I) B]`. The number of variables is `{m : ℕ}`.
- The specified square presentation is
  `P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m)`.
- Choosing coefficientwise lifts is the structure `CoefficientLift I P`, whose `relation`
  field contains the f_i and whose `map_relation` field states
  `MvPolynomial.map (Ideal.Quotient.mk I) (relation i) = P.relation i` for each i.
  This equality is precisely coefficientwise reduction, not an extra hypothesis.
- The determinant Δ is `jacobianPolynomial`, the determinant of
  `fun i j ↦ MvPolynomial.pderiv j (L.relation i)`.
- The extra variable t is `MvPolynomial.X none`; the old variables are indexed by
  `some i : Option (Fin m)`. `liftIdeal` is the span of all renamed f_i together with
  `X none * rename some jacobianPolynomial - 1`.
- `LiftRing` is exactly `MvPolynomial (Option (Fin m)) A ⧸ L.liftIdeal`.
  It is an abbreviation so Mathlib supplies the quotient ring/algebra instances directly.
- `polynomialReduction` reduces coefficients through A → A/I → B, sends `some i`
  to `P.val i`, and sends `none` to `↑(P.jacobian_isUnit.unit⁻¹)`.
  `reduction` descends this very homomorphism through `Ideal.Quotient.lift`, so its value
  on t is the specified inverse of the original Jacobian.

Dependency used: `def-exc-jacobian-presentation`, recorded declaration
`Algebra.SquareJacobianPresentation` in
`WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive`.
Its full structure/docstring were read: it extends the submersive presentation with
`map_eq_id`, and includes the relations, specified generators, quotient presentation,
and unit Jacobian. Mathlib APIs used include `MvPolynomial.pderiv`, `Matrix.det`,
`MvPolynomial.rename`, `Ideal.span`, `MvPolynomial.eval₂Hom`, and `Ideal.Quotient.lift`.

Only `liftIdeal_vanish` has `sorry`. This named theorem records the proof needed for
well-definedness of the reduction map, and is included in the item's declaration record.
Its docstring explains every step: relations evaluate to zero, derivatives and determinant
commute with reduction, the inverse relation evaluates to zero, and the ideal span is killed.
All definition data is explicit; no theorem is proved at this stage.

Edge cases checked before writing: m = 0 gives the empty determinant 1 and the quotient
A[t]/(t - 1); the empty presentation of B then agrees with A/I. I = 0 is permitted and
keeps the same construction; I = top and zero rings are permitted (units exist in the
zero ring). No characteristic, nonzero-ring, nilpotence, or finite-type hypothesis on A
is imposed. The algebra B has independent universe v; the explicit quotient lives in u,
so larger universes for a presented B are not excluded. The matrix convention in Mathlib
is transposed relative to the displayed derivative matrix, with the same determinant.

Searches (2026-10-11):
- LeanFinder via msearch.py: "lifting a square Jacobian presentation by adjoining the
  inverse of the lifted Jacobian determinant". Eight hits, including
  `Algebra.SubmersivePresentation.invJacobianOfHasCoeffs` and `ofHasCoeffs`;
  these descend existing submersive presentations along coefficient subrings and do not
  define the specified quotient adjoining a new inverse variable.
- Loogle via msearch.py: "MvPolynomial, Matrix.det, Ideal.Quotient". No hits;
  unknown identifier Ideal.Quotient in that search service.
- Mathlib grep via msearch.py: "etaleLift|jacobianLift|lift.*[Jj]acobian|[Jj]acobian.*lift".
  Four unrelated elliptic-curve Jacobian hits; no lift construction.
- LeanSearch via msearch.py: "lift an etale algebra by lifting polynomial relations and
  adjoining inverse Jacobian determinant". Service unavailable (Internal Server Error).
- rg of the same lift-pattern in the source WeilConjectures and project lean/Sheaf:
  no hits. rg of the blueprint id in WeilConjectures: no hits.
- rg of CoefficientLift, jacobianPolynomial, liftIdeal_vanish, JacobianPresentationLift
  in upstream names, Mathlib, WeilConjectures, and project lean/Sheaf: no name collision.

No statement correction, dependency replacement, or new notion node is needed.
The source blueprint file is not present in this remote read-only literature checkout;
the construction is available verbatim in the node and its reviewed stage-1 report.

## Second reading by G1

Read the sandbox node and all 83 lines of JacobianPresentationLift.lean independently.
The blueprint markdown is absent from the read-only literature checkout; fetching its
recorded commit/path returned HTTP 404. I read the construction directly in the primary
Stacks source instead: https://stacks.math.columbia.edu/tag/04D1 and
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
`lemma-lift-etale`, especially its proof (lines 39564–39587 in the fetched text).
This explicitly introduces an arbitrary ring R and ideal I, a square presentation over
R/I with invertible Jacobian, coefficient lifts, and the quotient adjoining its inverse.
There is no nilpotence, domain, field, characteristic, or Noetherian assumption.
The node agrees with that construction; no correction is needed.

The following is my object/hypothesis/conclusion checklist, with a verdict for every clause:

1. A is a commutative ring and I an arbitrary ideal. Lean: `{A : Type u} [CommRing A]
   (I : Ideal A)`. PASS: ordinary commutative rings, including the zero ring.
2. The specified A/I-algebra Bbar. Lean: `{B : Type v} [CommRing B]
   [Algebra (A ⧸ I) B]`. PASS: the quotient coefficient ring and algebra structure are
   precisely the source's, with independent universe v and no finiteness assumption on A.
3. A chosen square presentation with m variables and m relations and invertible Jacobian.
   Lean: `{m : ℕ}` and `P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m)`.
   PASS after reading the dependency node def-exc-jacobian-presentation and its recorded
   source module WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive.
   Its `map_eq_id` pairs relation i with variable i. I also opened Mathlib's inherited
   `Algebra.Generators`, `Algebra.Presentation`, `PreSubmersivePresentation`, and
   `SubmersivePresentation`: `val` and a section of evaluation give all generators,
   `span_range_relation_eq_ker` gives exactly the presented quotient, and
   `jacobian_isUnit` supplies invertibility. It is not merely a list of equations or
   a weaker presentation. The section is equivalent data for a surjective evaluation,
   available by choice, not an additional mathematical restriction.
4. Choose coefficientwise lifts f_i of the given relations. Lean: `CoefficientLift I P`,
   fields `relation : Fin m → MvPolynomial (Fin m) A` and `map_relation` asserting
   `MvPolynomial.map (Ideal.Quotient.mk I) (relation i) = P.relation i` for every i.
   PASS: reduction fixes the variables and reduces each coefficient, exactly as required.
   This structure records the chosen lifts; it does not impose any condition on I.
5. Put Delta = det(partial f_i / partial x_j). Lean: `L.jacobianPolynomial`, defined as
   `Matrix.det (fun i j ↦ MvPolynomial.pderiv j (L.relation i))`. PASS: rows are relations,
   columns are variables as in the displayed formula. Reading `jacobiMatrix_apply` and
   `jacobian_eq_jacobiMatrix_det` shows the dependency's evaluated Jacobian is its
   transpose determinant, equal to this determinant because `P.map_eq_id` holds.
6. Define B_lift = A[x_1,...,x_m,t]/(f_1,...,f_m,t Delta - 1). Lean: `L.liftIdeal`
   spans the renamed relations and `MvPolynomial.X none *
   MvPolynomial.rename some L.jacobianPolynomial - 1`; `L.LiftRing` abbreviates exactly
   `MvPolynomial (Option (Fin m)) A ⧸ L.liftIdeal`. PASS: `some i` indexes old variables,
   `none` indexes the one new variable, and all generators occur in the ideal.
7. Its map to Bbar sends t to Deltabar inverse. Lean: `L.polynomialReduction` evaluates
   coefficients via A → A/I → B, old variables via `P.val i`, and `none` via
   `(↑(P.jacobian_isUnit.unit⁻¹) : B)`. `L.reduction` is `Ideal.Quotient.lift` of exactly
   that homomorphism using `L.liftIdeal_vanish`. PASS: both coefficient reduction and
   the specified generator images are explicit. The inverse is determined by its unit,
   not a newly chosen arbitrary element. The ring-hom form specifies the canonical map
   completely; its compatibility with the coefficient algebra map follows from eval₂.

Edge cases: m = 0 is allowed (`Fin 0`); Delta is the determinant of the empty matrix, 1,
and the construction is A[t]/(t-1). The empty presentation forces Bbar to be the
specified quotient algebra. I = bottom, I = top, and A or B a zero ring are allowed;
units in a zero ring still have the needed multiplicative identities. Arbitrary
characteristic is allowed. No test-object universe occurs; u and v are bound explicitly,
and the quotient lives in u even if B is represented in a larger universe v.
There are no schemes or additional index families to restrict.

Independent searches, recorded by msearch.py in searches.jsonl:
- LeanFinder: "construct a polynomial quotient over a ring lifting relations modulo an
  ideal and invert the determinant of their derivatives". Eight hits, including
  `SubmersivePresentation.ofHasCoeffs`, `invJacobianOfHasCoeffs`, `jacobianRelations`,
  and `StandardEtalePair.Ring`. Opened the ofHasCoeffs/invJacobianOfHasCoeffs definitions
  in Presentation/Core.lean: they descend coefficients along an injective coefficient
  map, using `FaithfulSMul`, and do not lift arbitrary chosen relations across a quotient.
  Opened StandardEtalePair.Ring in Etale/StandardEtale.lean: it is a monic univariate
  standard-etale pair quotient R[X][Y], not the general m-relation chosen lift here.
- Loogle: `MvPolynomial.eval₂Hom, Ideal.Quotient.lift`. Two hits: left/right inverses of
  `quotientEquivQuotientMvPolynomial`; these commute polynomial formation with a
  coefficient quotient and do not construct this lifted Jacobian quotient.
- Mathlib grep: `lift.*presentation|presentation.*lift|inverse.*determinant|determinant.*inverse`
  under RingTheory. One unrelated localized module finite-presentation result.
- LeanSearch: "Given polynomial equations over a quotient ring choose lifts and form a
  quotient with a new variable inverse to their Jacobian". Service unavailable with
  Internal Server Error, recorded as unavailable; no verdict inferred from this failure.
- Direct rg on WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json:
  `lift.*presentation|presentation.*lift|invert.*jacobi|jacobi.*invert|CoefficientLift|JacobianPresentationLift`.
  Hits concerned other finite presentations or other Jacobians; no duplicate of the
  chosen multivariate quotient lift. In particular the dependency is used, not copied.

H5/H6/H8/H9: every definition has explicit data. The sole postponed proof is the named
`liftIdeal_vanish`; its docstring explains relation evaluation, coefficient reduction
commuting with derivatives/determinants, the inverse relation, and ideal-span containment.
The definition node has no proof steps to omit. The docstrings identify the blueprint
source and id; the header, topic, namespace, imports, bound variables/universes, and
100-character line convention agree with the example module. No theorem is proved.
No new definition nodes, dependency replacements, or statement corrections are present.
The recorded main signature `abbrev LiftRing : Type u` is verbatim from its declaration.

Mismatches found: none. Changes: appended this independent reading only; left the Lean
module and node record unchanged. Server compilation through scompile.py succeeded
without errors or warnings (1.6 seconds).
