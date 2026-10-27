## Worker report

The delivery states `AlgebraicGeometry.etaleAway_completedCotangent_torsion` in
`Sheaf.RingTheory.EtaleAwayCompletedCotangentTorsion`. Every theorem has proof `sorry`.
The completion abbreviation has real data, namely Mathlib's inverse-limit completion.
No mathematical statement was corrected, and no new DAG node was created.
The item gains the existing definition node `def-per-completed-polynomial-conormal`,
whose Lean interface has now landed through Q147. This repair imports that landed
module and delivers no dependency module or dependency node change.

Hypotheses and clauses, in the order of the node:

- Commutative Noetherian A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- Commutative finite type A-algebra S: `(S : Type u) [CommRing S] [Algebra A S]`
  and `[Algebra.FiniteType A S]`. The recorded ring-map notion `RingHom.FiniteType`
  is the same finite-type condition with its algebra structure supplied by a ring map;
  the conclusion below uses that precise recorded predicate.
- Ideal I: `(I : Ideal A)`.
- Étale over Spec A minus V(I): `het` is `Etale` of `Spec.map` of the structure map,
  restricted by `∣_` to the open complement of `PrimeSpectrum.zeroLocus (I : Set A)`.
  This is restriction on both source and target, hence exactly étale over that open.
- B is the completion lim S/I^n S: `etaleAwayAlgebraCompletion A S I` is
  `AdicCompletion (I.map (algebraMap A S)) S`. Powers of this mapped ideal are I^n S.
  Mathlib includes the n=0 zero quotient, which does not change the inverse limit.
- B Noetherian: the first conjunct is `IsNoetherianRing` of this B.
- B IB-adically complete: the second conjunct is `IsAdicComplete` with the ideal
  `I.map (algebraMap A B)`, acting on B itself.
- B/IB finite type over A/I: the third conjunct applies `RingHom.FiniteType` to
  `Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map`.
  Its domain is A/I, codomain B/IB, and it is the canonical induced structure map.
  This avoids choosing an unrelated quotient-algebra structure.
- A finite restricted polynomial presentation exists: `∃ (r : ℕ) (β :
  rigPolynomialCompletion A I r →ₐ[A] B), Function.Surjective β`.
  The source is the completion of `MvPolynomial (Fin r) A` at the extended I.
- Every such presentation: the last conjunct quantifies every r and every β, then
  assumes its surjectivity, before asserting `∃ c : ℕ`.
- Q is the kernel: it is literally `RingHom.ker β.toRingHom`.
- The two-term completed cotangent arrow: `rigPresentationDifferential A I r β`
  is a map from Q.Cotangent = Q/Q² to `Fin r → B`, the finite free module B^r.
  It is built from β applied coordinatewise to the unique extended polynomial partial
  derivatives. This arrow is the specified two-term complex in degrees -1 and 0;
  the assertion only uses its kernel and cokernel, so it requires no additional
  choice of a model in a category of complexes.
- I^c kills ker δ: for every `a ∈ I ^ c` and every x in Q/Q² with δ x = 0,
  `a • x = 0`. The scalar action is the canonical A-action through P then P/Q = B.
- I^c kills coker δ: for every `a ∈ I ^ c` and every vector y in B^r,
  `a • y ∈ LinearMap.range δ`. This is exactly zero of the class of a·y in
  B^r/range δ, not a stronger vanishing assertion on the whole free module.
  Both annihilation clauses use the same c.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the definition that every
  ideal is finitely generated.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` and `RingHom.FiniteType`;
  also read `Algebra.FiniteType.iff_quotient_mvPolynomial''` for its finite-presentation form.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`;
  `Mathlib.RingTheory.AdicCompletion.Algebra` supplies their ring and algebra structures.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`;
  `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial.algHom_ext`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.RingTheory.CompletedPolynomialConormal`: the landed Q147 declarations
  `rigPolynomialCompletion`, `rigPartialDerivative`, and `rigJacobianDifferential`.
  The item's helper `rigPresentationDifferential` postcomposes that differential
  coordinatewise with the canonical `Ideal.kerLiftAlg β : P/ker β →ₐ[A] B`.
  Hence it uses the landed continuous derivative and conormal quotient, with no copy.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent`, `Ideal.Cotangent.lift`,
  `Ideal.Cotangent.equivOfEq` were read for the original packet. The repaired packet
  directly consumes Q147's conormal quotient and adds no second quotient construction.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.quotientMap` and
  `Ideal.Quotient.mkₐ` for the canonical quotient maps, and `Ideal.kerLiftAlg`
  for the canonical map from the kernel quotient to the presentation target.

Proof-only imports are `WeilConjectures.RingTheory.AdicCompletionNoetherian`
(`AdicCompletion.isNoetherianRing`), `Mathlib.RingTheory.AdicCompletion.LocalRing`
(the completion/mod-ideal results and their public imports), and
`Mathlib.RingTheory.FinitePresentation` (finite-presentation permanence).
The proof nodes `lem-per-completed-cotangent-transitivity`,
`lem-per-completed-jacobian-homology-comparison`, and
`lem-per-finite-type-jacobian-torsion-etale-away` have no recorded Lean declaration
or Mathlib match in the read repository, so there is no module to import yet.
Their proof plans are named verbatim in the theorem docstring; they are not needed
as statement prerequisites and are not replaced or assumed.

Source read: `literature/stacks-project/restricted.tex`, lemma-rig-etale (0ALQ),
lemma-equivalent-with-artin (0AJU), lemma-topologically-finite-type (0AJP),
lemma-topologically-finite-type-Noetherian (0AJQ), equation-NL (0AJR), and
lemma-NL-is-completion (0GAF). In particular 0ALQ(1) gives the rig-étale conclusion,
0AJU(3) identifies the two cohomology annihilation assertions, and 0AJP/0AJQ give
completeness, reduction and presentation existence. No change to the unit is needed.

Edge cases checked before drafting and on the final signature:

- r=0: `Fin 0 → B` is the zero module; no nonempty-variable hypothesis occurs.
- I=0: the étale-open hypothesis is over the empty open; c=1 annihilates everything,
  and the completion is S, as required. No hypothesis incorrectly asserts S/A étale.
- I=A: the completion B is the zero ring. A/I and B/IB are zero rings, all presentations
  to B are covered, and the canonical derivative construction remains meaningful.
- S is the zero algebra: no Nontrivial or inhabited-spectrum assumption occurs.
- c=0 is allowed; I^0=A forces actual vanishing of both homology modules.
- The common ambient universe u puts no cardinality bound on the mathematical rings:
  any pair of rings can be taken in a common universe; the helper target E also
  lives in this common universe, which contains the specified completion B.
- Different surjective β are all quantified; no arbitrary map or derivative is accepted
  as a replacement for the canonical derivative.

Searches actually run:

- msearch LeanFinder: “For a finite type algebra etale away from an ideal its adic
  completion has bounded completed cotangent torsion”: eight hits including
  `Ideal.isTorsionBySet_cotangent`, `Algebra.IsEtaleAt`, `Algebra.exists_etale_of_isEtaleAt`,
  `Algebra.Extension.Cotangent.finite`, and `Algebra.etaleLocus_eq_compl_support`.
  None states the completed finite-presentation assertion.
- msearch Loogle: `AdicCompletion, KaehlerDifferential`: zero hits.
- msearch LeanSearch: “The completed cotangent complex of an algebra etale outside an
  ideal has bounded ideal power torsion”: eight hits about ordinary conormal modules,
  H1Cotangent and formally étale vanishing; no exact match.
- msearch grep: `AdicCompletion.*(deriv|pderiv)|(deriv|pderiv).*AdicCompletion`: zero hits.
- Direct rg in Mathlib, WeilConjectures and Sheaf for completed cotangent, completed
  conormal, restricted polynomial, continuous derivative, and the proposed names:
  the initial search found no surviving exact completed-polynomial conormal interface.
  The existing local-field
  completed differential modules treat different objects. No occurrence of the item's
  blueprint id in WeilConjectures.
- DAG search found the existing `def-per-completed-polynomial-conormal`; it has
  `lean: null` and `lean_removed` recording removal of its former module. The permitted
  `scompile.py --source Sheaf.RingTheory.CompletedPolynomialConormal` lookup returned
  “Module source unavailable”, confirming that this is not merely a stale read clone.
  This described the initial packet. For this repair, the current record and
  `scompile.py --source Sheaf.RingTheory.CompletedPolynomialConormal` show Q147's
  landed restoration. The repair uses it and removes our duplicate restoration.

There is no STATEMENT-DISPUTED finding. The repaired item module compiled cleanly
through scompile.py against the landed dependency, in sandbox and library module modes.

## Repair of returned delivery 72181f229a3c

The return has one point: the immutable packet added
`def-per-completed-polynomial-conormal` to stmt_deps before that node had a Lean
record on the base accepted by the review gate. The current main branch now has
Q147's landed record for this definition and its module. I read its full source
both locally and through `scompile.py --source`; the continuous derivatives and
conormal arrow have the same mathematical meaning as the original packet.

The repair changes the actual module and packet rather than resubmitting the
returned head. It removes our `CompletedPolynomialConormal.lean` and the dependency
node copy, preserves the added stmt_dep as a citation of an already landed node,
and implements `rigPresentationDifferential` in the item's module as the composite
of the landed `rigJacobianDifferential` with the coordinatewise canonical
`Ideal.kerLiftAlg β`. Thus no landed definition is overwritten and the statement
uses precisely the shared canonical derivative. The helper has no proof obligation
and contains real data. The torsion theorem signature and all its hypotheses and
conclusions stay verbatim; only the helper implementation and declaration inventory
change. The item's node was rebuilt from current main with only lean and the added
landed dependency changed. No source-based statement correction is needed.

This directly repairs the gate condition: the dependency is now present with a
Lean record on the new delivery base, and is not a prerequisite being introduced
only inside the same packet. The corrected helper compiled cleanly in both sandbox
and library modes. Preflight and delivery checks are rerun on this repaired packet.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
