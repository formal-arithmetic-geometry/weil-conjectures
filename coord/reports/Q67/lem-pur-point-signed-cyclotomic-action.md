## Worker report

The module `Sheaf.Paper.PointSignedCyclotomicAction` states
`WeilConjectures.PointSignedCyclotomicAction.point_signed_cyclotomic_action`.
It has one postponed theorem and concrete helper definitions assembling the existing
root comparison, inverse-image unit, signed maps, tensor sections, and evaluation.
The node's statement, dependencies, and proof are unchanged; only `lean` is set.
There is no statement dispute or definition containing postponed data.

Hypotheses and clause correspondence:

- `D : FiniteFieldDatum.{u}` supplies prime p, positive a, q=p^a, the field k0
  of cardinality q and its fixed algebraic closure k. `l`, `[Fact l.Prime]`, and
  `hl : l ≠ D.p` supply the coefficient prime. `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]` supply precisely
  the finite extension. The recorded coefficient rings already include its
  valuation ring and the chosen uniformizer quotients.
- `point D` is Spec k, `finalObject D` is (s,id), and the map is the recorded
  `(frobeniusPointIso D).hom`, constructed from inverse arithmetic field Frobenius.
  No additional map or action is assumed.
- `e` is a section of the actual `purTwistZlOne`, the limit of the root sheaves.
  Its projections are the chosen zeta_(r+1); `he` says each is primitive of order
  l^(r+1). Compatibility zeta_(r+2)^l=zeta_(r+1) is part of being a section of
  this limit, rather than an extra independent hypothesis or an arbitrary basis.
- `coefficientRing`, `line`, and `scalars` simply dispatch between the two
  existing coefficients. `none` is completed O_E; `some n` is A_(E,n+1).
  Thus all positive quotient exponents, starting at 1, are included. The ULift
  changes only the coefficient size required by the site, not the coefficient ring.
- `sectionArrow` is the canonical comma arrow followed by base change of
  `frobeniusPointRestriction`. `rootAction`, `rootLimitAction`, and `action`
  apply the specified inverse-image unit, the specified comparison tau, and
  restriction back to the final object. By naturality this is Gamma(tau) after
  restriction/coprojection sigma, exactly the displayed Psi; it is not an action
  defined to be scalar multiplication. It uses the adjunction-unit model rather
  than replacing the pullback site by unrelated coordinates.
- The first conjunct asserts q is a unit in Z_l, with its exact underlying value.
  The second gives inverse exponents q' modulo l^(r+1) and the root action formula
  for every such q'. `rootValue` uses `proEtaleRootsOfUnitySections` and `ΓSpecIso`
  to read the root in k. The third conjunct explicitly identifies its value with
  inverse `FiniteField.frobeniusAlgEquivOfAlgebraic`, namely gamma.
- The fourth conjunct states that the inverse-image comparison itself is the
  identity on roots of the unchanged underlying scheme, using the recorded
  `proEtaleIsoInverseImageIdentification`. It keeps that comparison distinct from
  the preceding restriction. The fifth conjunct is commutation of `rootAction`
  with the actual l-power transition map. The sixth asserts the limit sends e
  to q inverse times e using `purTwistZlAction` and the actual constant-to-completion map.
- The seventh conjunct fixes 1 in the constant Z_l and O_E factors and in every
  finite quotient factor, with `constantAction` built from the same actual
  constant inverse-image comparison and unit.
- `generator a e d` is literally e_B tensor-powered d times using the existing
  pure tensor constructions, and is the coefficient unit for d=0. Integral
  coefficient insertion is `pointIntegralSectionMap`, and finite insertion is
  `pointConstantSectionMap`; these are exposed uniformly as `scalarAt` and `scale`.
- The eighth conjunct states Psi_m(b*x)=b*q^(-m)*x for every section x. Here the
  signed power is written `Ring.inverse q ^ m.toNat * q ^ (-m).toNat`: it is
  q inverse to exponent m for m≥0 and q to exponent -m for m<0, with both factors
  1 at m=0. Under the node's coordinates Gamma(s,B(m))=B e_(m,B), this is exactly
  its formula for all b e_(m,B). This form is independent of choosing a separate
  dual trivialization and immediately applies to every normalized dual generator.
  It adds no hypothesis and is equivalent to the node's coordinate formula,
  by the root-coordinate lemma already in the node's proof dependencies.
- The ninth conjunct states Psi_0(1)=1. The tenth uses `tensor` to state precisely
  the successor pure-tensor equation for m=n+1≥1; no claim that arbitrary global
  sections commute with tensor products is made.
- `evaluate` is actual internal-Hom evaluation on the identity slice. The eleventh
  conjunct gives Psi_(-r)(phi)(Psi_r(x))=phi(x), and the twelfth explicitly gives
  bijectivity of Psi_r and the requested formula phi composed with Psi_r inverse,
  using `Function.invFun` of that very operator. Here r=n+1>0.
- The final conjunct quantifies over a dual section phi with phi(e_r)=1 and says
  Psi_(-r)(phi)(e_r)=q^r. Such a phi is exactly e_(-r,B); quantifying over the
  normalized section avoids choosing from a bare existence theorem or adding
  any arbitrary internal-Hom identification.

Recorded dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including
  its coefficient conventions from the existing Padic coefficient-extension rings.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: its public original
  coefficient interfaces, particularly `coefficientTwistPower`,
  `coefficientTwistLine`, and `finiteCoefficientTwist`; the integral specialization
  is also exactly `FrobeniusCoefficientTwists.line`.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`:
  `rootSection`, `signedLineMaps`, `finiteSignedLineMaps`, `moduleSection`,
  `finiteModuleSection`, `generator`, and `positiveLine`. These are the canonical
  root-tensor/evaluation-normalized maps recorded for this node's dependency.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso` and
  `frobeniusPointRestriction`; these preserve the geometric Frobenius convention.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleRootsOfUnityInverseImageMap`.
- The proof imports are the recorded modules of every stated proof dependency:
  `PointAutomorphismRestrictionNatural`, `ProEtaleRootsOfUnitySheaf`,
  `RootsOfUnityInverseImageIso`, `FrobeniusRootsOfUnityPower`,
  `Mathlib.CategoryTheory.Limits.HasLimits`, `ConstantWeilStructure`,
  `ProEtaleInverseImage`, `PurInverseImageTensorHom`, `CochainTensorUniverses`,
  and the upstream `InternalHom`. The unstated proof dependency
  `lem-pur-point-tate-root-coordinates` has no module to import. Its future theorem
  proves the coordinate interpretation; no missing object from it is required
  to type the present statement, since the chosen root system is a real section
  of the existing inverse limit and normalized duals are quantified directly.

Edge cases: m=0 uses both exponent-zero factors and the actual unit generator;
m=1 and m=-1 have the opposite scalars q inverse and q. The successor tensor
formula starts at m=1, and dual formula starts at r=1. `some 0` covers n=1 in
paper notation. Ramification, l=2, and nonreduced coefficient quotients are
unrestricted; ring inverse is used instead of field division. b=0 and the zero
section satisfy the same formulas. The chosen root system may be changed: `e`
is universally quantified with its primitive projections. There is no imposed
characteristic, cardinality, coefficient embedding, or invertibility assumption
beyond the finite-field datum and l≠p. Site object universe u+1 and morphism
universe u are retained; the Z_l constant map is formed directly to avoid forcing
its small type universe to equal u.

Source reading: read the current main-20261015 blueprint ancestor
`sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md`,
Deligne I (2.2), printed p.280 (root inverse system, tensor powers, negative duals),
and Deligne II (1.1.7), printed p.150 (geometric Frobenius inverse convention).
Read the full signatures and docstrings of the recorded statement dependencies,
including the canonical root/tensor/dual constructions exported by their modules.

Searches (fresh logged `msearch.py` results in `searches.jsonl`):

- LeanFinder: “Geometric Frobenius on signed Tate twist global sections acts by
  inverse cardinality powers through root inverse image tensor powers and duals”.
  Eight results, including `FiniteField.frobeniusAlgEquiv_apply`,
  `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, and Witt-vector isocrystal results.
  None states the sheaf-level signed point action with its prescribed comparisons.
- Loogle: `"cyclotomicCharacter"`. Twelve results, including
  `cyclotomicCharacter`, `cyclotomicCharacter.toFun_apply`, and
  `modularCyclotomicCharacter.toFun_spec''`. These are algebraic root characters,
  not the canonical sheaf section operators, coefficient factors, tensors and duals.
- Logged Mathlib grep: `cyclotomicCharacter|restrictRootsOfUnity`, subdirectory
  `NumberTheory/Cyclotomic`. Five hits in `CyclotomicCharacter.lean`, no match.
- Project `rg` searches for signed cyclotomic names, point/Tate coordinates, and
  line sections in both `lean/WeilConjectures` and `lean/Sheaf`, plus the prescribed
  literal item-id grep in `lean/WeilConjectures`, found no matching declaration.
  The broader hits led to reading `TwistFrobeniusScalar.lean`: its theorem is a
  cohomology/derived and coefficient-comparison statement, not this section-level
  theorem. Its scalar helper was deliberately not duplicated; signed powers are
  expressed inline here. Existing canonical constructions are reused throughout.

Verification: `scompile.py` compiled this file separately in sandbox and library
module modes on the server, within 60 seconds each, with no errors or warnings.
The sole theorem is postponed with `sorry`, with the full six-step DAG proof in
its docstring. All variables/universes are explicit, all helper data are real,
and every declaration is listed in the node's Lean record.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
