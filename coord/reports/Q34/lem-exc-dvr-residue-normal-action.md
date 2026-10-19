## Worker report

The module `Sheaf.FieldTheory.FiniteDVRResidueNormalAction` states
`IsDiscreteValuationRing.residue_normal_action`, with `sorry`, and exposes the
canonical residue-action homomorphism and the instances needed to type it.
I read the item and its five statement dependencies, their recorded Mathlib
interfaces, and Stacks Project `more-algebra.tex`, Tag 09ED
(`lemma-galois-galois`), assertions (1)--(2), with the preceding decomposition-group
definition. I also read Tag 0BRJ (`lemma-one-orbit-geometric`), which the proof uses.
The node statement needs no correction; only its `lean` record changes.

Hypothesis and clause correspondence:

- The DVR is `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. Mathlib's class means a local principal ideal
  domain whose maximal ideal is nonzero, exactly the recorded definition.
- The fraction field is `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`.
- The finite normal separable extension is `(L : Type w) [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]`.
  `IsGalois` supplies exactly `Normal K L` and `Algebra.IsSeparable K L`.
  The compatible `[Algebra A L] [IsScalarTower A K L]` expresses the composite
  map from A through K, not an additional mathematical restriction.
- The integral closure B is Mathlib's `integralClosure A L`.
- The chosen maximal ideal is `(n : Ideal (integralClosure A L)) [n.IsMaximal]`.
- The fields k and E are literally `A ⧸ IsLocalRing.maximalIdeal A` and
  `integralClosure A L ⧸ n`. Their field instances are the existing
  `Ideal.Quotient.field` construction. No residue separability is assumed.
- The induced k-algebra structure is Mathlib's `Ideal.Quotient.algebraOfLiesOver`.
  `residueNormalLiesOverInstance` supplies its required contraction equality,
  using `Ideal.LiesOver.mk`, `IsLocalRing.eq_maximalIdeal`, and
  `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` directly. There is no extra
  lies-over hypothesis in the item statement and no postponed helper proof.
- D is `MulAction.stabilizer (Gal(L / K)) n`, for the canonical Galois action
  on the integral closure and its ideals. This is precisely the subgroup of
  K-automorphisms carrying n to itself.
- The first conjunct is `Normal k E`. Reading
  `Mathlib.FieldTheory.Normal.Defs`, this supplies algebraicity and
  `Polynomial.Splits ((minpoly k x).map (algebraMap k E))` for every x in E.
  Algebraicity is part of normality in Stacks 0BRJ and follows here from
  integrality of B over A; this does not add a residue separability clause.
- The second conjunct is
  `Function.Surjective (residueNormalActionHom A K L n)`.
  This map is exactly `Ideal.Quotient.stabilizerHom n (maximalIdeal A)
  (Gal(L / K))`, with codomain the group of k-algebra automorphisms of E.
  Mathlib's `Ideal.Quotient.stabilizerHom_apply` identifies its value on the
  class of b with the class of the action on b. Thus it is the source's rho.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`,
  available through the public imports.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`, used through `IsGalois.to_isSeparable`.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` and
  `Ideal.ResidueField`, `Mathlib.RingTheory.Localization.AtPrime.Basic` and
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. The item's explicit
  maximal-ideal residue quotients are used as stated in the node; no second
  residue-field notion is introduced.

The proof docstring carries all five node steps and their node references:
PID integral closedness; the finite Galois fixed field; stability of B;
B^G=A; maximal contraction and locality; then the two clauses of 0BRJ.
The Mathlib proof-dependency modules are imported, including
`PrincipalIdealDomain`, `Polynomial.RationalRoot`, `Ideal.GoingUp`,
`FieldTheory.Galois.Basic`, and `RingTheory.Invariant.Galois`.
No dependency module or new definition node is needed.

Edge cases: for L=K the statement specializes to the identity residue extension
and trivial automorphism group. Neither residue characteristic nor perfectness
is restricted; inseparable residue extensions are allowed. A field A is
excluded by the DVR definition itself. A maximal ideal is proper, so both
quotients are nontrivial fields. All three universes u, v, w are independent.
No henselianity, completeness, or residue separability has been inserted.

Searches repeated in this worker session through `msearch.py`:

- LeanFinder, "finite DVR integral closure residue field normal decomposition
  group automorphism surjective": eight hits, including `Ideal.Quotient.normal`,
  `IsFractionRing.stabilizerHom_surjective`, and valuation inertia groups; no
  exact combined DVR statement.
- Loogle, `Ideal.Quotient.stabilizerHom_surjective`: one hit, the general
  invariant-ring theorem, not the DVR specialization with normality.
- LeanSearch, "Finite Galois extension fraction field discrete valuation ring
  normal residue extension decomposition action surjective": eight hits,
  including `IsGalois`, `Normal`, and normal-restriction surjectivity; no exact
  combined theorem.
- Grep, `stabilizerHom_surjective|Quotient.normal` in `RingTheory/Invariant`:
  ten hits, locating the general quotient results. I read the actual signatures
  and their section hypotheses in `Invariant/Galois.lean` and
  `Invariant/Basic.lean`; these require the fixed-ring reduction of steps 1--4.
- `rg` in the upstream `WeilConjectures/` and the side `lean/Sheaf/` for
  `residueNormal|residue_normal_action|stabilizerHom_surjective|integralClosure.*normal`:
  the upstream `Ideal.Quotient.stabilizerHom_surjective_integralClosure` in
  `WeilConjectures.Mathlib.RingTheory.Invariant.Profinite` gives only
  surjectivity and assumes a chosen lies-over ideal. It does not state both
  clauses with the item's hypotheses. Other hits concern normal rings.
- The required upstream grep for `lem-exc-dvr-residue-normal-action` found no
  occurrence. The proposed declaration names were also searched in
  `dag/lean_names_upstream.json`, with no match.

The earlier attempt compiled but had a proved helper theorem. I removed that
helper and used the existing Mathlib theorem terms directly in the canonical
instance. All definitions contain real data; the sole theorem in the final
file is the item's theorem, with `sorry`. I removed the inherited second-reading
section so that the independent second reader can write their own assessment.

## Second reading by Q34

I read the node statement and Stacks Project `more-algebra.tex`, Tag 09ED
(`lemma-galois-galois`), assertions (1)--(2), including the surrounding
definition of the decomposition group and the note that the residue extension
may be inseparable. The item is a statement node and its own statement is
unchanged.

Statement list and Lean correspondence:

1. The base object is a commutative domain `A` carrying
   `IsDiscreteValuationRing A`; Lean uses `(A : Type u) [CommRing A] [IsDomain A]
   [IsDiscreteValuationRing A]`. This is the same DVR notion and does not add
   completeness, henselianity, noetherianity, or a residue characteristic.
2. The fraction field is `K`; Lean uses `(K : Type v) [Field K] [Algebra A K]
   [IsFractionRing A K]`. The universes `u` and `v` are independent.
3. The extension is `L/K` finite, normal, and separable. Lean uses
   `(L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
   [IsGalois K L]`; Mathlib's `IsGalois` supplies normality and separability,
   while `FiniteDimensional` supplies finiteness. The required compatible
   `Algebra A L` and `IsScalarTower A K L` are present.
4. The integral closure is exactly Mathlib's `integralClosure A L`; Lean uses
   `Ideal (integralClosure A L)` for the chosen maximal ideal `n` with
   `[n.IsMaximal]`. No alternate closure or localization is introduced.
5. The residue fields are literally
   `A ⧸ IsLocalRing.maximalIdeal A` and `integralClosure A L ⧸ n`, with the
   canonical quotient field instances and the induced algebra structure. The
   `residueNormalLiesOverInstance` supplies only the canonical contraction
   equality needed to type that structure.
6. The decomposition group is exactly
   `MulAction.stabilizer (Gal (L / K)) n`, and
   `residueNormalActionHom` is Mathlib's
   `Ideal.Quotient.stabilizerHom n (IsLocalRing.maximalIdeal A) (Gal (L / K))`.
   Its codomain is the group of automorphisms of the residue quotient over the
   base residue quotient, matching the source's `D → Aut_k(E)` and the formula
   `bar b ↦ overline{sigma b}`.
7. The conclusion is the conjunction
   `Normal (A ⧸ maximalIdeal A) (integralClosure A L ⧸ n)` and
   `Function.Surjective (residueNormalActionHom A K L n)`. `Normal` includes
   algebraicity and splitting of every minimal polynomial; the second clause
   is the source's surjectivity. No residue separability is assumed.

The declarations `residueNormalLiesOverInstance`,
`residueNormalBaseField`, `residueNormalQuotientField`, and
`residueNormalActionHom` are canonical typing/construction helpers for the
item's objects, with real data and source/blueprint docstrings. The theorem
`residue_normal_action` is the only postponed proof. Its `lean.statement` is
verbatim the theorem signature in the module. The module compiled cleanly with
the required `scompile.py` wrapper.

Edge cases checked: `L = K` gives the identity residue extension and trivial
decomposition action; the residue characteristic is unrestricted; the residue
extension may be inseparable; and all three universes are independent. A field
cannot satisfy the DVR class used here, as in the source. A maximal ideal makes
both quotient objects fields. There is no index set, zero-object, or `n = 0`
case in this statement.

I independently repeated searches through `msearch.py`:

- LeanFinder: "A finite Galois extension of the fraction field of a discrete
  valuation ring induces a normal residue field extension and lifts every
  residue field automorphism" returned eight hits, including
  `IsLocalRing.ResidueField.mapAut`, valuation inertia, and residue algebraicity
  instances; none states both clauses of this item.
- Loogle: `Normal (_ ⧸ _) (_ ⧸ _)` returned `Ideal.Quotient.normal`.
- Grep: `residue.*normal|normal.*residue|stabilizerHom_surjective` in
  `RingTheory` returned eleven hits, including the general invariant-ring
  stabilizer-surjectivity theorems.

I read `Ideal.Quotient.normal` (Mathlib
`RingTheory/Invariant/Galois.lean:140`) and
`Ideal.Quotient.stabilizerHom_surjective` (Mathlib
`RingTheory/Invariant/Basic.lean:362`), including their section hypotheses.
These are the separate clauses used by the proof route and are not the complete
DVR-specialized statement. Grep of
the upstream `WeilConjectures/`, the project's `lean/Sheaf/`, and
`dag/lean_names_upstream.json` found no existing declaration of this item or
its helper names. The search records are in `searches.jsonl`.

No mismatch was found, so no statement, dependency, or definition was changed.
The direct citer `lem-exc-dvr-inertia-order-prime-part` uses exactly the normal
residue clause and the stabilizer action supplied here, so its use still holds;
the other search hits are blueprint/proof references rather than incompatible
citers. No statement correction or new definition/dependency module is needed.
