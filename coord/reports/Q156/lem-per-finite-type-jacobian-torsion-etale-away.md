## Worker report

The module `Sheaf.RingTheory.FiniteTypeJacobianTorsionEtaleAway` states
`Algebra.Generators.finite_type_jacobian_torsion_etale_away`, with its proof `sorry`.
There are no added definitions, helper theorems, dependency repairs, or statement corrections.
The source read was `literature/stacks-project/restricted.tex`, Tag 0ALQ,
`lemma-rig-etale`, especially the converse paragraph at lines 1807 onward; the node expands
its ordinary finite-module and common-power argument. The module docstring contains all
three proof steps and the exact named prerequisites.

The correspondence with each hypothesis and clause of the unchanged node is as follows.

- Commutative rings A and S: `{A S : Type u} [CommRing A] [CommRing S]`.
  Their common universe is the usual scheme convention; any two rings can be placed in
  a common universe. No bound on cardinality, nonzero hypothesis, or domain hypothesis
  is imposed. All variables are explicit, and `autoImplicit` is disabled.
- The A-algebra S: `[Algebra A S]`, whose structure map is `algebraMap A S`.
- A Noetherian: `[IsNoetherianRing A]`, exactly the recorded dependency definition.
- The ideal I: `(I : Ideal A)`.
- S of finite type over A: `(hfinite : (algebraMap A S).FiniteType)` uses the dependency's
  recorded `RingHom.FiniteType` literally. Its equivalence with `Algebra.FiniteType A S`
  is `RingHom.finiteType_algebraMap`.
- Etale over Spec A minus V(I): `hetale` applies `AlgebraicGeometry.Etale` to the
  restriction `Spec.map (CommRingCat.ofHom (algebraMap A S)) ∣_ U`, where U has carrier
  `(PrimeSpectrum.zeroLocus (I : Set A))ᶜ`. This is the entire inverse-image restriction
  to that target open, with no extra etaleness elsewhere.
- The chosen finite presentation: `(r : ℕ) (P : Generators A S (Fin r))` bundles the
  surjection `MvPolynomial.aeval P.val : MvPolynomial (Fin r) A →ₐ[A] S` and a section.
  Surjectivity is `P.aeval_val_surjective`. Conversely every chosen surjection α in the
  node gives this bundle by `Algebra.Generators.ofAlgHom α hα`; no extra algebraic
  hypothesis is imposed by the section, which exists by choice for every surjection.
  The polynomial ring is the recorded `MvPolynomial`, and `P.ker` is its map kernel.
- The conormal module K/K² and its S-action: Mathlib's
  `P.toExtension.Cotangent`, constructed as the conormal quotient with scalars descended
  through the surjection. This is not an arbitrary replacement module.
- The specified derivative map d_α: the EXISTING Mathlib map
  `P.cotangentRestrict (u := _root_.id) Function.injective_id` has source that conormal
  module and target `Fin r →₀ S`, exactly the finite direct sum S^{⊕r}.
  `Algebra.Generators.cotangentRestrict_mk` states that its i-coordinate on the class of
  f is `MvPolynomial.aeval P.val (MvPolynomial.pderiv i f.val)`. Taking the index map
  to be the identity keeps every variable and every coordinate. The full definition
  and formula were read in `Mathlib/RingTheory/Extension/Cotangent/Basic.lean:467–483`.
  Thus no new conormal-map definition, arbitrary map assumption, or existential
  replacement for the canonical differential is used.
- A common exponent c ≥ 0: `∃ c : ℕ` includes c = 0 and binds ONE exponent for both
  homology modules. No positive-exponent restriction is imposed.
- I^c kills ker d_α: `∀ a ∈ I ^ c`, the first conjunct says
  `∀ x : LinearMap.ker (...), algebraMap A S a • x = 0`.
- I^c kills coker d_α: with the same a and c, the second conjunct says
  `∀ x : (Fin r →₀ S) ⧸ LinearMap.range (...), algebraMap A S a • x = 0`.
  The quotient by the range is the usual module cokernel.
- The action through A → S is explicit in BOTH conjuncts as `algebraMap A S a`.

Recorded statement dependencies used, with the source declaration and docstring read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (lines 191–197).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (lines 215–222), together with
  `Algebra.FiniteType` (lines 37–40).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (lines 469–480).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (lines 38–45).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (lines 75–83).

All statement dependency modules are public imports. The proof dependency modules are
plain imports when not already public statement imports: `Mathlib.RingTheory.Noetherian.Basic`,
`Mathlib.RingTheory.Finiteness.Basic`, `Mathlib.RingTheory.Finiteness.Defs`,
`Mathlib.AlgebraicGeometry.OpenImmersion`,
`WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent`,
`WeilConjectures.RingTheory.EtaleRingMapConormalCriterion`,
`Mathlib.RingTheory.Kaehler.Polynomial`,
`Mathlib.Algebra.Module.LocalizedModule.Exact`, and
`Mathlib.Algebra.Module.LocalizedModule.Basic`.
The etale-open-restriction and composition-cancellation nodes are supplied by the
already public `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
The two recorded upstream conormal/localization statements were read in full; neither
states the common-power result, but both supply the planned stage-3 proof interface.

Edge cases checked before writing:

- I = 0: the etale hypothesis is over the empty open and is vacuous, while c = 1
  makes I^c zero, so the conclusion is correct even for a non-etale S.
- I = ⊤: the hypothesis is etaleness everywhere; conormal kernel and cokernel vanish,
  so c = 0 is allowed and works.
- r = 0: `Fin 0 →₀ S` is zero, but K/K² need not be zero. The kernel conclusion is
  retained; the theorem does not silently discard the conormal module.
- The zero ring S has empty spectrum and zero modules, which the binders allow.
  A = 0 is also allowed (and forces S = 0 for a unital algebra).
- Empty finite generating lists and I with no nonzero generators cause no problem
  in the proof's choice of exponent; the docstring explicitly gives c = 1 when m = 0.
- Non-finite A-modules S are allowed; finite type is not replaced by module finite.

Searches actually run in this session:

- `msearch.py ... leanfinder` with query "For a finite type algebra etale away from an
  ideal the kernel and cokernel of the conormal differential are killed by a common
  power of the ideal": 8 hits, including `Algebra.etaleLocus_eq_compl_support`,
  `Algebra.IsEtaleAt`, and `Algebra.Extension.Cotangent.mk_eq_zero_iff`. None states a
  common ideal-power bound for both modules of an arbitrary finite presentation.
- `msearch.py ... loogle` with query `Algebra.Generators.cotangentComplex, Ideal`:
  0 hits; unknown identifier `Algebra.Generators.cotangentComplex`. This failed-name
  search is not evidence that the needed cotangent map is absent.
- `msearch.py ... grep` with query
  `etaleLocus_eq_compl_support|subsingleton_h1Cotangent|cotangentComplex`, subdirectory
  `RingTheory`: 25 hits, including cotangent-localization and formal-etale results.
  They do not state the common-power theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `jacobian.*torsion|torsion.*etale|finite_type.*cotangent`, followed by the narrower
  `etale.*away|conormal.*torsion|Jacobian.*torsion|jacobian.*torsion` in ring theory,
  algebraic geometry, and `dag/lean_names_upstream.json`: no identical theorem.
  The nearby upstream `exists_etale_away_of_localized_cotangent_vanishing` was read;
  it gives an etale neighbourhood from local vanishing and has a different conclusion.
- Direct Mathlib `rg` for `ofSurjective`, `cotangentSpaceBasis`, `cotangentComplex`,
  and `cotangentRestrict` located `Generators.ofAlgHom`, the conormal quotient and
  differential, and the exact coordinate map. These existing constructions are used.

No statement dispute or node fault was found. The library's unqualified `Etale` and
`id` names resolve to other Algebra declarations in this namespace; the delivered
statement explicitly qualifies `AlgebraicGeometry.Etale` and `_root_.id`.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
