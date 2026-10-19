## Worker report

Item: sk-lem-sp-tower, Q02, stage 2, 2026-10-18 UTC.
Module: Sheaf.Paper.SmoothPurityTowerReconstruction.
Main declaration: AlgebraicGeometry.ProEtale.spTower_reconstruction.

The statement is unchanged. The module states both reconstruction conclusions for the
recorded normalized constructible finite-Tor coefficient tower. It defines the actual
completed-to-ell-power coefficient projection, the restricted evaluations and their
transitions, and the canonical scalar-adjoint reduction map. No independent notion is
introduced. These are helpers belonging to the canonical limit/map of this item; all
are listed in lean.declarations and have source/blueprint docstrings. Every theorem
has sorry as its proof; every definition has real data. The two transition choices
come from existence-and-uniqueness statements, not mere existence. The completed-ring
comparison already has an existence-and-uniqueness characterization in the dependency.

Hypothesis and clause matching:

- The fixed prime is `(l : ℕ) [Fact l.Prime]`.
- The finite extension E/Q_l and its integer ring are the recorded coefficient datum:
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`, with Padic.coefficientExtensionIntegers inside
  spCoefficientRing. No extra finite-field datum, residue characteristic, or
  invertibility of l on the scheme is assumed.
- The arbitrary scheme T is `(T : Scheme.{u})`, following exactly the universe
  convention of both recorded input/target category definitions. Its small pro-etale
  site still has object universe u+1 and morphism universe u; neither is collapsed.
  Coefficients and module sections occupy u+1. spReconstructionSiteSmall supplies
  the already valid small-model fact with explicitly fixed universe parameters.
- The ambient derived coefficient tower is
  `C : spDerivedCoefficientTowers l E T D`; D is the exact normalized interface
  SpCoefficientTowersAbelian supplied by sp_coefficient_towers_abelian. This is a
  presentation of the recorded tower category, not a new hypothesis on a tower.
- Membership in Dctf is `hC : spConstructibleTorTowers l E T D C`. Its recorded
  definition includes bounded constructible finite-Tor levels and independent
  common cohomological and Tor intervals over all positive indices.
- Normalization is `hnorm : IsSpNormalizedTower l E T D C`, the recorded predicate
  requiring IsIso of the actual D.reduction at every m <= n, including equality.
- The object denoted Rlim is M with its Roos presentation p, δ, hlim.
  `hlim : IsDerivedLimitTriangle (fun n =>
  (spDerivedCompletedTransition l E T D n).app C) M p δ` asserts exactly the
  distinguished product triangle with operator 1-s. The product witness, M, p and
  δ are presentation data for the derived inverse limit and its projections; they
  are not additional conditions on C. The strict-tower homotopy-limit dependency
  supplies such presentations, with exact products on this pro-etale site. The
  theorem holds for every presentation, as does the existing NormalizedDVREffectivity
  interface. It does not choose an arbitrary object from a mere Nonempty assertion.
- The first conclusion is `WeilConjectures.sfIntegralConstructible l E T M`.
  This uses exactly the recorded target predicate: derived completeness, every
  positive uniformizer reduction constructible, and one common finite support
  interval for those reductions. It is not replaced by ell-level constructibility
  alone, and no global finite-field datum is reintroduced.
- The second conclusion is `∀ n : ℕ, IsIso (spTowerReconstructionMap ... n)`.
  Natural n is the source's positive exponent n+1, so every positive m is included.
  The source of that arrow is the universal K-flat-derived scalar extension
  `(D.scalar (spCompletedEllCommProjection ... n)).model.T.obj M`; its target is
  `(spDerivedCoefficientEvaluation ... n).obj C`. Both live in the finite-quotient
  derived module category, so the conclusion is IsIso there, not merely after
  forgetting its finite scalar action.
- The word natural is fixed by construction: spTowerReconstructionMap is the inverse
  derived tensor-restriction Hom equivalence applied to `p ≫ Pi.π _ n`. The
  SystemScalarModel adjunction is normalized on ordinary pure tensors and on derived
  representative comparisons. The limit coefficient projection is fixed by the
  coefficient-tower comparison and the actual limit coordinate. The ordinary
  transition helper is fixed sectionwise by D.equivalence's original transition;
  the derived transition is fixed on all localized complexes by its factorization
  equation. There is no free or uncharacterized comparison morphism.

Dependencies read and used:

- Sheaf.Paper.SmoothPurityNormalizedTowers:
  spDerivedCoefficientTowers, spDerivedCoefficientEvaluation,
  spConstructibleTorTowers, IsSpNormalizedTower, plus their full definitions.
- Sheaf.Paper.SmoothPurityCoefficientTowers:
  spCoefficientRing, spCoefficientRings, spCoefficientTowers,
  sp_completed_coefficient_limit. The ell-power tower is kept even when ramified.
- Sheaf.Paper.SmoothPurityCoefficientTowersAbelian:
  SpCoefficientTowersAbelian, spCoefficientEvaluation, spCoefficientCommRings;
  its equivalence identifies all sections and actual transitions.
- Sheaf.Paper.SfIntegralConstructible:
  WeilConjectures.sfIntegralConstructible, based on IsSfDerivedComplete and the
  uniformizer reduction functors. This is the item's recorded dependency binding.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  SheafOfModules.DerivedChangeOfRingsCochainModel and its universal scalar functor;
  D.scalar uses that model via the recorded SystemScalarModel interface.
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients:
  CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients, with its
  total derived functor, evaluated transitions, natural Roos triangles and
  pro-zero conclusions. CategoryTheory.IsDerivedLimitTriangle is its exact
  imported definition of the Roos presentation.
- Mathlib: SheafOfModules.restrictScalars, Functor.mapDerivedCategory,
  Functor.mapDerivedCategoryFactors, Functor.preimage, Pi.π, IsIso,
  and the existing scalar extension/restriction adjunction interfaces.

All recorded proof-dependency modules are imported privately unless already needed
publicly for the signature. This includes K-flat resolution, sequential tower
fullness, repleteness, exact countable products, constant-completion equivalence,
DVR integers, derived adjunction, finite-coefficient scalar extension and Tor
amplitude. The main docstring carries all twelve DAG proof steps, including the
ramified coefficient calculation, both completeness limits and the passage from
ell-power to uniformizer-power constructible reductions.

Edge cases checked:

- First level m=1 is n=0. There is no missing first positive quotient. The paper's
  categories are indexed by m>=1, not by the zero exponent; n=0 never means O/1.
- Identity and longer reductions remain in IsSpNormalizedTower; normalization is
  not tested only on adjacent levels or on restricted R-linear maps.
- The zero tower, zero limit and empty scheme satisfy the same predicates and
  maps. The common finite intervals permit zero cohomology, and no nonempty scheme
  or nonzero module is assumed.
- No quasi-compactness, Noetherian hypothesis on T or invertibility of l is added.
- In a ramified extension ell=unit*pi^e, no equality ell=pi is used. The input uses
  ell-power quotients; the output uses the recorded uniformizer-complete predicate.
- Negative cohomological degrees and arbitrary finite interval endpoints are
  retained by the imported predicates. The theorem does not add a sharper bound.
- The natural map is checked in D(B_m), not only in D(R).

Searches for an existing statement (raw remote-search records are in searches.jsonl):

- leanfinder: "A normalized tower of constructible finite Tor amplitude complexes
  over powers of a prime is reconstructed by its derived inverse limit". Eight
  hits concerned BDeRham, ordinary adic completion and local cohomology; none matched.
- loogle: "Functor.rightDerived, SheafOfModules.restrictScalars, Limits.lim".
  No hits; Functor.rightDerived was reported unknown. No result was used.
- grep through msearch: "normalized.*tower|tower.*normalized|systemLimit".
  Four unrelated normalized-field-trace hits; none matched.
- leansearch: "derived inverse limit normalized constructible tower finite Tor
  amplitude". Eight hits concerned ordinary directed limits, tensor/direct-limit
  comparisons and the derived T-structure; none matched.
- rg in the upstream WeilConjectures tree and shared lean/Sheaf for
  "sk-lem-sp-tower|normalized.*tower|tower.*normalized". Found the generic adic
  framework and related normalizedDVR material, not this statement. In particular
  normalizedDVRTower_effectivity has different tower data, uniformizer indices,
  an extrinsic finite-field datum and only a completeness conclusion. Its Roos
  presentation pattern is reused, not its distinct notion or statement.
- rg for the new principal helper/declaration names in dag/lean_names_upstream.json,
  upstream WeilConjectures and shared lean/Sheaf found no collisions.
- Read the missing live proof source with the prescribed
  `scompile.py --source WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`;
  its actual theorem and docstring confirm the exact-product computation and
  cohomology preservation used in proof steps 3, 7 and 11.

Validation: scompile.py compiled the sandbox file and its library-path form cleanly
within the 60-second per-file limit, including the complete proof import list.
No non-sorry warning remains. Initial errors were repaired by using the correct
Functor namespace, parenthesizing the mapped complex functor, and explicitly fixing
the smallness theorem's independent lift universe to zero. No target statement,
dependency node, upstream source or launcher tool was edited.

No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by Q02

Independent reading by the maintainer's reviewer (the delivered section was the worker's
own cross-check, delivery-errors H11). I had the node, its five statement dependencies
with their recorded Lean, and the delivered module open. The node's statement as a list:

1. Fixed prime l, finite E/Q_l, ring O_E, any scheme T. Lean: `(l : ℕ) [Fact l.Prime]`,
   `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`,
   `(T : Scheme.{u})`. Same as both recorded categories (SmoothPurityNormalizedTowers,
   SfIntegralConstructible); the shared universe u is inherited from them, and the
   pro-etale site keeps objects in u+1 and morphisms in u. Verdict: correct.
2. The ambient category D(Tow(T,O_E)). Lean: `C : spDerivedCoefficientTowers l E T D`, with
   D : SpCoefficientTowersAbelian the interface that the recorded normalized-tower
   declarations themselves take as a parameter. Not an extra hypothesis. Correct.
3. C in Dctf(T,O_E/l^•). Lean: `hC : spConstructibleTorTowers l E T D C` (levelwise
   Dctf, common [a,b] and common Tor interval). Correct, the recorded predicate.
4. C normalized. Lean: `hnorm : IsSpNormalizedTower l E T D C`, the recorded predicate
   (IsIso of D.reduction for all m ≤ n, m = n included). Correct.
5. R lim_n C_n, in D(T, O_{E,T}). Lean: any M in D(scalarReductionSource l E T) (modules
   over the completed ring) with p, δ such that IsDerivedLimitTriangle holds for the
   levels restricted to the completed ring and the transitions n+1 → n induced by the
   tower's own strict transitions. IsDerivedLimitTriangle is the distinguished triangle
   M → ∏ → ∏ → M[1] with 1 − shift (towerTransitionEndomorphism). This is the
   homotopy-limit description of Stacks 08TB/0940, which is the same as the strict-tower
   derived limit of the dependency lem-weil-pbc-ringed-strict-tower-homotopy-limit.
   Any two presentations are isomorphic compatibly with p (TR3 plus the five lemma), so
   quantifying over all of them is neither stronger nor weaker; `[HasProduct …]` is a
   Prop and holds on this site. Helpers: spCompletedEllProjection takes the
   ∃!-characterized iso O_{E,T} ≅ lim R_n, then the limit projection.
   spCompletedTransition and spDerivedCompletedTransition are taken from ∃! statements
   whose characterizations hold (the restricted scalar actions agree because π_n =
   π_{n+1} ≫ q_n; the derived map is fixed on Q-objects and Q is essentially
   surjective). Correct, not arbitrary, not hollow.
6. Conclusion (i): R lim ∈ D^b_c(T,O_E). Lean: `sfIntegralConstructible l E T M`, the
   recorded binding of def-weil-derived-complete-integral-detailed (IsSfDerivedComplete,
   constructible uniformizer reductions, one common support interval). Correct.
7. Conclusion (ii): for every m ≥ 1, the natural map (R lim) ⊗^L R_m → C_m is an iso in
   D(T, O_E/l^m). Lean: `∀ n : ℕ, IsIso (spTowerReconstructionMap … n)`, n meaning m = n+1.
   The source is `(D.scalar φ_n).model.T.obj M`, the universal derived scalar extension
   along φ_n : O_{E,T} → R_{n+1}. The target is the level evaluation
   `spDerivedCoefficientEvaluation … n` in the finite-coefficient derived category. The map is
   `adjunction.homEquiv.symm (p ≫ Pi.π _ n)`. The right adjoint of that adjunction is
   restrictScalars(φ_n).mapDerivedCategory, which is the same restriction used for the Roos
   levels. So this is the canonical adjoint of the limit projection, the node's proof
   step 8. Every m, in the right category, quantifier order unchanged. Correct.

Edge cases: m = 1 is n = 0 (O/l, not O/1); m = n is included in hnorm; zero tower,
empty T, ramified E (l = u·π^e, l is not identified with π), negative degrees: none is
excluded by an added assumption. No quasi-compactness, Noetherian condition, l ≠ p or
finite-field datum is added.

Searches: I searched with `rg` in the side clone's lean/ tree and slopmaster2 for
IsSpNormalizedTower, spDerivedCoefficientEvaluation and the new names. The only other
use is the dependency module, and there are no collisions. normalizedDVRTower_effectivity
(Sheaf/Paper/NormalizedDVREffectivity.lean) uses another tower notion with uniformizer
indices and a finite-field datum, so it is not a duplicate. Imports: the public imports
are the statement's own; the private imports are the recorded modules of the
proof_deps. Mathlib DerivedCategory.Fractions and DerivedCategory.HomologySequence
stand in for the two proof deps that have no Lean record.

Compile: nt_compile.py --json on the delivered file gives exit 0 in 5.8 s, with no
diagnostics.

Mismatches: none in the statement. Changed: only this section (H11). The worker report
and the module are unchanged.
