# Minimal reproduction: kernel deterministic timeout on the finite étale Tate reading (K4 / smooth purity, Weil Rf^! orientation)
Base: slopmaster2 08fcdf1cca + 22 files from branch sheaf/k4-smooth-purity-wip (commit a1ee12d022, unchanged except the two `set_option` lines).
Build: `lake build WeilConjectures.WeilSheaf.SmoothPurityFiniteTateOneReading` (≈ 40 s elaboration, then `(kernel) deterministic timeout` at the lemma).
Generic lemma: `CategoryTheory.purity_reading_composition_named` (WeilSheaf/SmoothPurityReadingComposition.lean): composes a reduction square and a reading square
through a pullback comparison α : P ⋙ F ≅ F₀ ⋙ Q; it is instantiated with P = condensed pullback ī^* of Λ-module objects, F/F₀ = finiteCoefficientModEquivalence,
Q = étale pullback of ModuleCat(ℤ/ℓⁿ)-sheaves, α = upperStarFiniteCoefficientModEquivalenceIso, to prove the concrete instance
`purity_finiteCoefficientIntegralTateOneReading_pullback` (the finite-coefficient reading of the integral Tate line commutes with pullback).
Symptom: elaboration succeeds (`cast_proofs` casts 73 + 83 + 156 differing proof subterms, one `Eq.mpr` each over the whole goal), then the KERNEL times out at 200000
heartbeats; the variant `_exact` (plain `exact`, maxHeartbeats 2000000) elaborates in ~480 s and the kernel STILL times out at 2M.
Measured (set_option diagnostics true, logs C1-20261105T175418 / 180044): non-proof differences between `h` and the goal are 1854 reducible-abbrev mismatches
(`integersModPowCoeff ℓ E n` vs `ULift (PadicAlgCl.integersModPow ℓ E n)` ×1106, `Profinite.integersModPowRingObj` vs `continuousMapRingObj (integersModPow …)` ×748);
155 of the 180 proof differences are the `Precoherent Profinite` instance inside `coherentTopology Profinite` (Mathlib `instPrecoherentOfFinitaryPreExtensiveOfPreregular`
vs the auxiliary constant `ProEtale.pointLowerStar._proof_1`); the unifier/kernel unfold CategoryStruct.comp ×20378, Classical.choose ×6207, Mod.comap ×5752,
presheafToSheaf ×5451, sheafPullback ×3588, Functor.lan ×3375, CondensedRing.upperStar ×2810, Mod.comapEquivalenceOfIsIso ×2806, Mod.extendScalars ×1912, …:
the explicitly spelled functor arguments of the generic lemma are only definitionally (not syntactically) equal to the functors in the types of pullIso / α / the named isos.
Tried: cast_proofs (kernel timeout), exact_mod_proofs, plain exact at 2M heartbeats (kernel timeout), direct goal assignment without Meta check (kernel timeout),
dsimp-normalizing the two aliases + exact_mod_proofs (K4, pending). Question: how to state/prove such instances so that neither the unifier nor the kernel
compares the condensed pullback functors structurally (e.g. a canonical form for the Precoherent instance, or an API to instantiate α/pullIso with `_` functors).
