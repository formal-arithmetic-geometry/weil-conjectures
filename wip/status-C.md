# Workstream C status

## Item 1 (lem-coef-integral-hom-reduction) — ReductionExtendScalars COMPILES. ReductionHom: fixed
## HasCountableCoproducts timeout (local instance); remaining: kernel deterministic timeouts in
## derivedExtendScalarsTensorIso / derivedHomRestrictScalarsIso, elaboration fixes in last lemma.
## Scratch test file Etale/Derived/ScratchC.lean (DELETE before finishing).
Route: derived extension of scalars LF along Λ → Λ/(ϖⁿ), LF ⊣ Res, LF monoidal,
RHom_Λ(K, Res N) ≅ Res RHom(LF K, N) by conjugate of left-adjoint iso; Res(LF L) ≅ L ⊗ (Λ/ϖⁿ).
New files (all mine):
- WeilConjectures/CategoryTheory/DerivedCategory/LeftDerivedFunctor/MonoidalKFlat.lean
  (generalised derived tensor comparison for non-exact F) — COMPILES.
- WeilConjectures/Algebra/Category/ModuleCat/Sheaf/ReductionExtendScalars.lean
  (ReductionDatum.adjunction, Sheaf.extendScalars, iso to reductionFunctor, T : F⋙Res ≅ ⊗c,
   preservesFlat_extendScalars, extendScalarsReductionDatum) — fixing errors (last round:
   adjunction def, unit_app lemmas, include hf, σ_comp_r).
- WeilConjectures/SixFunctors/Etale/Derived/ReductionHom.lean (derivedExtendScalars,
  adjunction, isDerivedBaseChange of unit, tensor iso, derivedHomRestrictScalarsIso,
  nonempty_iso_derivedRestrictScalars_derivedExtendScalars) — NOT YET COMPILED.
- IntegralCoefficients.lean: imports ReductionHom; sorry of
  nonempty_iso_reductionModIdeal_derivedHom replaced by proof — NOT YET COMPILED.
New modules added to WeilConjectures.lean (done).

Build helper: /task/scratch/C/build.sh <file> → /task/scratch/C/<base>.log (EXIT line).

## Items not started
- Item 2 boundedConstructibleIntegral_exceptionalAdjoint (3 sorries): needs finite-level
  Rf^! for Noetherian Λ torsion objects + lem-coef-finite-exceptional (bundle) + integral
  Verdier (other subsections). Judged very large.
- Item 3 isIdempotentComplete_boundedConstructibleRational: needs a t-structure on the
  rationalization (Balmer–Schlichting K0 obstruction rules out pure categorical proof). Large.
- Item 4: lem-weil-qbar-idempotent-complete already has decl in ProEtale/Adic/Karoubian.lean.
  rem-ptr-weil-exceptional-adjoint-admissibility-9: remark, no Lean content.
  Others (lem-coef-finite-direct-image, lem-coef-finite-exceptional,
  lem-coef-rational-operations, rem-weil-biduality-coefficients) not started.
