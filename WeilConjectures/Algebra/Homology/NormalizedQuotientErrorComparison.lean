/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorComparisonMap

/-! # Comparisons for the normalized quotient error cone

Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
namespace SheafOfModules.NormalizedQuotientError
variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The prescribed error map is a quasi-isomorphism on a componentwise K-flat model.
Source: blueprint sk-lem-sp-tower proof, paragraph 2, principal quotient calculation
(blueprint: lem-sp-normalized-quotient-error-map-quasiiso).

Proof: evaluate the whole tower at n. Identify the module cokernel R/t^(k+1)
with the restriction of the actual sheafified ring quotient, preserving the
quotient projection. Under these identifications the finite coefficient error
complex is [B_(m+n) --t^(m+1)--> B_(m+n) --> B_m]. On sectionwise quotients,
regularity of t identifies its only cohomology, in degree -1, with B_m by
x mapping to t^n*x: the kernel of t^(m+1) in R/(t^(m+n+1)) is t^n*B_(m+n),
and cancellation identifies this image with R/(t^(m+1)). The quotient map is
surjective and its kernel is the image of t^(m+1), so the other cohomology
vanishes. Exact module sheafification preserves this calculation, the explicit
comparison and its B_(m+n)-linearity. This is the principal quotient error-cone
comparison. Tensor over B_(m+n) with the K-flat P_(m+n); K-flatness makes the
resulting total-tensor comparison a quasi-isomorphism even when P is unbounded.
The canonical total-tensor, shift and cocone comparisons identify its source
with V_n[1] via M.nu and its target with Cocone(M.epsilon)_n via M.epsilon_eq.
The unit-generator and target-summand formulas identify the transported map
with E.j (the quotient projections are locally surjective, so these generators
determine an R-linear map locally). Hence every evaluated E.j is a
quasi-isomorphism. Evaluation detects quasi-isomorphisms of whole-tower complexes. -/
theorem errorComparisonMap_quasiIso (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : Mono ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (q : ∀ n : ℕ, B.obj (op n) ≅
      principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : ∀ n : ℕ, a.app (op n) ≫ (q n).hom =
      principalPowerRingProjection R (ringSection R t) (n + 1))
    (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (hP : systemComponentwiseKFlat B P)
    (m : ℕ)
    (M : QuotientModel R t B a A P m)
    (E : ErrorComparisonMap R t B a A P m M) : QuasiIso E.j := by sorry

end SheafOfModules.NormalizedQuotientError
