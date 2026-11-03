/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.CondensedFourierGeometricModel

/-! # Tate compatibility before compact support

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
prop-base-linear.proof.md, paragraphs 1, 2 and (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
open PurityTransport
variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback and kernel tensor in the prescribed transform, before compact support.
Source: def-fd-transform, displayed formula
(blueprint: lem-fd-tate-kernel-comparison). -/
def kernelPart {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) :
    category D Λ V ⥤ category D Λ (square D p p') :=
  (upperStar Λ (map D (fst D p p'))).leftDerivedFunctor ⋙
    tensorRight (kernel D Λ p p' ψ b)

/-- The specified tensor of pullback and arithmetic-kernel Weil structures.
Source: prop-base-linear.proof.md, final paragraph
(blueprint: lem-fd-tate-kernel-comparison). -/
def kernelPartDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) (K : category D Λ V)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ
      (StrictWeilCondensed.modelFrobenius D (square D p p'))).obj
        ((kernelPart D Λ p p' ψ b).obj K) ≅ (kernelPart D Λ p p' ψ b).obj K :=
  StrictWeilCondensed.tensorDatum Λ (StrictWeilCondensed.modelFrobenius D (square D p p'))
    (pullDatum D Λ (fst D p p') K φ) (kernelDatum D Λ p p' ψ b)

/-- Tate tensor commutes with the pullback and kernel tensor, including the actual Weil maps.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/prop-base-linear.proof.md,
paragraphs 1, 2 and (2) (blueprint: lem-fd-tate-kernel-comparison).

Proof: apply the root-normalized signed Tate pullback along the first Fourier projection.
For nonnegative degrees this is the integral root comparison, scalar extension, and
ordered tensor recursion. For negative degrees use the evaluation inverse transpose of
the positive comparison and the coefficient-unit comparison. Derive the degree-zero
comparison using the exact single-functor isomorphism. Monoidality identifies the
pullback of K tensor the Tate line; associate, braid the Tate line past the kernel,
and reassociate. These constraints are natural in K. The signed comparison's Weil
square, monoidality of pullback-square compositors, and naturality of the associator
and braiding show that the composite intertwines precisely kernelPartDatum on the
source and tensorDatum on the target. This includes degree zero, zero K, empty schemes,
and negative degrees; no rank or primitive-root choice is made. -/
theorem fourier_tate_kernel_comparison
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (p : V ⟶ S) (p' : V' ⟶ S)
    [LocallyOfFiniteType (square D p p').hom] [QuasiCompact (square D p p').hom]
    (ψ : AddChar D.k₀ (MonObj.Γ (Coefficient.rational E |>.obj ell)))
    (b : Γ(pullback p.left p'.left, ⊤)) (m : ℤ) :
    ∃ e :
      (constantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V)).ι ⋙
        twist D ell E V m ⋙ kernelPart D ((Coefficient.rational E).obj ell) p p' ψ b ≅
      (constantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V)).ι ⋙
        kernelPart D ((Coefficient.rational E).obj ell) p p' ψ b ⋙
        twist D ell E (square D p p') m,
      ∀ (K : ConstantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V))
        (φ : (StrictWeilCondensed.action ((Coefficient.rational E).obj ell)
          (StrictWeilCondensed.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (StrictWeilCondensed.action ((Coefficient.rational E).obj ell)
            (StrictWeilCondensed.modelFrobenius D (square D p p'))).map (e.hom.app K) ≫
          (StrictWeilCondensed.tensorDatum ((Coefficient.rational E).obj ell)
            (StrictWeilCondensed.modelFrobenius D (square D p p'))
            (kernelPartDatum D ((Coefficient.rational E).obj ell) p p' ψ b K.obj φ)
            (StrictWeilCondensed.tateDatum ell (.rational E)
              (StrictWeilCondensed.modelFrobenius D (square D p p')) m)).hom =
        (kernelPartDatum D ((Coefficient.rational E).obj ell) p p' ψ b
          ((twist D ell E V m).obj K.obj)
          (StrictWeilCondensed.tensorDatum ((Coefficient.rational E).obj ell)
            (StrictWeilCondensed.modelFrobenius D V) φ
            (StrictWeilCondensed.tateDatum ell (.rational E)
              (StrictWeilCondensed.modelFrobenius D V) m))).hom ≫ e.hom.app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
