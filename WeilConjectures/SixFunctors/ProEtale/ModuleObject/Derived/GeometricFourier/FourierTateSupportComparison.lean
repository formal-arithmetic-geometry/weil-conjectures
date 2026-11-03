/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.FourierTateKernelComparison

/-! # Tate compatibility of compact support and rank shift

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
prop-base-linear.proof.md, paragraphs 3, 4 and (2).
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

/-- The compact support and shift factors of the prescribed Fourier transform.
Source: def-fd-transform, displayed formula
(blueprint: lem-fd-tate-support-comparison). -/
def supportPart {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) (r : ℤ) : category D Λ X ⥤ category D Λ Y :=
  rightDerivedLowerShriekOfCompactification Λ (compactification D c) ⋙ shiftFunctor _ r

/-- The existing compactification Frobenius exchange followed by its exact shift map.
Source: prop-base-linear.proof.md, final paragraph
(blueprint: lem-fd-tate-support-comparison). -/
def supportPartDatum {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) (r : ℤ) (K : category D Λ X)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).obj
      ((supportPart D Λ c r).obj K) ≅ (supportPart D Λ c r).obj K :=
  ((StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).commShiftIso r).app _ ≪≫
    (shiftFunctor _ r).mapIso (pushDatum D Λ c K φ)

/-- Tate tensor commutes with compact support and the rank shift, on the kernel inputs.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/prop-base-linear.proof.md,
paragraphs 3, 4 and (2) (blueprint: lem-fd-tate-support-comparison).

Proof: use the signed Tate pullback comparison along the second Fourier projection.
Its target Tate line is lisse of rank one and has Tor amplitude [0,0]. The kernel
input is bounded constructible, by pullback stability and the kernel's rank-one
lisseness. Apply the compact-support projection isomorphism to this input and Tate
line, identifying its pulled-back line by the signed comparison. Commute the rank
shift with tensor by shifting the first tensor factor. Naturality of the projection,
Tate comparison and tensor/shift constraints gives a natural isomorphism on the
specified inputs. For the Weil equation, expand the proper/open exchange on the
base-changed arithmetic compactification. The proper projection is the counit mate,
so pullback monoidality and mate naturality give its Frobenius square. For the open
factor the normalized comparison restricts to the identity; open-adjunction
injectivity gives its square. Paste both squares with the signed Tate Weil square
and the shift coherence square. The resulting equation is exactly the displayed
one for supportPartDatum. The argument uses neither an arbitrary Weil lift nor an
unrestricted projection isomorphism. Zero inputs and empty schemes are included. -/
theorem fourier_tate_support_comparison
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (p : V ⟶ S) (p' : V' ⟶ S)
    [LocallyOfFiniteType (square D p p').hom] [QuasiCompact (square D p p').hom]
    (ψ : AddChar D.k₀ (MonObj.Γ (Coefficient.rational E |>.obj ell)))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r m : ℤ) :
    ∃ e :
      (constantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V)).ι ⋙
        kernelPart D ((Coefficient.rational E).obj ell) p p' ψ b ⋙
        twist D ell E (square D p p') m ⋙
        supportPart D ((Coefficient.rational E).obj ell) (f := snd D p p') c r ≅
      (constantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V)).ι ⋙
        transform D ((Coefficient.rational E).obj ell) p p' ψ b c r ⋙
        twist D ell E V' m,
      ∀ (K : ConstantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V))
        (φ : (StrictWeilCondensed.action ((Coefficient.rational E).obj ell)
          (StrictWeilCondensed.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (StrictWeilCondensed.action ((Coefficient.rational E).obj ell)
            (StrictWeilCondensed.modelFrobenius D V')).map (e.hom.app K) ≫
          (StrictWeilCondensed.tensorDatum ((Coefficient.rational E).obj ell)
            (StrictWeilCondensed.modelFrobenius D V')
            (transformDatum D ((Coefficient.rational E).obj ell) p p' ψ b c r K.obj φ)
            (StrictWeilCondensed.tateDatum ell (.rational E)
              (StrictWeilCondensed.modelFrobenius D V') m)).hom =
        (supportPartDatum D ((Coefficient.rational E).obj ell) (f := snd D p p') c r
          ((twist D ell E (square D p p') m).obj
            ((kernelPart D ((Coefficient.rational E).obj ell) p p' ψ b).obj K.obj))
          (StrictWeilCondensed.tensorDatum ((Coefficient.rational E).obj ell)
            (StrictWeilCondensed.modelFrobenius D (square D p p'))
            (kernelPartDatum D ((Coefficient.rational E).obj ell) p p' ψ b K.obj φ)
            (StrictWeilCondensed.tateDatum ell (.rational E)
              (StrictWeilCondensed.modelFrobenius D (square D p p')) m))).hom ≫
          e.hom.app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
