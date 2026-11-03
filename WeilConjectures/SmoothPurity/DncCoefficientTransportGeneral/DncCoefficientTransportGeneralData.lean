/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData

/-!
# General-field canonical coefficient transport data

This module supplies the field-indexed coefficient and deformation assertions used
by the general-ring transport theorem.  It reuses the canonical maps from the
finite-field data module and introduces no alternate geometric construction.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md,
Proof (2) (blueprint: def-pur-dnc-coefficient-transport-general-data).
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace DncCoefficientTransportGeneral
open DncCoefficientTransport

/-- Arbitrary-base-change coefficient square, without imposing any section on g0.
All morphisms remain in the separated finite-type k-setting for the supplied field k.
Source: Proof (2), Step 2 (blueprint: def-pur-dnc-coefficient-transport-general-data). -/
def MixedBaseChange (k : Type u) [Field k] {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) : Prop :=
  ∀ (V S S' : Over (Spec (.of k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S'.hom] [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom]
    (g : V ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r g.left]
    [HasCompactification g.left] [QuasiCompact g.left] (h : S' ⟶ S),
    IsIso (Etale.smoothDualizingBaseChangeMap A g.left h.left) ∧
      IsIso (Etale.smoothDualizingBaseChangeMap B g.left h.left) ∧
      Etale.ExceptionalCoefficients.BaseChangeCompatibility φ g.left h.left (𝟙_ _)

/-- The counit-normalized chart equation, including the standard coordinate pair over k.
The right-adjoint comparisons are fixed by etale summation and ordered affine trace;
the model coefficient map is the canonical root-normalized Tate reassociation.
Source: Proof (2), Step 3 (blueprint: def-pur-dnc-coefficient-transport-general-data). -/
def ChartCompatibility (k : Type u) [Field k] {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) : Prop :=
  ∀ (V S : Over (Spec (.of k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsNoetherian V.left] [IsNoetherian S.left]
    (g : V ⟶ S) [HasCompactification g.left] (d : ℕ)
    [SmoothOfRelativeDimension d g.left]
    {U : Scheme.{u}} [IsNoetherian U] (i : U ⟶ V.left) [IsOpenImmersion i]
    (e : U ⟶ affineTraceTower S.left d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g.left = e ≫ affineTraceProjection S.left d)
    (MA : Etale.EtaleCompactSupportNormalization A)
    (MB : Etale.EtaleCompactSupportNormalization B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : Etale.OrdinaryFiniteTwistTransport A N hA)
    (tB : Etale.OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum B N hB tB T hT)
    (hS : IsUnit (N : Γ(S.left, ⊤))),
    (Etale.scalarExtension φ U).map
        ((ProEtale.reductionEtaleChartRightIso A MA g.left i d e he
          (HasCompactification.compactification g.left)
          (Etale.rightDerivedUpperShriek A g.left)
          (Etale.rightDerivedUpperShriekAdjunction A g.left)
          N hA tA PA hS).hom.app (𝟙_ _)) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e (𝟙_ _)).hom ≫
      (Etale.affineTraceRight B N hB S.left d ⋙ Etale.ordinaryFinitePullback B e).map
        (Etale.ExceptionalCoefficients.unitIso φ S.left).hom =
    (Etale.scalarPullbackIso φ i).inv.app
        (Etale.dualizingComplex A g.left) ≫
      (Etale.ordinaryFinitePullback B i).map (DncCoefficientTransport.dualizingMap φ g.left) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g.left i d e he
        (HasCompactification.compactification g.left)
        (Etale.rightDerivedUpperShriek B g.left)
        (Etale.rightDerivedUpperShriekAdjunction B g.left)
        N hB tB PB hS).hom.app (𝟙_ _)

/-- The complete finite coefficient transport assertion in canonical coordinates over k.
Source: Proof (2), all clauses (blueprint: def-pur-dnc-coefficient-transport-general-data). -/
def Assertions (k : Type u) [Field k] (ell n : ℕ) [Fact ell.Prime]
    {V S : Scheme.{u}} (g : V ⟶ S) [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (G : DncCoefficientTransport.Geometry g s) {B : Type u} [CommRing B] [Finite B]
    (φ : DncCoefficientTransport.BaseRing.{u} ell n →+* B) : Prop := by
  letI := G.compact
  letI := G.compactFamily
  letI := G.compactNormal
  letI := G.quasiCompactNormal
  exact
    IsIso (realizedSectionMap φ g s) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.normalConeProj g s)
      s.normalConeZeroSection) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne
      (ULift.{u + 1, u} (DncCoefficientTransport.BaseRing.{u} ell n)) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero
      (ULift.{u + 1, u} (DncCoefficientTransport.BaseRing.{u} ell n)) g s) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne (ULift.{u + 1, u} B) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero (ULift.{u + 1, u} B) g s) ∧
    (∃! κR : Etale.NoetherianSectionSpecialization.family
        (ULift.{u + 1, u} (DncCoefficientTransport.BaseRing.{u} ell n)) g s ≅
        (Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (DncCoefficientTransport.BaseRing.{u} ell n)))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant
              (ULift.{u + 1, u} (DncCoefficientTransport.BaseRing.{u} ell n)) g s),
      Etale.NoetherianSectionSpecialization.Normalized
        (ULift.{u + 1, u} (DncCoefficientTransport.BaseRing.{u} ell n)) g s hs κR) ∧
    FibreCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs ∧
    LocalizationCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s ∧
    MixedBaseChange k (RingHom.ulift.{u + 1, u + 1, u, u} φ) ∧
    ChartCompatibility k (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ell ^ n) ∧
    NormalizedTransport (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs


end DncCoefficientTransportGeneral
end WeilConjectures
