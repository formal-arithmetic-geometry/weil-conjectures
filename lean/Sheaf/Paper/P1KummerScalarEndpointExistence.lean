/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.P1KummerScalarEndpoints
import all Sheaf.CategoryTheory.ExactDegreeZeroAdjoint
import all Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all Sheaf.AlgebraicGeometry.SupportedKummerScalarMaps
import all Sheaf.SixFunctors.GeoCartierCoeffExtension
import Sheaf.AlgebraicGeometry.SupportedKummerScalarDerived
import Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar
import Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum

/-! # Existence of the normalized ordinary coefficient endpoints

Source: Stacks 03PK, 06YY and 0D6D; blueprint Charts, scalar Kummer comparison
(blueprint: lem-sp-p1-kummer-scalar-endpoint-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cachedModSheafify (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedModSheafify

private def normalizedLineMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) :
    Scheme.finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N B hB) :=
  (Scheme.lineHomEquiv T N A hA _).symm (ordinaryFiniteRootMap B N hB T)

private theorem normalizedLineMap_apply
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (W : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (normalizedLineMap φ N hA hB T).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z := by
  have h := congrArg (fun f ↦ f.hom.app W z)
    ((Scheme.lineHomEquiv T N A hA
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N B hB))).apply_symm_apply
      (ordinaryFiniteRootMap B N hB T))
  rw [Scheme.lineHomEquiv_generator] at h
  change (normalizedLineMap φ N hA hB T).hom.app W
    (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
      Scheme.finiteEtaleTateOneGenerator B N T hB W 1 z at h
  rw [Scheme.finiteEtaleGenerator_smul T N A hA W a z, _root_.map_smul, h]
  change (φ a) • Scheme.finiteEtaleTateOneGenerator B N T hB W 1 z = _
  exact (Scheme.finiteEtaleGenerator_smul T N B hB W (φ a) z).symm

private theorem lineMap_ext
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u})
    (f g : Scheme.finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N B hB))
    (h : ∀ (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W),
      f.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
        g.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z)) : f = g := by
  apply (Scheme.lineHomEquiv T N A hA _).injective
  ext W z
  simpa only [Scheme.lineHomEquiv_generator] using h W z

set_option maxRecDepth 2000

private theorem derivedUnit_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)
    (θ : G ⟶ (Sheaf.restrictScalars T.smallEtaleTopology ψ).obj H)
    (ζ : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology (ψ.comp φ)).obj H)
    (hζ : ζ = η ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map θ ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app H) :
    SheafExactDegreeZero.scalarUnit T.smallEtaleTopology (ψ.comp φ) F H ζ =
      SheafExactDegreeZero.scalarUnit T.smallEtaleTopology φ F G η ≫
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
          (SheafExactDegreeZero.scalarUnit T.smallEtaleTopology ψ G H θ) ≫
        (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology (f := φ) (g := ψ) rfl).hom.app
          (SheafExactDegreeZero.scalarObj T.smallEtaleTopology C H) := by
  unfold SheafExactDegreeZero.scalarUnit SheafExactDegreeZero.scalarObj
  exact SheafExactDegreeZero.unit_comp
    (Sheaf.restrictScalars T.smallEtaleTopology ψ)
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (Sheaf.restrictScalars T.smallEtaleTopology (ψ.comp φ))
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology (f := φ) (g := ψ) rfl)
    rfl η θ ζ hζ


private theorem scalar_unit_cancel
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)
    (θ : G ⟶ (Sheaf.restrictScalars T.smallEtaleTopology ψ).obj H)
    (ζ : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology (ψ.comp φ)).obj H)
    (hζ : ζ = η ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map θ ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app H)
    (hη : SupportedDerivedScalarUnit φ T F G η)
    (hζu : SupportedDerivedScalarUnit (ψ.comp φ) T F H ζ) :
    SupportedDerivedScalarUnit ψ T G H θ := by
  unfold SupportedDerivedScalarUnit SheafExactDegreeZero.scalarUniversal at *
  exact universalArrow_cancel
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ)
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (ψ.comp φ))
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology rfl) _ _ hη (by
      rw [← derivedUnit_comp φ ψ T η θ ζ hζ]
      exact hζu)

private theorem constant_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    SupportedDerivedScalarUnit φ T (ordinaryFiniteConstant A T) (ordinaryFiniteConstant B T)
      (normalizedConstantMap φ T) :=
  (supported_kummer_scalar_derived_units T A B φ (𝟙 T)
    (normalizedConstantMap φ T) (normalizedConstantMap φ T)
    (normalizedConstantMap_apply φ T) (normalizedConstantMap_apply φ T)).2.2

private theorem normalizedLineMap_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (hC : (N : C) = 0) (T : Scheme.{u}) :
    normalizedLineMap (ψ.comp φ) N hA hC T = normalizedLineMap φ N hA hB T ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        (normalizedLineMap ψ N hB hC T) ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        (Scheme.finiteEtaleTateLine T N C hC) := by
  apply lineMap_ext
  intro W z
  change (normalizedLineMap (ψ.comp φ) N hA hC T).hom.app W
      (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
    (normalizedLineMap ψ N hB hC T).hom.app W
      ((normalizedLineMap φ N hA hB T).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z))
  rw [normalizedLineMap_apply, normalizedLineMap_apply, normalizedLineMap_apply]
  rfl

private theorem residueLineData (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hT : IsUnit (N : Γ(T, ⊤)))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    let R := p1KummerResidue.{u} N
    let hR : (N : R) = 0 := congrArg (ULift.up : ZMod N → R) (ZMod.natCast_self N)
    ∃ θ : Scheme.finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology (p1KummerResidueMap N A hA)).obj
        (Scheme.finiteEtaleTateLine T N A hA),
      (∀ (W : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf N).obj.obj W),
        θ.hom.app W (Scheme.finiteEtaleTateOneGenerator R N T hR W r z) =
          Scheme.finiteEtaleTateOneGenerator A N T hA W (p1KummerResidueMap N A hA r) z) ∧
      SupportedDerivedScalarUnit (p1KummerResidueMap N A hA) T
        (Scheme.finiteEtaleTateLine T N R hR) (Scheme.finiteEtaleTateLine T N A hA) θ := by
  let : NeZero N := ⟨hN.ne'⟩
  intro R hR
  obtain ⟨κ, hκ, _⟩ := supported_cartier_boundary_existsUnique T N hN A hA hT i hI
  obtain ⟨κR, hκR, _⟩ := supported_cartier_boundary_existsUnique T N hN R hR hT i hI
  have hs := supported_kummer_boundary_scalar T N hN A hA hT i hI κ hκ κR hκR
  unfold SupportedKummerScalar at hs
  obtain ⟨ηD, θ, _, hθ, _, hl, _⟩ := hs
  exact ⟨θ, hθ, hl⟩

private theorem derivedInsertion_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)
    (hη : SupportedDerivedScalarUnit φ T F G η) :
    IsIso (p1KummerDerivedInsertion φ T η) := by
  unfold p1KummerDerivedInsertion
  unfold SupportedDerivedScalarUnit at hη
  exact SheafExactDegreeZero.isIso_scalarAdjointInsertion T.smallEtaleTopology φ η hη

private def makeEndpoints
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hl : SupportedDerivedScalarUnit φ T (Scheme.finiteEtaleTateLine T N A hA)
      (Scheme.finiteEtaleTateLine T N B hB) (normalizedLineMap φ N hA hB T)) :
    P1KummerScalarEndpoints φ N hA hB T := by
  letI := derivedInsertion_isIso φ T (normalizedConstantMap φ T) (constant_unit φ T)
  letI := derivedInsertion_isIso φ T (normalizedLineMap φ N hA hB T) hl
  exact {
    unitInsertion := normalizedConstantMap φ T
    lineInsertion := normalizedLineMap φ N hA hB T
    unit_normalization := normalizedConstantMap_apply φ T
    line_normalization := normalizedLineMap_apply φ N hA hB T
    unitIso := asIso (p1KummerDerivedInsertion φ T (normalizedConstantMap φ T))
    lineIso := asIso (p1KummerDerivedInsertion φ T (normalizedLineMap φ N hA hB T))
    unit_derived := rfl
    line_derived := rfl }

private theorem residue_line_unit (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hT : IsUnit (N : Γ(T, ⊤)))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    let R := p1KummerResidue.{u} N
    let hR : (N : R) = 0 := congrArg (ULift.up : ZMod N → R) (ZMod.natCast_self N)
    SupportedDerivedScalarUnit (p1KummerResidueMap N A hA) T
      (Scheme.finiteEtaleTateLine T N R hR) (Scheme.finiteEtaleTateLine T N A hA)
      (normalizedLineMap (p1KummerResidueMap N A hA) N hR hA T) := by
  intro R hR
  have hI : (Scheme.emptyTo T).ker.IsInvertible := by
    rw [Scheme.ker_eq_top_of_isEmpty]
    exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨θ, hθ, hl⟩ := residueLineData T N hN hT A hA (Scheme.emptyTo T) hI
  have he : θ = normalizedLineMap (p1KummerResidueMap N A hA) N hR hA T := by
    apply lineMap_ext
    intro W z
    exact (hθ W 1 z).trans
      (normalizedLineMap_apply (p1KummerResidueMap N A hA) N hR hA T W 1 z).symm
  exact he ▸ hl

private theorem residueMap_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    φ.comp (p1KummerResidueMap N A hA) = p1KummerResidueMap N B hB := by
  have hz : (φ.comp (p1KummerResidueMap N A hA)).comp ULift.ringEquiv.symm.toRingHom =
      (p1KummerResidueMap N B hB).comp ULift.ringEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  ext r
  exact congrArg (fun f : ZMod N →+* B ↦ f r.down) hz


/-- The normalized unit and Tate-line scalar endpoints exist for finite coefficients.
Source: Stacks 03PK, 06YY and 0D6D; blueprint Charts, scalar Kummer comparison
(blueprint: lem-sp-p1-kummer-scalar-endpoint-existence).

Proof: construct the constant insertion by the constants/global-sections adjunction
and the Tate insertion by the root/Tate Hom equivalence. These maps have the displayed
coefficient formulas. The existing supported constant scalar-unit theorem, applied to
the identity immersion, gives the ambient constant universal property. Apply supported
Kummer boundary scalar compatibility to the empty Cartier divisor, whose ideal is top,
to obtain the residue-to-A ambient Tate universal property. The supported boundaries
needed for that application exist by the Cartier boundary existence theorem. The root
generator formula identifies the resulting insertion with the constructed one. The
residue map to B is the composite residue map through A. The Tate insertions compose,
as can be checked on their root generators, and cancellation of the residue-to-A
universal arrow gives the Tate universal property for A to B. The adjunction transpose
of each universal insertion is invertible. Apply asIso to these constructed arrows;
the ordinary and derived normalizations then fill the endpoint record. No arbitrary
object is chosen from an existence theorem. Zero coefficient rings and the empty
scheme are included by the same universal-property argument. -/
theorem p1KummerScalarEndpointExistence
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hT : IsUnit (N : Γ(T, ⊤)))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    Nonempty (P1KummerScalarEndpoints φ N hA hB T) := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let R := p1KummerResidue.{u} N
  let hR : (N : R) = 0 := congrArg (ULift.up : ZMod N → R) (ZMod.natCast_self N)
  let χ := p1KummerResidueMap N A hA
  have ha := residue_line_unit T N hN hT A hA
  have hb := residue_line_unit T N hN hT B hB
  rw [← residueMap_comp φ N hA hB] at hb
  have hl := scalar_unit_cancel χ φ T
    (normalizedLineMap χ N hR hA T) (normalizedLineMap φ N hA hB T)
    (normalizedLineMap (φ.comp χ) N hR hB T)
    (normalizedLineMap_comp χ φ N hR hA hB T) ha hb
  exact ⟨makeEndpoints φ T N hA hB hl⟩

end AlgebraicGeometry.Etale
