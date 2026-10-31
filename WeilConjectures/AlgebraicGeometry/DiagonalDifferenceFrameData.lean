/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.ReesConeNormalization
public import WeilConjectures.AlgebraicGeometry.ReesConeNormalizedExistence
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.PurityDncFamilyIntrinsic
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Coordinate differences and the homogeneous normal frame

Source: current blueprint, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Steps 1--3; sk-thm-dnc, Local construction;
Stacks Tags 0630--0635 and 08S2.
(blueprint: def-pur-diagonal-difference-frame-data).

The structures only spell out the witnesses and equations in the statement. In particular,
the conormal algebra, its symmetric comparison, its relative spectrum and the extended-Rees
space are the published constructions. The deformation over a centred open is represented
by the inverse image of that open in the extended-Rees space; this uses its actual gluing
charts and is the restriction description of the same relative spectrum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

/-- The normalized conormal and homogeneous frame for the specified ordered functions.
The equation on all `a` fixes the positive difference sign. The normal coordinates are
functions obtained from the degree-one inclusions by the relative-Spec counit, so no
arbitrary zero-preserving cone isomorphism is substituted.
Source: chart proof, Step 2; Stacks 0632, 08S2
(blueprint: lem-pur-diagonal-difference-rees-frame). -/
structure NormalFrame {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    (x : ULift.{u} (Fin d) → Γ(U, ⊤)) where
  symmetric : IsIso (ConormalGradedAlgebra.symmetricComparison (pullback.diagonal h))
  conormal : ConormalGradedAlgebra.piece (pullback.diagonal h) 1 ≅ h.relativeDifferentials
  sign : ∀ a : Γ(U, ⊤),
    ∃ b : (ConormalGradedAlgebra.power (pullback.diagonal h) 1).val.obj (op ⊤),
      (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val.app (op ⊤) b =
          (pullback.snd h h).appTop a - (pullback.fst h h).appTop a ∧
      conormal.hom.val.app (op ((pullback.diagonal h) ⁻¹ᵁ ⊤))
          (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
        h.relativeDifferentials.val.map (homOfLE le_top).op
          (h.relativeDifferentialsDerivation.d (X := op ⊤) a)
  differentialFrame : SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin d)) ≅
    h.relativeDifferentials
  differentialFrame_value : ∀ i : ULift.{u} (Fin d),
    differentialFrame.hom.val.app (op ⊤)
        ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (op ⊤)
          (1 : U.ringCatSheaf.obj.obj (op ⊤))) =
      h.relativeDifferentialsDerivation.d (X := op ⊤) (x i)
  normal : PurityNormalBundle.normalCone (pullback.diagonal h) ≅
    AffineSpace (ULift.{u} (Fin d)) U
  normal_over : normal.hom ≫ (AffineSpace (ULift.{u} (Fin d)) U ↘ U) =
    PurityNormalBundle.projection (pullback.diagonal h)
  normal_zero : PurityNormalBundle.zeroSection (pullback.diagonal h) ≫ normal.hom =
    AffineSpace.zeroSection (ULift.{u} (Fin d)) U
  normal_coordinate : ∀ (T : U.Opens) (i : ULift.{u} (Fin d)),
    normal.hom.appLE ⊤ (PurityNormalBundle.projection (pullback.diagonal h) ⁻¹ᵁ T)
        (by simp) (AffineSpace.coord U i) =
      (coneAlgebraIso (pullback.diagonal h)).hom.right.hom.app (op T)
        (((ConormalGradedAlgebra.presentation (pullback.diagonal h)).inclusion 1).val.app
          (op T) ((differentialFrame ≪≫ conormal.symm).hom.val.app (op T)
            ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (op T)
              (1 : U.ringCatSheaf.obj.obj (op T)))))
  comparison_independent : ∀ q q' : (pullback.diagonal h).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal h),
    ReesConeNormalized (pullback.diagonal h) q →
    ReesConeNormalized (pullback.diagonal h) q' → q.hom ≫ normal.hom = q'.hom ≫ normal.hom
  rank_zero_conormal : d = 0 → IsZero (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)
  rank_zero_symmetric : d = 0 →
    Nonempty (SymmetricAlgebraSheaf.algebra
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅ Under.mk (𝟙 U.sheaf))

/-- The centred zero square and the actual Rees-coordinate map on the centred open.
`deformation` has domain the restriction of the published extended-Rees space to `O`.
Its charts send t to t and v_i to (y_i-x_i)/t; the endpoint equations use the actual
one-fibre and zero-fibre inclusions. Every normalized comparison is quantified over.
Source: chart proof, Steps 1 and 3; sk-thm-dnc, Local construction
(blueprint: lem-pur-diagonal-difference-rees-frame). -/
structure CentredChart {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    (x : ULift.{u} (Fin d) → Γ(U, ⊤)) (N : NormalFrame d h x) where
  O : (pullback h h).Opens
  s : U ⟶ O.toScheme
  section_diagonal : s ≫ O.ι = pullback.diagonal h
  etale : Etale (O.ι ≫ AffineSpace.homOfVector (pullback.fst h h)
    (fun i ↦ (pullback.snd h h).appTop (x i) - (pullback.fst h h).appTop (x i)))
  zero_square : IsPullback s (𝟙 U)
    (O.ι ≫ AffineSpace.homOfVector (pullback.fst h h)
      (fun i ↦ (pullback.snd h h).appTop (x i) - (pullback.fst h h).appTop (x i)))
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) U)
  deformation : ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).toScheme ⟶
    AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) U)
  deformation_model : s.ker.deformationSpace ≅
    ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).toScheme
  model_ambient : deformation_model.hom ≫
      ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).ι ≫
        (pullback.diagonal h).ker.deformationSpaceProj = s.ker.deformationSpaceProj ≫ O.ι
  model_parameter : deformation_model.hom ≫
      ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).ι ≫
        Scheme.Hom.deformationSpaceProj (pullback.fst h h) (pullback.diagonal h) =
    Scheme.Hom.deformationSpaceProj (O.ι ≫ pullback.fst h h) s
  deformation_etale : Etale deformation
  deformation_over : deformation ≫
      (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) U) ↘
        AffineSpace (ULift.{u} (Fin 1)) U) =
    ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).ι ≫
      Scheme.Hom.deformationSpaceProj (pullback.fst h h) (pullback.diagonal h)
  one : O.toScheme ⟶ ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).toScheme
  one_inclusion : one ≫ ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).ι =
    O.ι ≫ Scheme.Hom.deformationSpaceOneFibre (pullback.fst h h) (pullback.diagonal h)
  one_endpoint : one ≫ deformation =
    O.ι ≫ AffineSpace.homOfVector (pullback.fst h h)
      (fun i ↦ (pullback.snd h h).appTop (x i) - (pullback.fst h h).appTop (x i)) ≫
        AffineSpace.map (ULift.{u} (Fin d))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) U)
  zero : (pullback.diagonal h).ker.normalCone ⟶
    ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).toScheme
  zero_inclusion : zero ≫ ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).ι =
    (pullback.diagonal h).ker.normalConeToDeformationSpace
  zero_endpoint : ∀ q : (pullback.diagonal h).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal h),
    ReesConeNormalized (pullback.diagonal h) q →
      zero ≫ deformation = q.hom ≫ N.normal.hom ≫
        AffineSpace.map (ULift.{u} (Fin d))
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) U)
  charts : ∀ A : (pullback h h).AffineZariskiSite, A.1 ≤ O →
    ∃ j : Spec ((pullback.diagonal h).ker.reesPresheaf.obj (op A)) ⟶
        ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).toScheme,
      j ≫ ((pullback.diagonal h).ker.deformationSpaceProj ⁻¹ᵁ O).ι =
        colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
          (pullback.diagonal h).ker.coequifibered_toReesPresheaf).functor A ∧
      (j ≫ deformation ≫
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) U) ↘
          AffineSpace (ULift.{u} (Fin 1)) U)).appTop
            (AffineSpace.coord U (ULift.up (0 : Fin 1))) =
        (Scheme.ΓSpecIso ((pullback.diagonal h).ker.reesPresheaf.obj (op A))).inv
          (Ideal.extendedReesAlgebraT _) ∧
      ∀ i : ULift.{u} (Fin d),
        ∃ hi : (pullback h h).presheaf.map (homOfLE le_top).op
            ((pullback.snd h h).appTop (x i) - (pullback.fst h h).appTop (x i)) ∈
              (pullback.diagonal h).ker.siteIdeal A,
          (j ≫ deformation).appTop
              (AffineSpace.coord (AffineSpace (ULift.{u} (Fin 1)) U) i) =
            (Scheme.ΓSpecIso ((pullback.diagonal h).ker.reesPresheaf.obj (op A))).inv
              ⟨LaurentPolynomial.C ((pullback h h).presheaf.map (homOfLE le_top).op
                  ((pullback.snd h h).appTop (x i) - (pullback.fst h h).appTop (x i))) *
                LaurentPolynomial.T (-1), Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra hi⟩
  rank_zero : d = 0 → IsIso s
  rank_zero_deformation : d = 0 → IsIso deformation

/-- The same coordinate map with domain literally the deformation of the restricted
closed section. The model is the restriction isomorphism over the ambient scheme and
parameter; on Rees charts these two conditions fix every Laurent representative.
Source: sk-thm-dnc, Local construction and open restriction
(blueprint: lem-pur-diagonal-difference-rees-frame). -/
def CentredChart.map {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V} [IsSeparated h]
    {x : ULift.{u} (Fin d) → Γ(U, ⊤)} {N : NormalFrame d h x}
    (C : CentredChart d h x N) : C.s.ker.deformationSpace ⟶
      AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) U) :=
  C.deformation_model.hom ≫ C.deformation

end AlgebraicGeometry.DiagonalDifferenceReesFrame
