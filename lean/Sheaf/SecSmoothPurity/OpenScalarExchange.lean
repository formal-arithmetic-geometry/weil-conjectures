/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.ProjectionFormulaCompactified
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! Scalar extension respects the open base-change comparison.
Source: Stacks Project, Tag 03S6, label `lemma-shriek-base-change`, together with
Tags 07A4 and 09AE (blueprint: lem-fix-open-scalar-exchange).

All objects are in the constant-ring module coordinates `proEtaleConstantRing T A`
(`A` lifted to the site's coefficient universe) of def-weil-pbc-proetale-operations.
The open base-change map is the recorded `StrictTower.singleBeta` of
lem-cbc-proetale-extension-zero-base-change, at the lifted coefficient ring; its
constant coefficients, module pullback and open extension are definitionally the ones below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Derived scalar extension `S_T = - ⊗^L_{A_T} B_T` along a constant coefficient-ring map.
Source: Stacks Tag 06YY (blueprint: lem-pur-derived-change-of-rings). -/
noncomputable abbrev scalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)) :=
  Scheme.proEtaleRingDerivedExtension
    (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- Derived restriction of scalars `Res_T`, right adjoint to `scalarExtension`.
Source: Stacks Tag 07A6 (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable abbrev scalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) :=
  (Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The exact derived constant-coefficient inverse image `f_A^{-1}`.
Source: Stacks Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev constantPullback {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) :
    DerivedCategory (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) :=
  Scheme.proEtaleRingDerivedPullback f
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison f A)

/-- The exact derived extension by zero `j_!^A`, left adjoint to `j_A^{-1}`.
Source: Stacks Tags 03DI and 09AE (blueprint: lem-cbc-proetale-extension-zero). -/
noncomputable abbrev openExtension {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  Scheme.proEtaleRingDerivedOpenExtension j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)

/-- The canonical tensor/inverse-image comparison `λ_f : f_B^{-1} S_X ≅ S_U f_A^{-1}`,
the inverse of the mate of the restriction/pullback identification; on K-flat
representatives it is the balancing map.
Source: Stacks Tags 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def tensorPullbackIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (f : U ⟶ X) :
    scalarExtension φ X ⋙ constantPullback f ≅
      constantPullback f ⋙ scalarExtension φ U :=
  Scheme.proEtaleReductionPullbackIso f
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B)
    (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

/-- The scalar/open comparison `β_j : S_X j_!^A ≅ j_!^B S_U`, the unique isomorphism of
left adjoints whose right-adjoint comparison is the identification
`j_A^{-1} Res_X = Res_U j_B^{-1}` of lem-weil-pbc-ring-sheaf-change-adjunction.
Source: Stacks Tags 07A6 and 03DI (blueprint: lem-fix-open-scalar-exchange). -/
noncomputable def openScalarIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openExtension j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ openExtension j := by
  let adjA := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)
  let adjB := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X B) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingComparison j B)
  let adjX := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := X) φ)
  let adjU := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := U) φ)
  let rightIso := Scheme.proEtaleRingRestrictionDerivedPullback j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison j A)
    (Scheme.proEtaleConstantRingComparison j B) (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality j
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
  exact (adjA.comp adjX).leftAdjointUniq
    ((adjU.comp adjB).ofNatIsoRight rightIso)

/-- The actual open base-change map `e_j : g^{-1} j_! ≅ j'_! h^{-1}` of
lem-cbc-proetale-extension-zero-base-change, i.e. the recorded `StrictTower.singleBeta`
at the lifted coefficient ring; its inverse is the `j'_! ⊣ j'^{-1}` adjunct of `h^{-1} η_j`
followed by the cartesian inverse-image identification.
Source: Stacks Tags 03S6 and 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def openBaseChangeIso {A : Type u} [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j'] :
    openExtension (A := A) j ⋙ constantPullback (A := A) g ≅
      constantPullback (A := A) gU ⋙ openExtension (A := A) j' :=
  StrictTower.singleBeta (ULift.{u + 1, u} A) gU j' j g sq.toCommSq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

/-- Scalar extension respects the open base-change comparison, naturally in the input:
`j'_!(λ_{h,K}) ∘ e^B_{j,S_U K} ∘ g_B^{-1}(β_{j,K})
  = β_{j',h^{-1}K} ∘ S_{X'}(e^A_{j,K}) ∘ λ_{g,j_!K}`.
Source: Stacks Project, Tag 03S6, label `lemma-shriek-base-change`
(blueprint: lem-fix-open-scalar-exchange).
Proof: (1) `S_T ⊣ Res_T` and `j_! ⊣ j^{-1}`; the composite left adjoints `S_X j_!^A` and
`j_!^B S_U` have right adjoints identified by the restriction/pullback comparison, giving
`β_j`; transposing `β_j^{-1}` gives `δ_j = λ_j^{-1} ∘ S_U η_j^A`.
(2) On a flat-term K-flat representative both paths send `(gj')^{-1}p ⊗ b` to
`(gj')^{-1}(p ⊗ b)`, so `J'_B λ_g^{-1} ∘ λ_{j'}^{-1} G_A = H_B λ_j^{-1} ∘ λ_h^{-1} J_A` (C).
(3) Invert both sides: `L^{-1}` and `R^{-1}` start at an open extension; by the
inverse-mate normalization of `e_j` (lem-cbc-finite-open-exchange-scalars) the
`j'_! ⊣ j'^{-1}` transpose of `L^{-1}` is `H_B(δ_{j,K}) ∘ λ_{h,K}^{-1}`.
(4) The transpose of `R^{-1}` is `J'_B(λ_{g,N}^{-1}) ∘ λ_{j',G_A N}^{-1} ∘ S_{U'} H_A(η^A_{j,K})`
by naturality of `λ_{j'}` and the same normalization.
(5) Apply (C) at `N = j_!K` and naturality of `λ_h^{-1}` on `η_{j,K}`: the transposes agree,
so `L^{-1} = R^{-1}` and `L = R`. -/
theorem openScalarExchange
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (K : DerivedCategory (Scheme.proEtaleRingModules U
      (Scheme.proEtaleConstantRing U A))) :
    (constantPullback g).map ((openScalarIso φ j).hom.app K) ≫
      (openBaseChangeIso gU j' j g sq).hom.app ((scalarExtension φ U).obj K) ≫
      (openExtension j').map ((tensorPullbackIso φ gU).hom.app K) =
    (tensorPullbackIso φ g).hom.app ((openExtension j).obj K) ≫
      (scalarExtension φ X').map ((openBaseChangeIso gU j' j g sq).hom.app K) ≫
      (openScalarIso φ j').hom.app ((constantPullback gU).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
