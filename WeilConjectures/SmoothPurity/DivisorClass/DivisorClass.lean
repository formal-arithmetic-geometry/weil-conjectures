/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerChernClass
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalEtale
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence

/-!
# Kummer class of a smooth Cartier divisor

Source: \`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-divisor-class.md\`
(blueprint: \`lem-pur-divisor-class\`).

This module states the Λ-level theorem in the purity conventions.  The deferred
proof follows the blueprint route: construct rank-one equation frames, glue the
frame classes, identify the local Kummer boundary with the Cartier class, do the
three-by-three boundary-sign computation, and use the support ladder and local
product equations for the two additivity assertions.

Clause (b) records the canonical Cartier comparison data explicitly.  Its finite Tate line is
constructed by the coefficient-extension map from the finite root-of-unity sheaf to the normalized
Tate sheaf, followed by the degree-zero single-functor comparison.  The `Ri_! ≅ Ri_*`
comparison on the degree-zero constant sheaf and the `Ri_! ⊣ Ri^!` mate are named in the
interface below.  Thus the comparison is independent of the divisor and is not obtained by
choosing an isomorphism from a mere `Nonempty` result.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures
namespace DivisorClass

/-- Forget support by the counit of \`Ri_! ⊣ Ri^!\`.

Source: \`WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedTensor.lean\`,
section \`Forget\` (blueprint: \`lem-pur-divisor-class\`). -/
abbrev forgetSupport {T D : Scheme.{u}} (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (i : D ⟶ T) [IsClosedImmersion i]
    {L : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : AlgebraicGeometry.Etale.constantComplex Λ T ⟶
      (AlgebraicGeometry.Etale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) i).obj
        ((AlgebraicGeometry.Etale.rightDerivedUpperShriek Λ i).obj L)) :=
  γ ≫ (AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction Λ i).counit.app L

/-- The supported target in codimension one. -/
abbrev supportedTarget {T D : Scheme.{u}} (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [AlgebraicGeometry.Etale.HasTateTwist Λ]
    (i : D ⟶ T) [IsClosedImmersion i] :
    DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (AlgebraicGeometry.Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ) i).obj
    ((AlgebraicGeometry.Etale.rightDerivedUpperShriek Λ i).obj
      ((AlgebraicGeometry.Etale.tateObject Λ T 1)⟦(2 : ℤ)⟧))

/-- A class with support on a closed divisor. -/
abbrev supportedHom {T D : Scheme.{u}} (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [AlgebraicGeometry.Etale.HasTateTwist Λ]
    (i : D ⟶ T) [IsClosedImmersion i] : Type (u + 1) :=
  AlgebraicGeometry.Etale.constantComplex Λ T ⟶ supportedTarget Λ i

/-- The supported morphism obtained from an ordinary Cartier Ext class.

The formula reads the Ext class `κ : Ext²(i_* Λ_D, μ_N ⊗ Λ)` as a derived morphism, precomposes
it with the canonical identification `Ri_! Λ_D ≅ Ri_* Λ_D ≅ i_* Λ_D` (proper `i`, degree-zero
single functor), transports the finite Tate line through `q`, and applies the `Ri_! ⊣ Ri^!`
hom-equivalence.  The inverse of the published
`supportedClassMap` bijection then gives a class with support.  Thus the output is constructed
from `κ`; it is not an existentially chosen negative of another class.

Source: `OrdinarySupportedKummerBoundary.lean`, `KummerClass.lean`, and the
coefficient-extension Tate-line comparison stated below (blueprint:
`lem-pur-divisor-class`). -/
noncomputable def canonicalCartierSupportedMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [AlgebraicGeometry.Etale.HasTateTwist Λ]
    (N : ℕ) (hN : (N : Λ) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (q : (DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine T N Λ hN) ≅
        AlgebraicGeometry.Etale.tateObject Λ T 1)
    (κ : Ext ((AlgebraicGeometry.Etale.lowerStar
        (ModuleCat.{u + 1} Λ) i).obj
        (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D))
        (Scheme.finiteEtaleTateLine T N Λ hN) 2) :
    supportedHom Λ i := by
  let L := (AlgebraicGeometry.Etale.tateObject Λ T 1)⟦(2 : ℤ)⟧
  let eShriek :=
    AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) i
  let lower := AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} Λ) i
  let eLower := eShriek.hom.app
      ((DerivedCategory.singleFunctor _ 0).obj
        (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D)) ≫
    lower.singleFunctorCompRightDerivedFunctorIso.hom.app
      (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D)
  let eκ := Abelian.Ext.homEquiv κ
  let hκ :
      (AlgebraicGeometry.Etale.rightDerivedLowerShriek
          (ModuleCat.{u + 1} Λ) i).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (AlgebraicGeometry.Etale.ordinaryFiniteConstant Λ D)) ⟶ L :=
    eLower ≫ eκ ≫ (CategoryTheory.shiftFunctor _ (2 : ℤ)).map q.hom
  let hD : AlgebraicGeometry.Etale.constantComplex Λ D ⟶
      (AlgebraicGeometry.Etale.rightDerivedUpperShriek Λ i).obj L :=
    (AlgebraicGeometry.Etale.constantComplexIsoSingleFunctor Λ D).hom ≫
      (AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction Λ i).homEquiv _ _ hκ
  let E := Equiv.ofBijective
    (AlgebraicGeometry.Etale.supportedClassMap Λ i (L := L))
    (AlgebraicGeometry.Etale.supportedClassMap_bijective Λ i L)
  exact E.symm hD

/-- The scalar-extension functor along `ℤ/N → Λ` agrees with forgetting to abelian groups
followed by `- ⊗_ℤ Λ`; the isomorphism is the uniqueness of left adjoints of restriction of
scalars, so on elements it is `m ⊗ λ ↦ m ⊗ λ`.

Source: `def-pur-affine-line-datum`, the coefficient extension `u ↦ u ⊗ 1_Λ` of the roots of
unity (blueprint: `lem-pur-divisor-class`, clause (b), coefficient extension). -/
noncomputable def canonicalZmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := Scheme.finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite Tate line `μ_N ⊗_{ℤ/N} Λ` is the étale sheaf `μ_N ⊗_ℤ Λ`, by the
scalar-extension identification above applied objectwise before sheafification.

Source: `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist` (`finiteEtaleTateLine`) and
`def-pur-affine-line-datum` (blueprint: `lem-pur-divisor-class`, clause (b), coefficient
extension). -/
noncomputable def canonicalFiniteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Scheme.finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N)
      (canonicalZmodScalarExtensionIso N A hA))

/-- The canonical coefficient-extension comparison from the finite root line to `Λ(1)`.

The first factor is the explicit scalar-extension identification of the published finite Tate
line with `μ_N ⊗ Λ`; the second is the canonical power-map identification of `μ_N ⊗ Λ` with the
normalized Tate sheaf; the last factor is the published degree-zero Tate-object comparison.  All
three factors depend only on `Λ`, `N`, and `T`, not on a divisor or on its ideal.  This is the
coefficient-extension map `u ↦ θ_T⁻¹ (u ⊗ 1)` required by `def-pur-affine-line-datum` and
`lem-amb-cartier-kummer-map`.

Source: `Sheaf.AlgebraicGeometry.FiniteEtaleTateLocalLine`,
`WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence`, and
`WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic` (blueprint:
`lem-pur-divisor-class`, clause (b)). -/
noncomputable def canonicalFiniteTateLineIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)]
    [AlgebraicGeometry.Etale.HasTateTwist.IsNormalized Λ]
    (N : ℕ) (hNpos : 0 < N) (hN : (N : Λ) = 0)
    {T : Scheme.{u}} (hT : IsUnit (N : Γ(T, ⊤))) :
    (DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine T N Λ hN) ≅
      AlgebraicGeometry.Etale.tateObject Λ T 1 :=
  letI : AlgebraicGeometry.HasInvertibleExponent Λ T :=
    ⟨N, hNpos, hN, hT⟩
  (DerivedCategory.singleFunctor _ 0).mapIso
      (canonicalFiniteEtaleLineAbIso T N Λ hN) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (AlgebraicGeometry.Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf
        Λ N hN hT) ≪≫
    (AlgebraicGeometry.Etale.tateTwistObjectIsoSingleFunctor Λ T 1).symm

/--
The canonical comparison interface for the Cartier class.

The predicate says that `cD` is the supported class `c_D` of `lem-amb-cartier-kummer-map`,
namely `canonicalCartierSupportedMap` applied to the normalized ordinary Cartier Ext class
`geoCartierEtaleClass` and to the coefficient-extension Tate-line comparison
`canonicalFiniteTateLineIso` (which depends only on `Λ`, `N`, `T`), and that `cD = -cl`.
No datum of the predicate is free.

Source: \`geoCartierEtaleClass\` of \`def-sfb-geo-cartier-canonical-etale\`, the
`Ri_! ⊣ Ri^!` mate and the `supportedClassMap` bijection of \`KummerClass.lean\`
(blueprint: \`lem-pur-divisor-class\`, clause (b)). -/
def canonicalCartierSupportedComparison
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)]
    [AlgebraicGeometry.Etale.HasTateTwist.IsNormalized Λ]
    (N : ℕ) (hNpos : 0 < N) (hN : (N : Λ) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    (cD cl : supportedHom Λ i) : Prop :=
  let q := canonicalFiniteTateLineIso Λ N hNpos hN hT
  let κ := AlgebraicGeometry.Etale.geoCartierEtaleClass Λ N hNpos hN i hI hT
  cD = canonicalCartierSupportedMap Λ N hN i q κ ∧
    cD = -cl

/-- The Kummer class of a smooth Cartier divisor, with clauses (a), (b), and
(c) of \`lem-pur-divisor-class\`.

Source: \`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-divisor-class.md\`
(blueprint: \`lem-pur-divisor-class\`).  The proof is deferred at stage 2.

The proof steps are, in order: (1) obtain rank-one equation frames from the
closed smooth pure-codimension-one pair; (2) glue their frame classes and use
frame independence; (3) identify a local equation with the Kummer boundary; (4)
compare the normalized Cartier witness through the \`Ri_! ≅ Ri_*\` comparison, the
\`Ri_! ⊣ Ri^!\` adjunction, and the Tate line; (5) compute the opposite Kummer/support
boundaries in the three-by-three diagram; (6) forget support and apply the dual-line
Chern identity; (7) use Kummer multiplication and the canonical support ladder for
arbitrary functions; and (8) use local product equations and gluing for the divisor
sum. -/
theorem divisor_frame_class
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)]
    [AlgebraicGeometry.Etale.HasTateTwist.IsNormalized Λ]
    (N : ℕ) (hNpos : 0 < N) (hN : (N : Λ) = 0)
    {B T D : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (v : T ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n v]
    (i : D ⟶ T) [IsClosedImmersion i] [Smooth (i ≫ v)]
    (hcodim : ∀ z : D, ringKrullDim (T.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞))
    (hT : IsUnit (N : Γ(T, ⊤))) :
    letI : AlgebraicGeometry.HasInvertibleExponent Λ T :=
      ⟨N, hNpos, hN, hT⟩
    ∃ (hI : i.ker.IsInvertible)
      (cl cD : supportedHom Λ i),
      letI := hI.isInvertible_toModules
      letI := hI.isInvertible_dual_toModules
      (∀ F : i.EtaleFrame 1,
        AlgebraicGeometry.Etale.frameRestriction Λ F cl =
          AlgebraicGeometry.Etale.frameClass Λ F) ∧
      (∀ F : i.EtaleFrame 1,
        AlgebraicGeometry.Etale.frameRestriction Λ F cl =
          AlgebraicGeometry.Etale.kummerBoundaryProduct Λ F.f) ∧
      (forgetSupport Λ i cl =
        AlgebraicGeometry.Etale.chernClass Λ T
          (Scheme.Pic.ofIsInvertible i.ker.toModules)) ∧
      (AlgebraicGeometry.Etale.chernClass Λ T
          (Scheme.Pic.ofIsInvertible i.ker.toModules) =
        -AlgebraicGeometry.Etale.chernClass Λ T
          (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules))) ∧
      canonicalCartierSupportedComparison Λ N hNpos hN i hI hT cD cl ∧
      (∀ F : i.EtaleFrame 1,
        AlgebraicGeometry.Etale.frameRestriction Λ F (-cl) =
          -AlgebraicGeometry.Etale.frameClass Λ F) ∧
      (∀ {U : Scheme.{u}} (e : U ⟶ T) [IsOpenImmersion e]
          (f₁ f₂ : Γ(U, ⊤)),
        letI : AlgebraicGeometry.HasInvertibleExponent Λ U :=
          AlgebraicGeometry.HasInvertibleExponent.of_hom e
        let i₁ := U.zeroLocusSubschemeι (Set.range (fun _ : Fin 1 => f₁))
        let i₂ := U.zeroLocusSubschemeι (Set.range (fun _ : Fin 1 => f₂))
        let i₁₂ := U.zeroLocusSubschemeι (Set.range (fun _ : Fin 1 => f₁ * f₂))
        ∀ (h₁₂ : Set.range i₁.base ⊆ Set.range i₁₂.base)
          (h₂₂ : Set.range i₂.base ⊆ Set.range i₁₂.base),
          AlgebraicGeometry.Etale.kummerBoundaryProduct Λ
              (fun _ : Fin 1 => f₁) ≫
              AlgebraicGeometry.Etale.supportedForget Λ i₁ i₁₂ h₁₂
                ((AlgebraicGeometry.Etale.tateObject Λ U 1)⟦(2 : ℤ)⟧) +
            AlgebraicGeometry.Etale.kummerBoundaryProduct Λ
              (fun _ : Fin 1 => f₂) ≫
              AlgebraicGeometry.Etale.supportedForget Λ i₂ i₁₂ h₂₂
                ((AlgebraicGeometry.Etale.tateObject Λ U 1)⟦(2 : ℤ)⟧) =
            AlgebraicGeometry.Etale.kummerBoundaryProduct Λ
              (fun _ : Fin 1 => f₁ * f₂)) ∧
      (∀ {D₁ D₂ S : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T)
          (s : S ⟶ T) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
          [IsClosedImmersion s] [Smooth (i₁ ≫ v)] [Smooth (i₂ ≫ v)]
          [Smooth (s ≫ v)]
          (hcodim₁ : ∀ z : D₁, ringKrullDim (T.presheaf.stalk (i₁ z)) =
            ringKrullDim (D₁.presheaf.stalk z) + (1 : WithBot ℕ∞))
          (hcodim₂ : ∀ z : D₂, ringKrullDim (T.presheaf.stalk (i₂ z)) =
            ringKrullDim (D₂.presheaf.stalk z) + (1 : WithBot ℕ∞))
          (hcodimₛ : ∀ z : S, ringKrullDim (T.presheaf.stalk (s z)) =
            ringKrullDim (S.presheaf.stalk z) + (1 : WithBot ℕ∞))
          (hs : s.ker = i₁.ker * i₂.ker),
        ∀ (c₁ : supportedHom Λ i₁) (c₂ : supportedHom Λ i₂)
          (cₛ : supportedHom Λ s),
          (∀ F : i₁.EtaleFrame 1,
            AlgebraicGeometry.Etale.frameRestriction Λ F c₁ =
              AlgebraicGeometry.Etale.frameClass Λ F) →
          (∀ F : i₂.EtaleFrame 1,
            AlgebraicGeometry.Etale.frameRestriction Λ F c₂ =
              AlgebraicGeometry.Etale.frameClass Λ F) →
          (∀ F : s.EtaleFrame 1,
            AlgebraicGeometry.Etale.frameRestriction Λ F cₛ =
              AlgebraicGeometry.Etale.frameClass Λ F) →
          ∀ (h₁ : Set.range i₁.base ⊆ Set.range s.base)
            (h₂ : Set.range i₂.base ⊆ Set.range s.base),
            cₛ = c₁ ≫ AlgebraicGeometry.Etale.supportedForget Λ i₁ s h₁
                ((AlgebraicGeometry.Etale.tateObject Λ T 1)⟦(2 : ℤ)⟧) +
              c₂ ≫ AlgebraicGeometry.Etale.supportedForget Λ i₂ s h₂
                ((AlgebraicGeometry.Etale.tateObject Λ T 1)⟦(2 : ℤ)⟧)) := by
  sorry

end DivisorClass
end WeilConjectures
