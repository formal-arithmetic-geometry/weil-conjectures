/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DncSectionFamilyOver
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DncSectionInvariantStatement

/-!
# The canonical fibre maps of the deformation family over a general purity base field

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc).

Additive general version of the base-change / theta / eta block of
`Sheaf.SmoothPurity.DncSectionInvariantStatement`. The base is any
`K : PurityBaseField ell`; the coefficient is any `Λ` with
`IsLocalizingAdmissibleCoefficient ell Λ`. Bodies are those of the existing module with
`D.k` replaced by `K.K`, `sectionInvariant D ell hell (bottomField ell) n hn Λ (Or.inl hcoeff)`
replaced by `sectionInvariantOver ell K Λ ha`, and the derived cohomological-dimension proof
replaced by `purityBaseField_cd ell K`. The field-general `dncCompactSupportExchange`,
`dncOneBaseIso`, `dncZeroBaseIso` are reused. The pulled-pair block of the existing module is
not copied.

## Main declarations
* `dncDualizingBaseChangeMapOver`, `dncSectionBaseChangeMapOver`: the native mates.
* `dncCanonicalThetaOver`, `dncCanonicalEtaOver`: the canonical fibre isomorphisms at `t = 1`
  and `t = 0`.
* `*_geometric`: the existing declarations are the case `K = PurityBaseField.ofDatum D ell hell`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite-type schemes over a field are Noetherian; used only for unit membership.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 1 (blueprint: sk-thm-dnc). -/
local instance dncBaseNoetherianOver {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom

section BaseChange

variable (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
  {B V B' V' : Over (Spec (.of K.K))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
  [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (g' : V' ⟶ B') [Smooth g'.left] [IsSeparated g'.left]
  [LocallyOfFiniteType g'.left] [QuasiCompact g'.left]
  (b : B' ⟶ B) (v : V' ⟶ V)
  (sq : IsPullback v.left g'.left g.left b.left)

/-- Native compact-support exchange is invertible on Dctf over a general purity base field.
Statement copied from `dncCompactSupportExchange_isIso` with `D.k ↦ K.K` and the coefficient
`A_{Q_ell,n}` replaced by an admissible `Λ`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof steps 3 and 12 (blueprint: sk-thm-dnc).
Proof (postponed): as `dncCompactSupportExchange_isIso`; transport the proper/open mate to the
finite etale-origin formalism, where proper base change and exact open extension make it
invertible, then use dense-refinement normalization. For a non-torsion admissible `Λ` pass
through the localizing closure, on which both sides are exact and commute with the defining
colimits. -/
theorem dncCompactSupportExchangeOver_isIso :
    ∀ F : ConstantModelConstructibleFiniteTor Λ V.left,
      IsIso (dncCompactSupportExchange Λ ell K.K (purityBaseField_cd ell K) ha
        g g' b v sq F) := by
  sorry

/-- The smooth dualizing base-change mate over a general purity base field: the transpose,
under the pulled pair's exceptional adjunction, of inverse compact-support exchange followed by
the pullback of the original counit and the pullback-unit comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 3, using thm-pur-cohomological-smoothness (3) (blueprint: sk-thm-dnc). -/
def dncDualizingBaseChangeMapOver :
    let hcd := purityBaseField_cd ell K
    let U : ConstantModelConstructibleFiniteTor Λ B.left :=
      ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B.left⟩
    let U' : ConstantModelConstructibleFiniteTor Λ B'.left :=
      ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B'.left⟩
    (moduleObjectDerivedPullback Λ v.left).obj
      ((ctfExceptionalInverseImage Λ ell K.K hcd g ha).obj U).obj ⟶
      ((ctfExceptionalInverseImage Λ ell K.K hcd g' ha).obj U').obj := by
  let hcd := purityBaseField_cd ell K
  let U : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B.left⟩
  let U' : ConstantModelConstructibleFiniteTor Λ B'.left :=
    ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B'.left⟩
  let F := (ctfExceptionalInverseImage Λ ell K.K hcd g ha).obj U
  let F' : ConstantModelConstructibleFiniteTor Λ V'.left :=
    ⟨(moduleObjectDerivedPullback Λ v.left).obj F.obj,
      (condensedCtfSixFunctorStability Λ ell K.K hcd v ha).1 F⟩
  let bc := dncCompactSupportExchange Λ ell K.K hcd ha g g' b v sq F
  letI : IsIso bc := dncCompactSupportExchangeOver_isIso ell K Λ ha g g' b v sq F
  let ε := (ctfExceptionalAdjunction Λ ell K.K hcd g ha).counit.app U
  let e : (ctfLowerShriek Λ ell K.K hcd g' ha).obj F' ⟶ U' :=
    ObjectProperty.homMk (inv bc ≫
      (moduleObjectDerivedPullback Λ b.left).map ε.hom ≫
      (leftDerivedUpperStarUnitIso Λ b.left).hom)
  exact ((ctfExceptionalAdjunction Λ ell K.K hcd g' ha).homEquiv F' U' e).hom

/-- Base change of a general section invariant, with literal pullback composition. The first
two factors identify `Lb^* Ls^*` with `Ls'^* Lv^*` using the equation of sections; the last is
`Ls'^*` applied to `dncDualizingBaseChangeMapOver`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof steps 3 and 12, using sk-lem-geometry (1) (blueprint: sk-thm-dnc). -/
def dncSectionBaseChangeMapOver
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (s' : B' ⟶ V') [IsClosedImmersion s'.left] (hs' : s' ≫ g' = 𝟙 B')
    (w : b.left ≫ s.left = s'.left ≫ v.left) :
    (moduleObjectDerivedPullback Λ b.left).obj
      (sectionInvariantOver ell K Λ ha B V g s hs) ⟶
      sectionInvariantOver ell K Λ ha B' V' g' s' hs' := by
  let hcd := purityBaseField_cd ell K
  let U : ConstantModelConstructibleFiniteTor Λ B.left :=
    ⟨𝟙_ _, condensedCoefficientUnit_mem Λ B.left⟩
  let F := ((ctfExceptionalInverseImage Λ ell K.K hcd g ha).obj U).obj
  exact ((leftDerivedUpperStarComp Λ b.left s.left).app F).inv ≫
    (eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj F) w)).hom ≫
    ((leftDerivedUpperStarComp Λ s'.left v.left).app F).hom ≫
    (moduleObjectDerivedPullback Λ s'.left).map
      (dncDualizingBaseChangeMapOver ell K Λ ha g g' (b := b) (v := v) (sq := sq))

end BaseChange

section Fibres

variable (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
  (B V : Over (Spec (.of K.K)))
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
  [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (s : B ⟶ V) [IsClosedImmersion s.left]
  (hs : s ≫ g = 𝟙 B)

/-- The canonical one-fibre composite over a general purity base field: the native section
base-change map for the Cartesian square at `i₁`
(`Scheme.Hom.isPullback_deformationSpaceOneFibre`). Its source and target are the actual
condensed objects; only invertibility is postponed.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc). -/
def dncCanonicalThetaCompositeOver :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamilyOver K B V g s Λ ha d hs) ⟶
      sectionInvariantOver ell K Λ ha B V g s hs := by
  let H := condensedDncDomainOver K B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  let sq := Scheme.Hom.isPullback_deformationSpaceOneFibre g.left s.left
  let b : B ⟶ condensedDncBaseOver K B := Over.homMk
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left) (by
      change AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left ≫
        ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) = B.hom
      rw [← Category.assoc, AffineSpace.oneSection_comp_over, Category.id_comp])
  let v : V ⟶ condensedDncSourceOver K B V g s := Over.homMk
    (Scheme.Hom.deformationSpaceOneFibre g.left s.left) (by
      change Scheme.Hom.deformationSpaceOneFibre g.left s.left ≫
        (Scheme.Hom.deformationSpaceProj g.left s.left ≫
          ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)) = V.hom
      calc
        _ = g.left ≫ ((AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left ≫
            (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) ≫ B.hom) := by
          rw [← Category.assoc, sq.w]
          simp only [Category.assoc]
        _ = V.hom := by
          rw [AffineSpace.oneSection_comp_over, Category.id_comp, g.w])
  exact dncSectionBaseChangeMapOver ell K Λ ha
    (condensedDncMapOver K B V g s) g b v sq
    (condensedDncSectionOver K B V g s hs) H.2.2.2.2.2.2.2.2.2.2.2 s hs
    (Scheme.Hom.comp_deformationSpaceOneFibre
      (congrArg (fun f ↦ f.left) hs)).symm

/-- The underlying one-fibre map over a general purity base field.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 3 (blueprint: sk-thm-dnc). -/
def dncCanonicalThetaMapOver :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamilyOver K B V g s Λ ha d hs) ⟶
      sectionInvariantOver ell K Λ ha B V g s hs :=
  dncCanonicalThetaCompositeOver ell K Λ ha B V d g s hs

/-- The general one-fibre map is invertible.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc).
Proof (postponed): as `dncCanonicalThetaMap_isIso`. The one-fibre square is Cartesian; the
smooth dualizing base-change mate is invertible by thm-pur-cohomological-smoothness (3); pull it
back along the section; the remaining factors are pullback composition isomorphisms. -/
theorem dncCanonicalThetaMapOver_isIso :
    IsIso (dncCanonicalThetaMapOver ell K Λ ha B V d g s hs) := by
  sorry

/-- The canonical one-fibre isomorphism `θ` over a general purity base field: `asIso` of
`dncCanonicalThetaMapOver` with the postponed invertibility proof.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc). -/
def dncCanonicalThetaOver :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamilyOver K B V g s Λ ha d hs) ≅
      sectionInvariantOver ell K Λ ha B V g s hs := by
  letI : IsIso (dncCanonicalThetaMapOver ell K Λ ha B V d g s hs) :=
    dncCanonicalThetaMapOver_isIso ell K Λ ha B V d g s hs
  exact asIso (dncCanonicalThetaMapOver ell K Λ ha B V d g s hs)

/-- The canonical zero-fibre composite over a general purity base field: the native section
base-change map for the Cartesian normal-cone square
`isPullback_normalConeToDeformationSpace`. The target is the actual normal-cone invariant;
only invertibility is postponed.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc). -/
def dncCanonicalEtaCompositeOver :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamilyOver K B V g s Λ ha d hs) ⟶
      dncNormalSectionInvariantOver ell K Λ ha B V d g s hs := by
  letI : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f => f.left) hs
  have hf := dncNormalGeometryFactsOver K d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) := hf.1
  letI : Smooth (Scheme.Hom.normalConeProj g.left s.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) := hf.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.2
  letI : IsSeparated ((dncNormalBundleOver K g s).hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalBundleOver K g s).hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalBundleOver K g s).hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSectionOver K g s hs).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection s.left)
    infer_instance
  letI : Smooth (dncNormalProjectionOver K g s).left := by
    change Smooth (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsSeparated (dncNormalProjectionOver K g s).left := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjectionOver K g s).left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjectionOver K g s).left := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  let H := condensedDncDomainOver K B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  let sq := Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left
  let b : B ⟶ condensedDncBaseOver K B := Over.homMk
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left) (by
      change AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left ≫
        ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) = B.hom
      rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp])
  let v : dncNormalBundleOver K g s ⟶ condensedDncSourceOver K B V g s := Over.homMk
    s.left.ker.normalConeToDeformationSpace (by
      change s.left.ker.normalConeToDeformationSpace ≫
        (Scheme.Hom.deformationSpaceProj g.left s.left ≫
          ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)) =
        Scheme.Hom.normalConeProj g.left s.left ≫ B.hom
      calc
        _ = Scheme.Hom.normalConeProj g.left s.left ≫
            ((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left ≫
              (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) ≫ B.hom) := by
          rw [← Category.assoc, sq.w]
          simp only [Category.assoc]
        _ = _ := by rw [AffineSpace.zeroSection_comp_over, Category.id_comp])
  exact dncSectionBaseChangeMapOver ell K Λ ha
    (condensedDncMapOver K B V g s) (dncNormalProjectionOver K g s) b v sq
    (condensedDncSectionOver K B V g s hs) H.2.2.2.2.2.2.2.2.2.2.2
    (dncNormalSectionOver K g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)
    (Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace (s := s.left)).symm

/-- The underlying zero-fibre map over a general purity base field.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 3 (blueprint: sk-thm-dnc). -/
def dncCanonicalEtaMapOver :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamilyOver K B V g s Λ ha d hs) ⟶
      dncNormalSectionInvariantOver ell K Λ ha B V d g s hs :=
  dncCanonicalEtaCompositeOver ell K Λ ha B V d g s hs

/-- The general zero-fibre map is invertible.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 3 (blueprint: sk-thm-dnc).
Proof (postponed): as `dncCanonicalEtaMap_isIso`. Apply smooth dualizing base change to the
Cartesian zero-fibre square `isPullback_normalConeToDeformationSpace` and pull back along its
zero section; the section equation identifies the two pullback composites. -/
theorem dncCanonicalEtaMapOver_isIso :
    IsIso (dncCanonicalEtaMapOver ell K Λ ha B V d g s hs) := by
  sorry

/-- The canonical zero-fibre isomorphism `η` over a general purity base field: `asIso` of
`dncCanonicalEtaMapOver` with the postponed invertibility proof.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc). -/
def dncCanonicalEtaOver :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).obj
      (condensedDncFamilyOver K B V g s Λ ha d hs) ≅
      dncNormalSectionInvariantOver ell K Λ ha B V d g s hs := by
  letI : IsIso (dncCanonicalEtaMapOver ell K Λ ha B V d g s hs) :=
    dncCanonicalEtaMapOver_isIso ell K Λ ha B V d g s hs
  exact asIso (dncCanonicalEtaMapOver ell K Λ ha B V d g s hs)

end Fibres

section PulledPair

/-- A pulled section pair over the fibre product V times_B B'.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
structure DncPulledPairOver
    {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B B' V : Over (Spec (.of K.K))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B) where
  V' : Over (Spec (.of K.K))
  g' : V' ⟶ B'
  s' : B' ⟶ V'

/-- The canonical lift of the pulled-back section through the fibre product.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
noncomputable def dncPullbackLiftOver
    {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B B' V : Over (Spec (.of K.K))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) : B'.left ⟶ pullback g.left b.left :=
  pullback.lift (b.left ≫ s.left) (𝟙 B'.left) (by
    calc
      (b.left ≫ s.left) ≫ g.left = b.left ≫ (s.left ≫ g.left) := Category.assoc _ _ _
      _ = b.left ≫ 𝟙 B.left := congrArg (fun f => b.left ≫ f) (congrArg (fun f => f.left) hs)
      _ = 𝟙 B'.left ≫ b.left := by simp)

/-- The actual pullback pair used for arbitrary base change.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairOver
    {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B B' V : Over (Spec (.of K.K))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) : DncPulledPairOver K g s b where
  V' := Over.mk (pullback.fst g.left b.left ≫ V.hom)
  g' := Over.homMk (pullback.snd g.left b.left) (by
    change pullback.snd g.left b.left ≫ B'.hom =
      pullback.fst g.left b.left ≫ V.hom
    rw [← g.w, ← Category.assoc, pullback.condition, Category.assoc, b.w])
  s' := Over.homMk (dncPullbackLiftOver K g s b hs) (by
    change dncPullbackLiftOver K g s b hs ≫
      (pullback.fst g.left b.left ≫ V.hom) = B'.hom
    rw [dncPullbackLiftOver, ← Category.assoc, pullback.lift_fst, Category.assoc, s.w, b.w])

/-- The pulled section is a section of the pulled morphism.

Proof: expand `dncPulledPairOver` and `dncPullbackLiftOver`; use `pullback.lift_snd`,
`pullback.lift_fst`, the original equation `hs`, and extensionality in `Over` to
obtain the displayed retraction.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`.
(blueprint: sk-thm-dnc). -/
theorem dncPulledPairOver_section_retraction
    {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B B' V : Over (Spec (.of K.K))}
    (g : V ⟶ B) (s : B ⟶ V) (b : B' ⟶ B)
    (hs : s ≫ g = 𝟙 B) :
    (dncPulledPairOver K g s b hs).s' ≫ (dncPulledPairOver K g s b hs).g' = 𝟙 B' := by
  apply Over.OverMorphism.ext
  change dncPullbackLiftOver K g s b hs ≫ pullback.snd g.left b.left = 𝟙 B'.left
  exact pullback.lift_snd _ _ _

/-- The canonical pullback pair inherits the geometric hypotheses needed by the
recorded DNC and section-invariant definitions.  The conclusion refers to the
actual `dncPulledPairOver`, so no arbitrary record can provide these instances.

Proof: apply smooth and closed-immersion base change to the displayed fibre
product and use `dncPulledPairOver_section_retraction`.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
proof step 1 (blueprint: sk-thm-dnc). -/
theorem dncPulledPairGeometryFactsOver
    {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    SmoothOfRelativeDimension d (dncPulledPairOver K g s b hs).g'.left ∧
    IsSeparated (dncPulledPairOver K g s b hs).g'.left ∧
    LocallyOfFiniteType (dncPulledPairOver K g s b hs).g'.left ∧
    QuasiCompact (dncPulledPairOver K g s b hs).g'.left ∧
    IsSeparated (dncPulledPairOver K g s b hs).V'.hom ∧
    LocallyOfFiniteType (dncPulledPairOver K g s b hs).V'.hom ∧
    QuasiCompact (dncPulledPairOver K g s b hs).V'.hom ∧
    IsClosedImmersion (dncPulledPairOver K g s b hs).s'.left := by
  change SmoothOfRelativeDimension d (pullback.snd g.left b.left) ∧
    IsSeparated (pullback.snd g.left b.left) ∧
    LocallyOfFiniteType (pullback.snd g.left b.left) ∧
    QuasiCompact (pullback.snd g.left b.left) ∧
    IsSeparated (pullback.fst g.left b.left ≫ V.hom) ∧
    LocallyOfFiniteType (pullback.fst g.left b.left ≫ V.hom) ∧
    QuasiCompact (pullback.fst g.left b.left ≫ V.hom) ∧
    IsClosedImmersion (dncPullbackLiftOver K g s b hs)
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have hdim : SmoothOfRelativeDimension d (pullback.snd g.left b.left) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_hasPullback g.left b.left) inferInstance
  have w : pullback.fst g.left b.left ≫ V.hom =
      pullback.snd g.left b.left ≫ B'.hom := by
    rw [← g.w, ← Category.assoc, pullback.condition, Category.assoc, b.w]
  have hsec : IsClosedImmersion
      (dncPullbackLiftOver K g s b hs ≫ pullback.snd g.left b.left) := by
    rw [dncPullbackLiftOver, pullback.lift_snd]
    infer_instance
  refine ⟨hdim, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_,
    IsClosedImmersion.of_comp _ (pullback.snd g.left b.left)⟩
  all_goals rw [w]; infer_instance

/-- The actual DNC family attached to the canonical pulled pair, using its own
Rees construction and section invariant.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-dnc-section-family (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairFamilyOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    let pair := dncPulledPairOver K g s b hs
    let H := dncPulledPairGeometryFactsOver K d g s hs b
    letI := H.1
    letI := SmoothOfRelativeDimension.smooth d pair.g'.left
    letI := H.2.1
    letI := H.2.2.1
    letI := H.2.2.2.1
    letI := H.2.2.2.2.1
    letI := H.2.2.2.2.2.1
    letI := H.2.2.2.2.2.2.1
    letI := H.2.2.2.2.2.2.2
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (condensedDncBaseOver K B').left) Ab.{u + 1})
      (condensedRingObj Λ (condensedDncBaseOver K B').left)) := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact condensedDncFamilyOver K B' pair.V' pair.g' pair.s' Λ ha d hpair

/-- The section invariant of the pulled pair, with the actual pulled section.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairSectionInvariantOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
      (condensedRingObj Λ B'.left)) := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact sectionInvariantOver ell K Λ ha B' pair.V' pair.g' pair.s' hpair

/-- The actual normal-cone invariant for the pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-normal-bundle (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairNormalInvariantOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
      (condensedRingObj Λ B'.left)) := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncNormalSectionInvariantOver ell K Λ ha B' pair.V' d pair.g' pair.s' hpair

/-- The named one-fibre comparison of the actual pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairThetaOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B'.left)).obj
      (dncPulledPairFamilyOver ell K Λ ha d g s hs b) ≅
      dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncCanonicalThetaOver ell K Λ ha B' pair.V' d pair.g' pair.s' hpair

/-- The named zero-fibre comparison of the actual pulled pair.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairEtaOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B'.left)).obj
      (dncPulledPairFamilyOver ell K Λ ha d g s hs b) ⟶
      dncPulledPairNormalInvariantOver ell K Λ ha d g s hs b := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  exact dncCanonicalEtaMapOver ell K Λ ha B' pair.V' d pair.g' pair.s' hpair

/-- The isomorphism underlying the pulled pair's zero-fibre comparison.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md`,
def-pur-section-invariant (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledPairEtaIsoOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B'.left)).obj
      (dncPulledPairFamilyOver ell K Λ ha d g s hs b) ≅
      dncPulledPairNormalInvariantOver ell K Λ ha d g s hs b := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  letI : LocallyOfFiniteType pair.V'.hom := H.2.2.2.2.2.1
  letI : QuasiCompact pair.V'.hom := H.2.2.2.2.2.2.1
  letI : IsSeparated pair.V'.hom := H.2.2.2.2.1
  letI : IsIso (dncPulledPairEtaOver ell K Λ ha d g s hs b) := by
    change IsIso (dncCanonicalEtaMapOver ell K Λ ha B' pair.V' d pair.g' pair.s' hpair)
    exact dncCanonicalEtaMapOver_isIso ell K Λ ha B' pair.V' d pair.g' pair.s' hpair
  exact asIso (dncPulledPairEtaOver ell K Λ ha d g s hs b)


/-- The fixed Rees and associated-graded maps form Cartesian squares and respect
the augmentation and zero sections. Proof: use the coefficientwise Rees base-change
calculation in centred smooth coordinates and pass to the quotient by t at zero;
the augmentation kills each degree-one coordinate. No map is selected by this theorem.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
theorem dncPulledPairSquaresOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLiftOver K g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLiftOver, pullback.lift_fst])
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLiftOver K g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLiftOver, pullback.lift_fst])
  IsPullback φ (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left)
    (Scheme.Hom.deformationSpaceProj g.left s.left) (dncLineBaseChangeOver K b).left ∧
  pair.s'.left.deformationSpaceSection ≫ φ =
    (dncLineBaseChangeOver K b).left ≫ s.left.deformationSpaceSection ∧
  IsPullback ν (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    (Scheme.Hom.normalConeProj g.left s.left) b.left ∧
  Scheme.Hom.normalConeZeroSection pair.s'.left ≫ ν =
    b.left ≫ Scheme.Hom.normalConeZeroSection s.left := by
  let pair := dncPulledPairOver K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  have w : pair.s'.left ≫ pullback.fst g.left b.left = b.left ≫ s.left :=
    pullback.lift_fst _ _ _
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left
    (pullback.fst g.left b.left) b.left w
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left w
  change IsPullback φ (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left)
      (Scheme.Hom.deformationSpaceProj g.left s.left) (dncLineBaseChangeOver K b).left ∧
    pair.s'.left.deformationSpaceSection ≫ φ =
      (dncLineBaseChangeOver K b).left ≫ s.left.deformationSpaceSection ∧
    IsPullback ν (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
      (Scheme.Hom.normalConeProj g.left s.left) b.left ∧
    Scheme.Hom.normalConeZeroSection pair.s'.left ≫ ν =
      b.left ≫ Scheme.Hom.normalConeZeroSection s.left
  obtain ⟨s', hc, w', he, hp, hcompat, _, ν', hν', hpν⟩ :=
    SectionReesBaseChange.base_change d g.left s.left hsg b.left
  have he' : s' = pair.s'.left := he
  clear he
  subst s'
  have htotal : IsPullback φ
      (Scheme.Hom.deformationSpaceProj pair.g'.left pair.s'.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left))
      (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)) b.left := by
    simpa only [φ, pair, dncPulledPairOver, Over.homMk_left,
      Scheme.Hom.deformationSpaceProj,
      Scheme.IdealSheafData.deformationSpaceProj_over',
      Scheme.IdealSheafData.deformationSpaceProj] using hp
  have hq := IsPullback.of_bot htotal hcompat.1 (AffineSpace.isPullback_map b.left)
  letI : IsClosedImmersion s.left.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left).flip inferInstance
  have hν : ν' = ν := by
    apply (cancel_mono s.left.ker.normalConeToDeformationSpace).mp
    exact hν'.trans
      (Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  rw [hν] at hpν
  obtain ⟨μ, _, _, hμ, _, hzero, _⟩ := hcompat.2.2.2
  have hμν : μ = ν := by
    apply (cancel_mono s.left.ker.normalConeToDeformationSpace).mp
    exact hμ.trans
      (Scheme.IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  exact ⟨hq, hcompat.2.1, hpν, hμν ▸ hzero⟩

/-- The native section-invariant base-change map for the canonical fibre-product
pair, constructed by the compact-support mate and the pullback compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledSectionMapOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ b.left).obj (sectionInvariantOver ell K Λ ha B V g s hs) ⟶
      dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let v : pair.V' ⟶ V := Over.homMk (pullback.fst g.left b.left) rfl
  exact dncSectionBaseChangeMapOver ell K Λ ha g pair.g' b v
    (IsPullback.of_hasPullback g.left b.left) s hs pair.s' hpair
    (by
      change b.left ≫ s.left =
        dncPullbackLiftOver K g s b hs ≫ pullback.fst g.left b.left
      simp only [dncPullbackLiftOver, pullback.lift_fst])

/-- The family base-change map: use the actual coefficientwise Rees map between
the two deformations and apply native section base change to their augmented sections.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledFamilyMapOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ (dncLineBaseChangeOver K b).left).obj (condensedDncFamilyOver K B V g s Λ ha d hs) ⟶
      dncPulledPairFamilyOver ell K Λ ha d g s hs b := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  let H := condensedDncDomainOver K B V g s hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  let Hp := condensedDncDomainOver K B' pair.V' pair.g' pair.s' hpair
  letI := Hp.1
  letI := Hp.2.1
  letI := Hp.2.2.1
  letI := Hp.2.2.2.1
  letI := Hp.2.2.2.2.1
  letI := Hp.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.2.2.1
  letI := Hp.2.2.2.2.2.2.2.2.2.2.1
  let φ := SectionReesBaseChange.pairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLiftOver K g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLiftOver, pullback.lift_fst])
  let Q := dncPulledPairSquaresOver ell K Λ ha d g s hs b
  let v : condensedDncSourceOver K B' pair.V' pair.g' pair.s' ⟶
      condensedDncSourceOver K B V g s := Over.homMk φ (by
    change φ ≫ (Scheme.Hom.deformationSpaceProj g.left s.left ≫
      (condensedDncBaseOver K B).hom) = _
    rw [← Category.assoc, Q.1.w, Category.assoc, (dncLineBaseChangeOver K b).w]
    rfl)
  exact dncSectionBaseChangeMapOver ell K Λ ha
    (condensedDncMapOver K B V g s) (condensedDncMapOver K B' pair.V' pair.g' pair.s')
    (dncLineBaseChangeOver K b) v Q.1
    (condensedDncSectionOver K B V g s hs) H.2.2.2.2.2.2.2.2.2.2.2
    (condensedDncSectionOver K B' pair.V' pair.g' pair.s' hpair)
    Hp.2.2.2.2.2.2.2.2.2.2.2 Q.2.1.symm

/-- The normal-invariant base-change map: the associated-graded map, the normal
projection Cartesian square and the native exceptional-adjunction mate determine it.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
noncomputable def dncPulledNormalMapOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B) :
    (moduleObjectDerivedPullback Λ b.left).obj (dncNormalSectionInvariantOver ell K Λ ha B V d g s hs) ⟶
      dncPulledPairNormalInvariantOver ell K Λ ha d g s hs b := by
  let pair := dncPulledPairOver K g s b hs
  let hpair := dncPulledPairOver_section_retraction K g s b hs
  let H := dncPulledPairGeometryFactsOver K d g s hs b
  letI := H.1
  letI := SmoothOfRelativeDimension.smooth d pair.g'.left
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2
  letI : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hsg : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f => f.left) hs
  have hf := dncNormalGeometryFactsOver K d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) := hf.1
  letI : Smooth (Scheme.Hom.normalConeProj g.left s.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) := hf.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := hf.2.2.2
  letI : IsSeparated ((dncNormalBundleOver K g s).hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalBundleOver K g s).hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalBundleOver K g s).hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSectionOver K g s hs).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection s.left)
    infer_instance
  letI : Smooth (dncNormalProjectionOver K g s).left := by
    change Smooth (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsSeparated (dncNormalProjectionOver K g s).left := by
    change IsSeparated (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjectionOver K g s).left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjectionOver K g s).left := by
    change QuasiCompact (Scheme.Hom.normalConeProj g.left s.left)
    infer_instance
  letI : IsNoetherian B'.left := isNoetherian_of_locallyOfFiniteType B'.hom
  have hsgp : pair.s'.left ≫ pair.g'.left = 𝟙 B'.left := congrArg (fun f => f.left) hpair
  have hfp := dncNormalGeometryFactsOver K d pair.g' pair.s' hpair
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.1
  letI : Smooth (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) :=
    SmoothOfRelativeDimension.smooth d _
  letI : IsSeparated (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.2.1
  letI : LocallyOfFiniteType (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.2.2.1
  letI : QuasiCompact (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left) := hfp.2.2.2
  letI : IsSeparated ((dncNormalBundleOver K pair.g' pair.s').hom) := by
    change IsSeparated (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left ≫ B'.hom)
    infer_instance
  letI : LocallyOfFiniteType ((dncNormalBundleOver K pair.g' pair.s').hom) := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left ≫ B'.hom)
    infer_instance
  letI : QuasiCompact ((dncNormalBundleOver K pair.g' pair.s').hom) := by
    change QuasiCompact (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left ≫ B'.hom)
    infer_instance
  letI : IsClosedImmersion (dncNormalSectionOver K pair.g' pair.s' hpair).left := by
    change IsClosedImmersion (Scheme.Hom.normalConeZeroSection pair.s'.left)
    infer_instance
  letI : Smooth (dncNormalProjectionOver K pair.g' pair.s').left := by
    change Smooth (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  letI : IsSeparated (dncNormalProjectionOver K pair.g' pair.s').left := by
    change IsSeparated (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  letI : LocallyOfFiniteType (dncNormalProjectionOver K pair.g' pair.s').left := by
    change LocallyOfFiniteType (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  letI : QuasiCompact (dncNormalProjectionOver K pair.g' pair.s').left := by
    change QuasiCompact (Scheme.Hom.normalConeProj pair.g'.left pair.s'.left)
    infer_instance
  let ν := dncNormalPairMap s.left pair.s'.left (pullback.fst g.left b.left) b.left (by
    change dncPullbackLiftOver K g s b hs ≫ pullback.fst g.left b.left = _
    simp only [dncPullbackLiftOver, pullback.lift_fst])
  let Q := dncPulledPairSquaresOver ell K Λ ha d g s hs b
  let v : dncNormalBundleOver K pair.g' pair.s' ⟶ dncNormalBundleOver K g s :=
    Over.homMk ν (by
      change ν ≫ (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom) = _
      rw [← Category.assoc, Q.2.2.1.w, Category.assoc, b.w]
      rfl)
  exact dncSectionBaseChangeMapOver ell K Λ ha
    (dncNormalProjectionOver K g s) (dncNormalProjectionOver K pair.g' pair.s') b v Q.2.2.1
    (dncNormalSectionOver K g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)
    (dncNormalSectionOver K pair.g' pair.s' hpair) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsgp) Q.2.2.2.symm

/-- The pulled pair has its own normalized comparison, its uniqueness and its own
zero-fibre formula. The two final equations compare these maps to pullbacks of
the original maps via the fixed, geometrically constructed section comparisons.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 12 (blueprint: sk-thm-dnc). -/
structure DncPulledNormalizedComparisonOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    {B B' V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (b : B' ⟶ B)
    (kappa : condensedDncFamilyOver K B V g s Λ ha d hs ≅
      (moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj
        (sectionInvariantOver ell K Λ ha B V g s hs))
    (zero_map : sectionInvariantOver ell K Λ ha B V g s hs ≅
      dncNormalSectionInvariantOver ell K Λ ha B V d g s hs) where
  kappa' : dncPulledPairFamilyOver ell K Λ ha d g s hs b ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj (dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b)
  normalized' :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B'.left)).mapIso kappa' ≪≫
      dncOneBaseIso Λ (dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b) =
      dncPulledPairThetaOver ell K Λ ha d g s hs b
  unique' : ∀ κ' : dncPulledPairFamilyOver ell K Λ ha d g s hs b ≅
      (moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj (dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b),
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B'.left)).mapIso κ' ≪≫
        dncOneBaseIso Λ (dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b) =
        dncPulledPairThetaOver ell K Λ ha d g s hs b → κ' = kappa'
  zero_map' : dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b ≅
    dncPulledPairNormalInvariantOver ell K Λ ha d g s hs b
  zero_formula' : zero_map' = (dncZeroBaseIso Λ (dncPulledPairSectionInvariantOver ell K Λ ha d g s hs b)).symm ≪≫
    ((moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B'.left)).mapIso kappa').symm ≪≫
    dncPulledPairEtaIsoOver ell K Λ ha d g s hs b
  family_base_change_isIso :
    IsIso (dncPulledFamilyMapOver ell K Λ ha d g s hs b)
  section_base_change_isIso :
    IsIso (dncPulledSectionMapOver ell K Λ ha d g s hs b)
  normal_base_change_isIso :
    IsIso (dncPulledNormalMapOver ell K Λ ha d g s hs b)
  kappa_base_change :
    dncPulledFamilyMapOver ell K Λ ha d g s hs b ≫ kappa'.hom =
    (moduleObjectDerivedPullback Λ (dncLineBaseChangeOver K b).left).map kappa.hom ≫
      (dncLinePullbackIso Λ b (sectionInvariantOver ell K Λ ha B V g s hs)).hom ≫
      (moduleObjectDerivedPullback Λ
        (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).map
        (dncPulledSectionMapOver ell K Λ ha d g s hs b)
  zero_base_change :
    dncPulledSectionMapOver ell K Λ ha d g s hs b ≫ zero_map'.hom =
    (moduleObjectDerivedPullback Λ b.left).map zero_map.hom ≫
      dncPulledNormalMapOver ell K Λ ha d g s hs b

/-- A native coefficient-module sheaf `M` is a line (rank one) if, placed in degree `0`, it has
a two-sided inverse for the relative derived tensor product. This is the coefficient-free form
of "finite locally constant of rank one" used for a general admissible `Λ`: for a finite
`ell`-primary ring it says that `M` is invertible, i.e. locally free of rank one; for the
coefficient `Z/ell^n` of the existing statement it is its rank-one condition. Same
invertibility shape as `sectionInvariantOver_mem_and_tensor_inverse`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
step 7 (blueprint: sk-thm-dnc). -/
def dncRankOneLineOver
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)),
    Nonempty (((derivedTensor Λ X).obj ((DerivedCategory.singleFunctor _ 0).obj M)).obj P ≅
      𝟙_ _) ∧
    Nonempty (((derivedTensor Λ X).obj P).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      𝟙_ _)

/-- The full condensed interface for the DNC section invariant over a purity base field `K`
and an admissible coefficient `Λ` (any finite `ell`-primary ring, `A_{E,n}` for any finite
`E`, `O_E`, `E`, `Q̄_ell`). The fibre maps are the named canonical declarations
`dncCanonicalThetaOver`, `dncCanonicalEtaOver`; the zero-fibre object is the actual
normal-cone invariant, and base change uses the actual pulled pair.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc). -/
structure DncNormalizedComparisonOver
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    (B V : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) where
  regular : WeilConjectures.PurityConventions.IsRegularOfPureCodimension s.left d
  family_pic : (constantModelBoundedConstructible Λ (condensedDncBaseOver K B).left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
      (condensedDncFamilyOver K B V g s Λ ha d hs)
  section_pic : (constantModelBoundedConstructible Λ B.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
      (sectionInvariantOver ell K Λ ha B V g s hs)
  kappa : condensedDncFamilyOver K B V g s Λ ha d hs ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj
      (sectionInvariantOver ell K Λ ha B V g s hs)
  kappa_normalized :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).mapIso kappa ≪≫
      dncOneBaseIso Λ (sectionInvariantOver ell K Λ ha B V g s hs) =
      dncCanonicalThetaOver ell K Λ ha B V d g s hs
  kappa_unique : ∀ (κ' : condensedDncFamilyOver K B V g s Λ ha d hs ≅
    (moduleObjectDerivedPullback Λ
      (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)).obj
      (sectionInvariantOver ell K Λ ha B V g s hs)),
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)).mapIso κ' ≪≫
      dncOneBaseIso Λ (sectionInvariantOver ell K Λ ha B V g s hs) =
      dncCanonicalThetaOver ell K Λ ha B V d g s hs → κ' = kappa
  zero_map : sectionInvariantOver ell K Λ ha B V g s hs ≅
    dncNormalSectionInvariantOver ell K Λ ha B V d g s hs
  zero_map_formula : zero_map =
    (dncZeroBaseIso Λ (sectionInvariantOver ell K Λ ha B V g s hs)).symm ≪≫
      ((moduleObjectDerivedPullback Λ
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)).mapIso kappa).symm ≪≫
      dncCanonicalEtaOver ell K Λ ha B V d g s hs
  deformation_relative_dimension : SmoothOfRelativeDimension d
    (Scheme.Hom.deformationSpaceProj g.left s.left)
  one_geometry : IsPullback (Scheme.Hom.deformationSpaceOneFibre g.left s.left)
    g.left (Scheme.Hom.deformationSpaceProj g.left s.left)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left)
  normal_geometry : IsPullback
    (Scheme.Hom.ker s.left).normalConeToDeformationSpace
    (Scheme.Hom.normalConeProj g.left s.left)
    (Scheme.Hom.deformationSpaceProj g.left s.left)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left)
  normal_section_projection :
    dncNormalSectionOver K g s hs ≫ dncNormalProjectionOver K g s = 𝟙 B
  M_F : Mod (Sheaf (Scheme.ProEt.topology (condensedDncBaseOver K B).left) Ab.{u + 1})
    (condensedRingObj Λ (condensedDncBaseOver K B).left)
  M_C : Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
    (condensedRingObj Λ B.left)
  F_shift : condensedDncFamilyOver K B V g s Λ ha d hs ≅
    (CategoryTheory.shiftFunctor _ (2 * (d : ℤ))).obj
      ((DerivedCategory.singleFunctor _ 0).obj M_F)
  C_shift : sectionInvariantOver ell K Λ ha B V g s hs ≅
    (CategoryTheory.shiftFunctor _ (2 * (d : ℤ))).obj
      ((DerivedCategory.singleFunctor _ 0).obj M_C)
  M_F_rank_one : dncRankOneLineOver Λ (condensedDncBaseOver K B).left M_F
  M_C_rank_one : dncRankOneLineOver Λ B.left M_C
  etale_local : ∀ (B' : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ B) [Etale b.left],
    DncPulledNormalizedComparisonOver ell K Λ ha
      (B := B) (B' := B') (V := V) d g s hs b kappa zero_map
  arbitrary_base_change : ∀ (B' : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ B),
    DncPulledNormalizedComparisonOver ell K Λ ha
      (B := B) (B' := B') (V := V) d g s hs b kappa zero_map

/-- Full statement of `sk-thm-dnc` over a purity base field `K` and an admissible coefficient
`Λ`; the existing `dncSectionInvariant_condensed_statement` is the case `K = k`,
`Λ = A_{Q_ell,n} = Z/ell^n`. For a general `Λ` the rank-one statements of step 7 are the
invertibility `dncRankOneLineOver`.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
with the twelve-step proof sk-thm-dnc/sk-thm-dnc.proof.md (blueprint: sk-thm-dnc).

Proof (postponed, following the node step by step):
1. Since $k$ is a field, $S$ and $V$ are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. The morphism $g$ is separated: $V\times_SV\to
V\times_kV$ is the base change of the closed diagonal of $S$ over $k$, hence a closed immersion
and a monomorphism by [lem-weil-pbc-proper-fp-permanence](b), and the diagonal of $V$ over $S$
is the base change of the closed diagonal of $V$ over $k$ along it, hence closed by the same
clause. Thus the pair $(g,s)$ satisfies the hypotheses of
[lem-trf-section-rees-noetherian-geometry]. Its deformation $D_sV$ is the blowup minus the
strict transform of the statement, because both are glued from the same affine charts
$\operatorname{Spec}R[t,I/t]$ of [def-pur-dnc-section-family]. That lemma gives: $D_sV$ is
Noetherian, $\widetilde g$ is smooth, separated, of finite type and of pure relative dimension
$d$, $\widetilde s$ is closed, $\widetilde g$ and $\pi$ are compactifiable, and there are the
two fibre identifications and the punctured trivialization. The projection $\mathbf A^1_S\to S$
is separated of finite type. By [lem-weil-pbc-proper-fp-permanence](d),(e), finite type and
separatedness compose (over Noetherian schemes finite type is finite presentation). Hence
$D_sV$, $N_s$ and $\mathbf A^1_S$ are separated finite-type $k$-schemes, and $\widetilde
g,\widetilde s,\pi,z,a,i_0,i_1$ are separated finite-type morphisms between them. So every
exceptional inverse image below is in the domain of [def-weil-exceptional-inverse-image].

2. Before invoking the normal bundle, the centred étale-coordinate lemma gives affine charts
with Cartesian zero fibre and a regular sequence of d coordinates, including the empty sequence
for d=0. Its associated-graded conclusion identifies the actual normal cone with the rank-d
vector bundle used by [def-pur-normal-bundle].

3. The actual blowup-minus-strict-transform and its augmented section are the objects of
[def-pur-dnc-section-family]. The fibre and base-change identifications, the equation x_i=t u_i,
and the closedness of the deformed section are supplied by [sk-lem-geometry] together with the
separated-section conclusion in [lem-trf-section-rees-noetherian-geometry]. Put
$\theta:Li_1^*F\simeq C$ and $\eta:Li_0^*F\simeq Lz^*\omega_\pi$ for the two fibre
identifications of [sk-lem-geometry](1); they are used in Steps 8-12.

4. Take the Zariski cover $\{S_i=\operatorname{Spec}R\}$ and the centred affine charts of Step
2: $P=R[X_1,\ldots,X_d]\to T$ étale with $I=(X_1,\ldots,X_d)T$ the section ideal and $T/I=R$.
Flatness of $T$ over $P$ and [lem-weil-pbc-flat-tensor-exact] identify each $I^m/I^{m+1}$ with
the corresponding polynomial quotient tensored with $T$. By
[lem-trf-section-rees-noetherian-geometry], the open of the deformation over
$\operatorname{Spec}T$ has algebra $T[t,I/t]\cong T\otimes_{R[X]}R[t,u_1,\ldots,u_d]$ with
$X_j\mapsto t u_j$. Its map to $\operatorname{Spec}R[t,u_1,\ldots,u_d]=\mathbf A^d_{\mathbf
A^1_{S_i}}$, the standard deformation chart, is the base change of the étale map
$\operatorname{Spec}T\to\operatorname{Spec}P$, hence étale by
[lem-weil-pbc-etale-scheme-base-change]. The augmentation sends every $u_j$ to $0$ and $T$ to
$T/I=R$, with $t$ unchanged, so this chart contains the whole deformed section over $S_i$. By
[lem-trf-section-rees-base-change-etale], the deformation of the base-changed pair over $S_i$ is
the base change of $D_sV$, compatibly with sections, fibres and these chart algebras.

5. Write $a_i:\mathbf A^1_{S_i}\to S_i$, and $F_i$, $C_i$ for the restrictions of $F$ to
$\mathbf A^1_{S_i}$ and of $C$ to $S_i$. By [lem-pur-co-smooth-etale-locality], every étale map
$e$ is cohomologically smooth with $\omega_e\simeq\Lambda$. A standard affine-space projection
$p$ is cohomologically smooth, since clauses (1)-(3) of [thm-pur-cohomological-smoothness] are
the three conditions of [def-pur-co-smoothness]. Thus [lem-pur-co-smooth-composition] gives
$\omega_{pe}\simeq Le^*\omega_p$, for the source chart $U_i\to\mathbf A^d_{S_i}\to S_i$ and for
the deformation chart of Step 4 over $\mathbf A^1_{S_i}$. The same formula for the open chart
inclusions, through which the sections factor, computes $C_i$ and $F_i$ from these charts. The
projections are trivial rank-$d$ vector bundles. So [cor-pur-vector-bundle-purity] at
$K=\Lambda$, pulled back along the zero sections as in the standard pair of
[sk-lem-geometry](4), gives isomorphisms $\alpha_i:F_i\simeq\Lambda_{\mathbf A^1_{S_i}}(d)[2d]$
and $\beta_i:C_i\simeq\Lambda_{S_i}(d)[2d]$. Its base-change compatibility identifies
$La_i^*\Lambda_{S_i}(d)[2d]$ with $\Lambda_{\mathbf A^1_{S_i}}(d)[2d]$. Arbitrary base change of
dualizing objects, [thm-pur-cohomological-smoothness](3), identifies all restrictions used here.
These are comparisons on neighbourhoods of the sections, not an assertion that the whole source
is affine space.

6. Affine principal restrictions of the source and deformation charts preserve the Rees algebra
and all exceptional maps. The finite-type, separated, Noetherian and compactifiability
conditions for these chart maps follow from the cited permanence statements, so every comparison
in the preceding step is defined in the stated category.

7. The finite-coefficient assertion of [prop-weil-twist-preserves] says that $\Lambda(d)$ is a
finite locally constant rank-one sheaf. Thus the local models in Step 5 are sheaves in the
common degree $r=-2d$. Apply [lem-pur-concentrated-complex-shift](2) to $F$ on the surjective
etale cover $\coprod_i\mathbf A^1_{S_i}\to\mathbf A^1_S$, and to $C$ on $\coprod_i S_i\to S$.
This lemma does not require the disjoint union to be of finite type. It gives concentration in
degree $-2d$ and finite local constancy of $M_F=\mathcal H^{-2d}F$ and $M_C=\mathcal H^{-2d}C$.
They have rank one, as checked on the cover in Step 5. Part (1) of the same lemma gives $F\simeq
M_F[2d]$ and $C\simeq M_C[2d]$. Constant-coefficient inverse image is exact and is computed
termwise by [def-weil-derived-pullback-tensor-hom], so these identifications also hold after
every pullback below. By [lem-weil-pbc-derived-single-fully-faithful], removing the common shift
identifies morphisms between these objects with ordinary module-sheaf morphisms, preserving
equality and composition. Consequently the gluing below is gluing of morphisms of fixed sheaves.

8. Using the twist-pullback comparison of Step 5, set
$\lambda_i=(La_i^*\beta_i)^{-1}\circ\alpha_i:F_i\simeq La_i^*C_i$. Let $\theta_i:Li_1^*F_i\simeq
C_i$ be Step 3's fibre identification, put $h_i=(Li_1^*\lambda_i)\circ\theta_i^{-1}$, and define
$\kappa_i=La_i^*(h_i^{-1})\circ\lambda_i$. Then $Li_1^*\kappa_i=h_i^{-1}\circ
h_i\circ\theta_i=\theta_i$ since $a_i i_1=\operatorname{id}$. Every factor is invertible. This
normalizes the comparison on every component, without choosing a scalar or a trivialization of
$C_i$.

9. Let $j:\mathbf G_{m,S}\hookrightarrow\mathbf A^1_S$. The punctured product of
[lem-pur-dnc-section-geometry](3) gives $\kappa^\circ:j^*F\simeq j^*La^*C$. At $t=1$ it is
$\theta$, because the product and fibre identifications are those of the same pair $(V,s)$. On
$\mathbf G_{m,S_i}$, the maps $j^*\kappa_i$ and $\kappa^\circ$ agree at $1$ by Step 8. By Step 7
they are maps of finite locally constant sheaves with a common shift. The second assertion of
[lem-pur-lisse-uniqueness] makes them equal on $\mathbf G_{m,S_i}$. On an overlap $S_{ij}$ the
two normalized local comparisons therefore agree on its punctured line. The first assertion of
[lem-pur-lisse-uniqueness] makes them agree on all of $\mathbf A^1_{S_{ij}}$. This is exactly
the punctured-comparison and rigidity argument in the unit; it does not use descent of arbitrary
local systems along the affine line.

10. For the etale cover of the base, its base-changed affine-line cover is a cover in the small
pro-etale site [def-weil-pbc-proetale-site]. By
[lem-weil-proetale-weakly-etale-localization](1)-(3), the module sheaves on these cover members,
with their constant coefficient rings, are precisely restrictions to the localized sites. Regard
the maps of Step 9 as module-sheaf morphisms using Step 7. On the pro-etale covering $\{\mathbf
A^1_{S_i}\to\mathbf A^1_S\}$, [lem-pur-sheaf-hom-cover-gluing] glues them uniquely; it also
glues their inverses since inverse maps agree wherever the original maps agree. The two
composites are the identity, by the uniqueness part of that same sheaf-gluing statement applied
to the local identities. Restore the common shift using
[lem-weil-pbc-derived-single-fully-faithful] to obtain an isomorphism $\kappa:F\simeq La^*C$,
with $Li_1^*\kappa=\theta$. For any other normalized isomorphism, compare it with $\kappa$ on
the punctured line: [lem-pur-lisse-uniqueness], second assertion, makes them equal there, and
the first assertion makes them equal on the whole line. Thus the isomorphism is unique and
independent of the charts and of $\alpha_i,\beta_i$.

11. Pull back $\kappa$ along $i_0$. With the isomorphism $\eta$ from Step 3 and
$Li_0^*La^*C\simeq C$, this gives $q=(Li_0^*\kappa)\circ\eta^{-1}:Lz^*\omega_\pi\simeq C$.
Define the asserted map to be $q^{-1}$. Its direction is therefore $Ls^*\omega_g\to
Lz^*\omega_\pi$, as required. In the standard coordinates, $F$ is $La^*C$ by the standard-pair
assertion of [lem-pur-dnc-section-geometry](4), and the identity is normalized at $1$. Step 10
forces $\kappa$ to be that identity, so the fibre map is also the identity on the standard
section invariant.

12. Let $b:S'\to S$ be any $k$-morphism with $S'$ separated finite type, and let $\bar b:\mathbf
A^1_{S'}\to\mathbf A^1_S$ be its base change. By [lem-pur-dnc-section-geometry](5) the
pulled-back actual deformation, section and normal bundle are those of the pulled-back pair; by
[thm-pur-cohomological-smoothness](3) its two dualizing objects are the pullbacks of the
original ones. Constant-coefficient pullback is a functor computed termwise by
[def-weil-derived-pullback-tensor-hom], so $L\bar b^*\kappa$ is an isomorphism $F'\to La'^*C'$
whose restriction at $1$ is the pulled-back fibre identification $\theta'$. Step 10 over $S'$
says there is only one such normalized map. Hence $L\bar b^*\kappa=\kappa'$. Pulling this
equality back along $i'_0$ and inverting shows that the fibre isomorphisms also agree. The same
argument applies to etale localization. The geometry and dualizing statements used here allow
arbitrary base change, so no flatness hypothesis on $b$ is introduced.
-/
theorem dncSectionInvariantOver_condensed_statement
    (ell : ℕ) [Fact ell.Prime] (K : WeilConjectures.PurityBaseField.{u} ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ha : IsLocalizingAdmissibleCoefficient ell Λ)
    (B V : Over (Spec (.of K.K)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    WeilConjectures.PurityConventions.IsRegularOfPureCodimension s.left d ∧
    Nonempty (DncNormalizedComparisonOver ell K Λ ha B V d g s hs) := by
  sorry

end PulledPair

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! ### The existing declarations are the case `K = ofDatum D ell hell`

Every statement below is expected to be `rfl`: the `Over` bodies are verbatim copies, the field
instance of `PurityBaseField.ofDatum D ell hell` is that of `D.k`, and the remaining differing
arguments (`Fact` instances, `BaseFieldFiniteCD`, admissibility, unit membership, the
geometric facts) are proofs of propositions. The admissibility used on the general side is
`sectionInvariant_admissible`, as in `sectionInvariantOver_geometric`. -/

section GeometricNormal

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) (hell : ell ≠ D.p)
  {B V B' : Over (Spec (.of D.k))} (g : V ⟶ B) (s : B ⟶ V)

/-- The general normal-cone object is `dncNormalOver` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): identical bodies. -/
theorem dncNormalBundleOver_geometric :
    dncNormalBundleOver (WeilConjectures.PurityBaseField.ofDatum D ell hell) g s =
      dncNormalOver D g s := by
  sorry

/-- The general zero section is `dncNormalSection` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): identical bodies; the `Over.homMk` side conditions are
proofs. -/
theorem dncNormalSectionOver_geometric (hs : s ≫ g = 𝟙 B) :
    dncNormalSectionOver (WeilConjectures.PurityBaseField.ofDatum D ell hell) g s hs =
      dncNormalSection D g s hs := by
  sorry

/-- The general normal-cone projection is `dncNormalProjection` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): identical bodies. -/
theorem dncNormalProjectionOver_geometric :
    dncNormalProjectionOver (WeilConjectures.PurityBaseField.ofDatum D ell hell) g s =
      dncNormalProjection D g s := by
  sorry

/-- The general affine-line base map is `dncBaseChangeMap` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): identical bodies. -/
theorem dncLineBaseChangeOver_geometric (b : B' ⟶ B) :
    dncLineBaseChangeOver (WeilConjectures.PurityBaseField.ofDatum D ell hell) b =
      dncBaseChangeMap D b := by
  sorry

end GeometricNormal

/-- The general normal-cone invariant is `dncNormalSectionInvariant` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): the instance `letI`s are proofs, the wrappers agree by
`dncNormal*Over_geometric`, and the invariants by `sectionInvariantOver_geometric`. -/
theorem dncNormalSectionInvariantOver_geometric
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    dncNormalSectionInvariant D ell hell E n hn Λ hcoeff B V d g s hs =
      dncNormalSectionInvariantOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell E n hn Λ hcoeff) B V d g s hs := by
  sorry

section GeometricBaseChange

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
    (Padic.coefficientExtensionRing ell (DiagonalCoefficients.bottomField ell).1 n))))
  {B V B' V' : Over (Spec (.of D.k))}
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
  [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (g' : V' ⟶ B') [Smooth g'.left] [IsSeparated g'.left]
  [LocallyOfFiniteType g'.left] [QuasiCompact g'.left]
  (b : B' ⟶ B) (v : V' ⟶ V)
  (sq : IsPullback v.left g'.left g.left b.left)

/-- The general dualizing mate is `dncDualizingBaseChangeMap` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 3 (blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): identical bodies; `hcd`, `ha`, the `IsIso` instance of the
exchange map and the `Fact` instances are proofs. -/
theorem dncDualizingBaseChangeMapOver_geometric :
    dncDualizingBaseChangeMap D ell hell n hn Λ hcoeff g g' (b := b) (v := v) (sq := sq) =
      dncDualizingBaseChangeMapOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) g g' (b := b) (v := v) (sq := sq) := by
  sorry

/-- The general section base-change map is `dncSectionBaseChangeMap` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof steps 3 and 12 (blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): identical bodies, using
`dncDualizingBaseChangeMapOver_geometric` for the last factor. -/
theorem dncSectionBaseChangeMapOver_geometric
    (s : B ⟶ V) [IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)
    (s' : B' ⟶ V') [IsClosedImmersion s'.left] (hs' : s' ≫ g' = 𝟙 B')
    (w : b.left ≫ s.left = s'.left ≫ v.left) :
    dncSectionBaseChangeMap D ell hell n hn Λ hcoeff g g' b v sq s hs s' hs' w =
      dncSectionBaseChangeMapOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) g g' b v sq s hs s' hs' w := by
  sorry

end GeometricBaseChange

section GeometricFibres

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
    (Padic.coefficientExtensionRing ell (DiagonalCoefficients.bottomField ell).1 n))))
  (B V : Over (Spec (.of D.k)))
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
  [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (s : B ⟶ V) [IsClosedImmersion s.left]
  (hs : s ≫ g = 𝟙 B)

/-- The general one-fibre composite is `dncCanonicalThetaComposite` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 3 (blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): the `letI`s from `condensedDncDomain(Over)` are proofs, the
square, `b`, `v` are identical terms, and `dncSectionBaseChangeMapOver_geometric` identifies
the final map. -/
theorem dncCanonicalThetaCompositeOver_geometric :
    dncCanonicalThetaComposite D ell hell n hn Λ hcoeff B V d g s hs =
      dncCanonicalThetaCompositeOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) B V d g s hs := by
  sorry

/-- The general one-fibre map is `dncCanonicalThetaMap` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): `dncCanonicalThetaCompositeOver_geometric`. -/
theorem dncCanonicalThetaMapOver_geometric :
    dncCanonicalThetaMap D ell hell n hn Λ hcoeff B V d g s hs =
      dncCanonicalThetaMapOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) B V d g s hs := by
  sorry

/-- The general `θ` is `dncCanonicalTheta` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): both are `asIso` of the same map; the `IsIso` instances are
proofs. -/
theorem dncCanonicalThetaOver_geometric :
    dncCanonicalTheta D ell hell n hn Λ hcoeff B V d g s hs =
      dncCanonicalThetaOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) B V d g s hs := by
  sorry

/-- The general zero-fibre composite is `dncCanonicalEtaComposite` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md,
proof step 3 (blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): as `dncCanonicalThetaCompositeOver_geometric`, with
`dncNormal*Over_geometric` for the normal-cone wrappers. -/
theorem dncCanonicalEtaCompositeOver_geometric :
    dncCanonicalEtaComposite D ell hell n hn Λ hcoeff B V d g s hs =
      dncCanonicalEtaCompositeOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) B V d g s hs := by
  sorry

/-- The general zero-fibre map is `dncCanonicalEtaMap` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): `dncCanonicalEtaCompositeOver_geometric`. -/
theorem dncCanonicalEtaMapOver_geometric :
    dncCanonicalEtaMap D ell hell n hn Λ hcoeff B V d g s hs =
      dncCanonicalEtaMapOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) B V d g s hs := by
  sorry

/-- The general `η` is `dncCanonicalEta` at `ofDatum`.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc).
Proof (postponed, expected `rfl`): both are `asIso` of the same map; the `IsIso` instances are
proofs. -/
theorem dncCanonicalEtaOver_geometric :
    dncCanonicalEta D ell hell n hn Λ hcoeff B V d g s hs =
      dncCanonicalEtaOver ell (WeilConjectures.PurityBaseField.ofDatum D ell hell) Λ
        (sectionInvariant_admissible D ell hell (DiagonalCoefficients.bottomField ell)
          n hn Λ (Or.inl hcoeff)) B V d g s hs := by
  sorry

end GeometricFibres

end AlgebraicGeometry.ProEtale.CondensedRing
