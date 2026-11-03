/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariantOver
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.DeformationSpace.SmoothProj

/-! # The deformation family over a general purity base field

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
def-pur-dnc-section-family.md, displayed family definition
(blueprint: def-pur-dnc-section-family).

Additive general version of `Sheaf.Paper.CondensedDncFamily`. The geometry (extended-Rees
deformation space, its projection to `A^1_B`, the augmentation section) is the existing
field-free `Scheme.Hom.deformationSpace*` construction; only the structure map to `Spec K`
changes. Bodies and proofs are those of `CondensedDncFamily` with `D.k` replaced by `K.K`.
The family is `sectionInvariantOver` of the actual projection and section; the coefficient is
any admissible `Λ`. The existing family is the case `K = ofDatum D ell hell`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
  (B V : Over (Spec (.of K.K))) (g : V ⟶ B) (s : B ⟶ V)
/-- The affine-line base of the deformation, with its given field structure.
Source: latest blueprint, deformation base (blueprint: def-pur-dnc-section-family); general base field. -/
def condensedDncBaseOver : Over (Spec (.of K.K)) :=
  Over.mk ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)

/-- The actual extended-Rees deformation space, with its field structure.
Source: latest blueprint, blowup complement (blueprint: def-pur-dnc-section-family); general base field. -/
def condensedDncSourceOver : Over (Spec (.of K.K)) :=
  Over.mk (Scheme.Hom.deformationSpaceProj g.left s.left ≫ (condensedDncBaseOver K B).hom)

/-- The projection of the constructed deformation to its affine-line base.
Source: latest blueprint, g tilde (blueprint: def-pur-dnc-section-family); general base field. -/
def condensedDncMapOver : condensedDncSourceOver K B V g s ⟶ condensedDncBaseOver K B :=
  Over.homMk (Scheme.Hom.deformationSpaceProj g.left s.left) rfl

/-- The Rees augmentation section respects the fixed field structure.
Source: latest blueprint, s tilde (blueprint: def-pur-dnc-section-family); general base field.
Proof: the augmentation sends t to t and every f/t to zero; its composite with
projection is the identity. Compose that identity with the affine-line field map.
This uses the geometric section identity of the extended-Rees construction. -/
theorem condensedDncSectionOver_over (hs : s ≫ g = 𝟙 B) :
    s.left.deformationSpaceSection ≫ (condensedDncSourceOver K B V g s).hom =
      (condensedDncBaseOver K B).hom := by
  have hs' : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  change s.left.deformationSpaceSection ≫
      (Scheme.Hom.deformationSpaceProj g.left s.left ≫ (condensedDncBaseOver K B).hom) = _
  rw [← Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs',
    Category.id_comp]

/-- The actual augmentation section, as a morphism over the fixed field.
Source: latest blueprint, s tilde (blueprint: def-pur-dnc-section-family); general base field. -/
def condensedDncSectionOver (hs : s ≫ g = 𝟙 B) :
    condensedDncBaseOver K B ⟶ condensedDncSourceOver K B V g s :=
  Over.homMk s.left.deformationSpaceSection (condensedDncSectionOver_over K B V g s hs)

variable [hBft : LocallyOfFiniteType B.hom] [hBqc : QuasiCompact B.hom]
  [hBsep : IsSeparated B.hom]
  [hVft : LocallyOfFiniteType V.hom] [hVqc : QuasiCompact V.hom]
  [hVsep : IsSeparated V.hom]
  [hgsm : Smooth g.left] [hgsep : IsSeparated g.left]
  [hgft : LocallyOfFiniteType g.left] [hgqc : QuasiCompact g.left]
  [hsclosed : IsClosedImmersion s.left]

include hBft hBqc hBsep hVft hVqc hVsep hgsm hgsep hgft hgqc hsclosed

/-- The geometric domain of the smooth deformation family, including its section law.
Source: latest blueprint, deformation family and sk-lem-geometry
(blueprint: def-pur-dnc-section-family); general base field.
Proof: near the section choose smooth etale coordinates, and write the Rees chart
as x_i=t*u_i. Projection to t is smooth. Away from the section it is the product
with Gm. These charts include varying relative dimension and the empty base.
Finite type follows from the finitely generated centre on the Noetherian source;
separatedness follows from the blowup of the separated product. The section is
closed since the projection is separated. The augmentation gives the section law.
The affine line is separated finite type over B, so both field structures have
the displayed properties. These are the geometric clauses of the dependency node. -/
theorem condensedDncDomainOver (hs : s ≫ g = 𝟙 B) :
    LocallyOfFiniteType (condensedDncBaseOver K B).hom ∧
    QuasiCompact (condensedDncBaseOver K B).hom ∧
    IsSeparated (condensedDncBaseOver K B).hom ∧
    LocallyOfFiniteType (condensedDncSourceOver K B V g s).hom ∧
    QuasiCompact (condensedDncSourceOver K B V g s).hom ∧
    IsSeparated (condensedDncSourceOver K B V g s).hom ∧
    Smooth (condensedDncMapOver K B V g s).left ∧
    IsSeparated (condensedDncMapOver K B V g s).left ∧
    LocallyOfFiniteType (condensedDncMapOver K B V g s).left ∧
    QuasiCompact (condensedDncMapOver K B V g s).left ∧
    IsClosedImmersion (condensedDncSectionOver K B V g s hs).left ∧
    condensedDncSectionOver K B V g s hs ≫ condensedDncMapOver K B V g s = 𝟙 _ := by
  have _ := hVft
  have _ := hVqc
  have _ := hVsep
  have _ := hgft
  have hs' : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  have hsection := Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs'
  have : Smooth (Scheme.Hom.deformationSpaceProj g.left s.left) :=
    Scheme.Hom.smooth_deformationSpaceProj g.left s.left hs'
  have : IsClosedImmersion (s.left.deformationSpaceSection ≫
      Scheme.Hom.deformationSpaceProj g.left s.left) := hsection ▸ inferInstance
  have : IsClosedImmersion s.left.deformationSpaceSection :=
    IsClosedImmersion.of_comp _ (Scheme.Hom.deformationSpaceProj g.left s.left)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change QuasiCompact ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change IsSeparated ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change LocallyOfFiniteType (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change QuasiCompact (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · change IsSeparated (Scheme.Hom.deformationSpaceProj g.left s.left ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  · exact inferInstanceAs (Smooth (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (IsSeparated (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (LocallyOfFiniteType (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (QuasiCompact (Scheme.Hom.deformationSpaceProj g.left s.left))
  · exact inferInstanceAs (IsClosedImmersion s.left.deformationSpaceSection)
  · apply Over.OverMorphism.ext
    exact hsection

omit hBft hBqc hBsep hVft hVqc hVsep hgsm hgsep hgft hgqc in
/-- The Rees projection retains the specified constant relative dimension.
Source: latest blueprint sk-lem-geometry (2), as scoped by Wei Yang #1412 item 6
(blueprint: def-pur-dnc-section-family); general base field.
Proof: apply the published centred-chart theorem: the coordinates x_i=t*u_i
make the Rees projection etale-locally affine d-space over the affine-line base. -/
theorem condensedDncRelativeDimensionOver (d : ℕ) [SmoothOfRelativeDimension d g.left]
    (hs : s ≫ g = 𝟙 B) :
    SmoothOfRelativeDimension d (condensedDncMapOver K B V g s).left := by
  exact Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g.left s.left
    (congrArg (fun f ↦ f.left) hs)

variable [Fact ell.Prime]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ha : IsLocalizingAdmissibleCoefficient ell Λ)

/-- The family `F = L s~^* R g~^! Λ` over a general purity base field and admissible
coefficient: `sectionInvariantOver` of the actual Rees projection and augmentation section.
Only proofs from `condensedDncDomainOver` type the expression; no existence choice.
Source: latest blueprint, family formula, with Wei Yang #1412 item 6
(blueprint: def-pur-dnc-section-family). -/
def condensedDncFamilyOver (d : ℕ) [SmoothOfRelativeDimension d g.left]
    (hs : s ≫ g = 𝟙 B) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (condensedDncBaseOver K B).left)
      Ab.{u + 1}) (condensedRingObj Λ (condensedDncBaseOver K B).left)) :=
  let H := condensedDncDomainOver K B V g s hs
  letI := condensedDncRelativeDimensionOver K B V g s d hs
  letI := H.1
  letI := H.2.1
  letI := H.2.2.1
  letI := H.2.2.2.1
  letI := H.2.2.2.2.1
  letI := H.2.2.2.2.2.1
  letI : Smooth (condensedDncMapOver K B V g s).left :=
    SmoothOfRelativeDimension.smooth d _
  letI := H.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.1
  letI := H.2.2.2.2.2.2.2.2.2.2.1
  sectionInvariantOver ell K Λ ha
    (condensedDncBaseOver K B) (condensedDncSourceOver K B V g s)
    (condensedDncMapOver K B V g s) (condensedDncSectionOver K B V g s hs)
    H.2.2.2.2.2.2.2.2.2.2.2

/-- The general family lies in Pic(Dctf). Statement copied from `condensedDncFamily_pic`.
Source: latest blueprint, final family clause (blueprint: def-pur-dnc-section-family).
Proof (postponed): `sectionInvariantOver_mem_and_tensor_inverse` for the Rees pair, typed by
`condensedDncDomainOver` and `condensedDncRelativeDimensionOver`. -/
theorem condensedDncFamilyOver_pic (d : ℕ) [SmoothOfRelativeDimension d g.left]
    (hs : s ≫ g = 𝟙 B) :
    (constantModelBoundedConstructible Λ (condensedDncBaseOver K B).left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
      (condensedDncFamilyOver K B V g s Λ ha d hs) ∧
    ∃ P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (condensedDncBaseOver K B).left)
        Ab.{u + 1}) (condensedRingObj Λ (condensedDncBaseOver K B).left)),
      (constantModelBoundedConstructible Λ (condensedDncBaseOver K B).left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) P ∧
      Nonempty (((derivedTensor Λ (condensedDncBaseOver K B).left).obj
        (condensedDncFamilyOver K B V g s Λ ha d hs)).obj P ≅ 𝟙_ _) ∧
      Nonempty (((derivedTensor Λ (condensedDncBaseOver K B).left).obj P).obj
        (condensedDncFamilyOver K B V g s Λ ha d hs) ≅ 𝟙_ _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing family is the case `K = ofDatum D ell hell`.
Source: def-pur-dnc-section-family (blueprint: def-pur-dnc-section-family).
Proof (postponed, expected `rfl` after unfolding): the Over wrappers have identical bodies,
and `sectionInvariantOver_geometric` identifies the invariants; the remaining arguments are
proofs of propositions. -/
theorem condensedDncFamilyOver_geometric
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (B V : Over (Spec (.of D.k))) (g : V ⟶ B) (s : B ⟶ V)
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [Smooth g.left] [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    [IsClosedImmersion s.left]
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (d : ℕ) [SmoothOfRelativeDimension d g.left] (hs : s ≫ g = 𝟙 B) :
    condensedDncFamily D B V g s ell hell E n hn Λ hcoeff d hs =
      condensedDncFamilyOver (WeilConjectures.PurityBaseField.ofDatum D ell hell) B V g s Λ
        (sectionInvariant_admissible D ell hell E n hn Λ hcoeff) d hs := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! ### The normal bundle and its section invariant over a general purity base field

Copies of `dncNormalOver`, `dncNormalSection`, `dncNormalProjection`, `dncBaseChangeMap`,
`dncNormalGeometryFacts` and `dncNormalSectionInvariant`
(`Sheaf.SmoothPurity.DncSectionInvariantStatement`) with `D.k` replaced by `K.K`. The
geometry is the field-free `Scheme.Hom.normalCone*` construction. The `_geometric`
comparisons live in `Sheaf.SmoothPurity.DncThetaEtaOver`. -/

/-- The normal-cone object `N = N_s(V)` over the purity base field, used by the zero-fibre
clause. Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc); general base field. -/
def dncNormalBundleOver {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B V : Over (Spec (.of K.K))} (g : V ⟶ B) (s : B ⟶ V) : Over (Spec (.of K.K)) :=
  Over.mk (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom)

/-- The actual normal-cone zero section, as a morphism over the purity base field.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc); general base field. -/
def dncNormalSectionOver {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B V : Over (Spec (.of K.K))} (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) :
    B ⟶ dncNormalBundleOver K g s :=
  Over.homMk (Scheme.Hom.normalConeZeroSection s.left) (by
    change Scheme.Hom.normalConeZeroSection s.left ≫
      (Scheme.Hom.normalConeProj g.left s.left ≫ B.hom) = B.hom
    rw [← Category.assoc,
      Scheme.Hom.normalConeZeroSection_normalConeProj (congrArg (fun f => f.left) hs),
      Category.id_comp])

/-- The actual normal-cone projection, as a morphism over the purity base field.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc); general base field. -/
def dncNormalProjectionOver {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B V : Over (Spec (.of K.K))} (g : V ⟶ B) (s : B ⟶ V) :
    dncNormalBundleOver K g s ⟶ B :=
  Over.homMk (Scheme.Hom.normalConeProj g.left s.left) (by rfl)

/-- The affine-line base map induced by a morphism of bases.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc); general base field. -/
def dncLineBaseChangeOver {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B B' : Over (Spec (.of K.K))} (b : B' ⟶ B) :
    condensedDncBaseOver K B' ⟶ condensedDncBaseOver K B :=
  Over.homMk (AffineSpace.map (ULift.{u} (Fin 1)) b.left) (by
    change AffineSpace.map (ULift.{u} (Fin 1)) b.left ≫
      ((AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ B.hom) =
      (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left) ≫ B'.hom
    rw [← Category.assoc, AffineSpace.map_over]
    rw [Category.assoc, b.w])

/-- The geometric facts used to type the normal-cone invariant over a general base field.
Statement copied from `dncNormalGeometryFacts` with `D.k ↦ K.K`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc); general base field.
Proof (postponed): as `dncNormalGeometryFacts`; smooth base change along the normal-cone
pullback square, inheritance of separated/finite type/quasi-compact from the pair, and the
normal-cone relative-dimension calculation. No field property is used. -/
theorem dncNormalGeometryFactsOver {ell : ℕ} (K : WeilConjectures.PurityBaseField.{u} ell)
    {B V : Over (Spec (.of K.K))}
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g.left] [Smooth g.left]
    [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    (s : B ⟶ V) [IsClosedImmersion s.left]
    (hs : s ≫ g = 𝟙 B) :
    SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) ∧
    IsSeparated (Scheme.Hom.normalConeProj g.left s.left) ∧
    LocallyOfFiniteType (Scheme.Hom.normalConeProj g.left s.left) ∧
    QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) := by
  sorry

/-- The normal-cone invariant `L z^* R π^! Λ_B` over a general purity base field and an
admissible coefficient: `sectionInvariantOver` of the actual normal-cone projection and zero
section. Only proofs from `dncNormalGeometryFactsOver` type the expression.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/_section.md
(blueprint: sk-thm-dnc); general base field. -/
def dncNormalSectionInvariantOver
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
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left)) := by
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
  exact sectionInvariantOver ell K Λ ha B (dncNormalBundleOver K g s)
    (dncNormalProjectionOver K g s) (dncNormalSectionOver K g s hs) (by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.normalConeZeroSection_normalConeProj hsg)

end AlgebraicGeometry.ProEtale.CondensedRing
