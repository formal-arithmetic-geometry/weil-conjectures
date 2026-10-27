/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.CommonQuotientPullbackData
import all Sheaf.Paper.RingedCoefficientPullbackComparison

/-! # Identity normalization of geometric scalar insertion

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-common-quotient-insertion-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections (Mod D)
open SheafOfModules.RingedCoefficientProjection
open SheafOfModules.SuccessiveDerivedQuotient (restriction sectionTensor)
namespace SheafOfModules.CommonQuotientPullback

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  {iInv : Sheaf J (Type r) ⥤ Sheaf J (Type r)}
  {iPush : Sheaf J (Type r) ⥤ Sheaf J (Type r)} {iadj : iInv ⊣ iPush}
  {pY : Scalars.{c, v, r} J}
  (nY : SuccessiveDerivedQuotient.Normalization (J := J) pY)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  (g0 : Geometry iInv iPush iadj) (a0 : g0.rings.obj B ⟶ B)
  (θ0 : iInv ≅ 𝟭 (Sheaf J (Type r)))
  (ρ0 : g0.rings ≅ 𝟭 (Sheaf J CommRingCat.{r}))
  (i0 : Insertion g0 nY nY φ a0)
  (d : IdentityData nY φ g0 a0 θ0 ρ0)

private theorem insertion_underlying (M : Mod J B) :
    (underlying (g0.rings.obj R)).map (i0.ordinary.app M) =
      (g0.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        pullbackInsertion g0 nY a0 M := by
  ext U x
  change (i0.ordinary.app M).val.app U x =
    ((nY.ordinaryAdjunction a0).unit.app _).val.app U
      (((g0.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        (g0.inverse B).moduleUnderlying.inv.app M).hom.app U x)
  rw [nY.ordinary_unit]
  exact i0.sections M U x

private theorem ordinary_identity (M : Mod J B) :
    i0.ordinary.app M ≫ d.target.ordinary.hom.app M =
      d.source.ordinary.hom.app M := by
  apply (underlying (g0.rings.obj R)).map_injective
  rw [Functor.map_comp, insertion_underlying]
  rw [Category.assoc, d.target_sections, d.source_sections]
  rfl

private theorem representative_identity (P : CochainComplex (Mod J B) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := B) (P.X i)) :
    i0.derived.app (DerivedCategory.Q.obj P) ≫
      d.target.derived.hom.app (DerivedCategory.Q.obj P) =
        d.source.derived.hom.app (DerivedCategory.Q.obj P) := by
  let H := (HomotopyCategory.quotient (Mod J B) (.up ℤ)).obj P
  let F := (restrictionModel nY φ).comp (restrictionModel nY (ρ0.hom.app R))
  have hi : IsIso (F.computation H) := by
    dsimp only [F, Model.comp, restrictionModel]
    infer_instance
  apply (cancel_mono (F.computation H)).mp
  rw [Category.assoc, d.target.representative P ⟨hk, hf⟩]
  dsimp only [targetModel]
  rw [← Category.assoc]
  erw [i0.representative P hk hf]
  rw [Category.assoc]
  rw [← DerivedCategory.Qh.map_comp]
  have he : i0.ordinary ≫ d.target.ordinary.hom = d.source.ordinary.hom := by
    apply NatTrans.ext
    funext M
    exact ordinary_identity nY φ g0 a0 θ0 ρ0 i0 d M
  have heh := congrArg (fun f ↦ (NatTrans.mapHomotopyCategory f (.up ℤ)).app H) he
  simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at heh
  erw [heh]
  exact (d.source.representative P ⟨hk, hf⟩).symm

/-- The normalized scalar insertion for an identity geometry is the identity after
its specified unitors.

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, identity case;
sites-modules.tex, Tag 03EL (tensor pullback unit).
(blueprint: lem-weil-pbc-common-quotient-insertion-identity).

Proof: on underlying sheaves the insertion is the scalar-extension unit. The target
unitor sends its image to the identity inverse-image section, precisely the source
unitor's formula. Apply this equality degreewise. The two representative squares
identify the resulting maps after the common exact-restriction computation, which
is invertible. Cancel it. Flat-term K-flat complexes present the derived category,
so localization detects equality of these natural transformations on all objects.
Finally cancel the source unitor against its inverse. -/
theorem insertion_identity (M : D J B) :
    d.source.derived.inv.app M ≫ i0.derived.app M ≫
      d.target.derived.hom.app M = 𝟙 _ := by
  let τ := i0.derived ≫ d.target.derived.hom
  have he : τ = d.source.derived.hom := by
    let P := flatHomotopy (J := J) B
    let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory (Mod J B) (.up ℤ) ⥤ D J B)
    let W := (HomotopyCategory.quasiIso (Mod J B) (.up ℤ)).inverseImage P.ι
    have : L.IsLocalization W := flat_localization (J := J) B
    apply Localization.natTrans_ext L W
    intro H
    exact representative_identity nY φ g0 a0 θ0 ρ0 i0 d
      H.obj.as H.property.1 H.property.2
  have h := NatTrans.congr_app he M
  change i0.derived.app M ≫ d.target.derived.hom.app M =
    d.source.derived.hom.app M at h
  rw [h]
  exact Iso.inv_hom_id_app _ _

end SheafOfModules.CommonQuotientPullback
