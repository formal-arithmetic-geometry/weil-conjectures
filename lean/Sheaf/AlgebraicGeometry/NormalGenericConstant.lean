/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.NormalScheme
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.FinitePushforward
import Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-!
# Constant abelian sheaves at the generic point of a normal scheme

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, node
`lem-fin-normal-generic-constant`, order 1606 (blueprint: lem-fin-normal-generic-constant).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_abelian_unit_of_module_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : AddCommGrpCat.{u + 1})
    (h : IsIso ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).unit.app
        ((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
            (ModuleCat.of (ULift.{u + 1} ℤ) M)))) :
    IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) := by
  let R := ULift.{u + 1} ℤ
  let N := ModuleCat.of R M
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let J := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N
  let SY := sheafCompose Y.smallEtaleTopology U
  let SX := sheafCompose X.smallEtaleTopology U
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let t := SY.map ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app J)
  let c := (adj.homEquiv (SY.obj J)
    (SX.obj ((Etale.upperStar (ModuleCat.{u + 1} R) f).obj J))).symm t
  have : IsIso t := by dsimp [t]; infer_instance
  have : IsIso c := Etale.isIso_moduleAbelianInverseImageComparison f R J
  have ht := (adj.homEquiv (SY.obj J)
    (SX.obj ((Etale.upperStar (ModuleCat.{u + 1} R) f).obj J))).apply_symm_apply t
  change adj.homEquiv _ _ c = t at ht
  rw [Adjunction.homEquiv_unit] at ht
  have : IsIso (adj.unit.app (SY.obj J)) := by
    rw [← isIso_comp_right_iff _ ((Etale.lowerStar AddCommGrpCat.{u + 1} f).map c), ht]
    infer_instance
  have : Y.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification _ _
  let e := (constantCommuteCompose Y.smallEtaleTopology U).app N
  have he : adj.unit.app (SY.obj J) ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} f ⋙
        Etale.lowerStar AddCommGrpCat.{u + 1} f).map e.hom =
      e.hom ≫ adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj M) :=
    (adj.unit.naturality e.hom).symm
  have : IsIso (e.hom ≫ adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj M)) :=
    he ▸ inferInstance
  rw [← isIso_comp_left_iff e.hom]
  infer_instance

private theorem isIso_generic_residue (V : Scheme.{u}) [IsIntegral V] :
    IsIso (V.residue (genericPoint V)) := by
  let : Field (V.presheaf.stalk (genericPoint V)) :=
    inferInstanceAs (Field V.functionField)
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨(V.residue (genericPoint V)).hom.injective, IsLocalRing.residue_surjective⟩

private theorem isIso_unit_comp_iso {X Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : X ⟶ Y) [IsIso g]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F)) :
    IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (g ≫ f)).unit.app F) := by
  let A := AddCommGrpCat.{u + 1}
  have hc : IsIso (((Etale.upperStarLowerStarAdjunction A f).comp
      (Etale.upperStarLowerStarAdjunction A g)).unit.app F) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  have he := Etale.upperStarComp_hom_app_unit_app A g f F
  have hi : IsIso (((Etale.upperStarLowerStarAdjunction A (g ≫ f)).unit.app F) ≫
      (Etale.lowerStar A (g ≫ f)).map ((Etale.upperStarComp A g f).hom.app F)) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

/-- On a normal integral Noetherian scheme, the natural map from a finite constant abelian
sheaf to its direct image from the generic point is an isomorphism.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, order 1606
(blueprint: lem-fin-normal-generic-constant).

Proof: Evaluate on affine etale objects over affine opens of the base; these form a basis.
Such objects are Noetherian. By `lem-fin-etale-normal-components`, each is a finite disjoint
union of normal integral open-and-closed affine components. Each nonempty component dominates
the base because an etale morphism is open (`lem-weil-pbc-flat-lfp-open`). Flatness embeds the
nonzero elements of the base domain into each component domain. By
`lem-weil-pbc-generic-fibre-localization-domain-irreducible`, its generic fibre is nonempty
and connected. Thus base change to the generic point preserves the finite set of components.
By `lem-weil-pbc-constant-sheaf-sections-connected`, both section groups are the product of
one copy of the coefficient group per component, and restriction is the identity on each
factor. The direct image evaluates on these generic fibres (`def-weil-pbc-direct-image`).
Consequently the natural map is an isomorphism on the basis, hence an isomorphism of sheaves.
The displayed map is the adjunction unit followed by pushforward of the canonical
identification of the pullback of a constant sheaf with the constant sheaf. -/
theorem Etale.isIso_constantSheaf_to_generic_lowerStar
    (V : Scheme.{u}) [IsNoetherian V] [IsIntegral V] (hV : IsNormalScheme V)
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    IsIso
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (V.fromSpecResidueField (genericPoint V))).unit.app
          ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1}
          (V.fromSpecResidueField (genericPoint V))).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (V.fromSpecResidueField (genericPoint V))).app M).hom) := by
  -- The source theorem works for arbitrary module coefficients.
  let R := ULift.{u + 1} ℤ
  let N := ModuleCat.of R M
  have hm := (Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed R
    (fun x ↦ (hV.2 x).2) N).1
  -- Forget coefficients using the canonical comparison determined by the unit.
  have hs := isIso_abelian_unit_of_module_unit
    (V.fromSpecStalk (genericPoint V)) M hm
  -- At the generic point the stalk is a field, so its residue map is an isomorphism.
  have : IsIso (V.residue (genericPoint V)) := isIso_generic_residue V
  have : IsIso (Spec.map (V.residue (genericPoint V))) := inferInstance
  have he := isIso_unit_comp_iso (V.fromSpecStalk (genericPoint V))
    (Spec.map (V.residue (genericPoint V)))
    ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) hs
  change IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (V.fromSpecResidueField (genericPoint V))).unit.app
    ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) at he
  infer_instance

end AlgebraicGeometry
