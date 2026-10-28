/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb

/-!
# Closed support for abelian pro-etale sheaves

Source: Stacks Project, Tags 09AA and 09AH
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

private instance abPreservesColimitsOfShape {U Z : Scheme.{u}} (g : Z ⟶ U) (Y) :
    PreservesColimitsOfShape
      (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y)
      (forget Ab.{u + 1}) := by
  have : IsFiltered (CostructuredArrow
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ Y.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem abZero {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    IsZero ((upperStar Ab.{u + 1} j).obj ((lowerStar Ab.{u + 1} i).obj M)) := by
  have hdisjoint : Set.range i.base ∩ Set.range j.base = ∅ := by
    rw [hij]
    exact Set.inter_compl_self _
  have hz : IsZero ((openImmersionRestriction Ab.{u + 1} j).obj
      ((lowerStar Ab.{u + 1} i).obj M)) := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
    have hempty : IsEmpty V.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (T.hom ≫ j) i ≫ T.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) i z), ?_⟩⟩
        · rw [pullback.condition]
          exact ⟨_, rfl⟩
        · rfl
      rw [hdisjoint] at hz
      exact hz
    exact (isZero_zero Ab.{u + 1}).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M V).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  have hz' : IsZero ((upperStar Ab.{u + 1} j).obj
      ((lowerStar Ab.{u + 1} i).obj M)) :=
    hz.of_iso ((upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  exact hz'

private theorem abJointZero {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj F))
    (hj : IsZero ((upperStar Ab.{u + 1} j).obj F)) : IsZero F := by
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else U
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by rintro (_ | _) <;> dsimp [g] <;> infer_instance
  refine (IsZero.iff_id_eq_zero F).2
    (eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g (fun x ↦ ?_) (𝟙 F) ?_)
  · by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, hij ▸ hx⟩
  · rintro (_ | _)
    · exact hj.eq_of_src _ _
    · exact hi.eq_of_src _ _

private theorem abDetectIso {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    {F G : Sheaf (ProEt.topology X) Ab.{u + 1}} (φ : F ⟶ G)
    [IsIso ((upperStar Ab.{u + 1} i).map φ)]
    [IsIso ((upperStar Ab.{u + 1} j).map φ)] : IsIso φ := by
  have hker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((g)^*[Ab.{u + 1}].map φ)],
      IsZero ((g)^*[Ab.{u + 1}].obj (kernel φ)) := fun g _ ↦
    (isZero_kernel_of_mono ((g)^*[Ab.{u + 1}].map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((g)^*[Ab.{u + 1}].map φ)],
      IsZero ((g)^*[Ab.{u + 1}].obj (cokernel φ)) := fun g _ ↦
    (isZero_cokernel_of_epi ((g)^*[Ab.{u + 1}].map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (abJointZero i j hij _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (abJointZero i j hij _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

private theorem abSupportOfCounit {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (hc : IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit)
    (F : Sheaf (ProEt.topology X) Ab.{u + 1})
    (hF : IsZero ((upperStar Ab.{u + 1} j).obj F)) :
    IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F) := by
  have := hc
  set adj := upperStarLowerStarAdjunction Ab.{u + 1} i
  have : IsIso ((i)^*[Ab.{u + 1}].map (adj.unit.app F)) := by
    have h := adj.left_triangle_components F
    have : IsIso ((i)^*[Ab.{u + 1}].map (adj.unit.app F) ≫
        adj.counit.app ((i)^*[Ab.{u + 1}].obj F)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have : IsIso ((j)^*[Ab.{u + 1}].map (adj.unit.app F)) :=
    ⟨⟨0, hF.eq_of_src _ _, (abZero i j hij
      _).eq_of_src _ _⟩⟩
  exact abDetectIso i j hij _

/-- The closed counit is invertible, and the closed unit is invertible on sheaves whose
restriction to the quasi-compact open complement vanishes.

Source: Stacks, Tags 09AA and 09AH; direct proof of supported units by conservative
restriction to a finite quasi-compact jointly surjective family
(auxiliary; not a blueprint node).

Proof:
1. A section whose image in an inverse image vanishes vanishes locally in the left Kan
extension, since sheafification is locally injective. The Kan-extension indexing categories
are filtered, so the underlying-set forgetful functor detects this equality at a stage.
2. For finitely many quasi-compact jointly surjective scheme maps, the resulting weakly
etale neighborhoods form a pro-etale covering family. The sheaf separation condition then
makes the original section zero. Apply this to morphisms to get joint faithfulness.
3. The closed immersion and its quasi-compact open complement are such a family.
Their exact inverse images therefore jointly detect zero objects and isomorphisms, by
applying the zero-detection statement to kernels and cokernels.
4. Use the abelian closed counit. The closed restriction of the unit is invertible by the
adjunction triangle identity. Its open restriction is a map between zero objects: its
source is zero by hypothesis, and the open restriction of a closed direct image is zero,
as its sections are evaluated on empty base changes. Joint detection proves the unit
invertible. This proves the supported-unit assertion directly, without a ringed module
comparison or an additional localization exact-sequence hypothesis. -/
theorem abelian_closed_support {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit ∧
    ∀ F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1},
      IsZero ((upperStar Ab.{u + 1} j).obj F) →
      IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F) := by
  have hc := abelian_closed_counit i
  exact ⟨hc, fun F hF ↦ abSupportOfCounit i j hij hc F hF⟩

end AlgebraicGeometry.ProEtale
