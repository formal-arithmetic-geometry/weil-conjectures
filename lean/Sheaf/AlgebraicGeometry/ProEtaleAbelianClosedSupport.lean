/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Mathlib.CategoryTheory.Sites.LocallyInjective
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Closed support for abelian pro-etale sheaves

Source: Stacks Project, Tags 09AA and 09AH
(blueprint: lem-weil-pbc-proetale-abelian-closed-support).
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

private theorem abLocalVanish {U Z : Scheme.{u}} (g : Z ⟶ U)
    (F : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) {V : U.ProEt} (s : ToType (F.obj.obj (op V)))
    (hs : ((upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app F).hom.app (op V) s =
      0) :
    ∃ (P : Presieve ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)),
      P ∈ Scheme.ProEt.precoverage Z _ ∧
      ∀ ⦃T⦄ (φ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V), P φ →
        ∃ (V' : U.ProEt) (f : V' ⟶ V)
          (ψ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
          ψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = φ ∧
            F.obj.map f.op s = 0 := by
  set G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  have hunit : ((upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app F).hom.app
      (op V) = (G.op.leftKanExtensionUnit F.obj).app (op V) ≫
        (toSheafify _ (G.op.leftKanExtension F.obj)).app (op (G.obj V)) := rfl
  rw [hunit, ConcreteCategory.comp_apply] at hs
  have hS := Presheaf.equalizerSieve_mem (Scheme.ProEt.topology Z)
    (toSheafify (Scheme.ProEt.topology Z) (G.op.leftKanExtension F.obj)) (X := op (G.obj V))
      ((G.op.leftKanExtensionUnit F.obj).app (op V) s) 0
      (hs.trans (map_zero _).symm)
  obtain ⟨P, hP, hle⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  refine ⟨P, hP, fun T φ hφ ↦ ?_⟩
  have h₁ := hle _ _ hφ
  obtain ⟨V', f, ψ, hψ, h⟩ := Functor.exists_map_eq_of_leftKanExtensionUnit_eq G F.obj φ s 0
    (by simpa using h₁)
  exact ⟨V', f, ψ, hψ, by simpa using h⟩


private theorem abDetectSections {U : Scheme.{u}} {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (F : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) {V : U.ProEt}
    (s : ToType (F.obj.obj (op V)))
    (hs : ∀ k, ((upperStarLowerStarAdjunction Ab.{u + 1} (g k)).unit.app F).hom.app
      (op V) s = 0) :
    s = 0 := by
  choose P hP hPs using fun k ↦ abLocalVanish (g k) F s (hs k)
  choose ι T φ hTφ using fun k ↦ (P k).exists_eq_ofArrows
  choose V' f ψ hψ hf using fun (p : Σ k, ι k) ↦
    hPs p.1 (φ p.1 p.2) (by rw [hTφ p.1]; exact .mk p.2)
  let D : PreZeroHypercover V.left := ⟨Σ k, ι k, fun p ↦ (V' p).left, fun p ↦ (f p).left⟩
  let E (k : κ) : PreZeroHypercover
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (g k)).obj V).left :=
    ⟨ι k, fun m ↦ (T k m).left, fun m ↦ (φ k m).left⟩
  have hE (k : κ) : (E k).presieve₀ ∈ Scheme.proetalePrecoverage _ := by
    have := hP k
    rw [hTφ k, Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at this
    exact this
  have : ∀ k, QuasiCompactCover (E k) := fun k ↦
    Scheme.presieve₀_mem_qcPrecoverage_iff.1 (hE k).1
  have hD : QuasiCompactCover D := by
    refine QuasiCompactCover.of_comp_factor (fun k ↦ pullback.fst V.hom (g k)) (fun x ↦ ?_) E D
      (fun k m ↦ ⟨k, m⟩) (fun k m ↦ (ψ ⟨k, m⟩).left ≫ pullback.fst _ _) fun k m ↦ ?_
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      exact ⟨k, w, hw⟩
    · have := congrArg (fun a ↦ a.left ≫ pullback.fst V.hom (g k)) (hψ ⟨k, m⟩)
      simpa using this
  have hDmem : D.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD, ?_⟩
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2 ⟨fun x ↦ ?_, fun p ↦ ?_⟩
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      obtain ⟨m, τ, rfl⟩ :=
        ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (hE k).2).1 w
      refine ⟨⟨k, m⟩, (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ |>.base τ, ?_⟩
      have key : (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left =
          (φ k m).left ≫ pullback.fst V.hom (g k) := by
        rw [← hψ ⟨k, m⟩]
        simp
      rw [← hw]
      change ((ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left).base τ =
        ((φ k m).left ≫ pullback.fst V.hom (g k)).base τ
      exact congrArg (fun a ↦ a.base τ) key
    · exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (f p).left
        V.hom V.prop (by rw [MorphismProperty.Over.w (f p)]; exact (V' p).prop)
  have hmem : Presieve.ofArrows V' f ∈ Scheme.ProEt.precoverage U V := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hDmem
  have hS : Sieve.generate (Presieve.ofArrows V' f) ∈ Scheme.ProEt.topology U V :=
    Scheme.ProEt.mem_topology_iff.2 ⟨_, hmem, Sieve.le_generate _⟩
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget Ab.{u + 1}) F.property) _ hS
  rw [← Presieve.isSheafFor_iff_generate] at hsh
  refine hsh.isSeparatedFor.ext fun _ _ ⟨p⟩ ↦ ?_
  change F.obj.map (f p).op s = F.obj.map (f p).op 0
  rw [hf p, map_zero]

private theorem abDetectMaps {U : Scheme.{u}} {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    {F G : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}} (φ : F ⟶ G)
    (h : ∀ k, (g k)^*[Ab.{u + 1}].map φ = 0) : φ = 0 := by
  apply Sheaf.hom_ext
  ext V x
  refine abDetectSections g hg G (φ.hom.app V x) fun k ↦ ?_
  have h0 : φ ≫ (upperStarLowerStarAdjunction Ab.{u + 1} (g k)).unit.app G = 0 := by
    have := (upperStarLowerStarAdjunction Ab.{u + 1} (g k)).unit.naturality φ
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map, h k,
      Functor.map_zero, comp_zero] at this
    exact this
  have := congrArg (fun ψ ↦ (ψ.hom.app V).hom x) h0
  simpa using this

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
  refine (IsZero.iff_id_eq_zero F).2 (abDetectMaps g (fun x ↦ ?_)
    (𝟙 F) ?_)
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
(blueprint: lem-weil-pbc-proetale-abelian-closed-support).

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
