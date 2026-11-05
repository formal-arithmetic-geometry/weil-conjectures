/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Characterizations of torsion abelian étale sheaves

Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement, and
`sec-abelian-varieties/def-weil-pbc-etale-sheaves`
(blueprint: lem-weil-pbc-torsion-sheaf-characterizations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement
(blueprint: lem-weil-pbc-torsion-sheaf-characterizations).

Proof: (1) Exactness of geometric stalks (prop-weil-pbc-geometric-stalks-exact) identifies
stalks of the kernel of multiplication by n with n-torsion in the stalk. Commutation with
colimits (lem-kun-stalks-commute-colimits) identifies the stalk of the canonical colimit map
with inclusion of the union of these subgroups, namely the torsion subgroup.
(2) Conservativity (lemma-weil-pbc-geometric-stalk-conservative, Stacks 03PU) gives the first
condition iff every stalk is torsion. (3) Locally annihilated sections give torsion stalks:
represent a germ on a pointed neighbourhood and lift its geometric point to the covering
(lem-weil-pbc-etale-cover-geometric-point-lift, Stacks 03PR).
(4) Conversely, choose a geometric point over each point of U; its germ is annihilated by a
positive integer. Equality with zero in the filtered stalk is witnessed on a smaller pointed
neighbourhood. These neighbourhoods cover U. The cofiltered-neighbourhood and composition
facts are lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered and
lem-weil-pbc-etale-composition-cancellation. Condition (2) is the recorded local-section
predicate `CategoryTheory.Sheaf.IsTorsion` (a covering sieve on whose arrows the restriction
has finite additive order), condition (3) is `IsAddTorsion` of every geometric stalk. -/
theorem isTorsionAbelianSheaf_characterizations {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (IsTorsionAbelianSheaf F ↔ F.IsTorsion) ∧
    (IsTorsionAbelianSheaf F ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)) := by
  classical
  have hstalk (hF : IsTorsionAbelianSheaf F) (Ω : Type u) [Field Ω]
      [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
      IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
    have : Nonempty PNat.DvdOrder := ⟨⟨1, Nat.one_pos⟩⟩
    have : IsDirectedOrder PNat.DvdOrder := ⟨fun n m ↦
      ⟨⟨n.val * m.val, Nat.mul_pos n.val_pos m.val_pos⟩,
        dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
    have : IsFiltered PNat.DvdOrder := inferInstance
    let D : PNat.DvdOrder ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      { obj := fun n ↦ kernel (n.val • 𝟙 F)
        map := fun {n m} hnm ↦ kernel.lift (m.val • 𝟙 F)
          (kernel.ι (n.val • 𝟙 F))
          (torsionKernelTransition_condition F n m hnm.down.down)
        map_id := fun n ↦ torsionKernelTransition_id F n
        map_comp := fun hnm hmk ↦
          (torsionKernelTransition_comp F _ _ _ hnm.down.down hmk.down.down).symm }
    let c : Cocone D :=
      { pt := F
        ι := { app := fun n ↦ kernel.ι (n.val • 𝟙 F)
               naturality := by intro n m hnm; simp [D] } }
    change IsIso (colimit.desc D c) at hF
    have := hF
    have : IsIso ((colimit.isColimit D).desc c) := hF
    have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit D)
    let L := (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
    have : L.Additive := (pointSmallEtale t).sheafFiber_additive
    have hLc := isColimitOfPreserves L hc
    have := preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
    intro x
    obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep (D ⋙ L) hLc x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n.val, n.val_pos, ?_⟩
    have hk : L.map (kernel.ι (n.val • 𝟙 F)) ≫ L.map (n.val • 𝟙 F) = 0 := by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at hk
    have he := ConcreteCategory.congr_hom hk y
    simpa [L, c, ConcreteCategory.comp_apply] using he
  have hlocal : F.IsTorsion ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
    refine ⟨fun hF Ω _ _ t ↦ ?_, fun h ↦ ?_⟩
    · exact (isTorsion_iff_isAddTorsion_sheafFiber F).mp hF Ω t
    · refine Sheaf.IsTorsion.of_isAddTorsion_sheafFiber
        (isConservativeFamilyOfPoints_ulift_pointSmallEtale T) ?_
      rintro ⟨-, ⟨x⟩⟩
      exact IsAddTorsion.of_surjective
        (f := ((((pointSmallEtale (T.algClosurePoint x)).uliftSheafFiberIso
          AddCommGrpCat.{u + 1}).app F).inv).hom)
        (ConcreteCategory.bijective_of_isIso _).2 (h _ _)
  have hiff : IsTorsionAbelianSheaf F ↔ F.IsTorsion := by
    refine ⟨fun hF ↦ hlocal.mpr (hstalk hF), fun hF ↦ ?_⟩
    classical
    have : Nonempty PNat.DvdOrder := ⟨⟨1, Nat.one_pos⟩⟩
    have : IsDirectedOrder PNat.DvdOrder := ⟨fun n m ↦
      ⟨⟨n.val * m.val, Nat.mul_pos n.val_pos m.val_pos⟩,
        dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
    have : IsFiltered PNat.DvdOrder := inferInstance
    dsimp only [IsTorsionAbelianSheaf]
    let D : PNat.DvdOrder ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      { obj := fun n ↦ CategoryTheory.Limits.kernel (n.val • 𝟙 F)
        map := fun {n m} hnm ↦ CategoryTheory.Limits.kernel.lift (m.val • 𝟙 F)
          (CategoryTheory.Limits.kernel.ι (n.val • 𝟙 F))
          (torsionKernelTransition_condition F n m hnm.down.down)
        map_id := fun n ↦ torsionKernelTransition_id F n
        map_comp := fun hnm hmk ↦
          (torsionKernelTransition_comp F _ _ _ hnm.down.down hmk.down.down).symm }
    let c : CategoryTheory.Limits.Cocone D :=
      { pt := F
        ι := { app := fun n ↦ CategoryTheory.Limits.kernel.ι (n.val • 𝟙 F)
               naturality := by intro n m hnm; simp [D] } }
    change IsIso (CategoryTheory.Limits.colimit.desc D c)
    have : AB5OfSize.{0, 0} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
    have : IsConnected PNat.DvdOrder := IsFiltered.isConnected _
    let φ := CategoryTheory.Limits.colimit.desc D c
    have hmono : Mono φ := by
      let α : D ⟶ (Functor.const _).obj F := { app n := c.ι.app n }
      have : ∀ n, Mono (α.app n) := fun n ↦
        inferInstanceAs (Mono (CategoryTheory.Limits.kernel.ι _))
      have : Mono α := NatTrans.mono_of_mono_app _
      have : Mono (CategoryTheory.Limits.colim.map α) := inferInstance
      let e := CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
        (CategoryTheory.Limits.colimit.isColimit ((Functor.const PNat.DvdOrder).obj F))
        (CategoryTheory.Limits.isColimitConstCocone PNat.DvdOrder F)
      have : φ = CategoryTheory.Limits.colim.map α ≫ e.hom := by
        refine CategoryTheory.Limits.colimit.hom_ext fun n ↦ ?_
        simp [φ, e, α]
      rw [this]
      infer_instance
    have hepi : Epi φ := by
      have : Sheaf.IsLocallySurjective φ := by
        refine ⟨fun {V} s ↦ ?_⟩
        obtain ⟨R, hR, hRs⟩ := hF (U := Opposite.op V) s
        refine T.smallEtaleTopology.superset_covering ?_ hR
        intro W g hg
        obtain ⟨n, hn, hns⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hRs hg)
        have hx : (n • 𝟙 F).hom.app (op W) (F.obj.map g.op s) = 0 := by
          change (((sheafToPresheaf _ _).map (n • 𝟙 F)).app (op W)) _ = 0
          rw [Functor.map_nsmul, NatTrans.app_nsmul]
          exact hns
        let E := sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation _ _).obj (op W)
        let e := PreservesKernel.iso E (n • 𝟙 F) ≪≫
          AddCommGrpCat.kernelIsoKer (E.map (n • 𝟙 F))
        let t := e.inv ⟨F.obj.map g.op s, hx⟩
        have ht : (kernel.ι (n • 𝟙 F)).hom.app (op W) t = F.obj.map g.op s := by
          change (e.inv ≫ E.map (kernel.ι (n • 𝟙 F))) ⟨F.obj.map g.op s, hx⟩ = _
          rw [Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι,
            AddCommGrpCat.kernelIsoKer_inv_comp_ι]
          rfl
        refine ⟨(CategoryTheory.Limits.colimit.ι D ⟨n, hn⟩).hom.app (Opposite.op W) t, ?_⟩
        rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.Limits.colimit.ι_desc]
        exact ht
      exact Sheaf.epi_of_isLocallySurjective _
    exact isIso_of_mono_of_epi φ
  exact ⟨hiff, hiff.trans hlocal⟩

-- The inherited statement names a nondependent index binder `n`.

end AlgebraicGeometry.Scheme
