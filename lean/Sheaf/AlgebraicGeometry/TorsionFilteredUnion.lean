/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing

/-!
# The filtered union of the torsion kernels of an étale sheaf

Source: blueprint `sec-curve-estimates/sk-prop-h2`, lemma-weil-pbc-torsion-filtered-union
(blueprint: lemma-weil-pbc-torsion-filtered-union).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A locally torsion abelian sheaf is the filtered colimit of its kernels of multiplication
by positive integers, ordered by divisibility. The conclusion `IsTorsionAbelianSheaf F`
is the existing definition of precisely this assertion: the transition maps are the kernel
inclusions and the canonical map `colimit.desc D c` to `F` is an isomorphism.

Source: blueprint `sec-curve-estimates/sk-prop-h2`, detailed proof of
lemma-weil-pbc-torsion-filtered-union (blueprint: lemma-weil-pbc-torsion-filtered-union).

Proof for stage 3:
1. By def-pur-abelian-sheaf-kernel, `F[n]` consists of sections killed by `n`.
If `n` divides `m`, a section killed by `n` is killed by `m`, yielding compatible kernel
inclusions. Positive integers ordered by divisibility form a nonempty filtered category:
`lcm(n,m)` is a common upper bound, and parallel arrows in a poset coincide. By
 def-weil-pbc-category-colimit and def-weil-pbc-etale-sheaves, the diagram has a colimit and
the kernel inclusions induce its canonical map to `F`.
2. Each kernel inclusion is monic. Exactness of filtered colimits in the Grothendieck
abelian category of étale abelian sheaves (lem-weil-pbc-abelian-etale-sheaves-grothendieck)
shows that the induced map to the colimit of the constant diagram on `F` is monic.
The index category is connected, so that constant diagram has colimit `F`; this identifies
the induced map with the canonical map of step 1.
3. For any section `s`, local torsion gives a covering on whose members the restrictions
of `s` are killed by positive integers `n`. Each such restriction lifts to `F[n]` and hence
to the colimit. Thus the canonical map is locally surjective, hence epic by
lem-weil-pbc-abelian-sheaf-epi-locally-surjective.
4. A morphism that is both monic and epic in an abelian category is an isomorphism. -/
theorem isTorsionAbelianSheaf_of_isTorsion {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    IsTorsionAbelianSheaf F := by
  classical
  have : Nonempty PositiveNat := ⟨⟨1, Nat.one_pos⟩⟩
  have : IsDirectedOrder PositiveNat := ⟨fun n m ↦
    ⟨⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩,
      dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
  have : IsFiltered PositiveNat := inferInstance
  dsimp only [IsTorsionAbelianSheaf]
  let D : PositiveNat ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
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
  have : AB5OfSize.{0, 0} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
  have : IsConnected PositiveNat := IsFiltered.isConnected _
  let φ := CategoryTheory.Limits.colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj F := { app n := c.ι.app n }
    have : ∀ n, Mono (α.app n) := fun n ↦ inferInstanceAs (Mono (CategoryTheory.Limits.kernel.ι _))
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (CategoryTheory.Limits.colim.map α) := inferInstance
    let e := CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
      (CategoryTheory.Limits.colimit.isColimit ((Functor.const PositiveNat).obj F))
      (CategoryTheory.Limits.isColimitConstCocone PositiveNat F)
    have : φ = CategoryTheory.Limits.colim.map α ≫ e.hom := by
      refine CategoryTheory.Limits.colimit.hom_ext fun n ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := hF (U := Opposite.op V) s
      refine X.smallEtaleTopology.superset_covering ?_ hR
      intro W g hg
      obtain ⟨n, hn, hns⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hRs hg)
      obtain ⟨t, ht⟩ := AlgebraicGeometry.Etale.exists_kernel_ι_app_eq
        (n • 𝟙 F) (F.obj.map g.op s) (by
        change (((sheafToPresheaf _ _).map (n • 𝟙 F)).app (Opposite.op W)) _ = 0
        rw [Functor.map_nsmul, NatTrans.app_nsmul]
        exact hns)
      refine ⟨(CategoryTheory.Limits.colimit.ι D ⟨n, hn⟩).hom.app (Opposite.op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.Limits.colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  exact isIso_of_mono_of_epi φ

end AlgebraicGeometry.Scheme
