/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.Mathlib.CategoryTheory.FintypeCat
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension

/-!
# Auxiliary results on fundamental groups and Weil groups

Small general facts used to compare the Weil group of base point data with the arithmetic
fundamental group (`WeilConjectures.WeilSheaf.WeilDescentFundamentalGroup`).

## Main results

- `AlgebraicGeometry.Scheme.FiniteEtale.nonempty_fiber_constantCover_of`: the geometric fibre of
  the constant cover attached to a finite étale field extension is nonempty.
- `AlgebraicGeometry.Scheme.FiniteEtale.toAut_fundamentalGroupMap_pullbackFiberIso`: the map of
  fundamental groups induced by a morphism along the canonical path is `pullbackPathHom`.
- `AlgebraicGeometry.Scheme.FiniteEtale.toAut_mem_weilGroup_iff`: membership in the Weil group
  can be tested in the automorphism group of the fibre functor.
-/

@[expose] public section

universe u

open CategoryTheory


namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The geometric fibre of the constant cover attached to a finite étale field extension `L` of
`K` at a geometric point with algebraically closed field is nonempty: `L` embeds into it. -/
lemma nonempty_fiber_constantCover_of {K : Type u} [Field K] {X₀ : Scheme.{u}}
    (p : X₀ ⟶ Spec (.of K)) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X₀) (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.Etale K L] :
    Nonempty ((fiber s).obj (constantCover p (FiniteEtaleAlgebra.of L))) := by
  let _ : Algebra K Ω := (baseRingHom p s).toAlgebra
  let φ : L →ₐ[K] Ω := IsAlgClosed.lift
  exact ⟨(fiberConstantCoverEquiv p s _).symm ⟨φ.toRingHom, φ.comp_algebraMap⟩⟩


open PreGaloisCategory in
/-- The map of fundamental groups induced by `f : Y' ⟶ Y` along the canonical path
`F_y ∘ f^* ≅ F_{y ≫ f}` is `pullbackPathHom`, under the identifications of the fundamental
groups with the automorphism groups of the fibre functors. -/
lemma toAut_fundamentalGroupMap_pullbackFiberIso {Y Y' : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y')
    (G' : Type u) [Group G'] [∀ P, MulAction G' ((fiber y).obj P)] [IsNaturalSMul (fiber y) G']
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber (y ≫ f)).obj P)] [IsFundamentalGroup (fiber (y ≫ f)) G] (k : G') :
    toAut (fiber (y ≫ f)) G (fundamentalGroupMap (pullbackFiberIso f y) G' G k) =
      pullbackPathHom f y (toAut (fiber y) G' k) := by
  ext P x
  obtain ⟨x, rfl⟩ : ∃ x', (pullbackFiberIso f y).hom.app P x' = x :=
    ⟨(pullbackFiberIso f y).inv.app P x,
      ConcreteCategory.congr_hom ((pullbackFiberIso f y).inv_hom_id_app P) x⟩
  rw [toAut_hom_app_apply, fundamentalGroupMap_smul, pullbackPathHom_apply]
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [FintypeCat.inv_app_hom_app_apply]
  rfl

open PreGaloisCategory in
/-- Membership in the Weil group can be tested in `Aut F_s` instead of a fundamental group `G`
acting naturally on the fibres. -/
lemma toAut_mem_weilGroup_iff {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}}
    (p : X₀ ⟶ Spec (.of K)) [GeometricallyConnected p] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X₀) (G : Type*) [Group G] [∀ P, MulAction G ((fiber s).obj P)]
    [IsNaturalSMul (fiber s) G] (g : G) (n : Multiplicative ℤ) :
    (toAut (fiber s) G g, n) ∈ weilGroup p s (Aut (fiber s)) ↔ (g, n) ∈ weilGroup p s G := by
  simp only [mem_weilGroup_iff, mulAction_def, toAut_hom_app_apply]

end AlgebraicGeometry.Scheme.FiniteEtale

