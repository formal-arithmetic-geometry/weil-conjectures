/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward

/-!
# Structure sheaves of finite locally free morphisms

Source: blueprint `sec-picard-framework/sk-the-hilbert-functor--definition-1`,
lemma `lem-pc-flf-properties`; Stacks Project, Tag 02KB
(blueprint: lem-pc-flf-properties).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

noncomputable section

set_option quotPrecheck false

variable {X S : Scheme.{u}} (f : X ⟶ S)

local notation "P(" s ")" => (f.base _* X.presheaf).stalk s
local notation "R(" s ")" => S.presheaf.stalk s
local notation "K(" s ")" => S.residueField s

local instance (s : S) : Algebra (R(s)) (P(s)) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat s).map f.c).hom.toAlgebra

local instance (s : S) : Algebra (R(s)) (K(s)) := (S.residue s).hom.toAlgebra

/-- A finite locally free morphism of degree `d` has structure-sheaf pushforward locally
free of rank `d`, and its stalk tensored with the residue field canonically identifies with
sections of its scheme-theoretic fibre. The equations specify this canonical identification
on every germ and residue-field scalar, rather than asserting an unspecified isomorphism.
Source: blueprint `lem-pc-flf-properties`; Stacks Project, Tag 02KB
(blueprint: lem-pc-flf-properties).

Proof: use `Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit` for the rank
assertion. Choose an affine neighbourhood of each point and use
`Scheme.Hom.exists_ringEquiv_stalk_pushforward_tensorProduct_fiber` for the isomorphism.
Restriction to the fibre on every neighbourhood defines a cocone, hence a ring map from
the pushforward stalk. Since that stalk is a localization of the sections on the chosen
affine neighbourhood, `IsLocalization.ringHom_ext` identifies this map with the isomorphism
on tensors with right factor one. The affine formula on tensors with left factor one
and multiplicativity then give the required formula on every neighbourhood. -/
theorem finiteLocallyFree_structureSheaf_properties (d : ℕ)
    [f.IsFiniteLocallyFreeOfDegree d] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) d ∧
    ∀ s : S, ∃ e : (P(s) ⊗[R(s)] K(s)) ≃+* Γ(f.fiber s, ⊤),
      ∀ (U : S.Opens) (hs : s ∈ U)
        (hU : ⊤ ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (a : Γ(X, f ⁻¹ᵁ U)) (k : K(s)),
        e (((f.base _* X.presheaf).germ U s hs).hom a ⊗ₜ[R(s)] k) =
          ((f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ hU).hom a *
            (f.fiberToSpecResidueField s).appTop.hom ((Scheme.ΓSpecIso (K(s))).inv.hom k) := by
  refine ⟨Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit f d, ?_⟩
  intro s
  obtain ⟨V, hV, hsV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  obtain ⟨e, he⟩ := f.exists_ringEquiv_stalk_pushforward_tensorProduct_fiber hV s hsV
  let F := f.base _* X.presheaf
  let c : Cocone ((TopologicalSpace.OpenNhds.inclusion s).op ⋙ F) :=
    { pt := Γ(f.fiber s, ⊤)
      ι :=
        { app := fun U ↦ (f.fiberι s).appLE (f ⁻¹ᵁ U.unop.1) ⊤
            (f.preimage_fiberι_preimage s U.unop.1 U.unop.2).ge
          naturality := by
            intro U W i
            dsimp
            rw [Category.comp_id]
            exact Scheme.Hom.map_appLE _ _ _ } }
  let q : P(s) ⟶ Γ(f.fiber s, ⊤) := colimit.desc _ c
  have hq (U : S.Opens) (hs : s ∈ U) :
      F.germ U s hs ≫ q =
        (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤
          (f.preimage_fiberι_preimage s U hs).ge :=
    colimit.ι_desc c (Opposite.op ⟨U, hs⟩)
  let : Algebra Γ(S, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) (P(s)) := (F.germ V s hsV).hom.toAlgebra
  have := f.isLocalization_stalk_pushforward hV (hV.preimage f) s hsV
  have hl : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = q.hom := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨s, hsV⟩).asIdeal.primeCompl)
    ext a
    change e (F.germ V s hsV a ⊗ₜ[R(s)] 1) = q.hom (F.germ V s hsV a)
    have H := he a 1
    simp only [map_one, mul_one] at H
    exact H.trans (congr($(hq V hsV).hom a)).symm
  have hl' (b : P(s)) : e (b ⊗ₜ[R(s)] 1) = q.hom b :=
    RingHom.congr_fun hl b
  refine ⟨e, ?_⟩
  intro U hs hU a k
  have hr := he 1 k
  simp only [map_one, one_mul] at hr
  calc
    e (F.germ U s hs a ⊗ₜ[R(s)] k) =
        e (F.germ U s hs a ⊗ₜ[R(s)] 1) * e (1 ⊗ₜ[R(s)] k) := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = q.hom (F.germ U s hs a) *
        (f.fiberToSpecResidueField s).appTop.hom ((Scheme.ΓSpecIso (K(s))).inv.hom k) := by
          rw [hl', hr]
          rfl
    _ = _ := by
      rw [← CommRingCat.comp_apply, hq]
      rfl

end

end AlgebraicGeometry
