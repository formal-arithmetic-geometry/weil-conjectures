/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Blowup.FiniteDegree.Algebra
import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel

/-! # Transport of strict-transform kernels under a Cartier factor

Source: Stacks Project, Divisors, Tags 080H (1), the geometric reduction in (2),
and 080D (1); Sheaves, Tags 0095 and 0097
(blueprint: lem-trf-cartier-factor-kernel-transport).

The two kernels remain distinct included submodules of the common pullback.
The existential isomorphisms below are specified by the canonical fibre-product map
and the normalized tensor-pullback composition comparison. The included module `KD`
is identified with the product-centre kernel by an isomorphism commuting with inclusions.
No condition on sections of `F` supported on the Cartier divisor is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem idealModule_quasicoherent {S : Scheme.{u}} (I : S.IdealSheafData) :
    I.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated I.subschemeι _
  exact isQuasicoherent_kernel I.toPushforwardSubscheme

private theorem ideal_finiteType {S : Scheme.{u}} (I : S.IdealSheafData)
    [I.toModules.IsFiniteType] : I.ofFiniteType := by
  have := idealModule_quasicoherent I
  intro U _
  have : Module.Finite Γ(S, U.1) Γ(I.toModules, U.1) :=
    finite_sections_of_finiteType I.toModules U.2
  have hr : LinearMap.range (I.toModulesι.val.app (op U.1)).hom = I.ideal U := by
    ext x
    exact Set.ext_iff.mp (I.range_toModulesι_app U) x
  rw [← hr]
  let l : Γ(I.toModules, U.1) →ₗ[Γ(S, U.1)] Γ(S, U.1) :=
    (I.toModulesι.val.app (op U.1)).hom
  exact Submodule.fg_range l

private theorem invertibleIdeal_finiteType {S : Scheme.{u}} (J : S.IdealSheafData)
    (hJ : J.IsInvertible) : J.ofFiniteType := by
  classical
  choose U hx hU using hJ
  have hcover : (⨆ x : S, (U x).1) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hlocal (x : S) : J.ofFiniteTypeOn (U x).1 := by
    intro V hV
    obtain ⟨a, _, ha⟩ := hU x
    rw [← J.map_ideal hV, ha]
    rw [Ideal.map_span, Set.image_singleton]
    exact Submodule.fg_span_singleton _
  have h := Scheme.IdealSheafData.ofFiniteTypeOn.iSup hlocal
  rwa [hcover] at h

private theorem cartierProduct_finiteType {S : Scheme.{u}} (I J : S.IdealSheafData)
    [I.toModules.IsFiniteType] (hJ : J.IsInvertible) :
    (I * J).toModules.IsQuasiCoherentFiniteType := by
  exact ⟨idealModule_quasicoherent (I * J),
    (I * J).isFiniteType_toModules_sheaf
      ((ideal_finiteType I).mul (invertibleIdeal_finiteType J hJ))⟩

private theorem supportedKernel_sections {T : Scheme.{u}} (H : T.Modules)
    (U V : T.Opens) (s : Γ(H, V)) :
    s ∈ Set.range ((kernel.ι ((restrictAdjunction U.ι).unit.app H)).app V) ↔
      H.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s = 0 := by
  have hr := Set.ext_iff.mp (range_map_kernelι V ((restrictAdjunction U.ι).unit.app H)) s
  change s ∈ Set.range ((kernel.ι ((restrictAdjunction U.ι).unit.app H)).app V) ↔
    H.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op s = 0 at hr
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V ⊓ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  let k : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) ⟶ V ⊓ U := eqToHom he
  have hm : H.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op =
      H.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op ≫
        H.presheaf.map k.op := by
    rw [← Functor.map_comp]
    congr 1
  refine hr.trans ?_
  rw [hm]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (H.presheaf.map k.op)).1

private theorem supportedKernel_transport {Y T : Scheme.{u}} (α : Y ≅ T)
    (H : T.Modules) (HD : Y.Modules) (θ : (tensorPullback α.hom).obj H ≅ HD)
    (U : T.Opens) (W : Y.Opens) (hW : α.hom ⁻¹ᵁ U = W)
    (hK : (kernel ((restrictAdjunction W.ι).unit.app HD)).IsQuasicoherent) :
    ∃ (KD : T.Modules) (ιD : KD ⟶ H), Mono ιD ∧ KD.IsQuasicoherent ∧
      (∃ eD : (tensorPullback α.hom).obj KD ≅
          kernel ((restrictAdjunction W.ι).unit.app HD),
        (tensorPullback α.hom).map ιD ≫ θ.hom =
          eD.hom ≫ kernel.ι ((restrictAdjunction W.ι).unit.app HD)) ∧
      (∀ (V : T.Opens) (s : Γ(H, V)), s ∈ Set.range (ιD.app V) ↔
        H.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s = 0) := by
  subst W
  classical
  let L := tensorPullback α.hom
  let R := pushforward α.hom
  let E : T.Modules ≌ Y.Modules :=
    CategoryTheory.Equivalence.mk (pushforward α.inv) R
      ((pushforwardId T).symm ≪≫ pushforwardCongr (by simp) ≪≫
        (pushforwardComp _ _).symm)
      (pushforwardComp _ _ ≪≫ pushforwardCongr (by simp) ≪≫ pushforwardId Y)
  let : R.IsEquivalence := inferInstanceAs E.inverse.IsEquivalence
  let adj := tensorPullbackSectionAdjunction α.hom
  let c : H ≅ R.obj HD := asIso (adj.unit.app H) ≪≫ R.mapIso θ
  let q := (restrictAdjunction (α.hom ⁻¹ᵁ U).ι).unit.app HD
  let K := kernel q
  let i := kernel.ι q
  let KD := R.obj K
  let ιD : KD ⟶ H := R.map i ≫ c.inv
  have : K.IsQuasicoherent := hK
  have : KD.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated α.hom K
  have hmono : Mono ιD := by dsimp only [ιD]; infer_instance
  let eD : L.obj KD ≅ K := asIso (adj.counit.app K)
  have hc : ιD ≫ c.hom = R.map i := by simp [ιD]
  have htransport : L.map ιD ≫ θ.hom = eD.hom ≫ i := by
    have h := adj.counit.naturality i
    have hθ : L.map c.inv ≫ θ.hom = adj.counit.app HD := by
      apply (cancel_epi (L.map c.hom)).mp
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
      change L.map (𝟙 H) ≫ θ.hom = L.map c.hom ≫ adj.counit.app HD
      rw [L.map_id, Category.id_comp]
      have hn : L.map (R.map θ.hom) ≫ adj.counit.app HD =
          adj.counit.app (L.obj H) ≫ θ.hom := adj.counit.naturality θ.hom
      change θ.hom = L.map (adj.unit.app H ≫ R.map θ.hom) ≫ adj.counit.app HD
      have ht : L.map (adj.unit.app H) ≫ adj.counit.app (L.obj H) = 𝟙 _ :=
        adj.left_triangle_components H
      rw [L.map_comp, Category.assoc, hn, ← Category.assoc, ht, Category.id_comp]
    dsimp only [ιD, eD, asIso_hom]
    rw [Functor.map_comp, Category.assoc, hθ]
    exact h
  refine ⟨KD, ιD, hmono, inferInstance, ⟨eD, htransport⟩, ?_⟩
  intro V s
  have hrange : s ∈ Set.range (ιD.app V) ↔
      c.hom.app V s ∈ Set.range (i.app (α.hom ⁻¹ᵁ V)) := by
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      exact (congrArg (fun k ↦ k.app V t) hc).symm
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      apply (ConcreteCategory.bijective_of_isIso (c.hom.app V)).1
      exact (congrArg (fun k ↦ k.app V t) hc).trans ht
  rw [hrange]
  have hs := supportedKernel_sections HD (α.hom ⁻¹ᵁ U) (α.hom ⁻¹ᵁ V)
    (c.hom.app V s)
  refine hs.trans ?_
  have hn := Hom.app_presheaf_map c.hom (homOfLE (inf_le_left : V ⊓ U ≤ V)) s
  change c.hom.app (V ⊓ U)
      (H.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s) =
    HD.presheaf.map
      (homOfLE (inf_le_left : α.hom ⁻¹ᵁ V ⊓ α.hom ⁻¹ᵁ U ≤ α.hom ⁻¹ᵁ V)).op
        (c.hom.app V s) at hn
  rw [← hn]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (c.hom.app (V ⊓ U))).1

/-- Cartier multiplication transports the two strict-transform quotient kernels to
quasi-coherent included submodules of the same ambient pullback. Ideal sheaf data encode
the closed subschemes `Z` and `D`; `J.IsInvertible` is the recorded affine-local regular
principal condition for an effective Cartier ideal and the existing invertible-ideal predicate.

The original kernel is the existing `moduleStrictTransformKernel`. Its inclusion and
that of `KD` are specified on sections by their images. These are also the kernels of
the defining quotient maps: each strict transform is the cokernel of its kernel inclusion
in the abelian category of module sheaves. The isomorphism `eD` identifies the inclusion
of `KD` with the product-centre kernel inclusion after the specified pullback comparison.
Thus both the submodules and their inclusions are retained.

Source: Stacks Project, Divisors, Tag 080H (1) and the geometric reduction in (2);
Tag 080D (1); Sheaves, Tags 0095 and 0097
(blueprint: lem-trf-cartier-factor-kernel-transport).

Proof:
1. Locally `J = (x)` with `x` a nonzerodivisor. Multiplication by `x` identifies `I`
with `I * J`; local finite generators of `I` give finite generators of the product.
This gives the invertible-ideal condition for `J` and finite-type quasi-coherence of the
product. Primality gives `V(I * J) = V(I) ∪ V(J)`.
2. The specified blowup isomorphism induces the fibre-product isomorphism `α` and the
projection equality `hα`. Composition of the normalized tensor pullbacks gives `θ`.
3. Apply lem-trf-strict-transform-sheaf-kernel to both centres. Their quotient kernels
are the existing supported-section kernels and are quasi-coherent.
4. On every open `V`, the pullback unit along `α`, followed by `θ`, identifies sections
of the common ambient pullback with product-centre sections on `α⁻¹(V)`. Its inverse
comes from `α⁻¹` and `θ⁻¹`. These identifications commute with restrictions and inclusions.
Transport the second kernel through these section identifications to obtain `KD` and `ιD`.
5. The projection equalities and `V(I * J) = V(I) ∪ V(J)` identify the transported
complement with the complement of the inverse image of that union. Restriction
compatibility proves the second displayed section formula; the first is the original
kernel formula. The inclusion equation with `eD` expresses the same transport as modules.
6. Pullback of the second quasi-coherent kernel along `α⁻¹` is quasi-coherent by
lem-weil-pbc-module-pullback-quasi-coherent, and the section identifications identify it
with `KD`. No equality of the two kernels or torsion hypothesis on `F` is used. -/
theorem moduleStrictTransform_cartierFactor_kernel_transport {X S : Scheme.{u}}
    (f : X ⟶ S) (I J : S.IdealSheafData) [I.toModules.IsFiniteType]
    (hJ : J.IsInvertible) (φ : (I * J).blowup ≅ I.blowup)
    (hφ : φ.hom ≫ I.blowupMap = (I * J).blowupMap)
    (F : X.Modules) [F.IsQuasicoherent] :
    J.IsInvertible ∧
    (I * J).toModules.IsQuasiCoherentFiniteType ∧
    ∃ (α : Limits.pullback f (I * J).blowupMap ≅ Limits.pullback f I.blowupMap)
      (hα : α.hom ≫ pullback.fst f I.blowupMap = pullback.fst f (I * J).blowupMap),
      α.hom = pullback.map f (I * J).blowupMap f I.blowupMap (𝟙 X) φ.hom (𝟙 S)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id (I * J).blowupMap).trans hφ.symm) ∧
      ∃ θ : (tensorPullback α.hom).obj
          ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ≅
            (tensorPullback (pullback.fst f (I * J).blowupMap)).obj F,
        θ = (tensorPullbackSectionComp α.hom (pullback.fst f I.blowupMap)).symm.app F ≪≫
          eqToIso (congrArg (fun g ↦ (tensorPullback g).obj F) hα) ∧
        (moduleStrictTransformKernel f I F).IsQuasicoherent ∧
        ∃ (KD : (Limits.pullback f I.blowupMap).Modules)
          (ιD : KD ⟶ (tensorPullback (pullback.fst f I.blowupMap)).obj F),
          Mono ιD ∧ KD.IsQuasicoherent ∧
          (∃ eD : (tensorPullback α.hom).obj KD ≅ moduleStrictTransformKernel f (I * J) F,
            (tensorPullback α.hom).map ιD ≫ θ.hom =
              eD.hom ≫ kernel.ι (moduleStrictTransformRestriction f (I * J) F)) ∧
          (∀ (V : (Limits.pullback f I.blowupMap).Opens)
            (s : Γ((tensorPullback (pullback.fst f I.blowupMap)).obj F, V)),
            s ∈ Set.range ((kernel.ι (moduleStrictTransformRestriction f I F)).app V) ↔
              ((tensorPullback (pullback.fst f I.blowupMap)).obj F).presheaf.map
                (homOfLE (inf_le_left :
                  V ⊓ (pullback.snd f I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ I.support.compl ≤
                    V)).op s = 0) ∧
          (∀ (V : (Limits.pullback f I.blowupMap).Opens)
            (s : Γ((tensorPullback (pullback.fst f I.blowupMap)).obj F, V)),
            s ∈ Set.range (ιD.app V) ↔
              ((tensorPullback (pullback.fst f I.blowupMap)).obj F).presheaf.map
                (homOfLE (inf_le_left :
                  V ⊓ (pullback.snd f I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ
                    (I.support ⊔ J.support).compl ≤ V)).op s = 0) := by
  classical
  have hIJ := cartierProduct_finiteType I J hJ
  have : (I * J).toModules.IsFiniteType := hIJ.2
  let a := pullback.map f (I * J).blowupMap f I.blowupMap (𝟙 X) φ.hom (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id (I * J).blowupMap).trans hφ.symm)
  let α := asIso a
  have hα : α.hom ≫ pullback.fst f I.blowupMap =
      pullback.fst f (I * J).blowupMap := by
    dsimp only [α, a, asIso_hom]
    simp only [Limits.pullback.map, Limits.pullback.lift_fst, Category.comp_id]
  let θ := (tensorPullbackSectionComp α.hom (pullback.fst f I.blowupMap)).symm.app F ≪≫
    eqToIso (congrArg (fun g ↦ (tensorPullback g).obj F) hα)
  refine ⟨hJ, hIJ, α, hα, rfl, θ, rfl,
    (moduleStrictTransform_properties f I F).2.2.1, ?_⟩
  let U := (pullback.snd f I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ
    (I.support ⊔ J.support).compl
  have hU : α.hom ⁻¹ᵁ U = moduleStrictTransformOpen f (I * J) := by
    change (α.hom ≫ (pullback.snd f I.blowupMap ≫ I.blowupMap)) ⁻¹ᵁ
      (I.support ⊔ J.support).compl = _
    have hw : α.hom ≫ (pullback.snd f I.blowupMap ≫ I.blowupMap) =
        pullback.snd f (I * J).blowupMap ≫ (I * J).blowupMap := by
      rw [← pullback.condition, ← Category.assoc, hα, pullback.condition]
    rw [hw]
    rfl
  have hK := (moduleStrictTransform_properties f (I * J) F).2.2.1
  obtain ⟨KD, ιD, hm, hqc, he, hs⟩ := supportedKernel_transport α _ _ θ U
    (moduleStrictTransformOpen f (I * J)) hU hK
  refine ⟨KD, ιD, hm, hqc, he, ?_, hs⟩
  intro V s
  exact supportedKernel_sections _ (moduleStrictTransformOpen f I) V s

end AlgebraicGeometry.Scheme.Modules
