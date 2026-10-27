/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.BlowupSquarePullbackQuotientData
import Sheaf.AlgebraicGeometry.SupportedKernelFlatPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Flat pullback of module strict transforms

Source: Stacks Project, Divisors, Tags 080D, 0805 and 080F; Flatness, Tag 0814,
proof paragraph 1; Properties, Tag 07ZP
(blueprint: lem-trf-module-strict-transform-flat-pullback).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The map `jᵇ` induced by the square and the specified flat blowup comparison.
The first projection of the upstream comparison is the map to the old blowup;
its second projection is the blowup map over `T`.
Source: Stacks, Tags 0805 and 080D
(blueprint: lem-trf-module-strict-transform-flat-pullback). -/
noncomputable def moduleStrictTransformFlatPullbackMap {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] (I : S.IdealSheafData) :
    Limits.pullback g (I.comap e).blowupMap ⟶ Limits.pullback f I.blowupMap :=
  pullback.lift (pullback.fst g (I.comap e).blowupMap ≫ j)
    (pullback.snd g (I.comap e).blowupMap ≫
      (I.blowupFlatBaseChangeIso e).hom ≫ pullback.fst I.blowupMap e)
    (by
      simp only [Category.assoc, h, pullback.condition]
      rw [← Category.assoc (I.blowupFlatBaseChangeIso e).hom
        (pullback.snd I.blowupMap e) e, I.blowupFlatBaseChangeIso_hom_snd e]
      exact congrArg (fun k ↦ k ≫ e)
        (pullback.condition (f := g) (g := (I.comap e).blowupMap)))

/-- The canonical comparison between the ordinary iterated pullbacks.
It uses the section-normalized composition isomorphisms, and the first-projection
identity of the explicitly constructed `jᵇ`.
Source: Stacks, Tag 080D, and Sheaves, Tag 0097
(blueprint: lem-trf-module-strict-transform-flat-pullback). -/
noncomputable def moduleStrictTransformFlatPullbackSourceIso {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] (I : S.IdealSheafData) (F : X.Modules) :
    (tensorPullback (moduleStrictTransformFlatPullbackMap f e g j h I)).obj
        ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ≅
      (tensorPullback (pullback.fst g (I.comap e).blowupMap)).obj
        ((tensorPullback j).obj F) :=
  (tensorPullbackSectionComp (moduleStrictTransformFlatPullbackMap f e g j h I)
    (pullback.fst f I.blowupMap)).symm.app F ≪≫
  (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F)
    (pullback.lift_fst _ _ _))) ≪≫
  (tensorPullbackSectionComp (pullback.fst g (I.comap e).blowupMap) j).app F

/-- Sectionwise equality of ranges identifies an injective arrow with a kernel. -/
private theorem exists_kernelIso_of_range {Z : Scheme.{u}} {A B C : Z.Modules}
    (a : A ⟶ B) (r : B ⟶ C)
    (ha : ∀ W : Z.Opens, Function.Injective (a.app W))
    (hr : ∀ W : Z.Opens, Set.range (a.app W) = Set.range ((kernel.ι r).app W)) :
    ∃ κ : A ≅ kernel r, a = κ.hom ≫ kernel.ι r := by
  have hz : a ≫ r = 0 := by
    ext W s
    have hs : a.app W s ∈ Set.range ((kernel.ι r).app W) := by
      rw [← hr W]
      exact ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := hs
    change r.app W (a.app W s) = 0
    rw [← ht]
    exact ConcreteCategory.congr_hom (congrArg (fun v ↦ v.app W) (kernel.condition r)) t
  let k : A ⟶ kernel r := kernel.lift r a hz
  have hk : k ≫ kernel.ι r = a := kernel.lift_ι _ _ _
  have : IsIso k := (Hom.isIso_iff_isIso_app).2 fun W ↦ by
    apply (ConcreteCategory.isIso_iff_bijective (k.app W)).2
    constructor
    · intro x y hxy
      apply ha W
      have he := congrArg (fun t ↦ (kernel.ι r).app W t) hxy
      simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, hk] using he
    · intro t
      have ht : (kernel.ι r).app W t ∈ Set.range (a.app W) := by
        rw [hr W]
        exact ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := ht
      refine ⟨s, injective_map_kernelι W r ?_⟩
      change (kernel.ι r).app W (k.app W s) = (kernel.ι r).app W t
      simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, hk] using hs
  exact ⟨asIso k, hk.symm⟩

/-- An isomorphism carries the subsheaf of sections vanishing on an open to itself. -/
private theorem exists_kernelIso_of_supported {Z : Scheme.{u}} {A B B' C : Z.Modules}
    (U : Z.Opens) (a : A ⟶ B) (γ : B ≅ B') (r : B' ⟶ C)
    (ha : ∀ W : Z.Opens, Function.Injective (a.app W))
    (hv : ∀ (W : Z.Opens) (s : Γ(B, W)), s ∈ Set.range (a.app W) ↔
      B.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s = 0)
    (hrange : ∀ W : Z.Opens, Set.range ((kernel.ι r).app W) =
      {s | B'.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s = 0}) :
    ∃ κ : A ≅ kernel r, a ≫ γ.hom = κ.hom ≫ kernel.ι r := by
  have hγ (W) (s : Γ(B, W)) :
      s ∈ Set.range (a.app W) ↔ γ.hom.app W s ∈ Set.range ((kernel.ι r).app W) := by
    rw [hv, hrange W]
    change _ = 0 ↔ _ = 0
    have hn := ConcreteCategory.congr_hom
      (γ.hom.mapPresheaf.naturality
        (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) s
    change γ.hom.app (W ⊓ U)
      (B.presheaf.map _ s) =
        B'.presheaf.map _ (γ.hom.app W s) at hn
    rw [← hn]
    constructor
    · intro hz
      rw [hz, map_zero]
    · intro hz
      exact (ConcreteCategory.bijective_of_isIso (γ.hom.app (W ⊓ U))).1
        (hz.trans (map_zero _).symm)
  have hαγ (W) : Set.range ((a ≫ γ.hom).app W) =
      Set.range ((kernel.ι r).app W) := by
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      exact (hγ W (a.app W t)).mp ⟨t, rfl⟩
    · intro ht
      let s' := γ.inv.app W s
      have hγs : γ.hom.app W s' = s := by
        change (γ.inv ≫ γ.hom).app W s = s
        simp
      obtain ⟨t, ht'⟩ := (hγ W s').mpr (by rwa [hγs])
      refine ⟨t, ?_⟩
      change γ.hom.app W (a.app W t) = s
      rw [ht', hγs]
  exact exists_kernelIso_of_range (a ≫ γ.hom) r
    (fun W ↦ (ConcreteCategory.bijective_of_isIso (γ.hom.app W)).1.comp (ha W)) hαγ

/-- The supported-kernel statement in terms of the open on which sections vanish. -/
private theorem restrictionKernel_flatPullback {Q P : Scheme.{u}}
    (u : Q ⟶ P) [Flat u] (U : P.Opens)
    (hU : ∀ x : P, ∃ (V : P.affineOpens) (b : Γ(P, V.1)),
      x ∈ V.1 ∧ V.1 ⊓ U = P.basicOpen b)
    (H : P.Modules) (hH : H.IsQuasicoherent) :
    ∀ W : Q.Opens,
      Function.Injective (((tensorPullback u).map
        (kernel.ι ((restrictAdjunction U.ι).unit.app H))).app W) ∧
      ∀ s : Γ((tensorPullback u).obj H, W),
        s ∈ Set.range (((tensorPullback u).map
          (kernel.ι ((restrictAdjunction U.ι).unit.app H))).app W) ↔
        ((tensorPullback u).obj H).presheaf.map
          (homOfLE (inf_le_left : W ⊓ (u ⁻¹ᵁ U) ≤ W)).op s = 0 := by
  obtain ⟨D, rfl⟩ := TopologicalSpace.Closeds.compl_bijective.surjective U
  have hs := (supportedSectionsKernel_flatPullback u D hU H hH).2.2.2.1
  intro W
  refine ⟨(hs W).1, ?_⟩
  intro s
  change s ∈ Set.range (((tensorPullback u).map (supportedSectionsKernelι D H)).app W) ↔ _
  rw [(hs W).2.1]
  exact (hs W).2.2 s

/-- Strict transform commutes with flat source and base pullback, uniquely compatibly
with the quotient maps from the ordinary pullbacks. The target cokernel is exactly
`moduleStrictTransform g (I.comap e) ((tensorPullback j).obj F)` unfolded: using the
cokernel expression avoids requiring finite-type and quasi-coherence instances as
extra hypotheses for the transported objects.
Source: Stacks, Tags 080D, 0805, 080F, 0814 (proof paragraph 1), and 07ZP
(blueprint: lem-trf-module-strict-transform-flat-pullback).

Proof: (1) The flat blowup comparison identifies the new blowup with the base change
of the old one. Fibre-product associativity identifies `jᵇ` with the base change of `j`,
so it is flat. The exceptional locus on its source is the inverse image of that on
its target, since extension of an ideal commutes with its vanishing locus.
(2) Write the strict transforms as quotients of the ordinary pullbacks by their
supported-section kernels, using def-trf-module-strict-transform and
lem-trf-strict-transform-sheaf-kernel. The normalized composition comparisons give
`moduleStrictTransformFlatPullbackSourceIso` between the ordinary pullbacks.
(3) Principalization of the blowup centre gives affine charts with exceptional locus
`V(a)`. On these charts supported sections are precisely the a-power torsion, by
lem-weil-pbc-affine-module-basic-open-localization. The affine pullback-sections
bijection identifies pullback with tensor product. Flat tensor exactness identifies
the pulled-back kernel with the power-torsion kernel after base change: tensor the
exact sequence from a-power torsion into M and then M localized at a; localization
commutes with tensor. Equality on this affine basis gives equality of the sheaf kernels.
(4) Pullback is a left adjoint, hence preserves cokernels. The kernel identification
therefore induces an isomorphism of the two cokernels with the displayed quotient
identity. The pulled-back quotient is epi, so this identity determines the isomorphism
uniquely, giving canonicity. -/
theorem existsUnique_moduleStrictTransform_flatPullback {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] [Flat j]
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃! θ : (tensorPullback (moduleStrictTransformFlatPullbackMap f e g j h I)).obj
        (moduleStrictTransform f I F) ≅
      cokernel (kernel.ι
        (moduleStrictTransformRestriction g (I.comap e) ((tensorPullback j).obj F))),
      (tensorPullback (moduleStrictTransformFlatPullbackMap f e g j h I)).map
          (moduleStrictTransformπ f I F) ≫ θ.hom =
        (moduleStrictTransformFlatPullbackSourceIso f e g j h I F).hom ≫
          cokernel.π (kernel.ι
            (moduleStrictTransformRestriction g (I.comap e) ((tensorPullback j).obj F))) := by
  obtain ⟨_, _, u, hu, huq, _, hflat, hopen, hcharts, _, hdata⟩ :=
    blowupSquare_pullback_quotientData f e g j h I
  have heq : u = moduleStrictTransformFlatPullbackMap f e g j h I := by
    apply pullback.hom_ext
    · simpa only [moduleStrictTransformFlatPullbackMap, pullback.lift_fst] using hu
    · simpa only [moduleStrictTransformFlatPullbackMap, pullback.lift_snd,
        Scheme.IdealSheafData.blowupFlatBaseChangeIso, asIso_hom] using huq
  subst u
  let u := moduleStrictTransformFlatPullbackMap f e g j h I
  let H := (tensorPullback (pullback.fst f I.blowupMap)).obj F
  let γ := moduleStrictTransformFlatPullbackSourceIso f e g j h I F
  let U := moduleStrictTransformOpen f I
  let U' := moduleStrictTransformOpen g (I.comap e)
  let a := (tensorPullback u).map (kernel.ι (moduleStrictTransformRestriction f I F))
  let r := moduleStrictTransformRestriction g (I.comap e) ((tensorPullback j).obj F)
  have : Flat u := hflat
  obtain ⟨hH, _, _, _, _, _, hrange, _⟩ := hdata F
  have hD : ∀ x, ∃ (V : (Limits.pullback f I.blowupMap).affineOpens)
      (b : Γ(Limits.pullback f I.blowupMap, V.1)),
      x ∈ V.1 ∧ V.1 ⊓ U = (Limits.pullback f I.blowupMap).basicOpen b := by
    intro x
    obtain ⟨V, hx, hV, b, hb, _⟩ := hcharts x
    exact ⟨⟨V, hV⟩, b, hx, hb⟩
  have hs := restrictionKernel_flatPullback u U hD H hH
  have ha (W) : Function.Injective (a.app W) := (hs W).1
  have hv (W) (s : Γ((tensorPullback u).obj H, W)) :
      s ∈ Set.range (a.app W) ↔
      ((tensorPullback u).obj H).presheaf.map
        (homOfLE (inf_le_left : W ⊓ U' ≤ W)).op s = 0 := by
    rw [show U' = u ⁻¹ᵁ U from hopen]
    exact (hs W).2 s
  obtain ⟨κ, hκ⟩ := exists_kernelIso_of_supported U' a γ r ha hv hrange
  have : (tensorPullback u).IsLeftAdjoint := (tensorPullbackSectionAdjunction u).isLeftAdjoint
  let θ := PreservesCokernel.iso (tensorPullback u)
    (kernel.ι (moduleStrictTransformRestriction f I F)) ≪≫
    cokernel.mapIso a (kernel.ι r) κ γ hκ
  have hθ : (tensorPullback u).map (moduleStrictTransformπ f I F) ≫ θ.hom =
      γ.hom ≫ cokernel.π (kernel.ι r) := by
    dsimp only [θ, Iso.trans_hom, moduleStrictTransformπ]
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    simp only [cokernel.mapIso_hom, cokernel.map]
    change cokernel.π a ≫ cokernel.desc a _ _ = _
    exact cokernel.π_desc _ _ _
  refine ⟨θ, hθ, ?_⟩
  intro θ' hθ'
  apply Iso.ext
  have : Epi ((tensorPullback u).map (moduleStrictTransformπ f I F)) := by
    dsimp only [moduleStrictTransformπ]
    infer_instance
  apply (cancel_epi ((tensorPullback u).map (moduleStrictTransformπ f I F))).mp
  exact hθ'.trans hθ.symm

end AlgebraicGeometry.Scheme.Modules
