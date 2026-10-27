/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
import Sheaf.AlgebraicGeometry.StrictTransformDifferentCenters
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Complement

/-!
# Exceptional support after two module strict transforms

Source: Stacks Project, Divisors, Tag 080I, final proof paragraph; Tag 080H (2);
Tag 02OS (blueprint: lem-trf-iterated-transform-exceptional-support).

The second transform is transported along the canonical fibre-product isomorphism
onto `X ×[S] J.blowup`. The open below is the complement of the inverse image of
both exceptional loci, and the theorem concerns sections on every open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem mono_of_app_injective {Y : Scheme.{u}} {M N : Y.Modules}
    (a : M ⟶ N) (ha : ∀ W : Y.Opens, Function.Injective (a.app W)) : Mono a where
  right_cancellation {Z} b c h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext s
    apply ha W.unop
    exact congrArg (fun q : Z ⟶ N ↦ q.app W.unop s) h

private theorem app_injective_of_mono {Y : Scheme.{u}} {M N : Y.Modules}
    (a : M ⟶ N) [Mono a] (W : Y.Opens) : Function.Injective (a.app W) := by
  exact (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation Y.ringCatSheaf (.op W)).map a)).mp inferInstance

private theorem unit_mono_of_mono {Y : Scheme.{u}} (U : Y.Opens)
    {M N : Y.Modules} (a : M ⟶ N) [Mono a]
    [Mono ((restrictAdjunction U.ι).unit.app N)] :
    Mono ((restrictAdjunction U.ι).unit.app M) := by
  exact mono_of_mono_fac ((restrictAdjunction U.ι).unit.naturality a).symm

private theorem unit_mono_of_kernel_eq {Y : Scheme.{u}} (M : Y.Modules)
    (U V : Y.Opens)
    (h : kernelSubobject ((restrictAdjunction U.ι).unit.app M) =
      kernelSubobject ((restrictAdjunction V.ι).unit.app M)) :
    Mono ((restrictAdjunction V.ι).unit.app
      (cokernel (kernel.ι ((restrictAdjunction U.ι).unit.app M)))) := by
  let r := (restrictAdjunction U.ι).unit.app M
  let t := (restrictAdjunction V.ι).unit.app M
  let e := Subobject.isoOfMkEqMk (kernel.ι r) (kernel.ι t) h
  let q := cokernel.mapIso (kernel.ι r) (kernel.ι t) e (Iso.refl M)
    (by simp [e])
  have : IsIso ((restrictAdjunction V.ι).unit.app
      ((pushforward V.ι).obj ((restrictFunctor V.ι).obj M))) :=
    (restrictAdjunction V.ι).isIso_unit_app_of_iso (Iso.refl _)
  have hN : Mono ((restrictAdjunction V.ι).unit.app
      ((restrictFunctor V.ι ⋙ pushforward V.ι).obj M)) := by
    change Mono ((restrictAdjunction V.ι).unit.app
      ((pushforward V.ι).obj ((restrictFunctor V.ι).obj M)))
    infer_instance
  exact unit_mono_of_mono V (q.hom ≫ Abelian.factorThruCoimage t)

private theorem unit_mono_restrict {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    [IsOpenImmersion g] (M : Y.Modules) (U : Y.Opens)
    [Mono ((restrictAdjunction U.ι).unit.app M)] :
    Mono ((restrictAdjunction (g ⁻¹ᵁ U).ι).unit.app ((restrictFunctor g).obj M)) := by
  apply mono_of_app_injective
  intro W
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  apply (app_injective_of_mono ((restrictAdjunction U.ι).unit.app M) (g ''ᵁ W))
  rw [map_zero]
  simp only [restrictAdjunction_unit_app_app] at hs ⊢
  change M.presheaf.map _ s = 0 at hs ⊢
  have he : g ''ᵁ ((g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ W)) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ W)) := by
    ext x
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    constructor
    · rintro ⟨z, ⟨hzU, hzW⟩, rfl⟩
      exact ⟨hzU, z, hzW, rfl⟩
    · rintro ⟨hxU, z, hzW, rfl⟩
      exact ⟨z, ⟨hxU, hzW⟩, rfl⟩
  have hh : M.presheaf.map
      (homOfLE (g.image_mono ((g ⁻¹ᵁ U).ι.image_preimage_le W))).op ≫
      M.presheaf.map (eqToHom he.symm).op =
      M.presheaf.map (homOfLE (U.ι.image_preimage_le (g ''ᵁ W))).op := by
    rw [← Functor.map_comp]
    rfl
  change M.presheaf.map
    (homOfLE (g.image_mono ((g ⁻¹ᵁ U).ι.image_preimage_le W))).op s = 0 at hs
  rw [← hh]
  change M.presheaf.map (eqToHom he.symm).op (M.presheaf.map _ s) = 0
  exact (congrArg (fun t ↦ M.presheaf.map (eqToHom he.symm).op t) hs).trans (map_zero _)

private theorem unit_mono_tensorPullback {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    [IsOpenImmersion g] (M : Y.Modules) (U : Y.Opens)
    [Mono ((restrictAdjunction U.ι).unit.app M)] :
    Mono ((restrictAdjunction (g ⁻¹ᵁ U).ι).unit.app ((tensorPullback g).obj M)) := by
  let e := ((nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (restrictAdjunction g)).app M
  have := unit_mono_restrict g M U
  exact unit_mono_of_mono (g ⁻¹ᵁ U) e.hom

private theorem exceptional_support_set {S : Scheme.{u}} (I : S.IdealSheafData)
    (J : I.blowup.IdealSheafData) :
    J.blowupMap ⁻¹' ((J.support : Set I.blowup) ∪
        I.blowupMap ⁻¹' (I.support : Set S)) =
      (J.blowupMap ≫ I.blowupMap) ⁻¹' ((I.support : Set S) ∪
        I.blowupMap '' (J.support : Set I.blowup)) := by
  have := I.isIso_blowupMap_restrict_support_compl
  ext t
  change (J.blowupMap t ∈ J.support ∨ I.blowupMap (J.blowupMap t) ∈ I.support) ↔
    (I.blowupMap (J.blowupMap t) ∈ I.support ∨
      I.blowupMap (J.blowupMap t) ∈ I.blowupMap '' (J.support : Set I.blowup))
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨_, h, rfl⟩
    · exact Or.inl h
  · rintro (h | ⟨z, hz, he⟩)
    · exact Or.inr h
    · by_cases ht : I.blowupMap (J.blowupMap t) ∈ I.support
      · exact Or.inr ht
      · have hz' : I.blowupMap z ∉ I.support := by simpa [he] using ht
        have hzt : z = J.blowupMap t := by
          have hp : (⟨z, hz'⟩ : I.blowupMap ⁻¹ᵁ I.support.compl) =
              ⟨J.blowupMap t, ht⟩ := by
            apply (I.blowupMap ∣_ I.support.compl).homeomorph.injective
            apply Subtype.ext
            simpa only [Scheme.Hom.homeomorph_apply, morphismRestrict_base_coe] using he
          exact congrArg Subtype.val hp
        exact Or.inl (hzt ▸ hz)

private theorem transported_open_eq {Y T : Scheme.{u}} (f : Y ⟶ T)
    (J D : T.IdealSheafData) (φ : (J * D).blowup ≅ J.blowup)
    (hφ : φ.hom ≫ J.blowupMap = (J * D).blowupMap) :
    moduleStrictTransformTransportedOpen f J D φ hφ =
      (pullback.snd f J.blowupMap ≫ J.blowupMap) ⁻¹ᵁ
        (J.support.compl ⊓ D.support.compl) := by
  let e := moduleStrictTransformCenterIso f J D φ hφ
  have he : e.hom ≫ pullback.snd f J.blowupMap ≫ J.blowupMap =
      pullback.snd f (J * D).blowupMap ≫ (J * D).blowupMap := by
    dsimp [e, moduleStrictTransformCenterIso]
    simp [hφ]
  have he' : e.inv ≫ pullback.snd f (J * D).blowupMap ≫ (J * D).blowupMap =
      pullback.snd f J.blowupMap ≫ J.blowupMap := by
    rw [← he]
    simp
  unfold moduleStrictTransformTransportedOpen moduleStrictTransformOpen
  rw [← Scheme.Hom.comp_preimage, he']
  congr 1
  ext x
  change x ∉ ((J * D).support : Set T) ↔
    x ∉ (J.support : Set T) ∧ x ∉ (D.support : Set T)
  simp only [IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup,
    Set.mem_union, not_or]

/-- Apply the recorded module strict transform twice and transport the result onto
`X ×[S] S₂` using the inverse of the canonical fibre-product pasting isomorphism.
Quasi-coherence of the first transform is supplied by the recorded kernel theorem,
not assumed as extra data. The transport is the tensor pullback along an isomorphism.
Source: Stacks Project, Divisors, Tag 080I, proof and its displayed diagram
(blueprint: lem-trf-iterated-transform-exceptional-support). -/
noncomputable def moduleIteratedStrictTransform {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    (Limits.pullback f (J.blowupMap ≫ I.blowupMap)).Modules :=
  letI : (moduleStrictTransform f I F).IsQuasicoherent :=
    (moduleStrictTransform_properties f I F).2.2.2.1
  (tensorPullback (pullbackLeftPullbackSndIso f I.blowupMap J.blowupMap).inv).obj
    (moduleStrictTransform (pullback.snd f I.blowupMap) J (moduleStrictTransform f I F))

/-- The complement of `f₂⁻¹ c⁻¹ (V(J) ∪ b⁻¹ V(I))` in `X ×[S] S₂`.
Intersections of complementary opens express the complement of the union without
requiring a choice of a closed subscheme structure on that union.
Source: Stacks Project, Divisors, Tag 080I, final proof paragraph
(blueprint: lem-trf-iterated-transform-exceptional-support). -/
noncomputable def moduleIteratedStrictTransformOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (J : I.blowup.IdealSheafData) :
    (Limits.pullback f (J.blowupMap ≫ I.blowupMap)).Opens :=
  (pullback.snd f (J.blowupMap ≫ I.blowupMap) ≫ J.blowupMap) ⁻¹ᵁ
    (J.support.compl ⊓ (I.blowupMap ⁻¹ᵁ I.support.compl))

/-- The second module strict transform has no nonzero local sections supported on the
inverse image of the union of the two exceptional loci. The second conjunct is the
asserted equality of subsets of `S₂`. The restriction-adjunction unit on an open `W`
is exactly restriction to `W` intersected with the complementary open above.

Source: Stacks Project, Divisors, Tag 080I, final proof paragraph; Tag 080H (2);
Tag 02OS (blueprint: lem-trf-iterated-transform-exceptional-support).

Proof:
1. By thm-nagata-blowup-principalizes-center, `L = I O_{S₁}` is an effective Cartier
ideal with support `E = b⁻¹ V(I)`. By lem-trf-strict-transform-sheaf-kernel the first
transform is quasi-coherent and has no nonzero local sections supported over `E`.
2. The ideal `J L` is finite type: locally, if `L = (e)` and `J = (a₁, …, aᵣ)`,
its generators are `e a₁, …, e aᵣ`. Its support is `V(J) ∪ E`.
lemma-nagata-blowup-invertible-factor identifies its blowup with that of `J` over `S₁`.
Apply lem-trf-strict-transform-different-centers to the first transform with this
Cartier divisor. The two quotient kernels agree on their canonically identified
pullbacks, so their quotient modules are canonically isomorphic.
3. By lem-trf-strict-transform-sheaf-kernel the transform for `J L` has no sections
supported over `V(J) ∪ E`. Transport through the quotient isomorphism and the canonical
fibre-product isomorphism of def-pc-fibre-product. Restrictions commute with these
isomorphisms, giving the asserted implication for every `W`, without compactness.
4. For the set equality, one inclusion follows directly from taking images under `b`.
Conversely, if `b(c(t))` is in `V(I)`, then `c(t)` is in `E`. Otherwise, if it is the
image of a point `z` of `V(J)`, thm-nagata-global-blowup-complement makes `b` an
isomorphism over `S \ V(I)`. Its fibre there has a single point, hence `c(t) = z`.
This gives the other inclusion. -/
theorem moduleIteratedStrictTransform_no_exceptional_sections {X S : Scheme.{u}}
    (f : X ⟶ S) (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    (∀ (W : (Limits.pullback f (J.blowupMap ≫ I.blowupMap)).Opens)
      (s : Γ(moduleIteratedStrictTransform f I J F, W)),
      ((restrictAdjunction (moduleIteratedStrictTransformOpen f I J).ι).unit.app
        (moduleIteratedStrictTransform f I J F)).app W s = 0 → s = 0) ∧
    J.blowupMap ⁻¹' ((J.support : Set I.blowup) ∪
        I.blowupMap ⁻¹' (I.support : Set S)) =
      (J.blowupMap ≫ I.blowupMap) ⁻¹' ((I.support : Set S) ∪
        I.blowupMap '' (J.support : Set I.blowup)) := by
  let F₁ := moduleStrictTransform f I F
  have hF₁ : F₁.IsQuasicoherent := (moduleStrictTransform_properties f I F).2.2.2.1
  let D := I.comap I.blowupMap
  have hD : D.IsInvertible := I.isInvertible_comap_blowupMap
  have hDopen : (pullback.snd f I.blowupMap) ⁻¹ᵁ D.support.compl =
      moduleStrictTransformOpen f I := by
    ext x
    simp [D, moduleStrictTransformOpen, IdealSheafData.support_comap]
  have hmono : Mono ((restrictAdjunction
      ((pullback.snd f I.blowupMap) ⁻¹ᵁ D.support.compl).ι).unit.app F₁) := by
    rw [hDopen]
    apply mono_of_app_injective
    intro W
    apply (injective_iff_map_eq_zero _).mpr
    exact (moduleStrictTransform_properties f I F).2.2.2.2.2 W
  obtain ⟨φ, hφ⟩ : ∃ φ : (J * D).blowup ≅ J.blowup,
      φ.hom ≫ J.blowupMap = (J * D).blowupMap := by
    have hcomm : J * D = D * J := mul_comm _ _
    rw [hcomm]
    exact IdealSheafData.exists_blowup_mul_isInvertible_iso hD J
  have hk := moduleStrictTransform_kernel_eq_of_cartier_factor
    (pullback.snd f I.blowupMap) J D hD φ hφ F₁ hmono
  have hmono₂ : Mono ((restrictAdjunction
      (moduleStrictTransformTransportedOpen (pullback.snd f I.blowupMap) J D φ hφ).ι).unit.app
        (moduleStrictTransform (pullback.snd f I.blowupMap) J F₁)) :=
    unit_mono_of_kernel_eq
      ((tensorPullback (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj F₁)
      (moduleStrictTransformOpen (pullback.snd f I.blowupMap) J)
      (moduleStrictTransformTransportedOpen (pullback.snd f I.blowupMap) J D φ hφ) hk
  let a := (pullbackLeftPullbackSndIso f I.blowupMap J.blowupMap).inv
  have hmono₃ := unit_mono_tensorPullback a
    (moduleStrictTransform (pullback.snd f I.blowupMap) J F₁)
    (moduleStrictTransformTransportedOpen (pullback.snd f I.blowupMap) J D φ hφ)
  have hopen : a ⁻¹ᵁ
      moduleStrictTransformTransportedOpen (pullback.snd f I.blowupMap) J D φ hφ =
      moduleIteratedStrictTransformOpen f I J := by
    rw [transported_open_eq, ← Scheme.Hom.comp_preimage]
    simp only [a, pullbackLeftPullbackSndIso_inv_snd_snd_assoc]
    ext x
    simp [D, moduleIteratedStrictTransformOpen, IdealSheafData.support_comap]
  constructor
  · intro W s hs
    have hmono₄ : Mono ((restrictAdjunction
        (moduleIteratedStrictTransformOpen f I J).ι).unit.app
          (moduleIteratedStrictTransform f I J F)) := by
      rw [← hopen]
      exact hmono₃
    exact (app_injective_of_mono _ W) (hs.trans (map_zero _).symm)
  · exact exceptional_support_set I J

end AlgebraicGeometry.Scheme.Modules
