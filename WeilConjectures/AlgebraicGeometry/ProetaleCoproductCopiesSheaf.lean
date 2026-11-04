/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Maps into a coproduct of copies represent the constant pro-étale sheaf

Let `p : V ⟶ X` be weakly étale and let `S` be a `u`-small set of labels. On the localized
pro-étale site over `V`, the presheaf `W ↦ Hom_V(W, ∐_S V)` is a sheaf (it is representable and
the pro-étale topology is subcanonical), and the labelled components `W ⟶ V ⟶ ∐_S V` exhibit it
as the sheafification of the constant presheaf `S`: the clopen decomposition of a map into the
coproduct gives local surjectivity, and disjointness of the components gives local injectivity.

Consequently, a trivialization `F|_V ≅ S` of a pro-étale sheaf `F` turns into natural bijections
`Hom_V(W, ∐_S V) ≃ F(W)` sending the labelled components to the sections of the constant sheaf.

Source: Stacks Project, Tags 098Z, 03P5 and 03YW
(blueprint: lem-sfb-proetale-constant-split-descent-data, steps 3 and 4).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The codiagonal of a coproduct of copies of a scheme is weakly étale: on each component it is
the identity.
Source: Stacks Project, Tag 03YW (auxiliary; not a blueprint node). -/
instance weaklyEtale_sigmaDesc_id (V : Scheme.{u}) (S : Type w) [Small.{u} S] :
    WeaklyEtale (Sigma.desc fun _ : S ↦ 𝟙 V) :=
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

namespace Scheme.ProEt

variable {X V : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p] (S : Type w) [Small.{u} S]


/-- The coproduct `∐_S V` of copies of `V`, as an object of the localized pro-étale site over
`V`, via the codiagonal.
Source: Stacks Project, Tags 098Z and 03YW (auxiliary; not a blueprint node). -/
noncomputable def coproductCopiesOver : Over (ProEt.mk p) :=
  Over.mk (MorphismProperty.Over.homMk (Sigma.desc fun _ : S ↦ 𝟙 V) rfl :
    ProEt.mk (Sigma.desc (fun _ : S ↦ 𝟙 V) ≫ p) ⟶ ProEt.mk p)

/-- The labelled component `W ⟶ V ⟶ ∐_S V` of an object of the localized pro-étale site.
Source: Stacks Project, Tag 03YW (auxiliary; not a blueprint node). -/
noncomputable def coproductCopiesLabel (W : Over (ProEt.mk p)) (s : S) :
    W ⟶ coproductCopiesOver p S :=
  Over.homMk (MorphismProperty.Over.homMk (W.hom.left ≫ Sigma.ι (fun _ : S ↦ V) s) (by
    dsimp [coproductCopiesOver]
    simpa using MorphismProperty.Over.w W.hom))
    (MorphismProperty.Over.Hom.ext ((Category.assoc _ _ _).trans
    ((congrArg (W.hom.left ≫ ·) (Sigma.ι_desc (fun _ : S ↦ 𝟙 V) s)).trans (Category.comp_id _))))

lemma coproductCopiesLabel_left_left (W : Over (ProEt.mk p)) (s : S) :
    (coproductCopiesLabel p S W s).left.left = W.hom.left ≫ Sigma.ι (fun _ : S ↦ V) s :=
  rfl

/-- Morphisms to `coproductCopiesOver p S` in the localized pro-étale site are the morphisms of
schemes over `V` to the coproduct.
Source: Stacks Project, Tag 098Z (auxiliary; not a blueprint node). -/
noncomputable def coproductCopiesOverHomEquiv (W : Over (ProEt.mk p)) :
    (W ⟶ coproductCopiesOver p S) ≃
      ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶
        Over.mk (Sigma.desc fun _ : S ↦ 𝟙 V)) where
  toFun g := Over.homMk g.left.left (congrArg (fun k ↦ k.left) (Over.w g))
  invFun f := Over.homMk (MorphismProperty.Over.homMk f.left (by
    have h₁ : f.left ≫ Sigma.desc (fun _ : S ↦ 𝟙 V) = W.hom.left := Over.w f
    have h₂ : W.hom.left ≫ p = W.left.hom := MorphismProperty.Over.w W.hom
    dsimp [coproductCopiesOver, ProEt.mk_hom]
    rw [← h₂, ← h₁, Category.assoc]
    rfl)) (MorphismProperty.Over.Hom.ext (Over.w f))
  left_inv g := by
    ext
    exact MorphismProperty.Over.Hom.ext rfl
  right_inv f := by
    ext
    rfl

/-- Restricting a labelled component along a morphism of the localized site gives the labelled
component with the same label.
Source: Stacks Project, Tag 03YW (auxiliary; not a blueprint node). -/
@[reassoc (attr := simp)]
lemma comp_coproductCopiesLabel {W W' : Over (ProEt.mk p)} (g : W' ⟶ W) (s : S) :
    g ≫ coproductCopiesLabel p S W s = coproductCopiesLabel p S W' s :=
  Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext (by
    rw [Over.comp_left, comp_left, coproductCopiesLabel_left_left,
      coproductCopiesLabel_left_left, ← Category.assoc, ← comp_left, Over.w g]))

section Sheaf

variable [UnivLE.{u, w}]

/-- The labelled components, as a morphism from the constant presheaf with value `S` to the
presheaf represented by `coproductCopiesOver p S`.
Source: Stacks Project, Tag 03YW (auxiliary; not a blueprint node). -/
noncomputable def coproductCopiesLabelNatTrans :
    (Functor.const (Over (ProEt.mk p))ᵒᵖ).obj S ⟶
      shrinkYoneda.{w}.obj (coproductCopiesOver p S) where
  app W := ↾fun s ↦ shrinkYonedaObjObjEquiv.{w}.symm (coproductCopiesLabel p S W.unop s)
  naturality W W' g := by
    ext s
    dsimp
    rw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm, comp_coproductCopiesLabel]

lemma coproductCopiesLabelNatTrans_app (W : (Over (ProEt.mk p))ᵒᵖ) (s : S) :
    (coproductCopiesLabelNatTrans p S).app W s =
      shrinkYonedaObjObjEquiv.{w}.symm (coproductCopiesLabel p S W.unop s) :=
  rfl

/-- The presheaf represented by `coproductCopiesOver p S` is a sheaf for the pro-étale topology,
since the pro-étale topology is subcanonical.
Source: Stacks Project, Tags 03P5 and 098Z (auxiliary; not a blueprint node). -/
noncomputable def coproductCopiesSheaf :
    Sheaf ((ProEt.topology X).over (ProEt.mk p)) (Type w) :=
  ⟨shrinkYoneda.{w}.obj (coproductCopiesOver p S), (isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩

omit [UnivLE.{u, w}] in
/-- Two labelled components of a nonempty object differ when the labels differ.
Source: Stacks Project, Tag 03YW (auxiliary; not a blueprint node). -/
lemma isEmpty_of_coproductCopiesLabel_eq {W : Over (ProEt.mk p)} {s t : S} (hst : s ≠ t)
    (h : coproductCopiesLabel p S W s = coproductCopiesLabel p S W t) :
    IsEmpty W.left.left := by
  have h' : W.hom.left ≫ Sigma.ι (fun _ : S ↦ V) s = W.hom.left ≫ Sigma.ι (fun _ : S ↦ V) t := by
    rw [← coproductCopiesLabel_left_left, ← coproductCopiesLabel_left_left, h]
  have hc := (coproductCopiesMorphismsClopen V W.left.left S W.hom.left).2.2.2.2.1
  have h₁ := hc s t
  have h₂ := hc t t
  rw [if_neg (Ne.symm hst)] at h₁
  rw [if_pos rfl, ← h', h₁] at h₂
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ (⊤ : W.left.left.Opens) := trivial
  rw [← h₂] at hx
  exact hx

instance isLocallyInjective_coproductCopiesLabelNatTrans :
    Presheaf.IsLocallyInjective ((ProEt.topology X).over (ProEt.mk p))
      (coproductCopiesLabelNatTrans p S) where
  equalizerSieve_mem {W} s t h := by
    by_cases hst : s = t
    · subst hst
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact GrothendieckTopology.top_mem _ _
    · have : IsEmpty W.unop.left.left :=
        isEmpty_of_coproductCopiesLabel_eq p S hst (shrinkYonedaObjObjEquiv.{w}.symm.injective h)
      refine GrothendieckTopology.superset_covering _ bot_le ?_
      rw [GrothendieckTopology.mem_over_iff, map_bot]
      exact ProEt.bot_mem_topology _

instance isLocallySurjective_coproductCopiesLabelNatTrans :
    Presheaf.IsLocallySurjective ((ProEt.topology X).over (ProEt.mk p))
      (coproductCopiesLabelNatTrans p S) where
  imageSieve_mem {W} x := by
    let φ := (shrinkYonedaObjObjEquiv x).left.left
    have hφ : φ ≫ Sigma.desc (fun _ : S ↦ 𝟙 V) = W.hom.left :=
      congrArg (fun k ↦ k.left) (Over.w (shrinkYonedaObjObjEquiv x))
    obtain ⟨⟨-, hcov⟩, hfac⟩ :=
      (coproductCopiesMorphismsClopen V W.left.left S W.hom.left).1 φ hφ
    have hpt (w : W.left.left) :
        ∃ s, w ∈ φ ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ V) s).opensRange := by
      have hw : w ∈ (⊤ : W.left.left.Opens) := trivial
      rw [← hcov] at hw
      exact TopologicalSpace.Opens.mem_iSup.1 hw
    choose lab hlab using hpt
    let T : Sieve W.left :=
      { arrows Z h := ∃ s, h.left ≫ φ = (h.left ≫ W.hom.left) ≫ Sigma.ι (fun _ : S ↦ V) s
        downward_closed := by
          rintro Z Z' h ⟨s, hs⟩ g
          refine ⟨s, ?_⟩
          rw [comp_left, Category.assoc, hs, Category.assoc, Category.assoc, Category.assoc] }
    have hT : T ∈ ProEt.topology X W.left := by
      refine ProEt.mem_topology_of_openImmersion T
        (fun w ↦ (φ ⁻¹ᵁ (Sigma.ι (fun _ : S ↦ V) (lab w)).opensRange).ι) (fun w ↦ ⟨w, ?_⟩)
        (fun w ↦ ⟨lab w, hfac (lab w)⟩)
      rw [Scheme.Opens.range_ι]
      exact hlab w
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.overEquiv_symm_mem_over _ _ _ hT)
    rintro Z g ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [coproductCopiesLabelNatTrans_app, shrinkYoneda_obj_map]
    congr 1
    refine Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext ?_)
    rw [coproductCopiesLabel_left_left, Over.comp_left, comp_left]
    have hs' : g.left.left ≫ φ = (g.left.left ≫ W.hom.left) ≫ Sigma.ι (fun _ : S ↦ V) s := hs
    have hg : g.left.left ≫ W.hom.left = Z.hom.left := by rw [← comp_left, Over.w g]
    rw [hg] at hs'
    exact hs'.symm

end Sheaf

/-- **The coproduct of copies represents a trivialized sheaf.** If `F` restricted to the localized
pro-étale site over `V` is identified with the constant sheaf `S`, then the morphisms over `V`
into `∐_S V` are naturally in bijection with the sections of `F`, and the labelled components
correspond to the sections of the constant sheaf.
Source: Stacks Project, Tags 098Z, 03P5 and 03YW
(blueprint: lem-sfb-proetale-constant-split-descent-data, steps 3 and 4). -/
theorem exists_coproductCopiesOver_equiv [UnivLE.{u + 1, w}]
    (F : Sheaf (ProEt.topology X) (Type w))
    (e : F.over (ProEt.mk p) ≅
      (constantSheaf ((ProEt.topology X).over (ProEt.mk p)) (Type w)).obj S) :
    ∃ rho : ∀ W : Over (ProEt.mk p),
        ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶
          Over.mk (Sigma.desc fun _ : S ↦ 𝟙 V)) ≃ F.obj.obj (op W.left),
      (∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
          (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶
            Over.mk (Sigma.desc fun _ : S ↦ 𝟙 V)),
        rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
          F.obj.map g.left.op (rho W f)) ∧
      (∀ (W : Over (ProEt.mk p)) (s : S),
        rho W (coproductCopiesOverHomEquiv p S W (coproductCopiesLabel p S W s)) =
          e.inv.hom.app (op W)
            ((toSheafify ((ProEt.topology X).over (ProEt.mk p))
              ((Functor.const (Over (ProEt.mk p))ᵒᵖ).obj S)).app (op W) s)) := by
  have : UnivLE.{u, w} := UnivLE.trans.{u, u + 1, w}
  let J := (ProEt.topology X).over (ProEt.mk p)
  let ψ := ((sheafificationAdjunction J (Type w)).homEquiv _ (coproductCopiesSheaf p S)).symm
    (coproductCopiesLabelNatTrans p S)
  have : IsIso ψ := Sheaf.isIso_sheafificationAdjunction_homEquiv_symm J _
  have fac : toSheafify J _ ≫ ψ.hom = coproductCopiesLabelNatTrans p S := by
    have h := ((sheafificationAdjunction J (Type w)).homEquiv _
      (coproductCopiesSheaf p S)).apply_symm_apply
      (coproductCopiesLabelNatTrans p S)
    rwa [Adjunction.homEquiv_unit] at h
  let β : coproductCopiesSheaf p S ≅ F.over (ProEt.mk p) := (asIso ψ).symm ≪≫ e.symm
  refine ⟨fun W ↦ (coproductCopiesOverHomEquiv p S W).symm.trans
    (shrinkYonedaObjObjEquiv.{w}.symm.trans (((sheafToPresheaf J _).mapIso β).app (op W)).toEquiv),
    fun W W' g f ↦ ?_, fun W s ↦ ?_⟩
  · have h₁ : (coproductCopiesOverHomEquiv p S W').symm
        ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        g ≫ (coproductCopiesOverHomEquiv p S W).symm f :=
      Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)
    simp only [Equiv.trans_apply, h₁]
    rw [shrinkYonedaObjObjEquiv_symm_comp]
    exact NatTrans.naturality_apply β.hom.hom g.op _
  · let t := (toSheafify J ((Functor.const (Over (ProEt.mk p))ᵒᵖ).obj S)).app (op W) s
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [← coproductCopiesLabelNatTrans_app, ← fac, NatTrans.comp_app, ConcreteCategory.comp_apply]
    have h : ((sheafToPresheaf J _).mapIso (asIso ψ)).inv.app (op W)
        (((sheafToPresheaf J _).mapIso (asIso ψ)).hom.app (op W)
          t) = t := by
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app]
      rfl
    exact congrArg (e.inv.hom.app (op W)) h

end Scheme.ProEt

end AlgebraicGeometry
