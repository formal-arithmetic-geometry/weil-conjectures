/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.AlgebraicGeometry.Sites.Ga
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Comparison of étale and Zariski cohomology

Let `X` be a scheme. Open subschemes are étale `X`-schemes, and the functor
`ε : X.Opens ⥤ X.Etale`, `U ↦ U`, is right adjoint to the functor sending an étale `X`-scheme to
its image, an open of `X` (étale morphisms are open). The image functor is cocontinuous, so `ε`
is continuous and induces the restriction `ε_*` of étale sheaves to Zariski sheaves, with an
exact left adjoint `ε^*`: the sheafification of `T ↦ F(image of T)`.

The `Ext`-adjunction (`CategoryTheory.Adjunction.mapExtCounit_bijective_of_forall`) then shows
that `Hⁿ(X_Zar, ε_* G) ≅ Hⁿ(X_ét, G)` for every abelian étale sheaf `G` without higher cohomology
on the affine opens of `X`: for such `G`, the restriction `ε_*` maps a short exact sequence
`0 → G → I → Q → 0` with `I` injective to a short exact sequence, since sections of `Q` lift to
`I` on affine opens, and `Q` has again no higher cohomology on affine opens.

## Main definitions

- `AlgebraicGeometry.Scheme.opensToEtale`: the functor `ε : X.Opens ⥤ X.Etale`.
- `AlgebraicGeometry.Scheme.etaleImage`: the image of an étale `X`-scheme, left adjoint to `ε`.
- `AlgebraicGeometry.Scheme.zariskiRestriction`: the restriction `ε_*` of étale sheaves to
  Zariski sheaves.
- `AlgebraicGeometry.Scheme.etaleExtension`: its exact left adjoint `ε^*`.

## Main statements

- `AlgebraicGeometry.Scheme.bijective_zariskiComparison`: `Hⁿ(X_Zar, ε_* G) ≅ Hⁿ(X_ét, G)` for
  `G` acyclic on affine opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

open scoped AlgebraicGeometry.Etale

/-- The open subsets of a topological space form an essentially small category in the next
universe. -/
instance TopologicalSpace.Opens.essentiallySmall_succ (X : TopCat.{u}) :
    EssentiallySmall.{u + 1} (Opens X) :=
  have : LocallySmall.{u + 1} (Opens X) :=
    @locallySmall_of_univLE (Opens X) _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Abelian sheaves with values in the next universe on the open subsets of a topological space
form a Grothendieck abelian category. -/
instance TopologicalSpace.Opens.isGrothendieckAbelian_sheaf_succ (X : TopCat.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-! ### Open subschemes and images of étale schemes -/

/-- There is at most one morphism of étale `X`-schemes into an open subscheme. -/
instance subsingleton_hom_etaleMk_ι {X : Scheme.{u}} (Z : X.Etale) (U : X.Opens) :
    Subsingleton (Z ⟶ Etale.mk U.ι) :=
  ⟨fun f g ↦ MorphismProperty.Over.Hom.ext (by
    rw [← cancel_mono U.ι]
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm)⟩

/-- An étale `X`-scheme whose image lies in the open `U` maps to `U`. -/
noncomputable def etaleHomEtaleMk {X : Scheme.{u}} (Z : X.Etale) (U : X.Opens)
    (h : Set.range Z.hom ⊆ (U : Set X)) : Z ⟶ Etale.mk U.ι :=
  MorphismProperty.Over.homMk
    (IsOpenImmersion.lift U.ι Z.hom (h.trans_eq (Scheme.Opens.range_ι U).symm))
    (IsOpenImmersion.lift_fac _ _ _)

lemma range_subset_of_hom_etaleMk {X : Scheme.{u}} {Z : X.Etale} {U : X.Opens}
    (f : Z ⟶ Etale.mk U.ι) : Set.range Z.hom ⊆ (U : Set X) := by
  rintro _ ⟨z, rfl⟩
  rw [← MorphismProperty.Over.w f]
  exact (f.left z).2

/-- The functor `ε : X.Opens ⥤ X.Etale` sending an open to the open subscheme. -/
@[simps obj]
noncomputable def opensToEtale : X.Opens ⥤ X.Etale where
  obj U := Etale.mk U.ι
  map i := MorphismProperty.Over.homMk (X.homOfLE i.le) (X.homOfLE_ι i.le)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance (T : X.Etale) (U : X.Opens) : Subsingleton (T ⟶ X.opensToEtale.obj U) :=
  subsingleton_hom_etaleMk_ι T U

/-- The image of an étale `X`-scheme, an open of `X` since étale morphisms are open. -/
@[simps obj]
noncomputable def etaleImage : X.Etale ⥤ X.Opens where
  obj T := ⟨Set.range T.hom, by
    have : AlgebraicGeometry.Etale T.hom := T.prop
    exact T.hom.isOpenMap.isOpen_range⟩
  map {T T'} f := homOfLE (by
    rintro _ ⟨t, rfl⟩
    refine ⟨f.left t, ?_⟩
    change (f.left ≫ T'.hom) t = T.hom t
    rw [MorphismProperty.Over.w f]
    rfl)

/-- The image functor is left adjoint to `ε`. -/
noncomputable def etaleImageAdjunction : X.etaleImage ⊣ X.opensToEtale :=
  Adjunction.mkOfHomEquiv
    { homEquiv T U :=
        { toFun i := etaleHomEtaleMk T U i.le
          invFun f := homOfLE (range_subset_of_hom_etaleMk f)
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right _ _ := Subsingleton.elim _ _ }

/-- The image functor is cocontinuous: a Zariski covering of the image of `T` pulls back to an
étale covering of `T` by the preimages of its members. -/
instance etaleImage_isCocontinuous :
    X.etaleImage.IsCocontinuous X.smallEtaleTopology (Opens.grothendieckTopology X) where
  cover_lift {T S} hS := by
    refine (Scheme.mem_smallEtaleTopology_iff _).2 fun t ↦ ?_
    obtain ⟨W, f, hf, htW⟩ := hS (T.hom t) ⟨t, rfl⟩
    let V : T.left.Opens := T.hom ⁻¹ᵁ W
    have : AlgebraicGeometry.Etale T.hom := T.prop
    let TV : X.Etale := MorphismProperty.Over.mk ⊤ (V.ι ≫ T.hom)
      (MorphismProperty.comp_mem _ _ _ inferInstance T.prop)
    let g : TV ⟶ T := MorphismProperty.Over.homMk V.ι rfl trivial
    refine ⟨TV, g, ?_, ⟨⟨t, htW⟩, rfl⟩⟩
    have hle : X.etaleImage.obj TV ≤ W := by
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      exact hv
    change S (X.etaleImage.map g)
    rw [Subsingleton.elim (X.etaleImage.map g) (homOfLE hle ≫ f)]
    exact S.downward_closed hf _

instance opensToEtale_isContinuous :
    X.opensToEtale.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology :=
  X.etaleImageAdjunction.isContinuous_of_isCocontinuous _ _

/-! ### Restriction to the Zariski site and its left adjoint -/

variable (A : Type*) [Category A] [HasWeakSheafify X.smallEtaleTopology A]

/-- The restriction `ε_*` of étale sheaves to the Zariski site: `(ε_* G)(U) = G(U)`. -/
noncomputable abbrev zariskiRestriction :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (Opens.grothendieckTopology X) A :=
  X.opensToEtale.sheafPushforwardContinuous A _ _

/-- The left adjoint `ε^*` of the restriction to the Zariski site: the sheafification of
`T ↦ F(image of T)`. -/
noncomputable abbrev etaleExtension :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  sheafToPresheaf _ A ⋙ (Functor.whiskeringLeft _ _ A).obj X.etaleImage.op ⋙
    presheafToSheaf _ A

/-- The adjunction `ε^* ⊣ ε_*`. -/
noncomputable def etaleExtensionAdjunction : X.etaleExtension A ⊣ X.zariskiRestriction A :=
  ((X.etaleImageAdjunction.op.whiskerLeft A).comp
    (sheafificationAdjunction X.smallEtaleTopology A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance : (X.etaleExtension A).IsLeftAdjoint := ⟨_, ⟨X.etaleExtensionAdjunction A⟩⟩

instance : (X.zariskiRestriction A).IsRightAdjoint := ⟨_, ⟨X.etaleExtensionAdjunction A⟩⟩

instance : (X.zariskiRestriction AddCommGrpCat.{u + 1}).Additive :=
  (X.etaleExtensionAdjunction _).right_adjoint_additive

/-- The open `X` itself, as an étale `X`-scheme, is terminal. -/
noncomputable def isTerminalOpensToEtaleTop : IsTerminal (X.opensToEtale.obj ⊤) :=
  IsTerminal.ofUniqueHom (fun Z ↦ etaleHomEtaleMk Z ⊤ (by simp)) fun _ _ ↦ Subsingleton.elim _ _

/-! ### Cohomology -/

section Cohomology

/-- `ε^*` of the constant Zariski sheaf is the constant étale sheaf: both are left adjoint to
global sections. -/
noncomputable def constantSheafCompEtaleExtensionIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} ⋙
        X.etaleExtension AddCommGrpCat.{u + 1} ≅
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}
    isTerminalTop).comp (X.etaleExtensionAdjunction _)).leftAdjointUniq
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      X.isTerminalOpensToEtaleTop).ofNatIsoRight (Iso.refl _))

instance : PreservesFiniteLimits (X.etaleExtension AddCommGrpCat.{u + 1}) := by
  dsimp only [etaleExtension]
  infer_instance

noncomputable instance : (X.etaleExtension AddCommGrpCat.{u + 1}).Additive :=
  (X.etaleExtensionAdjunction _).left_adjoint_additive

/-- The comparison map `Hⁿ(X_Zar, ε_* G) ⟶ Hⁿ(X_ét, G)`: the `Ext`-adjunction for `ε^* ⊣ ε_*`,
followed by the identification of `ε^*` of the constant sheaf `ℤ` with `ℤ`. -/
noncomputable def zariskiComparison (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Sheaf.H ((X.zariskiRestriction AddCommGrpCat.{u + 1}).obj G) n →+ Sheaf.H G n :=
  (Abelian.Ext.precompAddEquiv ((X.constantSheafCompEtaleExtensionIso).symm.app
    (AddCommGrpCat.of (ULift ℤ))) G n).toAddMonoidHom.comp
    ((X.etaleExtensionAdjunction _).mapExtCounit _ G n)

/-- The comparison map is natural. -/
lemma zariskiComparison_map {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (g : G ⟶ G') (n : ℕ) (x : Sheaf.H ((X.zariskiRestriction AddCommGrpCat.{u + 1}).obj G) n) :
    X.zariskiComparison G' n
        (Sheaf.H.map ((X.zariskiRestriction AddCommGrpCat.{u + 1}).map g) n x) =
      Sheaf.H.map g n (X.zariskiComparison G n x) := by
  simp only [zariskiComparison, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, Abelian.Ext.precompAddEquiv_apply, Sheaf.H.map_apply]
  erw [Adjunction.mapExtCounit_comp_mk₀]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rfl

/-- If `G` has no higher cohomology on the affine opens of `X` and `0 → G → I → Q → 0` is short
exact with `I` injective, then neither has `Q`. -/
lemma subsingleton_H_upperStar_X₃ {S : ShortComplex (Sheaf X.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) [Injective S.X₂] (U : X.Opens) (n : ℕ)
    (hF : Subsingleton (Sheaf.H ((U.ι)^*[AddCommGrpCat.{u + 1}].obj S.X₁) (n + 2))) :
    Subsingleton (Sheaf.H ((U.ι)^*[AddCommGrpCat.{u + 1}].obj S.X₃) (n + 1)) := by
  let P := (U.ι)^*[AddCommGrpCat.{u + 1}]
  have hS' := hS.map_of_exact P
  have : Injective (S.map P).X₂ := Etale.injective_upperStar_obj_of_etale_addCommGrp U.ι S.X₂
  refine subsingleton_of_forall_eq 0 fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Sheaf.H.exact_map_δSucc hS' (n + 1) y).1 (@Subsingleton.elim _ hF _ _)
  rw [Abelian.Ext.eq_zero_of_injective x, map_zero]

/-- An abelian étale sheaf on `X` without higher cohomology on the affine opens of `X`. -/
def IsAffineAcyclic (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ n : ℕ,
    Subsingleton (Sheaf.H ((U.ι)^*[AddCommGrpCat.{u + 1}].obj G) (n + 1))

/-- The restriction to the Zariski site maps a short exact sequence `0 → G → I → Q → 0` with
`G` acyclic on affine opens to a short exact sequence: sections of `Q` lift to `I` on affine
opens. -/
lemma shortExact_map_zariskiRestriction {S : ShortComplex (Sheaf X.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) (hG : X.IsAffineAcyclic S.X₁) :
    (S.map (X.zariskiRestriction AddCommGrpCat.{u + 1})).ShortExact := by
  let R := X.zariskiRestriction AddCommGrpCat.{u + 1}
  have := hS.mono_f
  have hloc : Sheaf.IsLocallySurjective (R.map S.g) := ⟨fun {U} s x hx ↦ by
    obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
      X.isBasis_affineOpens) hx
    have : Subsingleton (Sheaf.H (((Etale.mk (Scheme.Opens.ι V)).hom)^*[AddCommGrpCat.{u + 1}].obj
        S.X₁) 1) := hG V hV 0
    obtain ⟨t, ht⟩ := Etale.surjective_app_of_subsingleton_H_one hS (Etale.mk (Scheme.Opens.ι V))
      ((R.obj S.X₃).obj.map (homOfLE hVU).op s)
    exact ⟨V, homOfLE hVU, ⟨t, ht⟩, hxV⟩⟩
  exact { exact := hS.exact.map_of_mono_of_preservesKernel R inferInstance inferInstance
          mono_f := inferInstanceAs (Mono (R.map S.f))
          epi_g := Sheaf.epi_of_isLocallySurjective (R.map S.g) }

/-- **Étale and Zariski cohomology agree for sheaves acyclic on affine opens.** Let `G` be an
abelian étale sheaf on `X` without higher cohomology on the affine opens of `X`. Then the
comparison map `Hⁿ(X_Zar, ε_* G) ⟶ Hⁿ(X_ét, G)` is bijective for every `n`. -/
theorem bijective_zariskiComparison (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : X.IsAffineAcyclic G) (n : ℕ) : Function.Bijective (X.zariskiComparison G n) := by
  refine (Abelian.Ext.precompAddEquiv _ G n).bijective.comp
    ((X.etaleExtensionAdjunction _).mapExtCounit_bijective_of_forall X.IsAffineAcyclic
      (fun {S} hS hI hP ↦ ?_) _ n G hG)
  exact ⟨fun U hU m ↦ by
    have := hI
    exact X.subsingleton_H_upperStar_X₃ hS U m (hP U hU (m + 1)),
    X.shortExact_map_zariskiRestriction hS hP⟩

end Cohomology

end AlgebraicGeometry.Scheme
