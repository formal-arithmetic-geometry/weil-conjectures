/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsModule
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Adjunction
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Restricting sections of the cohomology presheaf to points

TODO
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Sections

variable {X : Scheme.{u}}

/-- For `U` étale over `X` with structure map `p`, the section `𝟙 : U ⟶ U` identifies sections
of `G` over `U` with global sections of `p^* G`. -/
lemma pullSection_id_bijective (U : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (ModuleSheaf.pullSection U.hom G (V := Etale.finalObject U.left) (U := U)
      (𝟙 U.left) (by simp)) := by
  have hU : AlgebraicGeometry.Etale U.hom := U.prop
  let ι := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) U.hom hU
  let e : (MorphismProperty.Over.map ⊤ hU).obj (Etale.finalObject U.left) ⟶ U :=
    MorphismProperty.Over.homMk (𝟙 U.left) (Category.id_comp _)
  have : IsIso e := ⟨MorphismProperty.Over.homMk (𝟙 U.left) (Category.id_comp _),
    by ext; dsimp [e]; simp; rfl, by ext; dsimp [e]; simp⟩
  have key (s : G.obj.obj (op U)) : (ι.hom.app G).hom.app (op (Etale.finalObject U.left))
      (ModuleSheaf.pullSection U.hom G (V := Etale.finalObject U.left) (U := U)
        (𝟙 U.left) (by simp) s) = G.obj.map e.op s := by
    rw [ModuleSheaf.pullSection, NatTrans.naturality_apply]
    have h := Adjunction.unit_leftAdjointUniq_hom_app (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom) (Etale.localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.hom hU) G
    have h2 := congrArg (fun k => k.hom.app (op U) s) h
    dsimp at h2
    erw [h2]
    simp [Etale.localizationRestrictionLowerStarAdjunction, Etale.localizationRestriction]
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 3
    refine congrArg Quiver.Hom.op (MorphismProperty.Over.Hom.ext ?_)
    simp [e]
  have h₁ : Function.Bijective ((ι.hom.app G).hom.app (op (Etale.finalObject U.left))) :=
    ConcreteCategory.bijective_of_isIso _
  have h₂ : Function.Bijective (G.obj.map e.op) := ConcreteCategory.bijective_of_isIso _
  refine (h₁.of_comp_iff' _).1 ?_
  simpa only [Function.comp_def, key] using h₂

/-- Pulling sections back is natural in the sheaf. -/
lemma pullSection_naturality {R T : Scheme.{u}} (t : T ⟶ R)
    {G G' : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : G ⟶ G') {V : T.Etale}
    {U : R.Etale} (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) :
    ((t)^*[ModuleCat.{u + 1} Λ].map ψ).hom.app (op V) (ModuleSheaf.pullSection t G φ hφ g) =
      ModuleSheaf.pullSection t G' φ hφ (ψ.hom.app (op U) g) := by
  rw [ModuleSheaf.pullSection, ModuleSheaf.pullSection, NatTrans.naturality_apply
    ((t)^*[ModuleCat.{u + 1} Λ].map ψ).hom (homToPullback t φ hφ).op]
  exact congrArg _ (Etale.pullbackSection_naturality Λ t ψ U g)

/-- The composition isomorphism `t'^* ≅ t^* ⋙ u^*` for `t' = u ≫ t` turns the pullback along `u`
of a section of `t^* G` into its restriction along `u`. -/
lemma upperStarComp_inv_app_pullSection {R T T' : Scheme.{u}} (t : T ⟶ R) (u : T' ⟶ T)
    (t' : T' ⟶ R) (ht' : t' = u ≫ t) (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ u)
    (s : ((t)^*[ModuleCat.{u + 1} Λ].obj G).obj.obj (op V)) :
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) u t t' ht').inv.app G).hom.app (op V')
        (ModuleSheaf.pullSection u _ m hm s) =
      ModuleSheaf.restrictAlong t G u t' ht' m hm s := by
  exact (NatTrans.naturality_apply ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) u t t' ht').inv.app
    G).hom (homToPullback u m hm).op _).trans rfl

end Sections

section GlobalSections

variable {T : Scheme.{u}}

/-- Maps out of the constant sheaf `Λ` on `T_ét` are global sections. -/
noncomputable def constSheafHomEquiv (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) ≃
      G.obj.obj (op (Etale.finalObject T)) :=
  ((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv
    _ _).trans (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv)

lemma constSheafHomEquiv_comp {G G' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) (ψ : G ⟶ G') :
    constSheafHomEquiv Λ G' (φ ≫ ψ) = ψ.hom.app _ (constSheafHomEquiv Λ G φ) := by
  simp only [constSheafHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

/-- The global section corresponding to `φ : Λ ⟶ G` is the image of the section `1`. -/
lemma constSheafHomEquiv_apply (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶ G) :
    constSheafHomEquiv Λ G φ =
      φ.hom.app (op (Etale.finalObject T)) (Etale.constSheafOne Λ (Etale.finalObject T)) := by
  have h := constSheafHomEquiv_comp Λ (𝟙 _) φ
  rw [Category.id_comp] at h
  rw [h]
  rfl

/-- The isomorphism `Λ ≅ u^* Λ` corresponds to the pullback of the section `1`. -/
lemma constSheafHomEquiv_constantSheafCompUpperStarIso_inv {T' : Scheme.{u}} (u : T' ⟶ T) :
    constSheafHomEquiv Λ _ ((Etale.constantSheafCompUpperStarIso Λ u).app (ModuleCat.of Λ Λ)).inv =
      ModuleSheaf.pullSection u (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)
        (V := Etale.finalObject T') (U := Etale.finalObject T) u ((Category.comp_id _).trans (Category.id_comp _).symm)
        (Etale.constSheafOne Λ (Etale.finalObject T)) := by
  rw [constSheafHomEquiv_apply, ModuleSheaf.pullSection,
    ← Etale.constSheafOne_map Λ (homToPullback u (V := Etale.finalObject T')
      (U := Etale.finalObject T) u ((Category.comp_id _).trans (Category.id_comp _).symm)), NatTrans.naturality_apply,
    Etale.constantSheafCompUpperStarIso_inv_one]
  rfl

end GlobalSections

section Restrict

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The generating section of the free sheaf `Λ[V]` over `V`. -/
noncomputable def freeSheafGenerator (V : S.Etale) : ((Etale.freeSheaf Λ S).obj V).obj.obj (op V) :=
  Etale.freeSheafHomEquiv Λ V _ (𝟙 _)

lemma freeSheaf_map_generator {V V' : S.Etale} (g : V' ⟶ V) :
    ((Etale.freeSheaf Λ S).map g).hom.app (op V') (freeSheafGenerator Λ V') =
      ((Etale.freeSheaf Λ S).obj V).obj.map g.op (freeSheafGenerator Λ V) := by
  rw [freeSheafGenerator, freeSheafGenerator, ← Etale.freeSheafHomEquiv_comp,
    ← Etale.freeSheafHomEquiv_map, Category.id_comp, Category.comp_id]

/-- The pullback along `f` of the generating section of `Λ[V]`, a section of `f^* Λ[V]` over
`V ×_S X`. -/
noncomputable def freeSheafPullbackGenerator (V : S.Etale) :
    ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)) :=
  Etale.pullbackSection Λ f _ V (freeSheafGenerator Λ V)

lemma upperStar_map_freeSheafPullbackGenerator {V V' : S.Etale} (g : V' ⟶ V) :
    ((f)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ S).map g)).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'))
        (freeSheafPullbackGenerator Λ f V') =
      ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map g).op
        (freeSheafPullbackGenerator Λ f V) := by
  rw [freeSheafPullbackGenerator, freeSheafPullbackGenerator, Etale.pullbackSection_naturality,
    freeSheaf_map_generator, Etale.pullbackSection_map]

/-- The pullback generator corepresents sections over `V ×_S X`: a morphism `f^* Λ[V] ⟶ G` is
determined by the image of `freeSheafPullbackGenerator`. -/
lemma bijective_app_freeSheafPullbackGenerator (V : S.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun φ : (f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V) ⟶ G ↦
      φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
        (freeSheafPullbackGenerator Λ f V)) := by
  have h : (fun φ : (f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V) ⟶ G ↦
      φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
        (freeSheafPullbackGenerator Λ f V)) =
      (Etale.freeSheafHomEquiv Λ _ G) ∘ (Etale.upperStarFreeSheafHomEquiv Λ f V G) := by
    funext φ
    have h₁ : Etale.freeSheafHomEquiv Λ V _
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
          ((Etale.freeSheaf Λ S).obj V)) = freeSheafPullbackGenerator Λ f V := by
      conv_lhs => rw [← Category.id_comp
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
          ((Etale.freeSheaf Λ S).obj V))]
      rw [Etale.freeSheafHomEquiv_comp]
      rfl
    simp only [Function.comp_apply, Etale.upperStarFreeSheafHomEquiv, Equiv.trans_apply,
      Adjunction.homEquiv_unit, Etale.freeSheafHomEquiv_comp, h₁]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [h]
  exact (Etale.freeSheafHomEquiv Λ _ G).bijective.comp
    (Etale.upperStarFreeSheafHomEquiv Λ f V G).bijective

/-- For `t : T ⟶ X` and a `T`-point `b : T ⟶ V` of an étale `S`-scheme `V` over `f`, the
canonical global section of `t^* f^* Λ[V]`: the pullback generator of `f^* Λ[V]` pulled back
along the section `T ⟶ V ×_S X` given by `b` and `t`. -/
noncomputable def freeSheafPullbackSection {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    ((t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.freeSheaf Λ S).obj V))).obj.obj (op (Etale.finalObject T)) :=
  ModuleSheaf.pullSection t _ (V := Etale.finalObject T)
    (U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V) (pullback.lift b t hb)
    ((pullback.lift_snd _ _ _).trans (Category.id_comp t).symm) (freeSheafPullbackGenerator Λ f V)

/-- The morphism `Λ ⟶ t^* f^* Λ[V]` corresponding to `freeSheafPullbackSection`. -/
noncomputable def freeSheafPullbackSectionHom {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ ⟶
      (t)^*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj
        ((Etale.freeSheaf Λ S).obj V)) :=
  (constSheafHomEquiv Λ _).symm (freeSheafPullbackSection Λ f t V b hb)

lemma freeSheafPullbackSectionHom_comp {T : Scheme.{u}} (t : T ⟶ X) {V V' : S.Etale}
    (g : V' ⟶ V) (b' : T ⟶ V'.left) (hb' : b' ≫ V'.hom = t ≫ f) :
    freeSheafPullbackSectionHom Λ f t V' b' hb' ≫
        (t)^*[ModuleCat.{u + 1} Λ].map ((f)^*[ModuleCat.{u + 1} Λ].map
          ((Etale.freeSheaf Λ S).map g)) =
      freeSheafPullbackSectionHom Λ f t V (b' ≫ g.left)
        (by rw [Category.assoc, MorphismProperty.Over.w g, hb']) := by
  apply (constSheafHomEquiv Λ _).injective
  rw [constSheafHomEquiv_comp, freeSheafPullbackSectionHom, freeSheafPullbackSectionHom,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, freeSheafPullbackSection,
    freeSheafPullbackSection, pullSection_naturality, upperStar_map_freeSheafPullbackGenerator,
    ← ModuleSheaf.pullSection_comp]
  apply ModuleSheaf.pullSection_congr
  apply pullback.hom_ext <;> simp

lemma freeSheafPullbackSectionHom_restrict {T T' : Scheme.{u}} (t : T ⟶ X) (t' : T' ⟶ X)
    (u : T' ⟶ T) (hu : u ≫ t = t') (V : S.Etale) (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    ((Etale.constantSheafCompUpperStarIso Λ u).app (ModuleCat.of Λ Λ)).inv ≫
        (u)^*[ModuleCat.{u + 1} Λ].map (freeSheafPullbackSectionHom Λ f t V b hb) ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) u t t' hu.symm).inv.app _ =
      freeSheafPullbackSectionHom Λ f t' V (u ≫ b) (by rw [Category.assoc, hb, reassoc_of% hu]) := by
  apply (constSheafHomEquiv Λ _).injective
  rw [← Category.assoc, constSheafHomEquiv_comp, constSheafHomEquiv_comp,
    constSheafHomEquiv_constantSheafCompUpperStarIso_inv]
  refine (congrArg _ (pullSection_naturality Λ u (freeSheafPullbackSectionHom Λ f t V b hb)
    (V := Etale.finalObject T') (U := Etale.finalObject T) u
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (Etale.constSheafOne Λ (Etale.finalObject T)))).trans ?_
  rw [← constSheafHomEquiv_apply]
  simp only [freeSheafPullbackSectionHom, Equiv.apply_symm_apply]
  rw [freeSheafPullbackSection]
  refine (upperStarComp_inv_app_pullSection Λ t u t' hu.symm _ (V := Etale.finalObject T)
    (V' := Etale.finalObject T') u _ _).trans ?_
  refine (ModuleSheaf.restrictAlong_pullSection t _ u t' hu.symm (V := Etale.finalObject T)
    (V' := Etale.finalObject T') u _ _ _ _).trans ?_
  rw [freeSheafPullbackSection]
  apply ModuleSheaf.pullSection_congr
  apply pullback.hom_ext <;> simp [hu]

/-- For an étale `S`-scheme `V`, the adjoint `p_! Λ ⟶ f^* Λ[V]` of the canonical section of
`p^* f^* Λ[V]` over `V ×_S X` (where `p : V ×_S X ⟶ X` is the projection) is an isomorphism:
both sides corepresent sections over `V ×_S X`. -/
lemma isIso_homEquiv_symm_freeSheafPullbackSectionHom (V : S.Etale) :
    IsIso (((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).prop).homEquiv _ _).symm
        (freeSheafPullbackSectionHom Λ f ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom
          V (pullback.fst V.hom f) pullback.condition)) := by
  set U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  set adj := Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.hom U.prop
  rw [isIso_iff_coyoneda_map_bijective]
  intro G
  have h : (fun φ ↦ (adj.homEquiv _ _).symm (freeSheafPullbackSectionHom Λ f U.hom V
      (pullback.fst V.hom f) pullback.condition) ≫ φ) =
      (adj.homEquiv _ _).symm ∘ (constSheafHomEquiv Λ _).symm ∘
        (ModuleSheaf.pullSection U.hom G (V := Etale.finalObject U.left) (U := U) (𝟙 U.left)
          (by simp)) ∘
        (fun φ : (f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V) ⟶ G ↦
          φ.hom.app (op U) (freeSheafPullbackGenerator Λ f V)) := by
    funext φ
    apply (adj.homEquiv _ _).injective
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply,
      adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply (constSheafHomEquiv Λ _).injective
    rw [constSheafHomEquiv_comp, Equiv.apply_symm_apply, freeSheafPullbackSectionHom,
      Equiv.apply_symm_apply, freeSheafPullbackSection, pullSection_naturality]
    apply ModuleSheaf.pullSection_congr
    exact pullback.lift_fst_snd (f := V.hom) (g := f)
  rw [h]
  exact (adj.homEquiv _ _).symm.bijective.comp ((constSheafHomEquiv Λ _).symm.bijective.comp
    ((pullSection_id_bijective Λ U G).comp (bijective_app_freeSheafPullbackGenerator Λ f V G)))

variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)

/-- The restriction of a class `x ∈ Extᵠ(f^* Λ[V], F) = Hᵠ(V ×_S X, F|)` to a `T`-point `b` of
`V` over `t : T ⟶ X`: pull `x` back along `t` and precompose with the canonical section
`Λ ⟶ t^* f^* Λ[V]` given by `b`. -/
noncomputable def extRestrict {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale) (b : T ⟶ V.left)
    (hb : b ≫ V.hom = t ≫ f) :
    Ext ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)) F q →+
      Ext (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)
        ((t)^*[ModuleCat.{u + 1} Λ].obj F) q :=
  ((Ext.mk₀ (freeSheafPullbackSectionHom Λ f t V b hb)).precomp _ (zero_add q)).comp
    ((t)^*[ModuleCat.{u + 1} Λ].mapExtAddHom _ _ q)

lemma extRestrict_apply {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale) (b : T ⟶ V.left)
    (hb : b ≫ V.hom = t ≫ f)
    (x : Ext ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)) F q) :
    extRestrict Λ f F q t V b hb x = (Ext.mk₀ (freeSheafPullbackSectionHom Λ f t V b hb)).comp
      (x.mapExactFunctor (t)^*[ModuleCat.{u + 1} Λ]) (zero_add q) :=
  rfl

/-- Restriction to a point is compatible with the transition maps `V' ⟶ V`. -/
lemma extRestrict_mk₀_comp {T : Scheme.{u}} (t : T ⟶ X) {V V' : S.Etale} (g : V' ⟶ V)
    (b' : T ⟶ V'.left) (hb' : b' ≫ V'.hom = t ≫ f)
    (x : Ext ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)) F q) :
    extRestrict Λ f F q t V' b' hb'
        ((Ext.mk₀ ((f)^*[ModuleCat.{u + 1} Λ].map ((Etale.freeSheaf Λ S).map g))).comp x
          (zero_add q)) =
      extRestrict Λ f F q t V (b' ≫ g.left)
        (by rw [Category.assoc, MorphismProperty.Over.w g, hb']) x := by
  rw [extRestrict_apply, extRestrict_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, freeSheafPullbackSectionHom_comp]

/-- Restriction to a point is compatible with the restriction maps of étale cohomology. -/
lemma cohomologyRestrictOver_extRestrict {T T' : Scheme.{u}} (t : T ⟶ X) (t' : T' ⟶ X)
    (u : T' ⟶ T) (hu : u ≫ t = t') (V : S.Etale) (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f)
    (x : Ext ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ S).obj V)) F q) :
    cohomologyRestrictOver Λ t' t u hu F q (extRestrict Λ f F q t V b hb x) =
      extRestrict Λ f F q t' V (u ≫ b) (by rw [Category.assoc, hb, reassoc_of% hu]) x := by
  have : PreservesFiniteLimits ((t)^*[ModuleCat.{u + 1} Λ] ⋙ (u)^*[ModuleCat.{u + 1} Λ]) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits ((t)^*[ModuleCat.{u + 1} Λ] ⋙ (u)^*[ModuleCat.{u + 1} Λ]) :=
    comp_preservesFiniteColimits _ _
  have h : cohomologyRestrictOver Λ t' t u hu F q (extRestrict Λ f F q t V b hb x) =
      ((Ext.mk₀ ((Etale.constantSheafCompUpperStarIso Λ u).app (ModuleCat.of Λ Λ)).inv).comp
        ((extRestrict Λ f F q t V b hb x).mapExactFunctor (u)^*[ModuleCat.{u + 1} Λ])
        (zero_add q)).comp
        (Ext.mk₀ ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) u t t' hu.symm).inv.app F))
        (add_zero q) :=
    rfl
  rw [h, extRestrict_apply, extRestrict_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_mapExactFunctor,
    Ext.mapExactFunctor_comp_mk₀_app _ _
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) u t t' hu.symm).inv x,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc, freeSheafPullbackSectionHom_restrict Λ f t t' u hu]

/-- Restricting classes on `V ×_S X` to the tautological point of `V` over `V ×_S X` is
bijective: `Extᵠ(f^* Λ[V], F) ≅ Hᵠ(V ×_S X, F|)`. -/
theorem extRestrict_bijective (V : S.Etale) :
    Function.Bijective (extRestrict Λ f F q
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom V (pullback.fst V.hom f)
      pullback.condition) := by
  have := isIso_homEquiv_symm_freeSheafPullbackSectionHom Λ f V
  exact (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).prop).bijective_mk₀_comp_mapExactFunctor
      _ F q

end Restrict

end AlgebraicGeometry.Etale
