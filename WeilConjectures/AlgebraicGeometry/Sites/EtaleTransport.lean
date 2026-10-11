/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# Restriction of étale cohomology and torsors along an étale monomorphism

Let `f : X ⟶ Y` be an étale monomorphism of schemes, for instance an isomorphism. Restriction
along the localization functor `Φ : X.Etale ⥤ Y.Etale`, `U ↦ (U ⟶ X ⟶ Y)`, is an exact functor
`R : Sh(Y_ét) ⥤ Sh(X_ét)` with `(R F)(U) = F(Φ U)` (`AlgebraicGeometry.Scheme.etaleRestriction`).
It induces maps `H^n(Y, F) ⟶ H^n(X, R F)` on étale cohomology
(`AlgebraicGeometry.Scheme.etaleRestrictionH`), natural in `F`, compatible with connecting
homomorphisms and given in degree `0` by restriction of global sections. Restricting the
underlying sheaf of a `G`-torsor gives an `R G`-torsor
(`CategoryTheory.Sheaf.Torsor.etaleRestriction`), and the class of the restricted torsor in
`H¹(X, R G)` is the image of the class of the torsor
(`AlgebraicGeometry.Scheme.classH1_etaleRestriction`).

For an isomorphism `e : X ≅ Y` this is the transport of étale cohomology and torsors along `e`,
used to show that cup products and Kummer maps are invariant under automorphisms such as the
Frobenius of the geometric fibre of a curve over a finite field.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleRestriction`: the restriction functor `R`.
- `AlgebraicGeometry.Scheme.etaleRestrictionH`: the induced map on cohomology.

## Main statements

- `AlgebraicGeometry.Scheme.etaleRestrictionH_map`, `etaleRestrictionH_δSucc`,
  `equiv₀_etaleRestrictionH`: naturality, connecting homomorphisms, degree `0`.
- `AlgebraicGeometry.Scheme.classH1_etaleRestriction`: compatibility with classes of torsors.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
  {T : C} (hT : IsTerminal T)

/-- Morphisms out of the constant sheaf `ℤ` are global sections: the value at `1` over the
terminal object. -/
noncomputable def constantHomEquiv (F : Sheaf J AddCommGrpCat.{u}) :
    ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) ≃
      F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

lemma constantHomEquiv_comp {F G : Sheaf J AddCommGrpCat.{u}}
    (f : (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F)
    (g : F ⟶ G) :
    constantHomEquiv hT G (f ≫ g) = g.hom.app (op T) (constantHomEquiv hT F f) := by
  simp only [constantHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    Adjunction.homEquiv_naturality_right]
  rfl

lemma constantHomEquiv_naturality {F : Sheaf J AddCommGrpCat.{u}}
    (f : (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) {W : C}
    (ρ : W ⟶ T) :
    f.hom.app (op W) (((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.map ρ.op
          (constantHomEquiv hT _ (𝟙 _))) =
      F.obj.map ρ.op (constantHomEquiv hT F f) := by
  rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply,
    ← constantHomEquiv_comp, Category.id_comp]

lemma H.equiv₀_eq_constantHomEquiv (F : Sheaf J AddCommGrpCat.{u}) [HasExt.{u} (Sheaf J
    AddCommGrpCat.{u})] (x : H F 0) :
    H.equiv₀ F hT x = constantHomEquiv hT F (Ext.addEquiv₀ x) :=
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- The localization functor `X.Etale ⥤ Y.Etale`, `U ↦ (U ⟶ X ⟶ Y)`, along an étale `f`. -/
noncomputable abbrev etaleLocalization : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ ‹Etale f›

instance : (etaleLocalization f).IsContinuous (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) :=
  isContinuous_overMap ‹Etale f› le_rfl

instance : (etaleLocalization f).IsCocontinuous (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) :=
  isCocontinuous_overMap ‹Etale f› le_rfl

/-- The restriction `R : Sh(Y_ét) ⥤ Sh(X_ét)` along an étale morphism `f : X ⟶ Y`:
`(R F)(U) = F(U ⟶ X ⟶ Y)`. For `f` étale it is the pullback `f^*`
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`). -/
noncomputable abbrev etaleRestriction :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Etale.localizationRestriction AddCommGrpCat.{u + 1} f ‹_›

instance : (etaleRestriction f).Additive where
  map_add := rfl

instance : (etaleRestriction f).IsLeftAdjoint :=
  (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f ‹_›).isLeftAdjoint

instance [Mono f] : PreservesFiniteLimits (etaleRestriction f) :=
  inferInstance

instance : PreservesFiniteColimits (etaleRestriction f) :=
  inferInstance

/-- The localization `X ⟶ Y` of the terminal object `𝟙 : X ⟶ X` of `X.Etale`. -/
noncomputable abbrev etaleRestrictionTop : Y.Etale :=
  (etaleLocalization f).obj (MorphismProperty.Over.mk ⊤ (𝟙 X)
    (MorphismProperty.id_mem _ X))

variable (hX : IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem @Etale X)))
  (hY : IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem @Etale Y)))

/-- The comparison `ℤ_X ⟶ R ℤ_Y` of constant sheaves sending `1` to the restriction of `1`. -/
noncomputable def constantSheafToEtaleRestriction :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (etaleRestriction f).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) :=
  (Sheaf.constantHomEquiv hX _).symm
    (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))).obj.map (hY.from (etaleRestrictionTop f)).op
        (Sheaf.constantHomEquiv hY _ (𝟙 _)))

/-- The map `H^n(Y, F) ⟶ H^n(X, R F)` induced by the restriction along an étale monomorphism:
push an `Ext`-class forward along the exact functor `R` and precompose with the comparison
`ℤ_X ⟶ R ℤ_Y` of constant sheaves. -/
noncomputable def etaleRestrictionH [Mono f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Sheaf.H F n →+ Sheaf.H ((etaleRestriction f).obj F) n :=
  ((Ext.mk₀ (constantSheafToEtaleRestriction f hX hY)).precomp _ (zero_add n)).comp
    ((etaleRestriction f).mapExtAddHom _ F n)

variable [Mono f]

lemma etaleRestrictionH_apply (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H F n) :
    etaleRestrictionH f hX hY F n x = (Ext.mk₀ (constantSheafToEtaleRestriction f hX hY)).comp
      (x.mapExactFunctor (etaleRestriction f)) (zero_add n) :=
  rfl

/-- The map on cohomology is natural in the sheaf. -/
lemma etaleRestrictionH_map {F F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ F') (n : ℕ) (x : Sheaf.H F n) :
    etaleRestrictionH f hX hY F' n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((etaleRestriction f).map φ) n (etaleRestrictionH f hX hY F n x) := by
  simp only [etaleRestrictionH_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

/-- The map on cohomology commutes with the connecting homomorphisms. -/
lemma etaleRestrictionH_δSucc {S : ShortComplex (Sheaf Y.smallEtaleTopology
    AddCommGrpCat.{u + 1})} (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H S.X₃ n) :
    etaleRestrictionH f hX hY S.X₁ (n + 1) (Sheaf.H.δSucc hS n x) =
      Sheaf.H.δSucc (hS.map_of_exact (etaleRestriction f)) n
        (etaleRestrictionH f hX hY S.X₃ n x) := by
  simp only [etaleRestrictionH_apply, Sheaf.H.δSucc_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- In degree `0` the map on cohomology is the restriction of global sections along
`(X ⟶ Y) ⟶ (Y ⟶ Y)`. -/
lemma equiv₀_etaleRestrictionH (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ _ hX (etaleRestrictionH f hX hY F 0 x) =
      F.obj.map (hY.from (etaleRestrictionTop f)).op (Sheaf.H.equiv₀ F hY x) := by
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [etaleRestrictionH_apply, Ext.addEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀, Sheaf.H.equiv₀_eq_constantHomEquiv, Sheaf.H.equiv₀_eq_constantHomEquiv]
  erw [Ext.addEquiv₀.apply_symm_apply, Ext.addEquiv₀.apply_symm_apply]
  rw [Sheaf.constantHomEquiv_comp, constantSheafToEtaleRestriction, Equiv.apply_symm_apply]
  exact Sheaf.constantHomEquiv_naturality hY g _

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf.Torsor

open AlgebraicGeometry Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- The restriction of a `G`-torsor along an étale morphism `f : X ⟶ Y`, an `R G`-torsor:
its sections over `U` are those of the torsor over `U ⟶ X ⟶ Y`. -/
noncomputable def restrict (P : Torsor G) : Torsor ((etaleRestriction f).obj G) where
  sheaf := ((etaleLocalization f).sheafPushforwardContinuous
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)).obj P.sheaf
  vadd U a x := P.vadd (op ((etaleLocalization f).obj U.unop)) a x
  zero_vadd U x := P.zero_vadd _ x
  add_vadd U a b x := P.add_vadd _ a b x
  map_vadd g a x := P.map_vadd _ a x
  bijective_vadd U x := P.bijective_vadd _ x
  nonemptySieve_mem U := by
    refine X.smallEtaleTopology.superset_covering ?_
      ((etaleLocalization f).cover_lift (X.smallGrothendieckTopology @Etale)
        (Y.smallGrothendieckTopology @Etale) (P.nonemptySieve_mem _))
    intro V g hg
    exact hg

lemma restrict_vadd (P : Torsor G) (U : X.Etaleᵒᵖ) (a : G.obj.obj
    (op ((etaleLocalization f).obj U.unop))) (x) :
    (P.restrict f).vadd U a x =
      P.vadd (op ((etaleLocalization f).obj U.unop)) a x :=
  rfl

/-- Restriction preserves isomorphism of torsors. -/
lemma restrict_equiv {P P' : Torsor G} (h : P ≈ P') :
    P.restrict f ≈ P'.restrict f := by
  obtain ⟨e⟩ := h
  exact ⟨Iso.ofHom (((etaleLocalization f).sheafPushforwardContinuous
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)).map e.iso.hom)
    fun U a x ↦ e.map_vadd _ a x⟩

end CategoryTheory.Sheaf.Torsor

namespace AlgebraicGeometry.Scheme

open Sheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [Mono f]
  (hX : IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem @Etale X)))
  (hY : IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem @Etale Y)))

/-- The restriction of a lifting torsor is a lifting torsor. -/
lemma etaleRestriction_lifts_equiv {G I Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι : G ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0} (hS : (ShortComplex.mk ι d w).ShortExact)
    (s : Q.obj.obj (op _)) :
    (Torsor.lifts hY hS s).restrict f ≈
      Torsor.lifts hX (hS.map_of_exact (etaleRestriction f))
        (Q.obj.map (hY.from (etaleRestrictionTop f)).op s) := by
  refine ⟨Torsor.Iso.ofHom ⟨{ app U := ↾fun x ↦ ⟨(x : (Torsor.lifts hY hS s).sheaf.obj.obj
    (op ((etaleLocalization f).obj U.unop))).1, ?_⟩, naturality U V g := rfl }⟩ fun U a x ↦ rfl⟩
  have hx : d.hom.app _ (x : (Torsor.lifts hY hS s).sheaf.obj.obj
    (op ((etaleLocalization f).obj U.unop))).1 = _ := x.2
  change d.hom.app _ (x : (Torsor.lifts hY hS s).sheaf.obj.obj
    (op ((etaleLocalization f).obj U.unop))).1 = Q.obj.map ((etaleLocalization f).map
    (hX.from U.unop)).op (Q.obj.map (hY.from (etaleRestrictionTop f)).op s)
  rw [hx, ← ConcreteCategory.comp_apply, ← Q.obj.map_comp, ← op_comp]
  congr 3
  exact congrArg Quiver.Hom.op (hY.hom_ext _ _)

/-- **Classes of restricted torsors.** The class of the restriction of a `G`-torsor `P` is the
image of the class of `P` under `H¹(Y, G) ⟶ H¹(X, R G)`. -/
theorem classH1_etaleRestriction {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Torsor G) :
    Torsor.classH1 _ hX ⟦P.restrict f⟧ =
      etaleRestrictionH f hX hY G 1 (Torsor.classH1 G hY ⟦P⟧) := by
  have hS := Torsor.injectiveSequence_shortExact G
  obtain ⟨s, hs⟩ := Torsor.exists_equiv_lifts hY hS P
  obtain ⟨x, rfl⟩ := (H.equiv₀ _ hY).surjective s
  rw [_root_.Quotient.sound hs, _root_.Quotient.sound (Torsor.restrict_equiv f hs),
    _root_.Quotient.sound (etaleRestriction_lifts_equiv f hX hY hS _), Torsor.classH1_lifts,
    Torsor.classH1_lifts, ← equiv₀_etaleRestrictionH, ← H.δSucc_zero, ← H.δSucc_zero]
  exact (etaleRestrictionH_δSucc f hX hY hS 0 x).symm

end AlgebraicGeometry.Scheme
