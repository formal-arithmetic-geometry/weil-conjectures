/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportSumCompositor

import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange

/-!
# Étale localization of the ambient adjoint and composition

For a separated étale morphism `u : U ⟶ X` of finite type and `f : X ⟶ S`, a right adjoint `G`
of `R(u ≫ f)_!` is the restriction `F ⋙ u^*` of a right adjoint `F` of `Rf_!`, through a unique
isomorphism `e : F ⋙ u^* ≅ G` normalized by its counit
(`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`): the counit of
`R(u ≫ f)_! ⊣ G` is the inverse composition comparison, followed by the counit of the extension
by zero `u_! ⊣ u^*` and by the counit of `Rf_! ⊣ F`. This normalization is the predicate
`AlgebraicGeometry.Etale.IsEtaleAmbientLocalityIso`.

For a second separated étale morphism `u' : U' ⟶ U` of finite type, the isomorphism for `u' ≫ u`
is the composite of `u'^*` of the isomorphism for `u` and of the isomorphism for `u'` and `u ≫ f`
(`AlgebraicGeometry.Etale.etaleAmbientLocalityIso_comp`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- For right adjoints `F` of `Rf_!(c)` and `G` of `R(u ≫ f)_!(d)`, an isomorphism
`e : F ⋙ u^* ≅ G` is the étale localization isomorphism: for every normalization `N` of compact
supports, the counit of `R(u ≫ f)_!(d) ⊣ G` read through `e` is the inverse composition
comparison `R(u ≫ f)_!(d) ≅ Rf_!(c) ∘ u_!`, followed by the counit of `u_! ⊣ u^*` and by the
counit of `Rf_!(c) ⊣ F`. -/
def IsEtaleAmbientLocalityIso {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    {F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U}
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G)
    (e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G) : Prop :=
  ∀ (N : EtaleCompactSupportNormalization A) (K : DerivedCategoryModule A S),
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        (e.hom.app K) ≫ adjG.counit.app K =
      (etaleAmbientLeftComparison A N u f c d).inv.app
          ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u inferInstance).counit.app (F.obj K)) ≫
        adjF.counit.app K

/-- The étale localization isomorphism exists and is unique. -/
theorem existsUnique_isEtaleAmbientLocalityIso {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    {F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U}
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G) :
    ∃! e, IsEtaleAmbientLocalityIso A u f c d adjF adjG e :=
  existsUnique_etaleAmbientAdjointLocalityIso A u f c d F G adjF adjG

/-- Every normalization of compact supports has the canonical graph comparison. -/
theorem EtaleCompactSupportNormalization.comparison_eq_canonical
    (N : EtaleCompactSupportNormalization A) {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    [IsSeparated f] [QuasiCompact f] [IsNoetherian U] [IsNoetherian X]
    (c : Compactification f) :
    N.comparison f c = canonicalEtaleCompactSupportComparison A f c := by
  have hm (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      Mono ((compactificationSheafToDirectImage A c).app F) := by
    have ho (V : c.Z.Etaleᵒᵖ) :
        Mono (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F
          ).hom.app V) :=
      ConcreteCategory.mono_of_injective _
        (openExtensionProperSupport_range A c.i F V.unop).1
    have : Mono
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F).hom :=
      NatTrans.mono_of_mono_app _
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app F) :=
      Sheaf.Hom.mono_of_presheaf_mono c.Z.smallEtaleTopology (ModuleCat.{u + 1} A) _
    have : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom.app F) :=
      inferInstance
    exact this
  let core := canonicalEtaleCompactSupportCore A
  have hs : N.sheafComparison f c = core.sheafComparison f c := by
    apply NatTrans.ext
    funext F
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    rw [N.sheaf_normalization, core.sheaf_normalization]
  have key : N.comparison f c = core.comparison f c := by
    apply Iso.ext_inv
    apply (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh |>.map_injective
    apply NatTrans.ext
    funext K
    simp only [Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
    rw [N.derived_normalization, core.derived_normalization, hs]
  exact key

/-- The comparison isomorphisms between the compact-support functors of compactifications
compose. -/
theorem rightDerivedLowerShriekOfCompactificationIso_hom_comp_hom
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    (c d e : Compactification f) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A d e).hom =
      (rightDerivedLowerShriekOfCompactificationIso A c e).hom := by
  have := c.isSeparated
  have := c.locallyOfFiniteType
  exact congrArg Iso.hom ((unboundedEtaleCompactSupport_comparison_coherence A f).2 c d e)

/-- The comparison to the chosen compact-support functor factors through the comparison
between two compactifications. -/
theorem rightDerivedLowerShriekOfCompactificationIso_hom_comp_rightDerivedLowerShriekIso_hom
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} [HasCompactification f]
    (c d : Compactification f) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
        (rightDerivedLowerShriekIso A d).hom = (rightDerivedLowerShriekIso A c).hom :=
  rightDerivedLowerShriekOfCompactificationIso_hom_comp_hom A c d _

/-- Two comparisons to the chosen compact-support functor differ by the comparison between
the compactifications. -/
theorem rightDerivedLowerShriekIso_hom_comp_inv
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} [HasCompactification f]
    (c d : Compactification f) :
    (rightDerivedLowerShriekIso A c).hom ≫ (rightDerivedLowerShriekIso A d).inv =
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom := by
  rw [Iso.comp_inv_eq,
    rightDerivedLowerShriekOfCompactificationIso_hom_comp_rightDerivedLowerShriekIso_hom]

omit [Finite A] in
/-- The congruence isomorphism of the chosen compact-support functors along `rfl` is the
identity. -/
theorem unboundedEtaleLowerShriekCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    unboundedEtaleLowerShriekCongr A (rfl : f = f) = Iso.refl _ :=
  rfl

/-- Transporting a compactification along an equality of morphisms is compatible with the
congruence isomorphism of the chosen compact-support functors: composing with the comparisons
through the chosen functors does nothing. -/
theorem trans_rightDerivedLowerShriekIso_copy {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] {f f' : X ⟶ Y} [HasCompactification f] [HasCompactification f']
    {P : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y}
    (c : Compactification f) (h : f' = f)
    (α : P ≅ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) :
    α ≪≫ rightDerivedLowerShriekIso A c ≪≫ (unboundedEtaleLowerShriekCongr A h).symm ≪≫
      (rightDerivedLowerShriekIso A (c.copy h)).symm = α := by
  subst h
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    unboundedEtaleLowerShriekCongr_refl, Iso.refl_inv, Category.id_comp]
  exact (congrArg (α.hom.app K ≫ ·) (Iso.hom_inv_id_app _ _)).trans (Category.comp_id _)

/-- An equation of isomorphisms into `Rf_!(c.copy h)` through the comparisons with the chosen
compact-support functors is an equation of isomorphisms into `Rf_!(c)`. -/
theorem eq_trans_of_eq_trans_rightDerivedLowerShriekIso_copy {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f f' : X ⟶ Y} [HasCompactification f]
    [HasCompactification f'] (c : Compactification f) (h : f' = f)
    {P Q R T : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y}
    (a : P ≅ Q) (b : Q ≅ R) (e : R ≅ T)
    (α : T ≅ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (β : P ≅ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (c.copy h))
    (H : β = a ≪≫ b ≪≫ e ≪≫ α ≪≫ rightDerivedLowerShriekIso A c ≪≫
      (unboundedEtaleLowerShriekCongr A h).symm ≪≫ (rightDerivedLowerShriekIso A (c.copy h)).symm) :
    β = a ≪≫ b ≪≫ e ≪≫ α := by
  rw [H, trans_rightDerivedLowerShriekIso_copy]

/-- The ambient left comparison through the chosen compact-support functors: the inverse
canonical comparison of `u`, followed by the chosen composition isomorphism. -/
theorem etaleAmbientLeftComparison_hom_app (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S) [Etale u] [IsSeparated u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [HasCompactification u] [HasCompactification f] [HasCompactification (u ≫ f)]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (M : DerivedCategoryModule A U) :
    (etaleAmbientLeftComparison A N u f c d).hom.app M =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((canonicalEtaleCompactSupportComparison A u (d.ofComp c).restrict).inv.app M ≫
            (rightDerivedLowerShriekIso A (d.ofComp c).restrict).hom.app M) ≫
        (rightDerivedLowerShriekIso A c).hom.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).obj M) ≫
        (unboundedEtaleLowerShriekCompIso A u f).hom.app M ≫
        (rightDerivedLowerShriekIso A d).inv.app M := by
  have h := NatTrans.congr_app
    (unboundedEtaleLowerShriekCompIso_tower A u f c (d.ofComp c)) M
  have hd := (rightDerivedLowerShriekIso_hom_comp_inv A (c.comp (d.ofComp c)) d).symm
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at h
  rw [h]
  simp only [etaleAmbientLeftComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, hd,
    EtaleCompactSupportNormalization.comparison_eq_canonical,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Postcompose an equation between two-fold composites with a further morphism. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {X Y Y' Z W : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (t : Z ⟶ W) :
    f ≫ g ≫ t = f' ≫ g' ≫ t := by
  rw [← Category.assoc, h, Category.assoc]

/-- The sum composition comparison through the chosen compact-support functors: it is
the chosen composition isomorphism conjugated by the canonical comparisons. -/
theorem derivedEtaleSumCompIso_hom_app {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    [IsNoetherian T] (e : U ⟶ X) (v : X ⟶ T) [Etale e] [Etale v] [IsSeparated e]
    [IsSeparated v] [QuasiCompact e] [QuasiCompact v] [HasCompactification e]
    [HasCompactification v] [HasCompactification (e ≫ v)]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v))
    (M : DerivedCategoryModule A U) :
    (derivedEtaleSumCompIso A e v).hom.app M ≫
        (canonicalEtaleCompactSupportComparison A (e ≫ v) k).inv.app M ≫
        (rightDerivedLowerShriekIso A k).hom.app M =
      (canonicalEtaleCompactSupportComparison A v d).inv.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M) ≫
        (rightDerivedLowerShriekIso A d).hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) v).map
          ((canonicalEtaleCompactSupportComparison A e c).inv.app M ≫
            (rightDerivedLowerShriekIso A c).hom.app M) ≫
        (unboundedEtaleLowerShriekCompIso A e v).hom.app M := by
  have h1 := NatTrans.congr_app (etaleSupportSumCompositor A e v c d k) M
  have h2 := NatTrans.congr_app (unboundedEtaleLowerShriekCompIso_tower A e v d (k.ofComp d)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatTrans.hcomp_app, Category.assoc] at h1 h2
  have hc : (rightDerivedLowerShriekIso A c).hom.app M ≫
      (rightDerivedLowerShriekIso A (k.ofComp d).restrict).inv.app M =
        (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict).hom.app M := by
    rw [← NatTrans.comp_app, rightDerivedLowerShriekIso_hom_comp_inv]
  have hk : (rightDerivedLowerShriekIso A (d.comp (k.ofComp d))).hom.app M =
      (rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app M ≫
        (rightDerivedLowerShriekIso A k).hom.app M := by
    rw [← NatTrans.comp_app,
      rightDerivedLowerShriekOfCompactificationIso_hom_comp_rightDerivedLowerShriekIso_hom]
  have h1' :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          ((rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict).hom.app M) ≫
        (rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d)).hom.app M ≫
        (rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app M =
      (canonicalEtaleCompactSupportComparison A v d).hom.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((canonicalEtaleCompactSupportComparison A e c).hom.app M) ≫
        (derivedEtaleSumCompIso A e v).hom.app M ≫
        (canonicalEtaleCompactSupportComparison A (e ≫ v) k).inv.app M := by
    rw [← cancel_mono ((canonicalEtaleCompactSupportComparison A (e ≫ v) k).hom.app M)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact h1
  have h1'' := eq_whisker h1' ((rightDerivedLowerShriekIso A k).hom.app M)
  simp only [Category.assoc] at h1''
  rw [h2, ← (rightDerivedLowerShriekIso A d).hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    hk, CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc _
      ((rightDerivedLowerShriekIso A c).hom.app M), hc, h1'',
    ← (canonicalEtaleCompactSupportComparison A v d).inv.naturality_assoc,
    Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Associativity of the chosen composition isomorphisms for `u' ≫ u ≫ f`, transported along
the comparisons with the compactifications `c`, `d` and `d''` and evaluated on morphisms. -/
theorem unboundedEtaleLowerShriekCompIso_assoc_comparison_app
    {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X) (f : X ⟶ S)
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [HasCompactification u'] [HasCompactification u] [HasCompactification f]
    [HasCompactification (u' ≫ u)] [HasCompactification (u ≫ f)]
    [HasCompactification ((u' ≫ u) ≫ f)] [HasCompactification (u' ≫ u ≫ f)]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d'' : Compactification ((u' ≫ u) ≫ f)) {Z V : DerivedCategoryModule A X}
    {W : DerivedCategoryModule A U} {Y : DerivedCategoryModule A U'} (x₁ : Z ⟶ V)
    (x₂ : V ⟶ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).obj W)
    (g : W ⟶ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) u').obj Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (x₁ ≫ x₂ ≫ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).map g ≫
          (unboundedEtaleLowerShriekCompIso A u' u).hom.app Y) ≫
      (rightDerivedLowerShriekIso A c).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u' ≫ u)).obj Y) ≫
      (unboundedEtaleLowerShriekCompIso A (u' ≫ u) f).hom.app Y ≫
      (rightDerivedLowerShriekIso A d'').inv.app Y =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map (x₁ ≫ x₂) ≫
      (rightDerivedLowerShriekIso A c).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).obj W) ≫
      (unboundedEtaleLowerShriekCompIso A u f).hom.app W ≫
      (rightDerivedLowerShriekIso A d).inv.app W ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map g ≫
      (rightDerivedLowerShriekIso A d).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u').obj Y) ≫
      (unboundedEtaleLowerShriekCompIso A u' (u ≫ f)).hom.app Y ≫
      (unboundedEtaleLowerShriekCongr A (Category.assoc u' u f)).inv.app Y ≫
      (rightDerivedLowerShriekIso A d'').inv.app Y := by
  have hA := NatTrans.congr_app (unboundedEtaleLowerShriekCompIso_assoc A u' u f) Y
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] at hA
  have hA' : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((unboundedEtaleLowerShriekCompIso A u' u).hom.app Y) ≫
      (unboundedEtaleLowerShriekCompIso A (u' ≫ u) f).hom.app Y =
      (unboundedEtaleLowerShriekCompIso A u f).hom.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u').obj Y) ≫
        (unboundedEtaleLowerShriekCompIso A u' (u ≫ f)).hom.app Y ≫
        (unboundedEtaleLowerShriekCongr A (Category.assoc u' u f)).inv.app Y := by
    rw [← reassoc_of% hA, Iso.hom_inv_id_app, Category.comp_id]
  have hCI : (unboundedEtaleLowerShriekCompIso A u f).hom.app W ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (u ≫ f)).map g =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).map g) ≫
      (unboundedEtaleLowerShriekCompIso A u f).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u').obj Y) :=
    ((unboundedEtaleLowerShriekCompIso A u f).hom.naturality g).symm
  rw [← (rightDerivedLowerShriekIso A d).inv.naturality_assoc, Iso.inv_hom_id_app_assoc,
    reassoc_of% hCI, ← (rightDerivedLowerShriekIso A c).hom.naturality_assoc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [(rightDerivedLowerShriekIso A c).hom.naturality_assoc
      ((unboundedEtaleLowerShriekCompIso A u' u).hom.app Y), reassoc_of% hA']
  rfl

/-- The ambient left comparison for a composite `u' ≫ u`, for an arbitrary compactification
`d''` of `(u' ≫ u) ≫ f`, is the composite of the sum composition comparison, of the ambient
left comparisons for `(u, f)` and `(u', u ≫ f)`, and of the comparison of `d'` with `d''`
through the chosen compact-support functors. -/
theorem etaleAmbientLeftComparison_comp_of_compactification
    (N : EtaleCompactSupportNormalization A)
    {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X) (f : X ⟶ S)
    [Etale u'] [IsSeparated u'] [QuasiCompact u'] [Etale u] [IsSeparated u] [QuasiCompact u]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [HasCompactification ((u' ≫ u) ≫ f)] [HasCompactification (u' ≫ u ≫ f)]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d' : Compactification (u' ≫ u ≫ f)) (d'' : Compactification ((u' ≫ u) ≫ f)) :
    etaleAmbientLeftComparison A N (u' ≫ u) f c d'' =
      Functor.isoWhiskerRight (derivedEtaleSumCompIso A u' u).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (etaleAmbientLeftComparison A N u f c d) ≪≫
        etaleAmbientLeftComparison A N u' (u ≫ f) d d' ≪≫ rightDerivedLowerShriekIso A d' ≪≫
        (unboundedEtaleLowerShriekCongr A (Category.assoc u' u f)).symm ≪≫
        (rightDerivedLowerShriekIso A d'').symm := by
  have := c.hasCompactification
  have := d.hasCompactification
  have := (d.ofComp c).restrict.hasCompactification
  have := (d'.ofComp d).restrict.hasCompactification
  have := (d''.ofComp c).restrict.hasCompactification
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  have hS := derivedEtaleSumCompIso_hom_app A u' u (d'.ofComp d).restrict (d.ofComp c).restrict
    (d''.ofComp c).restrict Y
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
    etaleAmbientLeftComparison_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  have e1 : (canonicalEtaleCompactSupportComparison A (u' ≫ u)
        (d''.ofComp c).restrict).inv.app Y ≫
      (rightDerivedLowerShriekIso A (d''.ofComp c).restrict).hom.app Y =
      (derivedEtaleSumCompIso A u' u).inv.app Y ≫
        ((derivedEtaleSumCompIso A u' u).hom.app Y ≫
          (canonicalEtaleCompactSupportComparison A (u' ≫ u)
            (d''.ofComp c).restrict).inv.app Y ≫
          (rightDerivedLowerShriekIso A (d''.ofComp c).restrict).hom.app Y) := by
    simp
  rw [e1, hS, CategoryTheory.Functor.map_comp_assoc _
    ((derivedEtaleSumCompIso A u' u).inv.app Y)]
  refine congrArg ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
    ((derivedEtaleSumCompIso A u' u).inv.app Y) ≫ ·) ?_
  rw [unboundedEtaleLowerShriekCompIso_assoc_comparison_app A u' u f c d d''
    ((canonicalEtaleCompactSupportComparison A u (d.ofComp c).restrict).inv.app
      ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj Y))
    ((rightDerivedLowerShriekIso A (d.ofComp c).restrict).hom.app
      ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj Y))
    ((canonicalEtaleCompactSupportComparison A u' (d'.ofComp d).restrict).inv.app Y ≫
      (rightDerivedLowerShriekIso A (d'.ofComp d).restrict).hom.app Y)]

/-- The ambient left comparison for a composite `u' ≫ u` is the composite of the sum
composition comparison and of the ambient left comparisons for `(u, f)` and `(u', u ≫ f)`. -/
theorem etaleAmbientLeftComparison_comp (N : EtaleCompactSupportNormalization A)
    {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X) (f : X ⟶ S)
    [Etale u'] [IsSeparated u'] [QuasiCompact u'] [Etale u] [IsSeparated u] [QuasiCompact u]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d' : Compactification (u' ≫ u ≫ f)) :
    etaleAmbientLeftComparison A N (u' ≫ u) f c (d'.copy (Category.assoc u' u f)) =
      Functor.isoWhiskerRight (derivedEtaleSumCompIso A u' u).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (etaleAmbientLeftComparison A N u f c d) ≪≫
        etaleAmbientLeftComparison A N u' (u ≫ f) d d' := by
  have := d'.hasCompactification
  have := (d'.copy (Category.assoc u' u f)).hasCompactification
  exact eq_trans_of_eq_trans_rightDerivedLowerShriekIso_copy A d' (Category.assoc u' u f) _ _ _ _ _
    (etaleAmbientLeftComparison_comp_of_compactification A N u' u f c d d' _)

/-- The inverse ambient left comparison for `u' ≫ u`, evaluated on an object, through the
inverse ambient left comparisons for `(u', u ≫ f)` and `(u, f)` and the sum composition
comparison. -/
theorem etaleAmbientLeftComparison_comp_inv_app (N : EtaleCompactSupportNormalization A)
    {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X) (f : X ⟶ S)
    [Etale u'] [IsSeparated u'] [QuasiCompact u'] [Etale u] [IsSeparated u] [QuasiCompact u]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d' : Compactification (u' ≫ u ≫ f)) (Y : DerivedCategoryModule A U') :
    (etaleAmbientLeftComparison A N (u' ≫ u) f c (d'.copy (Category.assoc u' u f))).inv.app Y =
      (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app Y ≫
        (etaleAmbientLeftComparison A N u f c d).inv.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj Y) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((derivedEtaleSumCompIso A u' u).hom.app Y) := by
  rw [etaleAmbientLeftComparison_comp A N u' u f c d d']
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app]
  exact (congrArg (· ≫ _) (Category.comp_id _)).trans (Category.assoc _ _ _)

/-- The composite of the inverse ambient left comparisons for `(u', u ≫ f)` and `(u, f)`,
of the sum composition comparison and of the counit of the composite sum extension
factors through the sum-extension counits for `u'` and `u`. -/
theorem etaleAmbientLeftComparison_inv_app_comp_counit (N : EtaleCompactSupportNormalization A)
    {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X) (f : X ⟶ S)
    [Etale u'] [IsSeparated u'] [QuasiCompact u'] [Etale u] [IsSeparated u] [QuasiCompact u]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d' : Compactification (u' ≫ u ≫ f)) (M : DerivedCategoryModule A X)
    {T : DerivedCategoryModule A S}
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M ⟶ T) :
    (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
        ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj M) ≫
      (etaleAmbientLeftComparison A N u f c d).inv.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj M)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((derivedEtaleSumCompIso A u' u).hom.app
          ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj M)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) (u' ≫ u) inferInstance).counit.app M) ≫ t =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d').map
        ((unboundedEtaleUpperStarCompIso A u' u).hom.app M) ≫
      (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
        ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) u' inferInstance).counit.app
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M)) ≫
      (etaleAmbientLeftComparison A N u f c d).inv.app
        ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) u inferInstance).counit.app M) ≫ t := by
  have n1 : (etaleAmbientLeftComparison A N u f c d).inv.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj M)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory ⋙
          (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory).map
            ((unboundedEtaleUpperStarCompIso A u' u).hom.app M)) =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.map
          ((unboundedEtaleUpperStarCompIso A u' u).hom.app M)) ≫
      (etaleAmbientLeftComparison A N u f c d).inv.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M))) :=
    ((etaleAmbientLeftComparison A N u f c d).inv.naturality _).symm
  have n2 : (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
        ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.map
          ((unboundedEtaleUpperStarCompIso A u' u).hom.app M)) =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d').map
        ((unboundedEtaleUpperStarCompIso A u' u).hom.app M) ≫
      (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
        ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M)) :=
    ((etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.naturality _).symm
  have n3 : (etaleAmbientLeftComparison A N u f c d).inv.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M))) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory.map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u' inferInstance).counit.app
              ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M))) =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) u' inferInstance).counit.app
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M)) ≫
      (etaleAmbientLeftComparison A N u f c d).inv.app
        ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj M) :=
    ((etaleAmbientLeftComparison A N u f c d).inv.naturality _).symm
  rw [← CategoryTheory.Functor.map_comp_assoc, (etaleSumCompositionCounit A u' u).1 M]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [comp_comp_eq_of_comp_eq n1, comp_comp_eq_of_comp_eq n2, comp_comp_eq_of_comp_eq n3]

/-- The étale localization isomorphism is compatible with composition: for separated étale
morphisms `u' : U' ⟶ U`, `u : U ⟶ X` of finite type and `f : X ⟶ S`, if `e₁ : F ⋙ u^* ≅ G`,
`e₂ : G ⋙ u'^* ≅ H` and `e₃ : F ⋙ (u' ≫ u)^* ≅ H` are the localization isomorphisms for
`(u, f)`, `(u', u ≫ f)` and `(u' ≫ u, f)`, then `e₃` is the composite of
`(u' ≫ u)^* ≅ u^* ⋙ u'^*`, of `u'^*` applied to `e₁`, and of `e₂`. -/
theorem etaleAmbientLocalityIso_comp {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X)
    (f : X ⟶ S) [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d' : Compactification (u' ≫ u ≫ f))
    {F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U}
    {H : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U'}
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G)
    (adjH : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d' ⊣ H)
    (e₁ : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G)
    (e₂ : G ⋙ (upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory ≅ H)
    (e₃ : F ⋙ (upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory ≅ H)
    (h₁ : IsEtaleAmbientLocalityIso A u f c d adjF adjG e₁)
    (h₂ : IsEtaleAmbientLocalityIso A u' (u ≫ f) d d' adjG adjH e₂)
    (h₃ : IsEtaleAmbientLocalityIso A (u' ≫ u) f c (d'.copy (Category.assoc u' u f)) adjF adjH
      e₃) :
    e₃ = Functor.isoWhiskerLeft F
        (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) u' u) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) u)
            (upperStar (ModuleCat.{u + 1} A) u')).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ _ ≪≫ e₂ := by
  have hκ : Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) u' u) ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) u)
        (upperStar (ModuleCat.{u + 1} A) u')).symm = unboundedEtaleUpperStarCompIso A u' u :=
    rfl
  rw [hκ]
  obtain ⟨e, -, he⟩ := existsUnique_isEtaleAmbientLocalityIso A (u' ≫ u) f c
    (d'.copy (Category.assoc u' u f)) adjF adjH
  refine (he e₃ h₃).trans (he _ ?_).symm
  intro N K
  have n : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d').map
        ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.map (e₁.hom.app K)) ≫
      (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
        ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.obj (G.obj K)) =
      (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
        ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K))) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.map
          ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.map (e₁.hom.app K))) :=
    (etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.naturality _
  have hε := (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u'
    inferInstance).counit_naturality (e₁.hom.app K)
  have key :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d').map
          ((unboundedEtaleUpperStarCompIso A u' u).hom.app (F.obj K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d').map
          ((upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory.map (e₁.hom.app K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d').map
          (e₂.hom.app K) ≫ adjH.counit.app K =
      ((etaleAmbientLeftComparison A N u' (u ≫ f) d d').inv.app
          ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj (F.obj K)) ≫
        (etaleAmbientLeftComparison A N u f c d).inv.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) u' inferInstance).mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj (F.obj K))) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((derivedEtaleSumCompIso A u' u).hom.app
            ((upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory.obj (F.obj K)))) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (u' ≫ u) inferInstance).counit.app (F.obj K)) ≫
        adjF.counit.app K := by
    simp only [Category.assoc]
    rw [h₂ N K, comp_comp_eq_of_comp_eq n,
      ← CategoryTheory.Functor.map_comp_assoc (rightDerivedLowerShriekOfCompactification _ d),
      hε, CategoryTheory.Functor.map_comp_assoc, h₁ N K,
      etaleAmbientLeftComparison_inv_app_comp_counit]
    rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [etaleAmbientLeftComparison_comp_inv_app A N u' u f c d d']
  exact key

end AlgebraicGeometry.Etale
