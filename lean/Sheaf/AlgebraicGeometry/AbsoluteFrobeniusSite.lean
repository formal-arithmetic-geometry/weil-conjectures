/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusWellDefined
import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
import Sheaf.AlgebraicGeometry.WeaklyEtaleUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusUniversalHomeomorphism
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Canonical trivialization of absolute Frobenius on the small pro-etale site

Source: the main-20261015 blueprint, six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-trf-absolute-frobenius-site`, and Stacks Tag 0F6W
(blueprint: lem-trf-absolute-frobenius-site).

All constant commutative coefficient rings are allowed. The module adjunction unit,
evaluated on every section, fixes the trivialization; its derived version is exact
termwise descent. The comparisons in the compatibility equations are fixed by
fibre-product pasting and conjugation, not independently chosen isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Elaborate the dependent section APIs in declaration order.
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Exact descent of a module-pullback trivialization, including the identity comparison.
Source: blueprint, proof paragraph 4 and Stacks Section 0735
(blueprint: lem-trf-absolute-frobenius-site). -/
noncomputable def proEtaleFrobeniusDerivedIso (A : Type u) [CommRing A]
    {X : Scheme.{u}} {f : X ⟶ X} (e : proEtaleConstantRingPullback A f ≅ 𝟭 _) :
    proEtaleConstantRingDerivedPullback A f ≅ 𝟭 (proEtaleDerivedCategory X A) :=
  Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryIdIso (proEtaleRingModules X (proEtaleConstantRing X A))

/-- Exact descent of a module composition comparison, with the ordinary derived pasting.
Source: Stacks Tag 0D6D and blueprint proof paragraph 4
(blueprint: lem-trf-absolute-frobenius-site). -/
noncomputable def proEtaleFrobeniusDerivedComp (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f) :
    proEtaleConstantRingDerivedPullback A (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback A g ⋙ proEtaleConstantRingDerivedPullback A f :=
  Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso
      (proEtaleConstantRingPullback A g) (proEtaleConstantRingPullback A f)

attribute [local irreducible] proEtaleRingModuleAdjunction
  proEtaleRingModulePullback proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap

-- Keep the adjunction-defined coefficient map behind its constant-section API.
private noncomputable def coefficientDirectMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A) :=
  proEtaleCoefficientDirectImageMap f A

private theorem constantSection_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
      (coefficientDirectMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange f).op.obj W) := by
  unfold coefficientDirectMap
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))
  exact congrArg (fun t ↦ t.app W) h

private theorem constantRing_direct
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap f A)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (asIso (proEtaleCoefficientInverseImageMap f A)) =
        coefficientDirectMap f A := by
  unfold coefficientDirectMap
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (coefficientDirectMap f A)


attribute [local irreducible] coefficientDirectMap
  proEtaleRingDirectImageMap proEtaleConstantRingComparison

private noncomputable def moduleRho {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A) ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A)) :=
  ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

set_option backward.isDefEq.respectTransparency false in
private theorem iterateFrobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY n).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ p ^ n = (f.app U).hom (s ^ p ^ n)
  exact (map_pow (f.app U).hom s _).symm

/-- Specialize the finite-field absolute Frobenius theorem to the prime field.
The global section map also constructs the structure morphism for the empty scheme.
Source: Stacks Project, Tag 0CC8. -/
private theorem frobenius_one_universal (p : ℕ) (T : Scheme.{u})
    (hT : T.IsCharacteristic p) :
    IsUniversalHomeomorphism (T.iterateFrobenius hT.1 (hT.2 ⊤) 1) := by
  classical
  let : Fact p.Prime := ⟨hT.1⟩
  let k₀ := ULift.{u} (ZMod p)
  let D : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := p
      a := 1
      q := p
      prime := hT.1
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := k₀
      card_base := by simp [k₀, Nat.card_eq_fintype_card]
      k := AlgebraicClosure k₀ }
  let φ : k₀ →+* Γ(T, ⊤) :=
    (ZMod.castHom (ringChar.dvd (hT.2 ⊤)) Γ(T, ⊤)).comp ULift.ringEquiv.toRingHom
  let : T.Over (Spec (CommRingCat.of D.k₀)) :=
    ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)⟩
  exact D.absoluteFrobenius_isUniversalHomeomorphism T

private theorem frobenius_add (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p) (a b : ℕ) :
    X.iterateFrobenius hp (hX.2 ⊤) a ≫ X.iterateFrobenius hp (hX.2 ⊤) b =
      X.iterateFrobenius hp (hX.2 ⊤) (a + b) := by
  have h := fun n ↦ ((absoluteFrobenius_well_defined.{u, u} p hp).2 X hX n).1
  rw [← h a, ← h b, ← h (a + b), Nat.add_comm a b, pow_add, End.mul_def]

private theorem frobenius_zero (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p) :
    X.iterateFrobenius hp (hX.2 ⊤) 0 = 𝟙 X := by
  rw [← ((absoluteFrobenius_well_defined.{u, u} p hp).2 X hX 0).1, pow_zero, End.one_def]

private theorem frobenius_universal (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) :
    IsUniversalHomeomorphism (X.iterateFrobenius hp (hX.2 ⊤) n) := by
  induction n with
  | zero => rw [frobenius_zero p hp X hX]; infer_instance
  | succ n ih =>
    rw [← frobenius_add p hp X hX n 1]
    have := frobenius_one_universal p X hX
    exact IsUniversalHomeomorphism.comp _ _

private theorem characteristic_of_map {X V : Scheme.{u}} (p : ℕ)
    (hX : X.IsCharacteristic p) (v : V ⟶ X) : V.IsCharacteristic p := by
  refine ⟨hX.1, natCast_eq_zero_of_natCast_top_eq_zero ?_⟩
  rw [← map_natCast v.appTop.hom, hX.2 ⊤, map_zero]

private noncomputable def relativeFrobeniusMap
    (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
    (V : X.ProEt) : V ⟶ (proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n)).obj V :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (V.left.iterateFrobenius hp ((characteristic_of_map p hX V.hom).2 ⊤) n) V.hom
      (iterateFrobenius_naturality V.hom hp
        ((characteristic_of_map p hX V.hom).2 ⊤) (hX.2 ⊤) n))
    (pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem relativeFrobeniusMap_isIso
    (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
    (V : X.ProEt) : IsIso (relativeFrobeniusMap p hp X hX n V).left := by
  let F := X.iterateFrobenius hp (hX.2 ⊤) n
  let G := V.left.iterateFrobenius hp ((characteristic_of_map p hX V.hom).2 ⊤) n
  let r := (relativeFrobeniusMap p hp X hX n V).left
  have hr₂ : r ≫ pullback.snd V.hom F = V.hom := pullback.lift_snd _ _ _
  have hr₁ : r ≫ pullback.fst V.hom F = G := pullback.lift_fst _ _ _
  have : WeaklyEtale (r ≫ pullback.snd V.hom F) := hr₂.symm ▸ inferInstance
  have : WeaklyEtale r := WeaklyEtale.of_comp r (pullback.snd V.hom F)
  have : IsUniversalHomeomorphism F := frobenius_universal p hp X hX n
  have : IsUniversalHomeomorphism G :=
    frobenius_universal p hp V.left (characteristic_of_map p hX V.hom) n
  have : IsUniversalHomeomorphism (r ≫ pullback.fst V.hom F) := hr₁.symm ▸ inferInstance
  have : IsUniversalHomeomorphism r := .of_comp r (pullback.fst V.hom F)
  exact isIso_of_weaklyEtale_of_universalHomeomorphism r
    (@isUniversalHomeomorphism_le_universally_isHomeomorph _ _ r ‹_›)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def relativeFrobeniusIso
    (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) :
    𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n) := by
  letI (V : X.ProEt) := relativeFrobeniusMap_isIso p hp X hX n V
  refine NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk
      (asIso (relativeFrobeniusMap p hp X hX n V).left)
      (relativeFrobeniusMap p hp X hX n V).w) ?_
  intro V W f
  apply MorphismProperty.Over.Hom.ext
  change f.left ≫ (relativeFrobeniusMap p hp X hX n W).left =
    (relativeFrobeniusMap p hp X hX n V).left ≫
      ((proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n)).map f).left
  apply pullback.hom_ext
  · simpa [relativeFrobeniusMap, pullback.map, Category.assoc] using
      (iterateFrobenius_naturality f.left hp
        ((characteristic_of_map p hX V.hom).2 ⊤)
        ((characteristic_of_map p hX W.hom).2 ⊤) n).symm
  · simp [relativeFrobeniusMap, Category.assoc]

private theorem relativeFrobeniusIso_fst
    (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
    (V : X.ProEt) :
    ((relativeFrobeniusIso p hp X hX n).hom.app V).left ≫
      pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
        V.left.iterateFrobenius hp ((characteristic_of_map p hX V.hom).2 ⊤) n := by
  exact pullback.lift_fst _ _ _

attribute [local irreducible] relativeFrobeniusIso relativeFrobeniusMap

set_option backward.isDefEq.respectTransparency false in
private theorem rho_trivialization (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    coefficientDirectMap f A ≫
      (Functor.sheafPushforwardContinuousNatTrans r.hom CommRingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology X)).app (proEtaleConstantRing X A) = 𝟙 _ := by
  apply (sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, constantSection_unit]
  have hn := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).naturality
      (r.hom.app W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  change (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
      ((proEtaleBaseChange f).op.obj W) ≫
    (proEtaleConstantRing X A).obj.map (r.hom.app W.unop).op =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫ 𝟙 _
  rw [Category.comp_id]
  exact hn.symm.trans (Category.id_comp _)

private theorem moduleRho_trivialization (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    moduleRho f A ≫
      (Functor.sheafPushforwardContinuousNatTrans r.hom RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology X)).app
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing X A)) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  simp only [moduleRho, proEtaleConstantRingComparison, constantRing_direct]
  exact congrArg
    (fun h ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (h.hom.app W))
    (rho_trivialization A X f r)

attribute [local irreducible] CategoryTheory.constantSheaf

private noncomputable def constantPushforwardIso (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    proEtaleConstantRingPushforward A f ≅ 𝟭 _ :=
  SheafOfModules.pushforwardCongr₂ (moduleRho f A) r
    (moduleRho_trivialization A X f r) ≪≫ SheafOfModules.pushforwardId _

private theorem constantPushforwardIso_inv (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
    (m : M.val.obj (Opposite.op V)) :
    ((constantPushforwardIso A X f r).inv.app M).val.app (Opposite.op V) m =
      M.val.map (r.inv.app V).op m := rfl

private noncomputable def constantPullbackIso (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    proEtaleConstantRingPullback A f ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (proEtaleConstantRingAdjunction A f)).symm
    (constantPushforwardIso A X f r).symm

private theorem constantPullbackIso_unit (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
    (m : M.val.obj (Opposite.op V)) :
    ((proEtaleConstantRingAdjunction A f).unit.app M ≫
      (proEtaleConstantRingPushforward A f).map
        ((constantPullbackIso A X f r).hom.app M)).val.app (Opposite.op V) m =
      M.val.map (r.inv.app V).op m := by
  have h := unit_conjugateEquiv_symm Adjunction.id (proEtaleConstantRingAdjunction A f)
    (constantPushforwardIso A X f r).inv M
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at h
  exact (congrArg (fun q : M ⟶ (proEtaleConstantRingPushforward A f).obj M ↦
    q.val.app (Opposite.op V) m) h).symm.trans (constantPushforwardIso_inv A X f r M V m)

private noncomputable def constantPullbackComp (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f :=
  (proEtaleConstantRingModulePullbackComposition f g A).choose

private theorem constantPullbackComp_section (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
    (m : ((proEtaleConstantRingPushforward A f ⋙
      proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)) :
    ((conjugateIsoEquiv
      ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
      (proEtaleConstantRingAdjunction A (f ≫ g)) (constantPullbackComp A f g)).hom.app M).val.app
        (Opposite.op V) m =
      M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m := by
  obtain ⟨d, hd, he⟩ :=
    (proEtaleConstantRingModulePullbackComposition f g A).choose_spec
  unfold constantPullbackComp
  rw [he]
  exact hd M V m

attribute [local irreducible] constantPushforwardIso constantPullbackIso constantPullbackComp

attribute [local irreducible] iterateFrobenius

set_option backward.isDefEq.respectTransparency false in
private theorem derived_trivialization_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) (P : C ⥤ C) (S : D ⥤ D)
    [L.Additive] [P.Additive] [S.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : P ⋙ L ≅ L ⋙ S) (t : P ≅ 𝟭 C) (s : S ≅ 𝟭 D)
    (h : e.hom ≫ Functor.whiskerLeft L s.hom ≫ (Functor.rightUnitor L).hom =
      Functor.whiskerRight t.hom L ≫ (Functor.leftUnitor L).hom) :
    (Functor.mapDerivedCategorySquareIso e).hom ≫
      Functor.whiskerLeft L.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryIdIso D).hom ≫
      (Functor.rightUnitor _).hom =
    Functor.whiskerRight
      (Functor.mapDerivedCategoryNatIso t ≪≫ Functor.mapDerivedCategoryIdIso C).hom
      L.mapDerivedCategory ≫ (Functor.leftUnitor _).hom := by
  have he : e ≪≫ Functor.isoWhiskerLeft L s ≪≫ Functor.rightUnitor L =
      Functor.isoWhiskerRight t L ≪≫ Functor.leftUnitor L := Iso.ext h
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom) he
  have hiR : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor L)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hiL : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor L)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  simp only [Functor.mapDerivedCategoryNatIso_trans, hiR, hiL, Category.comp_id] at hh
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso P L).hom]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft L s),
    reassoc_of% (Functor.mapDerivedCategoryCompIso_comp_id L)]
  rw [← Category.assoc, hh]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight t L),
    reassoc_of% (Functor.mapDerivedCategoryCompIso_id_comp L)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem derived_triangle_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) (P : C ⥤ C) (S : D ⥤ D) (F G : C ⥤ D)
    [L.Additive] [P.Additive] [S.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (c1 : F ≅ P ⋙ L) (c2 : G ≅ L ⋙ S) (q : F ≅ G)
    (d : F.mapDerivedCategory ≅ G.mapDerivedCategory)
    (hd : (Functor.mapDerivedCategoryNatIso q).hom = d.hom)
    (t : P ≅ 𝟭 C) (s : S ≅ 𝟭 D)
    (h : c1.inv ≫ q.hom ≫ c2.hom ≫ Functor.whiskerLeft L s.hom ≫
      (Functor.rightUnitor L).hom =
      Functor.whiskerRight t.hom L ≫ (Functor.leftUnitor L).hom) :
    (Functor.mapDerivedCategoryNatIso c1 ≪≫
      Functor.mapDerivedCategoryCompIso P L).inv ≫ d.hom ≫
      (Functor.mapDerivedCategoryNatIso c2 ≪≫
        Functor.mapDerivedCategoryCompIso L S).hom ≫
      Functor.whiskerLeft L.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryIdIso D).hom ≫
      (Functor.rightUnitor _).hom =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso t ≪≫ Functor.mapDerivedCategoryIdIso C).hom
        L.mapDerivedCategory ≫ (Functor.leftUnitor _).hom := by
  have hh := derived_trivialization_square L P S (c1.symm ≪≫ q ≪≫ c2) t s
    (by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using h)
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc, hd] using hh

private theorem adjoint_trivialization_square
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} {P Q : C ⥤ C} {S T : D ⥤ D}
    {F : C ⥤ D} {G : D ⥤ C}
    (aL : L ⊣ R) (aP : P ⊣ Q) (aS : S ⊣ T) (aF : F ⊣ G)
    (c1 : F ≅ P ⋙ L) (c2 : F ≅ L ⋙ S) (t : P ≅ 𝟭 C) (s : S ≅ 𝟭 D)
    (h : (Functor.leftUnitor R).inv ≫
        Functor.whiskerRight (conjugateEquiv Adjunction.id aS s.hom) R ≫
          (conjugateIsoEquiv (aL.comp aS) aF c2).hom =
      (Functor.rightUnitor R).inv ≫
        Functor.whiskerLeft R (conjugateEquiv Adjunction.id aP t.hom) ≫
          (conjugateIsoEquiv (aP.comp aL) aF c1).hom) :
    c1.inv ≫ c2.hom ≫ Functor.whiskerLeft L s.hom ≫ (Functor.rightUnitor L).hom =
      Functor.whiskerRight t.hom L ≫ (Functor.leftUnitor L).hom := by
  apply (conjugateEquiv aL (aP.comp aL)).injective
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _ (aL.comp Adjunction.id),
    conjugateEquiv_rightUnitor_hom,
    ← conjugateEquiv_comp _ (aL.comp aS), conjugateEquiv_whiskerLeft,
    ← conjugateEquiv_comp _ (Adjunction.id.comp aL),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
    ← conjugateEquiv_comp _ aF]
  rw [← cancel_mono (conjugateIsoEquiv (aP.comp aL) aF c1).hom]
  change (_ ≫ _ ≫ ((conjugateIsoEquiv (aL.comp aS) aF c2).hom ≫
    (conjugateIsoEquiv (aP.comp aL) aF c1).inv)) ≫ _ = _
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
private theorem constantPushforward_obj_map_apply (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    {V W : Y.ProEt} (a : V ⟶ W)
    (m : ((proEtaleConstantRingPushforward A f).obj M).val.obj (Opposite.op W)) :
    ((proEtaleConstantRingPushforward A f).obj M).val.map a.op m =
      M.val.map ((proEtaleBaseChange f).map a).op m := rfl

-- Keep the explicit tensor adjunction and conjugation formula behind their APIs.
attribute [local irreducible] conjugateIsoEquiv conjugateEquiv

private theorem mapDerivedCategoryNatIso_eqToHom
    (A : Type u) [CommRing A] {S T : Scheme.{u}} {f g : S ⟶ T} (h : f = g) :
    ((Functor.mapDerivedCategoryNatIso
      (C := proEtaleRingModules T (proEtaleConstantRing T A))
      (D := proEtaleRingModules S (proEtaleConstantRing S A))
      (F := proEtaleConstantRingPullback A f) (G := proEtaleConstantRingPullback A g)
      (eqToIso (congrArg (proEtaleConstantRingPullback A) h))) :
      proEtaleConstantRingDerivedPullback A f ≅
        proEtaleConstantRingDerivedPullback A g).hom =
      eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) h) := by
  cases h
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem conjugate_section_of_unit
    (A : Type u) [CommRing A] (Z : Scheme.{u}) (f : Z ⟶ Z)
    (s : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (r : 𝟭 Z.ProEt ≅ proEtaleBaseChange f)
    (h : ∀ (M : proEtaleRingModules Z (proEtaleConstantRing Z A)) (V : Z.ProEt)
      (m : M.val.obj (Opposite.op V)),
      ((proEtaleConstantRingAdjunction A f).unit.app M ≫
        (proEtaleConstantRingPushforward A f).map (s.hom.app M)).val.app
          (Opposite.op V) m = M.val.map (r.inv.app V).op m)
    (M : proEtaleRingModules Z (proEtaleConstantRing Z A)) (V : Z.ProEt)
    (m : M.val.obj (Opposite.op V)) :
    ((conjugateEquiv Adjunction.id (proEtaleConstantRingAdjunction A f)
      s.hom).app M).val.app (Opposite.op V) m = M.val.map (r.inv.app V).op m := by
  have hh := unit_conjugateEquiv Adjunction.id (proEtaleConstantRingAdjunction A f)
    s.hom M
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at hh
  exact (congrArg (fun q : M ⟶ (proEtaleConstantRingPushforward A f).obj M ↦
    q.val.app (Opposite.op V) m) hh).trans (h M V m)

private theorem conjugate_comparison_section_transport
    (A : Type u) [CommRing A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
    (h : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
      (m : ((proEtaleConstantRingPushforward A f ⋙
        proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
      ((conjugateIsoEquiv
        ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
        (proEtaleConstantRingAdjunction A (f ≫ g)) c).hom.app M).val.app
          (Opposite.op V) m =
        M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m)
    (k : X ⟶ Z) (hk : k = f ≫ g)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
    (m : ((proEtaleConstantRingPushforward A f ⋙
      proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)) :
    ((conjugateIsoEquiv
      ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
      (proEtaleConstantRingAdjunction A k)
      (eqToIso (congrArg (proEtaleConstantRingPullback A) hk) ≪≫ c)).hom.app M).val.app
        (Opposite.op V) m =
      M.val.map ((MorphismProperty.Over.pullbackComp f g k hk).hom.app V).op m := by
  cases hk
  change ((conjugateIsoEquiv _ _ (Iso.refl _ ≪≫ c)).hom.app M).val.app
    (Opposite.op V) m = _
  rw [Iso.refl_trans]
  exact h M V m

private theorem presheaf_map_square
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) {U V V' W : C}
    (a : U ⟶ V) (b : V ⟶ W) (c : U ⟶ V') (d : V' ⟶ W)
    (h : a ≫ b = c ≫ d) (m : P.obj (Opposite.op W)) :
    P.map a.op (P.map b.op m) = P.map c.op (P.map d.op m) := by
  have hh : b.op ≫ a.op = d.op ≫ c.op := congrArg Quiver.Hom.op h
  calc
    _ = P.map (b.op ≫ a.op) m := by
      simp only [Functor.map_comp]
      rfl
    _ = P.map (d.op ≫ c.op) m := congrArg (fun v ↦ P.map v m) hh
    _ = _ := by
      simp only [Functor.map_comp]
      rfl

private theorem module_natTrans_ext
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat} {F G : C ⥤ SheafOfModules R} (a b : F ⟶ G)
    (h : ∀ (M : C) (V : D) (m : (F.obj M).val.obj (Opposite.op V)),
      (a.app M).val.app (Opposite.op V) m = (b.app M).val.app (Opposite.op V) m) :
    a = b := by
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  cases V with
  | op V =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact h M V

private theorem normalized_presheaf_square
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) {U V V' W : C}
    (a : U ⟶ V) (b : V ⟶ W) (c : U ⟶ V') (d : V' ⟶ W)
    (h : a ≫ b = c ≫ d)
    (x : P.obj (Opposite.op V)) (y : P.obj (Opposite.op V'))
    (m : P.obj (Opposite.op W))
    (hx : x = P.map b.op m) (hy : y = P.map d.op m) :
    P.map a.op x = P.map c.op y := by
  rw [hx, hy]
  exact presheaf_map_square P a b c d h m

private theorem constantPushforward_square
    (A : Type u) [CommRing A] {X Y : Scheme.{u}}
    (u : X ⟶ Y) (fX : X ⟶ X) (fY : Y ⟶ Y) (k : X ⟶ Y)
    (rx : 𝟭 X.ProEt ≅ proEtaleBaseChange fX)
    (ry : 𝟭 Y.ProEt ≅ proEtaleBaseChange fY)
    (cx : proEtaleBaseChange k ⟶ proEtaleBaseChange u ⋙ proEtaleBaseChange fX)
    (cy : proEtaleBaseChange k ⟶ proEtaleBaseChange fY ⋙ proEtaleBaseChange u)
    (hgeom : ∀ V, cx.app V ≫ rx.inv.app ((proEtaleBaseChange u).obj V) =
      cy.app V ≫ (proEtaleBaseChange u).map (ry.inv.app V))
    (sx : 𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)) ⟶
      proEtaleConstantRingPushforward A fX)
    (sy : 𝟭 (proEtaleRingModules Y (proEtaleConstantRing Y A)) ⟶
      proEtaleConstantRingPushforward A fY)
    (dx : proEtaleConstantRingPushforward A fX ⋙ proEtaleConstantRingPushforward A u ⟶
      proEtaleConstantRingPushforward A k)
    (dy : proEtaleConstantRingPushforward A u ⋙ proEtaleConstantRingPushforward A fY ⟶
      proEtaleConstantRingPushforward A k)
    (hsx : ∀ M V m, (sx.app M).val.app (Opposite.op V) m =
      M.val.map (rx.inv.app V).op m)
    (hsy : ∀ M V m, (sy.app M).val.app (Opposite.op V) m =
      M.val.map (ry.inv.app V).op m)
    (hdx : ∀ M V m, (dx.app M).val.app (Opposite.op V) m =
      M.val.map (cx.app V).op m)
    (hdy : ∀ M V m, (dy.app M).val.app (Opposite.op V) m =
      M.val.map (cy.app V).op m) :
    (Functor.leftUnitor (proEtaleConstantRingPushforward A u)).inv ≫
      Functor.whiskerRight sx (proEtaleConstantRingPushforward A u) ≫ dx =
    (Functor.rightUnitor (proEtaleConstantRingPushforward A u)).inv ≫
      Functor.whiskerLeft (proEtaleConstantRingPushforward A u) sy ≫ dy := by
  apply module_natTrans_ext
  intro M V m
  change (dx.app M).val.app (Opposite.op V)
      (((proEtaleConstantRingPushforward A u).map (sx.app M)).val.app
        (Opposite.op V) m) =
    (dy.app M).val.app (Opposite.op V)
      ((sy.app ((proEtaleConstantRingPushforward A u).obj M)).val.app (Opposite.op V) m)
  change (dx.app M).val.app (Opposite.op V)
      ((sx.app M).val.app (Opposite.op ((proEtaleBaseChange u).obj V)) m) = _
  have ex := hdx M V ((sx.app M).val.app
    (Opposite.op ((proEtaleBaseChange u).obj V)) m)
  have ey := hdy M V
    ((sy.app ((proEtaleConstantRingPushforward A u).obj M)).val.app (Opposite.op V) m)
  have hty := (hsy ((proEtaleConstantRingPushforward A u).obj M) V m).trans
    (constantPushforward_obj_map_apply A u M (ry.inv.app V) m)
  have hh := normalized_presheaf_square (C := X.ProEt)
    (M.val.presheaf ⋙ CategoryTheory.forget Ab)
    (U := (proEtaleBaseChange k).obj V)
    (V := (proEtaleBaseChange fX).obj ((proEtaleBaseChange u).obj V))
    (V' := (proEtaleBaseChange u).obj ((proEtaleBaseChange fY).obj V))
    (W := (proEtaleBaseChange u).obj V) (cx.app V)
    (rx.inv.app ((proEtaleBaseChange u).obj V)) (cy.app V)
    ((proEtaleBaseChange u).map (ry.inv.app V)) (hgeom V)
    _ _ m (hsx M ((proEtaleBaseChange u).obj V) m) hty
  exact ex.trans (hh.trans ey.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem frobenius_basechange_naturality
    (p : ℕ) (hp : p.Prime)
    (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
    𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n))
    (hr : (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
    ∃ hV : (p : Γ(V.left, ⊤)) = 0,
    ((r X hX n).hom.app V).left ≫
    pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
    V.left.iterateFrobenius hp hV n))
    (X Y : Scheme.{u}) (hX : X.IsCharacteristic p) (hY : Y.IsCharacteristic p)
    (u : X ⟶ Y) (b : ℕ)
    (w : X.iterateFrobenius hp (hX.2 ⊤) b ≫ u =
      u ≫ Y.iterateFrobenius hp (hY.2 ⊤) b) (V : Y.ProEt) :
      (MorphismProperty.Over.pullbackComp (X.iterateFrobenius hp (hX.2 ⊤) b) u
        (u ≫ Y.iterateFrobenius hp (hY.2 ⊤) b) w.symm).hom.app V ≫
          (r X hX b).inv.app ((proEtaleBaseChange u).obj V) =
        (MorphismProperty.Over.pullbackComp u (Y.iterateFrobenius hp (hY.2 ⊤) b)).hom.app V ≫
          (proEtaleBaseChange u).map ((r Y hY b).inv.app V) := by
  let fX := X.iterateFrobenius hp (hX.2 ⊤) b
  let fY := Y.iterateFrobenius hp (hY.2 ⊤) b
  have hgeom (V : Y.ProEt) :
      (r X hX b).hom.app ((proEtaleBaseChange u).obj V) ≫
        (MorphismProperty.Over.pullbackComp fX u (u ≫ fY) w.symm).inv.app V =
      (proEtaleBaseChange u).map ((r Y hY b).hom.app V) ≫
        (MorphismProperty.Over.pullbackComp u fY).inv.app V := by
    apply MorphismProperty.Over.Hom.ext
    change ((r X hX b).hom.app ((proEtaleBaseChange u).obj V)).left ≫
        ((MorphismProperty.Over.pullbackComp fX u (u ≫ fY) w.symm).inv.app V).left =
      ((proEtaleBaseChange u).map ((r Y hY b).hom.app V)).left ≫
        ((MorphismProperty.Over.pullbackComp u fY).inv.app V).left
    apply pullback.hom_ext (f := V.hom) (g := u ≫ fY)
    · obtain ⟨hW, hW'⟩ := hr X hX b ((proEtaleBaseChange u).obj V)
      obtain ⟨hV, hV'⟩ := hr Y hY b V
      simp only [Category.assoc, MorphismProperty.Over.pullbackComp_inv_app_left]
      dsimp only [pullback.map]
      simp only [pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
      rw [← Category.assoc]
      erw [hW']
      change _ = pullback.lift (f := pullback.snd V.hom fY) (g := u)
        (pullback.fst V.hom u ≫ ((r Y hY b).hom.app V).left)
        (pullback.snd V.hom u) _ ≫ _
      rw [← Category.assoc, pullback.lift_fst, Category.assoc]
      erw [hV']
      exact iterateFrobenius_naturality (pullback.fst V.hom u) hp hW hV b
    · have h₁ := ((r X hX b).hom.app ((proEtaleBaseChange u).obj V) ≫
          (MorphismProperty.Over.pullbackComp fX u (u ≫ fY) w.symm).inv.app V).w
      have h₂ := ((proEtaleBaseChange u).map ((r Y hY b).hom.app V) ≫
          (MorphismProperty.Over.pullbackComp u fY).inv.app V).w
      exact h₁.trans h₂.symm
  have hh :
      (r X hX b).app ((proEtaleBaseChange u).obj V) ≪≫
          (MorphismProperty.Over.pullbackComp fX u (u ≫ fY) w.symm).symm.app V =
        (proEtaleBaseChange u).mapIso ((r Y hY b).app V) ≪≫
          (MorphismProperty.Over.pullbackComp u fY).symm.app V :=
    Iso.ext (hgeom V)
  simpa only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv] using
    congrArg Iso.inv hh



-- Give adjunction mates explicit transformation types before applying coefficient APIs.
private def rightMate {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (t : L₂ ⟶ L₁) : R₁ ⟶ R₂ :=
  conjugateEquiv a b t

private def rightIsoMate {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (t : L₂ ≅ L₁) : R₁ ≅ R₂ :=
  conjugateIsoEquiv a b t

private theorem rightIsoMate_hom {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (t : L₂ ≅ L₁) : (rightIsoMate a b t).hom = (conjugateIsoEquiv a b t).hom := by
  unfold rightIsoMate
  rfl

attribute [local irreducible] rightMate rightIsoMate

set_option backward.isDefEq.respectTransparency false in
private theorem frobenius_basechange_iterate
    (p : ℕ) (hp : p.Prime)
    (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
      𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n))
    (hr : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
      ∃ hV : (p : Γ(V.left, ⊤)) = 0,
        ((r X hX n).hom.app V).left ≫
          pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
            V.left.iterateFrobenius hp hV n)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p) (a b : ℕ)
    (w : X.iterateFrobenius hp (hX.2 ⊤) a ≫ X.iterateFrobenius hp (hX.2 ⊤) b =
      X.iterateFrobenius hp (hX.2 ⊤) (a + b)) (V : X.ProEt) :
    (MorphismProperty.Over.pullbackComp (X.iterateFrobenius hp (hX.2 ⊤) a)
      (X.iterateFrobenius hp (hX.2 ⊤) b)
      (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) w.symm).hom.app V ≫
        (r X hX a).inv.app
          ((proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) b)).obj V) ≫
        (r X hX b).inv.app V = (r X hX (a + b)).inv.app V := by
  let fa := X.iterateFrobenius hp (hX.2 ⊤) a
  let fb := X.iterateFrobenius hp (hX.2 ⊤) b
  let fab := X.iterateFrobenius hp (hX.2 ⊤) (a + b)
  let c := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    fa fb fab w.symm
  have he : (r X hX b).app V ≪≫
      (r X hX a).app ((proEtaleBaseChange fb).obj V) ≪≫ c.symm.app V =
        (r X hX (a + b)).app V := by
    apply Iso.ext
    apply MorphismProperty.Over.Hom.ext
    change ((r X hX b).hom.app V).left ≫
        ((r X hX a).hom.app ((proEtaleBaseChange fb).obj V)).left ≫
          (c.inv.app V).left = ((r X hX (a + b)).hom.app V).left
    apply pullback.hom_ext (f := V.hom) (g := fab)
    · obtain ⟨hW, hWa⟩ := hr X hX a ((proEtaleBaseChange fb).obj V)
      obtain ⟨hV, hVb⟩ := hr X hX b V
      obtain ⟨hV', hVab⟩ := hr X hX (a + b) V
      simp only [c, Category.assoc, MorphismProperty.Over.pullbackComp_inv_app_left]
      dsimp only [pullback.map]
      simp only [pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
      erw [hVab]
      erw [← Category.assoc
        ((r X hX a).hom.app ((proEtaleBaseChange fb).obj V)).left
        (pullback.fst (pullback.snd V.hom fb) fa) (pullback.fst V.hom fb)]
      erw [hWa]
      erw [iterateFrobenius_naturality (pullback.fst V.hom fb) hp hW hV a]
      erw [← Category.assoc]
      erw [hVb]
      have h := frobenius_add p hp V.left (characteristic_of_map p hX V.hom) b a
      rw [Nat.add_comm b a] at h
      exact h
    · exact ((r X hX b).hom.app V ≫
        (r X hX a).hom.app ((proEtaleBaseChange fb).obj V) ≫ c.inv.app V).w.trans
          ((r X hX (a + b)).hom.app V).w.symm
  simpa only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Category.assoc] using
    congrArg Iso.inv he

set_option backward.isDefEq.respectTransparency false in
private theorem basechange_identity_unique
    (X : Scheme.{u}) (f : X ⟶ X) (w : f = 𝟙 X)
    (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (hr : ∀ V : X.ProEt, (r.hom.app V).left ≫ pullback.fst V.hom f = 𝟙 V.left) :
    r = (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).symm ≪≫
      eqToIso (congrArg proEtaleBaseChange w.symm) := by
  subst f
  simp only [eqToIso_refl, Iso.trans_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext V
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext (f := V.hom) (g := 𝟙 X)
  · simpa only [Iso.symm_hom, MorphismProperty.Over.pullbackId_inv_app_left_fst] using hr V
  · exact (r.hom.app V).w.trans
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V).w.symm

set_option backward.isDefEq.respectTransparency false in
private theorem frobenius_basechange_zero
    (p : ℕ) (hp : p.Prime)
    (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
      𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n))
    (hr : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
      ∃ hV : (p : Γ(V.left, ⊤)) = 0,
        ((r X hX n).hom.app V).left ≫
          pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
            V.left.iterateFrobenius hp hV n)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p) :
    ∃ w : X.iterateFrobenius hp (hX.2 ⊤) 0 = 𝟙 X,
      r X hX 0 = (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).symm ≪≫
        eqToIso (congrArg proEtaleBaseChange w.symm) := by
  refine ⟨frobenius_zero p hp X hX,
    basechange_identity_unique X _ (frobenius_zero p hp X hX) (r X hX 0) ?_⟩
  intro V
  obtain ⟨hV, hV0⟩ := hr X hX 0 V
  exact hV0.trans (frobenius_zero p hp V.left (characteristic_of_map p hX V.hom))

private theorem presheaf_map_three
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) {U V W Z : C}
    (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ Z) (d : U ⟶ Z)
    (h : a ≫ b ≫ c = d) (m : P.obj (Opposite.op Z)) :
    P.map a.op (P.map b.op (P.map c.op m)) = P.map d.op m := by
  have hh : c.op ≫ b.op ≫ a.op = d.op := by
    rw [← Category.assoc]
    exact congrArg Quiver.Hom.op h
  calc
    _ = P.map (c.op ≫ b.op ≫ a.op) m := by
      simp only [Functor.map_comp]
      rfl
    _ = _ := congrArg (fun v ↦ P.map v m) hh

set_option backward.isDefEq.respectTransparency false in
private theorem derived_trivialization_product
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P Q S : C ⥤ C) [P.Additive] [Q.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : S ≅ P ⋙ Q) (t : P ≅ 𝟭 C) (s : Q ≅ 𝟭 C) (z : S ≅ 𝟭 C)
    (h : e.hom ≫ Functor.whiskerLeft P s.hom ≫ (Functor.rightUnitor P).hom ≫
      t.hom = z.hom) :
    (Functor.mapDerivedCategoryNatIso z ≪≫ Functor.mapDerivedCategoryIdIso C).hom =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso P Q).hom ≫
        Functor.whiskerLeft P.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryIdIso C).hom ≫
        (Functor.rightUnitor _).hom ≫
        (Functor.mapDerivedCategoryNatIso t ≪≫ Functor.mapDerivedCategoryIdIso C).hom := by
  have he : e ≪≫ Functor.isoWhiskerLeft P s ≪≫ Functor.rightUnitor P ≪≫ t = z :=
    Iso.ext h
  have hh := congrArg (fun v ↦ (Functor.mapDerivedCategoryNatIso v).hom) he
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor P)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  simp only [Functor.mapDerivedCategoryNatIso_trans, hi, Category.id_comp] at hh
  simp only [Iso.trans_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft P s),
    reassoc_of% (Functor.mapDerivedCategoryCompIso_comp_id P)]
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.rightUnitor_hom_app]
  erw [Category.id_comp, Category.id_comp]
  simpa only [NatTrans.comp_app, Category.assoc] using
    congrArg (fun v ↦ v.app K ≫ (Functor.mapDerivedCategoryIdIso C).hom.app K) hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem adjoint_trivialization_product
    {C : Type*} [Category C]
    {P Q S R T U : C ⥤ C}
    (aP : P ⊣ R) (aQ : Q ⊣ T) (aS : S ⊣ U)
    (e : S ≅ P ⋙ Q) (t : P ≅ 𝟭 C) (s : Q ≅ 𝟭 C) (z : S ≅ 𝟭 C)
    (h : rightMate Adjunction.id aP t.hom ≫
        (Functor.leftUnitor R).inv ≫
        Functor.whiskerRight (rightMate Adjunction.id aQ s.hom) R ≫
        (rightIsoMate (aP.comp aQ) aS e).hom =
      rightMate Adjunction.id aS z.hom) :
    e.hom ≫ Functor.whiskerLeft P s.hom ≫ (Functor.rightUnitor P).hom ≫
      t.hom = z.hom := by
  unfold rightMate rightIsoMate at h
  apply (conjugateEquiv Adjunction.id aS).injective
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _ aP,
    ← conjugateEquiv_comp _ (aP.comp Adjunction.id),
    conjugateEquiv_rightUnitor_hom,
    ← conjugateEquiv_comp _ (aP.comp aQ), conjugateEquiv_whiskerLeft]
  simpa only [Category.assoc, conjugateIsoEquiv_apply_hom] using h

section RingedProduct

universe uC vC uR vM
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{uR}} {F G H : C ⥤ C}
variable [F.IsContinuous J J] [G.IsContinuous J J] [H.IsContinuous J J]
variable (φF : R ⟶ (F.sheafPushforwardContinuous RingCat J J).obj R)
variable (φG : R ⟶ (G.sheafPushforwardContinuous RingCat J J).obj R)
variable (φH : R ⟶ (H.sheafPushforwardContinuous RingCat J J).obj R)

set_option backward.isDefEq.respectTransparency false in
private theorem ringedMate_section (L : SheafOfModules.{vM} R ⥤ SheafOfModules.{vM} R)
    (a : L ⊣ SheafOfModules.pushforward.{vM} φF)
    (t : L ≅ 𝟭 (SheafOfModules.{vM} R)) (r : 𝟭 C ≅ F)
    (h : ∀ (M : SheafOfModules.{vM} R) (V : C) (m : M.val.obj (Opposite.op V)),
      (a.unit.app M ≫ (SheafOfModules.pushforward.{vM} φF).map (t.hom.app M)).val.app
          (Opposite.op V) m =
        M.val.map (r.inv.app V).op m)
    (M : SheafOfModules.{vM} R) (V : C) (m : M.val.obj (Opposite.op V)) :
    (((rightMate Adjunction.id a t.hom).app M).val.app
      (Opposite.op V)).hom'.toAddHom.toFun m =
        (M.val.map (r.inv.app V).op).hom'.toAddHom.toFun m := by
  unfold rightMate
  have hh := unit_conjugateEquiv Adjunction.id a t.hom M
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at hh
  exact (congrArg (fun q : M ⟶ (SheafOfModules.pushforward.{vM} φF).obj M ↦
    (q.val.app (Opposite.op V)).hom'.toAddHom.toFun m) hh).trans (h M V m)

set_option backward.isDefEq.respectTransparency false in
private theorem ringedPullback_product
    (LF LG LH : SheafOfModules.{vM} R ⥤ SheafOfModules.{vM} R)
    (aF : LF ⊣ SheafOfModules.pushforward.{vM} φF)
    (aG : LG ⊣ SheafOfModules.pushforward.{vM} φG)
    (aH : LH ⊣ SheafOfModules.pushforward.{vM} φH)
    (c : LH ≅ LG ⋙ LF)
    (rf : 𝟭 C ≅ F) (rg : 𝟭 C ≅ G) (rh : 𝟭 C ≅ H)
    (s : H ⟶ G ⋙ F)
    (hs : ∀ V, s.app V ≫ rf.inv.app (G.obj V) ≫ rg.inv.app V = rh.inv.app V)
    (tf : LF ≅ 𝟭 (SheafOfModules.{vM} R))
    (tg : LG ≅ 𝟭 (SheafOfModules.{vM} R))
    (th : LH ≅ 𝟭 (SheafOfModules.{vM} R))
    (hf : ∀ (M : SheafOfModules.{vM} R) (V : C) (m : M.val.obj (Opposite.op V)),
      (aF.unit.app M ≫ (SheafOfModules.pushforward.{vM} φF).map (tf.hom.app M)).val.app
          (Opposite.op V) m =
        M.val.map (rf.inv.app V).op m)
    (hg : ∀ (M : SheafOfModules.{vM} R) (V : C) (m : M.val.obj (Opposite.op V)),
      (aG.unit.app M ≫ (SheafOfModules.pushforward.{vM} φG).map (tg.hom.app M)).val.app
          (Opposite.op V) m =
        M.val.map (rg.inv.app V).op m)
    (hh : ∀ (M : SheafOfModules.{vM} R) (V : C) (m : M.val.obj (Opposite.op V)),
      (aH.unit.app M ≫ (SheafOfModules.pushforward.{vM} φH).map (th.hom.app M)).val.app
          (Opposite.op V) m =
        M.val.map (rh.inv.app V).op m)
    (δ : SheafOfModules.pushforward.{vM} φF ⋙ SheafOfModules.pushforward.{vM} φG ⟶
      SheafOfModules.pushforward.{vM} φH)
    (hδ : (rightIsoMate (aG.comp aF) aH c).hom = δ)
    (hd : ∀ (M : SheafOfModules.{vM} R) (V : C),
      (forget₂ (ModuleCat.{vM} (R.obj.obj (Opposite.op V))) Ab).map
        ((δ.app M).val.app (Opposite.op V)) = M.val.presheaf.map (s.app V).op) :
    c.hom ≫ Functor.whiskerLeft LG tf.hom ≫ (Functor.rightUnitor LG).hom ≫
      tg.hom = th.hom := by
  let sf : 𝟭 (SheafOfModules.{vM} R) ⟶ (SheafOfModules.pushforward.{vM} φF) := rightMate
      Adjunction.id aF tf.hom
  let sg : 𝟭 (SheafOfModules.{vM} R) ⟶ (SheafOfModules.pushforward.{vM} φG) := rightMate
      Adjunction.id aG tg.hom
  let sh : 𝟭 (SheafOfModules.{vM} R) ⟶ (SheafOfModules.pushforward.{vM} φH) := rightMate
      Adjunction.id aH th.hom
  let d := δ
  have hsf := ringedMate_section φF LF aF tf rf hf
  have hsg := ringedMate_section φG LG aG tg rg hg
  have hsh := ringedMate_section φH LH aH th rh hh
  have hright : sg ≫ (Functor.leftUnitor (SheafOfModules.pushforward.{vM} φG)).inv ≫
      Functor.whiskerRight sf (SheafOfModules.pushforward.{vM} φG) ≫ d = sh := by
    apply module_natTrans_ext
    intro M V m
    change ((d.app M).val.app (Opposite.op V)).hom'.toAddHom.toFun
        (((sf.app M).val.app (Opposite.op (G.obj V))).hom'.toAddHom.toFun
          (((sg.app M).val.app (Opposite.op V)).hom'.toAddHom.toFun m)) =
      ((sh.app M).val.app (Opposite.op V)).hom'.toAddHom.toFun m
    have hdd (x) : ((d.app M).val.app (Opposite.op V)).hom'.toAddHom.toFun x =
        (M.val.map (s.app V).op).hom'.toAddHom.toFun x :=
      congrArg (fun q ↦ q x) (hd M V)
    calc
      _ = (M.val.map (s.app V).op).hom'.toAddHom.toFun
          (((sf.app M).val.app (Opposite.op (G.obj V))).hom'.toAddHom.toFun
            (((sg.app M).val.app (Opposite.op V)).hom'.toAddHom.toFun m)) := hdd _
      _ = (M.val.map (s.app V).op).hom'.toAddHom.toFun
          ((M.val.map (rf.inv.app (G.obj V)).op).hom'.toAddHom.toFun
            (((sg.app M).val.app (Opposite.op V)).hom'.toAddHom.toFun m)) :=
        congrArg (fun x : M.val.obj (Opposite.op (F.obj (G.obj V))) ↦
          (M.val.map (s.app V).op).hom'.toAddHom.toFun x)
          (hsf M (G.obj V) _)
      _ = (M.val.map (s.app V).op).hom'.toAddHom.toFun
          ((M.val.map (rf.inv.app (G.obj V)).op).hom'.toAddHom.toFun
            ((M.val.map (rg.inv.app V).op).hom'.toAddHom.toFun m)) :=
        congrArg (fun x : M.val.obj (Opposite.op (G.obj V)) ↦
          (M.val.map (s.app V).op).hom'.toAddHom.toFun
            ((M.val.map (rf.inv.app (G.obj V)).op).hom'.toAddHom.toFun x))
          (hsg M V m)
      _ = (M.val.map (rh.inv.app V).op).hom'.toAddHom.toFun m :=
        presheaf_map_three (M.val.presheaf ⋙ CategoryTheory.forget Ab)
          (s.app V) (rf.inv.app (G.obj V)) (rg.inv.app V) (rh.inv.app V) (hs V) m
      _ = _ := (hsh M V m).symm
  dsimp only [d] at hright
  rw [← hδ] at hright
  exact adjoint_trivialization_product aG aF aH c tg tf th hright

end RingedProduct

-- Forget scalars before comparing the composite direct-image normalization.
private theorem constantComparison_forget (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f g k : X ⟶ X)
    (d : proEtaleConstantRingPushforward A f ⋙ proEtaleConstantRingPushforward A g ⟶
      proEtaleConstantRingPushforward A k)
    (s : proEtaleBaseChange k ⟶ proEtaleBaseChange g ⋙ proEtaleBaseChange f)
    (h : ∀ M V m, (d.app M).val.app (Opposite.op V) m = M.val.map (s.app V).op m) :
    ∀ M V, (forget₂ _ Ab).map ((d.app M).val.app (Opposite.op V)) =
      M.val.presheaf.map (s.app V).op := by
  intro M V
  apply ConcreteCategory.hom_ext
  intro m
  exact h M V m

-- Keep the specified adjunctions as parameters while changing the ring-sheaf presentation.
set_option backward.isDefEq.respectTransparency false in
private theorem constantAdjunction_product (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f g k : X ⟶ X)
    (LF LG LH : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A))
    (aF : LF ⊣ proEtaleConstantRingPushforward A f)
    (aG : LG ⊣ proEtaleConstantRingPushforward A g)
    (aH : LH ⊣ proEtaleConstantRingPushforward A k)
    (c : LH ≅ LG ⋙ LF)
    (rf : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (rg : 𝟭 X.ProEt ≅ proEtaleBaseChange g)
    (rh : 𝟭 X.ProEt ≅ proEtaleBaseChange k)
    (s : proEtaleBaseChange k ⟶ proEtaleBaseChange g ⋙ proEtaleBaseChange f)
    (hs : ∀ V, s.app V ≫ rf.inv.app ((proEtaleBaseChange g).obj V) ≫
      rg.inv.app V = rh.inv.app V)
    (tf : LF ≅ 𝟭 _)
    (tg : LG ≅ 𝟭 _)
    (th : LH ≅ 𝟭 _)
    (hf : ∀ M V m,
      (aF.unit.app M ≫ (proEtaleConstantRingPushforward A f).map (tf.hom.app M)).val.app
        (Opposite.op V) m = M.val.map (rf.inv.app V).op m)
    (hg : ∀ M V m,
      (aG.unit.app M ≫ (proEtaleConstantRingPushforward A g).map (tg.hom.app M)).val.app
        (Opposite.op V) m = M.val.map (rg.inv.app V).op m)
    (hh : ∀ M V m,
      (aH.unit.app M ≫ (proEtaleConstantRingPushforward A k).map (th.hom.app M)).val.app
        (Opposite.op V) m = M.val.map (rh.inv.app V).op m)
    (δ : proEtaleConstantRingPushforward A f ⋙ proEtaleConstantRingPushforward A g ⟶
      proEtaleConstantRingPushforward A k)
    (hδ : (rightIsoMate (aG.comp aF) aH c).hom = δ)
    (hd : ∀ M V, (forget₂ _ Ab).map ((δ.app M).val.app (Opposite.op V)) =
      M.val.presheaf.map (s.app V).op) :
    c.hom ≫ Functor.whiskerLeft LG tf.hom ≫
      (Functor.rightUnitor LG).hom ≫ tg.hom = th.hom := by
  exact ringedPullback_product.{u + 1, u, u + 1, u + 1} (C := X.ProEt)
    (J := ProEt.topology X)
    (F := proEtaleBaseChange f) (G := proEtaleBaseChange g) (H := proEtaleBaseChange k)
    (moduleRho f A) (moduleRho g A) (moduleRho k A)
    LF LG LH aF aG aH c rf rg rh s hs tf tg th hf hg hh δ hδ hd

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryIdIso

set_option backward.isDefEq.respectTransparency false in
/-- Absolute Frobenius has the canonical, open-compatible and iterate-compatible
trivialization on the ordinary unbounded derived category of its small pro-etale site.
The existential families are normalized on sections, so record the actual canonical maps.
The zero-iterate clause retains the identity, including on the empty scheme.

Source: main-20261015 blueprint, lem-trf-absolute-frobenius-site, and Stacks Tag 0F6W
(blueprint: lem-trf-absolute-frobenius-site).

Proof: the explicit relative Frobenius lift has projections `(F_V^n, v)` and is
natural by the two projection equations. It is weakly etale by cancellation along
the second projection and a universal homeomorphism by cancellation along the first;
the weakly-etale universal-homeomorphism criterion makes it an isomorphism.

On constant coefficients, restriction along this site isomorphism fixes constant
sections, hence agrees with the coefficient comparison after sheafification.
Conjugating the resulting direct-image isomorphism gives the module trivialization
and its normalized unit equation. The same constant-section argument constructs
the normalized composition comparison for every commutative coefficient ring.

Projection uniqueness gives the restriction, iterate and zero identities on site
objects. Restriction of module sections and injectivity of adjunction conjugation
give their module versions. The exact-derived natural-isomorphism coherence API
then gives the two displayed derived equations, without a K-flat resolution. -/
theorem absoluteFrobenius_proEtale_trivialization (p : ℕ) (hp : Nat.Prime p)
    (A : Type u) [CommRing A] :
    ∃ (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
        𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n)),
      (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
        ∃ hV : (p : Γ(V.left, ⊤)) = 0,
          ((r X hX n).hom.app V).left ≫
              pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
            V.left.iterateFrobenius hp hV n) ∧
      ∃ (comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
          proEtaleConstantRingPullback A (f ≫ g) ≅
            proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f),
        (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
          (m : ((proEtaleConstantRingPushforward A f ⋙
            proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
          ((conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
            (proEtaleConstantRingAdjunction A (f ≫ g)) (comp f g)).hom.app M).val.app
              (Opposite.op V) m =
            M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m) ∧
        ∃ (tau : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
            proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) n) ≅ 𝟭 _),
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
            (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
            (m : M.val.obj (Opposite.op V)),
            ((proEtaleConstantRingAdjunction A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).map ((tau X hX n).hom.app M)).val.app
                  (Opposite.op V) m = M.val.map ((r X hX n).inv.app V).op m) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (U : X.Opens),
            ∃ (hU : U.toScheme.IsCharacteristic p)
              (w : U.toScheme.iterateFrobenius hp (hU.2 ⊤) n ≫ U.ι =
                U.ι ≫ X.iterateFrobenius hp (hX.2 ⊤) n),
              (proEtaleFrobeniusDerivedComp A U.ι
                (X.iterateFrobenius hp (hX.2 ⊤) n)
                (comp U.ι (X.iterateFrobenius hp (hX.2 ⊤) n))).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (U.toScheme.iterateFrobenius hp (hU.2 ⊤) n) U.ι
                  (comp (U.toScheme.iterateFrobenius hp (hU.2 ⊤) n) U.ι)).hom ≫
                Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A U.ι)
                  (proEtaleFrobeniusDerivedIso A (tau U.toScheme hU n)).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight (proEtaleFrobeniusDerivedIso A (tau X hX n)).hom
                (proEtaleConstantRingDerivedPullback A U.ι) ≫ (Functor.leftUnitor _).hom) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (a b : ℕ),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) a ≫
                X.iterateFrobenius hp (hX.2 ⊤) b =
                  X.iterateFrobenius hp (hX.2 ⊤) (a + b),
              (proEtaleFrobeniusDerivedIso A (tau X hX (a + b))).hom =
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b)
                  (comp (X.iterateFrobenius hp (hX.2 ⊤) a)
                    (X.iterateFrobenius hp (hX.2 ⊤) b))).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
                  (proEtaleFrobeniusDerivedIso A (tau X hX a)).hom ≫
                (Functor.rightUnitor _).hom ≫
                (proEtaleFrobeniusDerivedIso A (tau X hX b)).hom) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) 0 = 𝟙 X,
              r X hX 0 =
                (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).symm ≪≫
                  eqToIso (congrArg proEtaleBaseChange w.symm)) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      let r := fun X hX n ↦ relativeFrobeniusIso p hp X hX n
      have hr : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
        ∃ hV : (p : Γ(V.left, ⊤)) = 0,
          ((r X hX n).hom.app V).left ≫
            pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
              V.left.iterateFrobenius hp hV n := by
        intro X hX n V
        exact ⟨(characteristic_of_map p hX V.hom).2 ⊤,
          relativeFrobeniusIso_fst p hp X hX n V⟩
      clear_value r
      let comp := @constantPullbackComp.{u} A _
      let tau := fun X hX n ↦ constantPullbackIso A X
        (X.iterateFrobenius hp (hX.2 ⊤) n) (r X hX n)
      have hc : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
        (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
        (m : ((proEtaleConstantRingPushforward A f ⋙
          proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
        ((conjugateIsoEquiv
          ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
          (proEtaleConstantRingAdjunction A (f ≫ g)) (comp f g)).hom.app M).val.app
            (Opposite.op V) m =
          M.val.map ((MorphismProperty.Over.pullbackComp
            (P := @WeaklyEtale) (Q := ⊤) f g).hom.app V).op m :=
        fun _ _ _ f g M V m ↦ constantPullbackComp_section A f g M V m
      clear_value comp
      have ht : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
        (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
        (m : M.val.obj (Opposite.op V)),
        ((proEtaleConstantRingAdjunction A
            (X.iterateFrobenius hp (hX.2 ⊤) n)).unit.app M ≫
          (proEtaleConstantRingPushforward A
            (X.iterateFrobenius hp (hX.2 ⊤) n)).map ((tau X hX n).hom.app M)).val.app
              (Opposite.op V) m = M.val.map ((r X hX n).inv.app V).op m :=
        fun X hX n M V m ↦ constantPullbackIso_unit A X
          (X.iterateFrobenius hp (hX.2 ⊤) n) (r X hX n) M V m
      clear_value tau
      refine ⟨r, hr, @comp, hc, tau, ht, ?_, ?_, ?_⟩
      · intro X hX b U
        let hU := characteristic_of_map p hX U.ι
        let u := U.ι
        let fX := U.toScheme.iterateFrobenius hp (hU.2 ⊤) b
        let fY := X.iterateFrobenius hp (hX.2 ⊤) b
        have w : fX ≫ u = u ≫ fY :=
          iterateFrobenius_naturality u hp (hU.2 ⊤) (hX.2 ⊤) b
        refine ⟨hU, w, ?_⟩
        let L := proEtaleConstantRingPullback A u
        have hgeom' := frobenius_basechange_naturality p hp r hr U.toScheme X hU hX u b w
        let aL := proEtaleConstantRingAdjunction A u
        let aX := proEtaleConstantRingAdjunction A fX
        let aY := proEtaleConstantRingAdjunction A fY
        let c2 := eqToIso (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp fX u
        let d1 := conjugateIsoEquiv (aY.comp aL)
          (proEtaleConstantRingAdjunction A (u ≫ fY)) (comp u fY)
        let d2 := conjugateIsoEquiv (aL.comp aX)
          (proEtaleConstantRingAdjunction A (u ≫ fY)) c2
        have hright : (Functor.leftUnitor (proEtaleConstantRingPushforward A u)).inv ≫
            Functor.whiskerRight (conjugateEquiv Adjunction.id aX (tau U.toScheme hU b).hom)
              (proEtaleConstantRingPushforward A u) ≫ d2.hom =
          (Functor.rightUnitor (proEtaleConstantRingPushforward A u)).inv ≫
            Functor.whiskerLeft (proEtaleConstantRingPushforward A u)
              (conjugateEquiv Adjunction.id aY (tau X hX b).hom) ≫ d1.hom := by
          have hsx := conjugate_section_of_unit A U.toScheme fX (tau U.toScheme hU b)
            (r U.toScheme hU b) (ht U.toScheme hU b)
          have hsy := conjugate_section_of_unit A X fY (tau X hX b) (r X hX b) (ht X hX b)
          have hdx := conjugate_comparison_section_transport A fX u (comp fX u)
            (hc U.toScheme U.toScheme X fX u) (u ≫ fY) w.symm
          have hdy := hc U.toScheme X X u fY
          exact constantPushforward_square A u fX fY (u ≫ fY) (r U.toScheme hU b) (r X hX b)
            (MorphismProperty.Over.pullbackComp
              (P := @WeaklyEtale) (Q := ⊤) fX u (u ≫ fY) w.symm).hom
            (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) u fY).hom hgeom'
            (conjugateEquiv Adjunction.id aX (tau U.toScheme hU b).hom)
            (conjugateEquiv Adjunction.id aY (tau X hX b).hom) d2.hom d1.hom
            hsx hsy hdx hdy
        have hmod := adjoint_trivialization_square.{u + 2, u + 2, u + 1, u + 1} aL aY aX
          (proEtaleConstantRingAdjunction A (u ≫ fY))
          (comp u fY) c2 (tau X hX b) (tau U.toScheme hU b) hright
        have hder := derived_triangle_square.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
          L (proEtaleConstantRingPullback A fY)
          (proEtaleConstantRingPullback A fX)
          (proEtaleConstantRingPullback A (u ≫ fY))
          (proEtaleConstantRingPullback A (fX ≫ u)) (comp u fY) (comp fX u)
          (eqToIso (congrArg (proEtaleConstantRingPullback A) w.symm))
          (Functor.mapDerivedCategoryNatIso
            (eqToIso (congrArg (proEtaleConstantRingPullback A) w.symm)))
          rfl (tau X hX b) (tau U.toScheme hU b)
          (by
            dsimp only [c2, Iso.trans_hom, eqToIso.hom] at hmod
            simpa only [eqToIso.hom, Category.assoc] using hmod)
        rw [mapDerivedCategoryNatIso_eqToHom A w.symm] at hder
        exact hder
      · intro X hX a b
        have w : (X.iterateFrobenius hp (hX.2 ⊤) a) ≫ (X.iterateFrobenius hp (hX.2 ⊤) b) =
            (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) := frobenius_add p hp X hX a b
        refine ⟨w, ?_⟩
        have hgeom : ∀ V : X.ProEt,
            (MorphismProperty.Over.pullbackComp
              (P := @WeaklyEtale) (Q := ⊤) (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp
                  (hX.2 ⊤) b) (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) w.symm).hom.app V ≫
              (r X hX a).inv.app ((proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) b)).obj V) ≫
                (r X hX b).inv.app V = (r X hX (a + b)).inv.app V := by
          exact frobenius_basechange_iterate p hp r hr X hX a b w
        let δ : proEtaleConstantRingPushforward A (X.iterateFrobenius hp (hX.2 ⊤) a) ⋙
            proEtaleConstantRingPushforward A (X.iterateFrobenius hp (hX.2 ⊤) b) ⟶
                proEtaleConstantRingPushforward A (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) :=
          (conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) b)).comp
              (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) a)))
            (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) (a + b)))
            (eqToIso (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp (X.iterateFrobenius
                hp (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b))).hom
        have hδ : (rightIsoMate ((proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤)
            b)).comp (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) a)))
            (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) (a + b))) (eqToIso
            (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp (X.iterateFrobenius hp (hX.2
            ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b))).hom = δ :=
          rightIsoMate_hom ((proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤)
              b)).comp (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) a)))
              (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) (a + b))) (eqToIso
              (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp (X.iterateFrobenius hp
              (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b))
        have hdm := conjugate_comparison_section_transport A (X.iterateFrobenius hp (hX.2 ⊤) a)
            (X.iterateFrobenius hp (hX.2 ⊤) b) (comp (X.iterateFrobenius hp (hX.2 ⊤) a)
            (X.iterateFrobenius hp (hX.2 ⊤) b))
          (hc X X X (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b))
              (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) w.symm
        have hd := constantComparison_forget A X (X.iterateFrobenius hp (hX.2 ⊤) a)
            (X.iterateFrobenius hp (hX.2 ⊤) b) (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) δ
          (MorphismProperty.Over.pullbackComp
              (P := @WeaklyEtale) (Q := ⊤) (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp
                  (hX.2 ⊤) b) (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) w.symm).hom hdm
        have hf : ∀ M V m,
            ((proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) a)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) a)).map
                  ((tau X hX a).hom.app M)).val.app (Opposite.op V) m =
              M.val.map ((r X hX a).inv.app V).op m := ht X hX a
        have hg : ∀ M V m,
            ((proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) b)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) b)).map
                  ((tau X hX b).hom.app M)).val.app (Opposite.op V) m =
              M.val.map ((r X hX b).inv.app V).op m := ht X hX b
        have hh : ∀ M V m,
            ((proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) (a + b))).unit.app M
                ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) (a + b))).map
                  ((tau X hX (a + b)).hom.app M)).val.app (Opposite.op V) m =
              M.val.map ((r X hX (a + b)).inv.app V).op m := ht X hX (a + b)
        have hmod : (eqToIso (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp
            (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b)).hom ≫
            Functor.whiskerLeft (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
                (tau X hX a).hom ≫
              (Functor.rightUnitor (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤)
                  b))).hom ≫
                (tau X hX b).hom = (tau X hX (a + b)).hom := by
          exact constantAdjunction_product A X (X.iterateFrobenius hp (hX.2 ⊤) a)
              (X.iterateFrobenius hp (hX.2 ⊤) b) (X.iterateFrobenius hp (hX.2 ⊤) (a + b))
            (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) a))
                (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
            (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) (a + b)))
                (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) a))
                (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) b))
                (proEtaleConstantRingAdjunction A (X.iterateFrobenius hp (hX.2 ⊤) (a + b))) (eqToIso
                (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp (X.iterateFrobenius hp
                (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b))
            (r X hX a) (r X hX b) (r X hX (a + b))
            (MorphismProperty.Over.pullbackComp
              (P := @WeaklyEtale) (Q := ⊤) (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp
                  (hX.2 ⊤) b) (X.iterateFrobenius hp (hX.2 ⊤) (a + b)) w.symm).hom hgeom
            (tau X hX a) (tau X hX b) (tau X hX (a + b)) hf hg hh δ hδ hd
        have hder := derived_trivialization_product.{u + 2, u + 1, u + 2}
          (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
              (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) a))
          (proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) (a + b))) (eqToIso
              (congrArg (proEtaleConstantRingPullback A) w.symm) ≪≫ comp (X.iterateFrobenius hp
              (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b))
          (tau X hX b) (tau X hX a) (tau X hX (a + b)) hmod
        simp only [Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom, Category.assoc] at hder
        rw [mapDerivedCategoryNatIso_eqToHom A w.symm] at hder
        dsimp only [proEtaleFrobeniusDerivedIso, proEtaleFrobeniusDerivedComp,
          Iso.trans_hom]
        simpa only [Category.assoc] using hder
      · exact frobenius_basechange_zero p hp r hr


end AlgebraicGeometry.Scheme
