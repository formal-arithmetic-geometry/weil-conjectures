/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-! # Closed exceptional coefficient transposes

Source: Weil blueprint, lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles).

All domain restrictions use the published etale-origin finite-Tor predicate.
The adjunctions below are conditional data, as in the node; no preservation or
invertibility assertion for exceptional coefficient change is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
namespace ClosedCoefficient

/-- Notation for the recorded fixed-module finite-Tor category; no new object property.
Source: blueprint finite-Tor convention (blueprint: lem-coef-closed-transpose-cocycles). -/
abbrev C (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).FullSubcategory

/-- Restrict an actual ambient functor to the indicated finite-Tor domains.
Source: blueprint conditional-domain convention
(blueprint: lem-coef-closed-transpose-cocycles). -/
def restrict {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}}
    (F : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B)))
    (h : ∀ K : C A X, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) Y
      (F.obj K.obj)) : C A X ⥤ C B Y :=
  ObjectProperty.lift _ ((DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} A) X).ι ⋙ F) h

/-- Closure of a domain under ordinary derived direct image along the closed map.
Source: blueprint conditional closed adjunction
(blueprint: lem-coef-closed-transpose-cocycles). -/
abbrev PushClosed (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  ∀ K : C A Z, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
    ((R(lowerStar (ModuleCat.{u + 1} A) i)).obj K.obj)

/-- Ordinary direct image on the stipulated domains, with no altered construction.
Source: blueprint closed ordinary image
(blueprint: lem-coef-closed-transpose-cocycles). -/
def push (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (h : PushClosed A i) :
    C A Z ⥤ C A X :=
  restrict (R(lowerStar (ModuleCat.{u + 1} A) i)) h

/-- Closure under the specified uncompleted derived coefficient extension.
Source: blueprint conditional-domain hypothesis
(blueprint: lem-coef-closed-transpose-cocycles). -/
abbrev ScalarClosed {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :=
  ∀ K : C A X, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) X
    ((@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A B
        inferInstance inferInstance φ).obj K.obj)

/-- Uncompleted derived scalar extension restricted using the given closure proof.
Source: blueprint notation S and Stacks 06YY
(blueprint: lem-coef-closed-transpose-cocycles). -/
def scalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (h : ScalarClosed φ X) :
    C A X ⥤ C B X :=
  restrict (@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A B
        inferInstance inferInstance φ) h

/-- The ordinary comparison, with its published components, on the given domains.
Source: blueprint c_i = lem-coef-finite-direct-image
(blueprint: lem-coef-closed-transpose-cocycles). -/
def comparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hA : PushClosed A i) (hB : PushClosed B i)
    (hZ : ScalarClosed φ Z) (hX : ScalarClosed φ X) :
    push A i hA ⋙ scalar φ X hX ⟶ scalar φ Z hZ ⋙ push B i hB where
  app K := ObjectProperty.homMk (finiteCoefficientChangeDirectImageMap φ i K.obj)
  naturality K L f := by
    ext
    exact finiteCoefficientDirectImageMap_naturality φ i f.hom

/-- The exceptional comparison is exactly the right mate of the inverse ordinary
comparison. Any supplied right adjoints are normalized by their given adjunctions;
these are the constructible exceptional functors of the node, not arbitrary maps.
Source: blueprint exceptional-counit transpose; Mathlib mateEquiv
(blueprint: lem-coef-closed-transpose-cocycles). -/
def transpose {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hA : PushClosed A i) (hB : PushClosed B i)
    (hZ : ScalarClosed φ Z) (hX : ScalarClosed φ X)
    {JA :
    C A X ⥤ C A Z} {JB :
    C B X ⥤ C B Z}
    (a : push A i hA ⊣ JA) (b : push B i hB ⊣ JB)
    [IsIso (comparison φ i hA hB hZ hX)] :
    JA ⋙ scalar φ Z hZ ⟶ scalar φ X hX ⋙ JB :=
  (mateEquiv a b (TwoSquare.mk _ _ _ _ (asIso (comparison φ i hA hB hZ hX)).inv)).natTrans

/-- Closure under the recorded transported etale exceptional inverse image.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
abbrev RightClosed (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ∀ K : C (ULift.{u + 1, u} A) X,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z
      ((sfFiniteExceptionalFixed A (Compactification.ofIsProper i)).obj K.obj)

/-- The actual exceptional functor, restricted to the stipulated domain.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
def right (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (h : RightClosed A i) :
    C (ULift.{u + 1, u} A) X ⥤ C (ULift.{u + 1, u} A) Z :=
  restrict (sfFiniteExceptionalFixed A (Compactification.ofIsProper i)) h

/-- The closed adjunction on the actual finite-Tor domains assumed in the node.
Both functors are fixed constructions, including the etale-origin exceptional functor.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
structure ClosedAdjunction (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] where
  pushClosed : PushClosed (ULift.{u + 1, u} A) i
  rightClosed : RightClosed A i
  adjunction : push (ULift.{u + 1, u} A) i pushClosed ⊣ right A i rightClosed

/-- The canonical scalar compositor restricted through the full inclusions.
It is the adjunction-normalized balancing map on K-flat representatives.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
def scalarComp {A B V : Type (u + 1)} [CommRing A] [CommRing B] [CommRing V]
    (φ : A →+* B) (ψ : B →+* V) (T : Scheme.{u})
    (hφ : ScalarClosed φ T) (hψ : ScalarClosed ψ T) (hχ : ScalarClosed (ψ.comp φ) T) :
    scalar φ T hφ ⋙ scalar ψ T hψ ≅ scalar (ψ.comp φ) T hχ :=
  by
    refine NatIso.ofComponents (fun K ↦ ?_) ?_
    · exact ObjectProperty.isoMk _
        ((@pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B V
          inferInstance inferInstance inferInstance φ ψ (ψ.comp φ) rfl).app K.obj)
    · intro K L f
      ext
      exact (@pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B V
        inferInstance inferInstance inferInstance φ ψ (ψ.comp φ) rfl).hom.naturality f.hom

/-- The direct-image compositor on the stipulated full subcategories.
Its components are exactly the recorded universal right-derived compositor.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
def pushComp (A : Type (u + 1)) [CommRing A]
    {W Z X : Scheme.{u}} (t : W ⟶ Z) (i : Z ⟶ X)
    (ht : PushClosed A t) (hi : PushClosed A i) (hti : PushClosed A (t ≫ i)) :
    push A (t ≫ i) hti ≅ push A t ht ⋙ push A i hi :=
  by
    refine NatIso.ofComponents (fun K ↦ ?_) ?_
    · exact ObjectProperty.isoMk _ ((finiteDirectImageComposition A t i).app K.obj)
    · intro K L f
      ext
      exact (finiteDirectImageComposition A t i).hom.naturality f.hom

/-- The identity restriction on sheaves is the sectionwise module identity.
Source: blueprint identity coefficient change
(blueprint: lem-coef-closed-transpose-cocycles). -/
def restrictionUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf.restrictScalars (Scheme.ProEt.topology T) (RingHom.id A) ≅
      𝟭 (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  by
    refine NatIso.ofComponents (fun K ↦ ?_) ?_
    · exact ObjectProperty.isoMk _
        (Functor.isoWhiskerLeft K.obj (ModuleCat.restrictScalarsId A) ≪≫
          Functor.rightUnitor K.obj)
    · intro K L f
      ext U x
      rfl

/-- Identity scalar extension is the multiplication-normalized adjunction comparison.
Source: blueprint identity coefficient change
(blueprint: lem-coef-closed-transpose-cocycles). -/
def scalarUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (h : ScalarClosed (RingHom.id A) T) : scalar (RingHom.id A) T h ≅ 𝟭 (C A T) :=
  by
    let e := Adjunction.leftAdjointIdIso
      (Adjunction.ofIsRightAdjoint
        (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
          A A inferInstance inferInstance (RingHom.id A)))
      (Functor.mapDerivedCategoryNatIso (restrictionUnit A T) ≪≫
        Functor.mapDerivedCategoryIdIso _)
    refine NatIso.ofComponents (fun K ↦ ?_) ?_
    · exact ObjectProperty.isoMk _ (e.app K.obj)
    · intro K L f
      ext
      exact e.hom.naturality f.hom

/-- A positive finite coefficient stage, reusing the recorded field and quotient.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
abbrev ring (l : ℕ) [Fact l.Prime]
    (E : WeilConjectures.ConstructibleExceptionalCoefficients.FieldStage.{u} l) (m : ℕ) :=
  Padic.coefficientExtensionRing l E.carrier (m + 1)

/-- The exceptional comparison with the specified closed adjunctions.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
def closedTranspose {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a : ClosedAdjunction A i) (b : ClosedAdjunction B i)
    (hZ : ScalarClosed φ Z) (hX : ScalarClosed φ X)
    [IsIso (comparison φ i a.pushClosed b.pushClosed hZ hX)] :=
  transpose φ i a.pushClosed b.pushClosed hZ hX a.adjunction b.adjunction

/-- The right-adjoint identification from the chained Hom adjunction.
Its left identification is exactly the published direct-image compositor.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles). -/
def rightComp {A : Type u} [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (t : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion t] [IsClosedImmersion i]
    (a : ClosedAdjunction A i) (b : ClosedAdjunction A t)
    (d : ClosedAdjunction A (t ≫ i)) :
    right A (t ≫ i) d.rightClosed ≅ right A i a.rightClosed ⋙ right A t b.rightClosed :=
  Adjunction.rightAdjointUniq
    (d.adjunction.ofNatIsoLeft
      (pushComp (ULift.{u + 1, u} A) t i b.pushClosed a.pushClosed d.pushClosed))
    (b.adjunction.comp a.adjunction)

-- The proofs use the published functor interfaces, not their underlying constructions.
attribute [local irreducible] sfFiniteExceptionalFixed
  finiteDirectImageComposition finiteCoefficientChangeDirectImageMap
  DerivedCategory.constructibleFiniteTor

private theorem restrictionComp_identity (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    @Sheaf.derivedRestrictScalarsCompIso.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
        A A inferInstance inferInstance (RingHom.id A) A inferInstance
        (RingHom.id A) (RingHom.id A) rfl =
      Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
            (restrictionUnit A T) ≪≫
            Functor.mapDerivedCategoryIdIso.{u + 2, u + 1, u + 1}
              (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
          (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
            (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
            A A inferInstance inferInstance (RingHom.id A)) ≪≫
        Functor.leftUnitor _ := by
  let R := Sheaf.restrictScalars.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (RingHom.id A)
  have he : Sheaf.restrictScalarsCompIso.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (RingHom.id A) (RingHom.id A) (RingHom.id A) rfl =
      Functor.isoWhiskerRight (restrictionUnit A T) R := by
    ext K U x
    rfl
  apply Iso.ext
  ext M
  change (Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} R R).inv.app M ≫
      (Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
        (Sheaf.restrictScalarsCompIso.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (RingHom.id A) (RingHom.id A) (RingHom.id A) rfl)).hom.app M =
    (Functor.mapDerivedCategory.{u + 1, u + 1} R).map
      ((Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
            (restrictionUnit A T)).hom.app M ≫
        (Functor.mapDerivedCategoryIdIso.{u + 2, u + 1, u + 1}
              (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))).hom.app M) ≫ 𝟙 _
  rw [he, Category.comp_id, Functor.map_comp]
  have hn := congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerRight.{u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (restrictionUnit A T) R) M
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp.{u + 2, u + 2,
    u + 1, u + 1, u + 1, u + 1} R) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} R R).hom.app M)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hn, hu]
  erw [Category.comp_id]

private theorem scalarComp_identity (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (h : ScalarClosed (RingHom.id A) T) (K : C A T) :
    (scalarComp (RingHom.id A) (RingHom.id A) T h h h).hom.app K =
      (scalarUnit A T h).hom.app ((scalar (RingHom.id A) T h).obj K) := by
  have hh := Adjunction.leftAdjointCompIso_comp_id
    (Adjunction.ofIsRightAdjoint
      (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
            (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
            A A inferInstance inferInstance (RingHom.id A)))
    (Adjunction.ofIsRightAdjoint
      (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
            (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
            A A inferInstance inferInstance (RingHom.id A)))
    (@Sheaf.derivedRestrictScalarsCompIso.{u} T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
      A A inferInstance inferInstance (RingHom.id A) A inferInstance
      (RingHom.id A) (RingHom.id A) rfl)
    (Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
            (restrictionUnit A T) ≪≫
      Functor.mapDerivedCategoryIdIso.{u + 2, u + 1, u + 1}
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (restrictionComp_identity A T)
  ext
  have hm := congr_app (congrArg Iso.hom hh) K.obj
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hm
  erw [Category.comp_id] at hm
  exact hm

private theorem iso_comparison_identity
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {S : C ⥤ C} {T : D ⥤ D}
    (c : F ⋙ T ⟶ S ⋙ F) [IsIso c] (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 D)
    (h : ∀ K, c.app K = t.inv.app (T.obj (F.obj K)) ≫ T.map (c.app K) ≫
      c.app (S.obj K) ≫ F.map (s.hom.app (S.obj K))) (K : C) :
    c.app K ≫ F.map (s.hom.app K) = t.hom.app (F.obj K) := by
  have hc := congrArg (fun f ↦ t.hom.app (T.obj (F.obj K)) ≫ f) (h K)
  simp only [Iso.hom_inv_id_app_assoc] at hc
  have ht := t.hom.naturality (c.app K)
  simp only [Functor.id_map, Functor.comp_obj] at ht
  erw [← ht] at hc
  have hn : c.app (S.obj K) ≫ F.map (s.hom.app (S.obj K)) =
      t.hom.app (F.obj (S.obj K)) := ((cancel_epi (T.map (c.app K))).1 hc).symm
  have hs : S.map (s.hom.app K) = s.hom.app (S.obj K) := by
    apply (cancel_mono (s.hom.app K)).1
    simpa only [Functor.id_map, Functor.id_obj] using s.hom.naturality (s.hom.app K)
  apply (cancel_epi (T.map (F.map (s.hom.app K)))).1
  calc
    T.map (F.map (s.hom.app K)) ≫ (c.app K ≫ F.map (s.hom.app K)) =
        c.app (S.obj K) ≫ F.map (S.map (s.hom.app K)) ≫ F.map (s.hom.app K) := by
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using
        congrArg (fun f ↦ f ≫ F.map (s.hom.app K)) (c.naturality (s.hom.app K))
    _ = t.hom.app (F.obj (S.obj K)) ≫ F.map (s.hom.app K) := by
      rw [hs, ← Category.assoc, hn]
    _ = T.map (F.map (s.hom.app K)) ≫ t.hom.app (F.obj K) :=
      (t.hom.naturality (F.map (s.hom.app K))).symm

private theorem mate_chain
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {Q : B ⥤ A} (adj : Q ⊣ P)
    {P' : C ⥤ D} {Q' : D ⥤ C} (adj' : Q' ⊣ P')
    {P'' : E ⥤ F} {Q'' : F ⥤ E} (adj'' : Q'' ⊣ P'')
    {S : B ⥤ D} {S' : A ⥤ C} {T : D ⥤ F} {T' : C ⥤ E}
    {U : B ⥤ F} {U' : A ⥤ E}
    (α : S ⋙ Q' ⟶ Q ⋙ S') (β : T ⋙ Q'' ⟶ Q' ⋙ T')
    (γ : U ⋙ Q'' ⟶ Q ⋙ U') (c : S ⋙ T ≅ U) (c' : S' ⋙ T' ≅ U')
    (hγ : ∀ M : B, γ.app M = Q''.map (c.inv.app M) ≫ β.app (S.obj M) ≫
      T'.map (α.app M) ≫ c'.hom.app (Q.obj M)) (K : A) :
    (mateEquiv adj adj'' (TwoSquare.mk _ _ _ _ γ)).natTrans.app K =
      c.inv.app (P.obj K) ≫
        T.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α)).natTrans.app K) ≫
        (mateEquiv adj' adj'' (TwoSquare.mk _ _ _ _ β)).natTrans.app (S'.obj K) ≫
        P''.map (c'.hom.app K) := by
  apply Adjunction.ext_of_comp_counit (adj := adj'')
  simp only [Functor.map_comp, Category.assoc]
  erw [adj''.counit_naturality]
  rw [mateEquiv_counit]
  rw [reassoc_of% (mateEquiv_counit adj' adj'' (TwoSquare.mk _ _ _ _ β) (S'.obj K)), hγ]
  simp only [Category.assoc]
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  erw [β.naturality_assoc]
  simp only [Functor.comp_map]
  slice_rhs 3 4 => rw [← T'.map_comp, mateEquiv_counit, T'.map_comp]
  simp only [Category.assoc]
  rw [← c'.hom.naturality]
  rfl

/-- Counit normalization and naturality of exactly the inverse-comparison mate.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles).

Proof: Use mateEquiv for the specified adjunctions and the inverse of the ordinary
comparison. The inverse Hom transpose gives the counit equation. For a morphism u,
transpose both proposed composites; naturality of the ordinary comparison and of
the A-counit identifies their transposes. Injectivity gives naturality. No inverse
of the exceptional mate is used. -/
theorem closedTranspose_counit_naturality
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E L : WeilConjectures.ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (m n : ℕ)
    (X Z : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (a : ClosedAdjunction (ring l E m) i.left)
    (b : ClosedAdjunction (ring l L n) i.left)
    (φ : ULift.{u + 1, u} (ring l E m) →+* ULift.{u + 1, u} (ring l L n))
    (hZ : ScalarClosed φ Z.left) (hX : ScalarClosed φ X.left)
    [IsIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)] :
    (∀ M : C (ULift.{u + 1, u} (ring l E m)) X.left,
      (push (ULift.{u + 1, u} (ring l L n)) i.left b.pushClosed).map
          ((closedTranspose φ i.left a b hZ hX).app M) ≫
        b.adjunction.counit.app ((scalar φ X.left hX).obj M) =
      (asIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)).inv.app
          ((right (ring l E m) i.left a.rightClosed).obj M) ≫
        (scalar φ X.left hX).map (a.adjunction.counit.app M)) ∧
    (∀ (M N : C (ULift.{u + 1, u} (ring l E m)) X.left) (f : M ⟶ N),
      (scalar φ Z.left hZ).map ((right (ring l E m) i.left a.rightClosed).map f) ≫
          (closedTranspose φ i.left a b hZ hX).app N =
        (closedTranspose φ i.left a b hZ hX).app M ≫
          (right (ring l L n) i.left b.rightClosed).map ((scalar φ X.left hX).map f)) := by
  constructor
  · intro M
    exact mateEquiv_counit a.adjunction b.adjunction
      (TwoSquare.mk _ _ _ _
        (asIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)).inv) M
  · intro M N f
    exact (closedTranspose φ i.left a b hZ hX).naturality f

/-- Geometric composition with the chained-adjunction right identification.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles).

Proof: Invert the ordinary geometric cocycle. Under the chained adjunction, the
transpose of Rt_B!(b_i) after b_t is the composite counit. Move b_i through the
t-counit by naturality, substitute both defining counit equations, then move the
A t-counit through the inverse ordinary comparison. The ordinary geometric cocycle
makes the result exactly the transpose of b_it. The chained Hom bijection is
injective. The rightComp factors display the identification without making a
strict equality of differently constructed right adjoints. -/
theorem closedTranspose_geometric
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E L : WeilConjectures.ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (m n : ℕ)
    (X Z : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (a : ClosedAdjunction (ring l E m) i.left)
    (b : ClosedAdjunction (ring l L n) i.left)
    (φ : ULift.{u + 1, u} (ring l E m) →+* ULift.{u + 1, u} (ring l L n))
    (hZ : ScalarClosed φ Z.left) (hX : ScalarClosed φ X.left)
    [IsIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)]
    (W : Over (Spec (.of D.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (t : W ⟶ Z) [IsClosedImmersion t.left]
    (aT : ClosedAdjunction (ring l E m) t.left)
    (bt : ClosedAdjunction (ring l L n) t.left)
    (ait : ClosedAdjunction (ring l E m) (t.left ≫ i.left))
    (bit : ClosedAdjunction (ring l L n) (t.left ≫ i.left))
    (hW : ScalarClosed φ W.left)
    [IsIso (comparison φ t.left aT.pushClosed bt.pushClosed hW hZ)]
    [IsIso (comparison φ (t.left ≫ i.left) ait.pushClosed bit.pushClosed hW hX)]
    (M : C (ULift.{u + 1, u} (ring l E m)) X.left) :
    (closedTranspose φ (t.left ≫ i.left) ait bit hW hX).app M ≫
        (rightComp t.left i.left b bt bit).hom.app ((scalar φ X.left hX).obj M) =
      (scalar φ W.left hW).map ((rightComp t.left i.left a aT ait).hom.app M) ≫
        (closedTranspose φ t.left aT bt hW hZ).app
          ((right (ring l E m) i.left a.rightClosed).obj M) ≫
        (right (ring l L n) t.left bt.rightClosed).map
          ((closedTranspose φ i.left a b hZ hX).app M) := by
  symm
  apply Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    aT.adjunction a.adjunction ait.adjunction bt.adjunction b.adjunction bit.adjunction
    (comparison φ t.left aT.pushClosed bt.pushClosed hW hZ)
    (comparison φ i.left a.pushClosed b.pushClosed hZ hX)
    (comparison φ (t.left ≫ i.left) ait.pushClosed bit.pushClosed hW hX)
    (pushComp _ t.left i.left aT.pushClosed a.pushClosed ait.pushClosed)
    (pushComp _ t.left i.left bt.pushClosed b.pushClosed bit.pushClosed) ?_ M
  constructor
  intro K
  ext
  have h := finiteCoefficientDirectImageMap_comp.{u} φ t.left i.left K.obj
  have hh := congrArg (fun f ↦ f ≫
    (finiteDirectImageComposition.{u} (ULift.{u + 1, u} (ring l L n))
      t.left i.left).hom.app
        ((@pbcFixedScalarExtension.{u} W.left.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology W.left)
          _ _ inferInstance inferInstance φ).obj K.obj)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

/-- Successive coefficient changes using the canonical scalar balancing isomorphisms.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles).

Proof: Resolve by flat-term K-flat complexes. Base change preserves that resolving
class, so iterated tensor is represented by (P tensor_A B) tensor_B C. The balanced
chain maps ((x tensor b) tensor c) ↦ x tensor ψ(b)c and x tensor c ↦
(x tensor 1) tensor c are inverse, natural under restrictions and chain maps,
and descend by K-flat localization. These are scalarComp, since their scalar-unit
normalization characterizes the adjunction comparison. Transpose the proposed
composite under the C exceptional adjunction; substitute the B-to-C counit equation,
use naturality of the inverse ordinary comparison on b_AB, then substitute the
A-to-B counit equation. The inverse ordinary scalar cocycle identifies the result
with the A-to-C defining transpose. Injectivity proves the equation, including
nonflat quotient changes. -/
theorem closedTranspose_coefficient
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E L : WeilConjectures.ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (m n : ℕ)
    (X Z : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (a : ClosedAdjunction (ring l E m) i.left)
    (b : ClosedAdjunction (ring l L n) i.left)
    (φ : ULift.{u + 1, u} (ring l E m) →+* ULift.{u + 1, u} (ring l L n))
    (hZ : ScalarClosed φ Z.left) (hX : ScalarClosed φ X.left)
    [IsIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)]
    (F : WeilConjectures.ConstructibleExceptionalCoefficients.FieldStage.{u} l) (s : ℕ)
    (c : ClosedAdjunction (ring l F s) i.left)
    (ψ : ULift.{u + 1, u} (ring l L n) →+* ULift.{u + 1, u} (ring l F s))
    (kZ : ScalarClosed ψ Z.left) (kX : ScalarClosed ψ X.left)
    (jZ : ScalarClosed (ψ.comp φ) Z.left) (jX : ScalarClosed (ψ.comp φ) X.left)
    [IsIso (comparison ψ i.left b.pushClosed c.pushClosed kZ kX)]
    [IsIso (comparison (ψ.comp φ) i.left a.pushClosed c.pushClosed jZ jX)]
    (M : C (ULift.{u + 1, u} (ring l E m)) X.left) :
    (closedTranspose (ψ.comp φ) i.left a c jZ jX).app M =
      (scalarComp φ ψ Z.left hZ kZ jZ).inv.app
          ((right (ring l E m) i.left a.rightClosed).obj M) ≫
        (scalar ψ Z.left kZ).map ((closedTranspose φ i.left a b hZ hX).app M) ≫
        (closedTranspose ψ i.left b c kZ kX).app ((scalar φ X.left hX).obj M) ≫
        (right (ring l F s) i.left c.rightClosed).map
          ((scalarComp φ ψ X.left hX kX jX).hom.app M) := by
  apply mate_chain a.adjunction b.adjunction c.adjunction
    (asIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)).inv
    (asIso (comparison ψ i.left b.pushClosed c.pushClosed kZ kX)).inv
    (asIso (comparison (ψ.comp φ) i.left a.pushClosed c.pushClosed jZ jX)).inv
    (scalarComp φ ψ Z.left hZ kZ jZ) (scalarComp φ ψ X.left hX kX jX) ?_ M
  intro N
  let e := (scalarComp φ ψ X.left hX kX jX).symm.app
        ((push _ i.left a.pushClosed).obj N) ≪≫
      (scalar ψ X.left kX).mapIso
        ((asIso (comparison φ i.left a.pushClosed b.pushClosed hZ hX)).app N) ≪≫
      (asIso (comparison ψ i.left b.pushClosed c.pushClosed kZ kX)).app
        ((scalar φ Z.left hZ).obj N) ≪≫
      (push _ i.left c.pushClosed).mapIso ((scalarComp φ ψ Z.left hZ kZ jZ).app N)
  have he : (asIso (comparison (ψ.comp φ) i.left a.pushClosed c.pushClosed jZ jX)).app N =
      e := by
    apply Iso.ext
    ext
    exact finiteCoefficientDirectImageMap_coefficientChain φ ψ i.left N.obj
  have hi := congrArg Iso.inv he
  simpa only [e, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc] using hi

/-- Identity coefficient change is the identity under the canonical scalar units.
Source: blueprint lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-transpose-cocycles).

Proof: On a K-flat representative the scalar unit is x tensor a ↦ ax. The ordinary
identity coefficient comparison has the same transpose as the identity direct-image
map. Hence its inverse is the identity after these identifications. The exceptional
mate has transpose the exceptional counit, which also transposes the identity of
Ri!. Injectivity gives the formula. -/
theorem closedTranspose_identity
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : WeilConjectures.ConstructibleExceptionalCoefficients.FieldStage.{u} l) (m : ℕ)
    (X Z : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (a : ClosedAdjunction (ring l E m) i.left)
    (hZ : ScalarClosed (RingHom.id (ULift.{u + 1, u} (ring l E m))) Z.left)
    (hX : ScalarClosed (RingHom.id (ULift.{u + 1, u} (ring l E m))) X.left)
    [IsIso (comparison (RingHom.id _) i.left a.pushClosed a.pushClosed hZ hX)]
    (M : C (ULift.{u + 1, u} (ring l E m)) X.left) :
    (closedTranspose (RingHom.id _) i.left a a hZ hX).app M ≫
        (right (ring l E m) i.left a.rightClosed).map
          ((scalarUnit (ULift.{u + 1, u} (ring l E m)) X.left hX).hom.app M) =
      (scalarUnit (ULift.{u + 1, u} (ring l E m)) Z.left hZ).hom.app
        ((right (ring l E m) i.left a.rightClosed).obj M) := by
  let A := ULift.{u + 1, u} (ring l E m)
  let c := comparison (RingHom.id A) i.left a.pushClosed a.pushClosed hZ hX
  let sz := scalarUnit A Z.left hZ
  let sx := scalarUnit A X.left hX
  have hc (K : C A Z.left) :
      c.app K ≫ (push A i.left a.pushClosed).map (sz.hom.app K) =
        sx.hom.app ((push A i.left a.pushClosed).obj K) := by
    apply iso_comparison_identity c sz sx ?_ K
    intro N
    have he : (scalarComp (RingHom.id A) (RingHom.id A) X.left hX hX hX).inv.app
        ((push A i.left a.pushClosed).obj N) =
      sx.inv.app ((scalar (RingHom.id A) X.left hX).obj
        ((push A i.left a.pushClosed).obj N)) := by
      apply (cancel_epi ((scalarComp (RingHom.id A) (RingHom.id A)
        X.left hX hX hX).hom.app ((push A i.left a.pushClosed).obj N))).1
      rw [Iso.hom_inv_id_app, scalarComp_identity, Iso.hom_inv_id_app]
      rfl
    rw [← he, ← scalarComp_identity A Z.left hZ N]
    ext
    exact finiteCoefficientDirectImageMap_coefficientChain (RingHom.id A) (RingHom.id A)
      i.left N.obj
  apply Adjunction.ext_of_comp_counit (adj := a.adjunction)
  simp only [Functor.map_comp, Category.assoc]
  erw [a.adjunction.counit_naturality]
  erw [reassoc_of% (mateEquiv_counit a.adjunction a.adjunction
    (TwoSquare.mk _ _ _ _ (asIso c).inv) M)]
  change (asIso c).inv.app ((right _ i.left a.rightClosed).obj M) ≫
      (scalar (RingHom.id A) X.left hX).map (a.adjunction.counit.app M) ≫
      sx.hom.app M = _
  erw [sx.hom.naturality]
  simp only [Functor.id_map]
  have hh := congrArg
    (fun f ↦ (asIso c).inv.app ((right _ i.left a.rightClosed).obj M) ≫ f)
    (hc ((right _ i.left a.rightClosed).obj M))
  change (asIso c).inv.app _ ≫ c.app _ ≫ _ = _ at hh
  erw [Iso.inv_hom_id_app_assoc] at hh
  rw [← Category.assoc, ← hh]
  rfl

end ClosedCoefficient
end AlgebraicGeometry.ProEtale
