/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.CategoryTheory.SheafSubcategoryComparison
import all Sheaf.CategoryTheory.ToposCompatibleGenerators
import all Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison
import Sheaf.CategoryTheory.Sites.RingedNerveSliceTransport
import Sheaf.CategoryTheory.SmallSetOfCoveringFamilies
import Sheaf.CategoryTheory.RingedToposEquivalenceRingTransport
import all Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.CategoryTheory.ElementSiteDescent
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.RingedToposRingSquare
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# A simultaneous site presentation for a binary subterminal cover

Source: Stacks Project, Sites, Tags 03A1, 03CI, 00Y1, 04GZ and 03EH;
Modules on Sites, Tags 03CR, 03D7, 04IE and 04J4
(blueprint: lem-sp-binary-cover-site-presentation).

The four indices are `0 = 1`, `1 = U`, `2 = V`, `3 = U × V`.
Internal commutative rings are encoded by their section-ring sheaves, as in the recorded
sectionwise reconstruction theorem. The source slice modules are encoded on the existing
category-of-elements site; the target slices use the actual localized topology `J.over`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The exact module equivalence induced by a specified ringed equivalence, together with
its termwise induced ordinary derived equivalence. The underlying-set and rank-one equations
fix the scalar action; the inverse is the specified module direct image.
Source: Stacks 03CR, 03D7 and 05RU
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R)) where
  modules : PresentationModules R ≌ PresentationModules S
  additive : modules.functor.Additive
  inverseAdditive : modules.inverse.Additive
  finiteLimits : PreservesFiniteLimits modules.functor
  finiteColimits : PreservesFiniteColimits modules.functor
  inverseFiniteLimits : PreservesFiniteLimits modules.inverse
  inverseFiniteColimits : PreservesFiniteColimits modules.inverse
  underlying : modules.functor ⋙ presentationForget S ≅ presentationForget R ⋙ g.inverse
  unit : modules.functor.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  structural : (presentationForget S).map unit.hom =
    underlying.hom.app (SheafOfModules.unit (localCoefficientRings R)) ≫ g.ringMap
  pushforward : modules.inverse ≅ g.modules
  derived : PresentationDerived R ≌ PresentationDerived S
  derivedFunctor : derived.functor =
    presentationDerivedMap modules.functor additive finiteLimits finiteColimits
  derivedInverse : derived.inverse = presentationDerivedMap modules.inverse inverseAdditive
    inverseFiniteLimits inverseFiniteColimits

/-- A restriction square preserves both adjunctions by their actual mates. Invertibility of
these mates says precisely that the adjoints are identified compatibly with units and counits,
rather than merely giving isomorphic endpoints.
Source: Stacks Categories, Tag 0B65; Sites, Tag 03EH
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationAdjointSquare
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') (F : A ⥤ B) (F' : A' ⥤ B') where
  comparison : F ⋙ E'.functor ≅ E.functor ⋙ F'
  rightMate : ∀ (G : B ⥤ A) (G' : B' ⥤ A') (a : F ⊣ G) (a' : F' ⊣ G'),
    IsIso ((mateEquiv a a' (TwoSquare.mk _ _ _ _ comparison.inv)).natTrans)
  leftMate : ∀ (L : B ⥤ A) (L' : B' ⥤ A') (a : L ⊣ F) (a' : L' ⊣ F'),
    IsIso (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ comparison.hom)).natTrans)

/-- All witnesses for one small finite-limit-closed presenting subcategory and the four
simultaneous ringed slices. Full faithfulness realizes the small category as a full
subcategory, with chosen representatives of its objects.
Source: Stacks Sites, Tags 03A1, 03CI and 00Y1; Modules on Sites, 03CR
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryCoverSitePresentation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : Sheaf J (Type u)) where
  E : Type u
  [category : SmallCategory E]
  [finiteLimits : HasFiniteLimits E]
  inclusion : E ⥤ Sheaf J (Type u)
  [full : inclusion.Full]
  [faithful : inclusion.Faithful]
  [preservesLimits : PreservesFiniteLimits inclusion]
  generators : ∀ X : C, ∃ Y : E,
    Nonempty (inclusion.obj Y ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj X))
  objects : Fin 4 → E
  terminal : inclusion.obj (objects 0) ≅ ⊤_ (Sheaf J (Type u))
  first : inclusion.obj (objects 1) ≅ U
  second : inclusion.obj (objects 2) ≅ V
  intersection : inclusion.obj (objects 3) ≅ U ⨯ V
  covers : Precoverage E
  site : covers.IsSiteForCoverings
  [subcanonical : covers.toGrothendieck.Subcanonical]
  epimorphic : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    P.presieve₀ ∈ covers X ↔
      ⟨X, P⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} inclusion
  representatives : Set (Σ X : E, PreZeroHypercover.{u} X)
  smallRepresentatives : Small.{u} representatives
  coveringClass : PreZeroHypercover.IsCoveringClass representatives
  representativeCovers : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    ⟨X, P⟩ ∈ representatives → P.presieve₀ ∈ covers X
  sameSupports : ∀ (X : E) (P : PreZeroHypercover.{u} X), P.presieve₀ ∈ covers X →
    ∃ Q : PreZeroHypercover.{u} X, ⟨X, Q⟩ ∈ representatives ∧ P.presieve₀ = Q.presieve₀
  binaryCover : ∀ X : E,
    Presieve.ofArrows (fun b : Bool ↦ X ⨯ objects (if b then 1 else 2))
      (fun _b ↦ prod.fst : ∀ b : Bool, X ⨯ objects (if b then 1 else 2) ⟶ X) ∈ covers X
  nerve : Sheaf J (Type u) ≌ Sheaf covers.toGrothendieck (Type u)
  nerveFormula : nerve.functor ⋙ sheafToPresheaf covers.toGrothendieck (Type u) ≅
    sheafSubcategoryNerve inclusion
  represented : ∀ X : E, Nonempty (nerve.functor.obj (inclusion.obj X) ≅
    covers.toGrothendieck.yoneda.obj X)
  ring : Sheaf covers.toGrothendieck CommRingCat.{u}
  ringed : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R)
  inverseNerve : ringed.inverse = nerve.functor
  directNerve : ringed.direct = nerve.inverse
  ringIsIso : IsIso ringed.ringMap
  wholeModules : BinaryPresentationModules ringed
  sourceSlice : ∀ i : Fin 4,
    RingedSheafSliceAdjunctionData (localCoefficientRings R) (inclusion.obj (objects i))
  slice : ∀ i : Fin 4,
    Over (inclusion.obj (objects i)) ≌ Sheaf (covers.toGrothendieck.over (objects i)) (Type u)
  sliceFormula : ∀ i : Fin 4,
    (slice i).functor ⋙ sheafToPresheaf (covers.toGrothendieck.over (objects i)) (Type u) ≅
      yoneda ⋙ (Functor.whiskeringLeft (Over (objects i))ᵒᵖ
        (Over (inclusion.obj (objects i)))ᵒᵖ (Type u)).obj (Over.post inclusion).op
  sliceRinged : ∀ i : Fin 4,
    RingedToposMorphism (localCoefficientRings (ring.over (objects i)))
      (localCoefficientRings (presentationElementRing R (inclusion.obj (objects i))))
  sliceInverse : ∀ i : Fin 4, Nonempty ((sliceRinged i).inverse ≅
    (sourceSlice i).fibreEquivalence.functor ⋙ (slice i).functor)
  sliceRingIsIso : ∀ i : Fin 4, IsIso (sliceRinged i).ringMap
  sliceModules : ∀ i : Fin 4, BinaryPresentationModules (sliceRinged i)
  sourceContinuous : ∀ (i j : Fin 4) (f : objects i ⟶ objects j),
    Functor.IsContinuous (elementMap (inclusion.map f))
      (elementTopology (inclusion.obj (objects i)))
      (elementTopology (inclusion.obj (objects j)))
  restriction : ∀ i : Fin 4, BinaryPresentationAdjointSquare
    wholeModules.modules (sliceModules i).modules
    (elementModulePullback.{u, u} (localCoefficientRings R) (inclusion.obj (objects i)))
    (SheafOfModules.overFunctor.{u} (localCoefficientRings ring) (objects i))

  further : ∀ (i j : Fin 4) (f : objects i ⟶ objects j),
    BinaryPresentationAdjointSquare (sliceModules j).modules (sliceModules i).modules
      (elementModulePullbackOver.{u, u} (localCoefficientRings R) (inclusion.map f)
        (sourceContinuous i j f))
      (SheafOfModules.overMap.{u} (localCoefficientRings ring) f)

  restrictionComposition : ∀ (i j : Fin 4) (f : objects i ⟶ objects j)
      (M : PresentationModules R),
    HEq ((restriction i).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullback.{u, u} (localCoefficientRings R)
            (inclusion.obj (objects j))).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((restriction j).comparison.hom.app M) ≫
        (SheafOfModules.overFunctorMap.{u} (localCoefficientRings ring) f).hom.app
          (wholeModules.modules.functor.obj M))
  furtherIdentity : ∀ (i : Fin 4)
      (M : PresentationModules (presentationElementRing R (inclusion.obj (objects i)))),
    HEq ((further i i (𝟙 (objects i))).comparison.hom.app M)
      (𝟙 ((sliceModules i).modules.functor.obj M))
  furtherComposition : ∀ (i j k : Fin 4) (f : objects i ⟶ objects j)
      (g : objects j ⟶ objects k)
      (M : PresentationModules (presentationElementRing R (inclusion.obj (objects k)))),
    HEq ((further i k (f ≫ g)).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullbackOver.{u, u} (localCoefficientRings R) (inclusion.map g)
            (sourceContinuous j k g)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((further j k g).comparison.hom.app M))

private theorem binaryRightMate_bijective
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (a : F ⊣ G) (a' : F' ⊣ G') (E : A ≌ A') (E' : B ≌ B')
    (b : E.functor ⋙ F' ≅ F ⋙ E'.functor) (X : A) (Y : B) :
    Function.Bijective (fun f : E.functor.obj X ⟶ E.functor.obj (G.obj Y) ↦
      f ≫ (mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app Y) := by
  let m := (mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).natTrans
  let h := E.fullyFaithfulFunctor.homEquiv.symm.trans (a.homEquiv X Y).symm
  let k := h.trans E'.fullyFaithfulFunctor.homEquiv
  let z := k.trans (Iso.homCongr (b.app X).symm (Iso.refl _))
  have hz (f : E.functor.obj X ⟶ E.functor.obj (G.obj Y)) :
      (a'.homEquiv _ _).symm (f ≫ m.app Y) = z f := by
    obtain ⟨f, rfl⟩ := E.fullyFaithfulFunctor.homEquiv.surjective f
    rw [Adjunction.homEquiv_counit, F'.map_comp, Category.assoc]
    have hm := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ b.hom) Y
    change F'.map (m.app Y) ≫ a'.counit.app (E'.functor.obj Y) =
      b.hom.app (G.obj Y) ≫ E'.functor.map (a.counit.app Y) at hm
    rw [hm, ← Category.assoc]
    have hn := b.hom.naturality f
    change F'.map (E.functor.map f) ≫ b.hom.app (G.obj Y) =
      b.hom.app X ≫ E'.functor.map (F.map f) at hn
    change (F'.map (E.functor.map f) ≫ b.hom.app (G.obj Y)) ≫
      E'.functor.map (a.counit.app Y) = z (E.functor.map f)
    rw [hn, Category.assoc, ← E'.functor.map_comp]
    simp [z, k, h, Adjunction.homEquiv_counit]
  rw [← (a'.homEquiv _ _).symm.bijective.of_comp_iff']
  change Function.Bijective (fun f ↦ (a'.homEquiv _ _).symm (f ≫ m.app Y))
  rw [show (fun f ↦ (a'.homEquiv _ _).symm (f ≫ m.app Y)) = z from funext hz]
  exact z.bijective

private theorem binaryRightMate_isIso
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (a : F ⊣ G) (a' : F' ⊣ G') (E : A ≌ A') (E' : B ≌ B')
    (b : E.functor ⋙ F' ≅ F ⋙ E'.functor) :
    IsIso (mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  apply isIso_of_yoneda_map_bijective
  intro X
  let m := (mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).natTrans
  let t := E.counitIso.app X
  have h := binaryRightMate_bijective a a' E E' b (E.inverse.obj X) Y
  constructor
  · intro f g hfg
    apply (cancel_epi t.hom).mp
    apply h.injective
    change (t.hom ≫ f) ≫ m.app Y = (t.hom ≫ g) ≫ m.app Y
    change f ≫ m.app Y = g ≫ m.app Y at hfg
    simp only [Category.assoc, hfg]
  · intro f
    obtain ⟨g, hg⟩ := h.surjective (t.hom ≫ f)
    refine ⟨t.inv ≫ g, ?_⟩
    change g ≫ m.app Y = t.hom ≫ f at hg
    change (t.inv ≫ g) ≫ m.app Y = f
    rw [Category.assoc, hg, ← Category.assoc, t.inv_hom_id, Category.id_comp]

private def binaryAdjointSquare
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') (F : A ⥤ B) (F' : A' ⥤ B')
    (b : F ⋙ E'.functor ≅ E.functor ⋙ F') :
    BinaryPresentationAdjointSquare E E' F F' where
  comparison := b
  rightMate _ _ a a' := binaryRightMate_isIso a a' E E' b.symm
  leftMate _ _ a a' := equivalentMate_isIso a a' E' E b

private def identityRingData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : RingedToposMorphism.RingData R R where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := 𝟙 _
  ring_zero _ _ h U t := h U t
  ring_one _ _ h U t := h U t
  ring_add _ _ _ _ h U t := h U t
  ring_mul _ _ _ _ h U t := h U t

private theorem binaryRingedEquivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (N : Sheaf J (Type u) ≌ Sheaf K (Type u)) :
    ∃ (S : Sheaf K CommRingCat.{u})
      (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R)),
      g.inverse = N.functor ∧ g.direct = N.inverse ∧ IsIso g.ringMap ∧
        Nonempty (RingedPresentationAt g) := by
  obtain ⟨S, d, _, hi, _, _, hmap⟩ := ringedTopos_equivalenceRingTransport R N
  let : d.inverse.Full := by rw [hi]; infer_instance
  let : d.inverse.Faithful := by rw [hi]; infer_instance
  let : IsIso d.ringMap := hmap
  let idR := identityRingData (localCoefficientRings R)
  let a : idR.inverse ⋙ idR.inverse ≅ N.functor ⋙ d.inverse := by
    simpa only [idR, identityRingData, Functor.id_comp, hi] using N.unitIso
  let q := RingedToposMorphism.RingData.square idR d idR N.functor a N.inverse
    N.toAdjunction (inferInstance)
  have hq : IsIso q.ringMap := by
    change IsIso (RingedToposMorphism.RingData.squareRingMap idR d idR N.functor a)
    have : IsIso (d.inverse.map
        (RingedToposMorphism.RingData.squareRingMap idR d idR N.functor a)) := by
      dsimp only [RingedToposMorphism.RingData.squareRingMap]
      rw [Functor.map_preimage]
      dsimp only [idR, identityRingData]
      infer_instance
    exact isIso_of_fully_faithful d.inverse _
  obtain ⟨m⟩ := SheafOfModules.ringData_inducedModules S R q
  let g := q.withModules m
  have : g.inverse.IsEquivalence := N.isEquivalence_functor
  have : IsIso g.ringMap := hq
  obtain ⟨T⟩ := presentationAt g
  exact ⟨S, g, rfl, rfl, hq, ⟨T⟩⟩

private def binaryModulesOfPresentation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R)}
    (T : RingedPresentationAt g) : BinaryPresentationModules g := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let := T.transport.forward.additive
  let := T.transport.forward.finiteLimits
  let := T.transport.forward.finiteColimits
  let := T.transport.backward.additive
  let := T.transport.backward.finiteLimits
  let := T.transport.backward.finiteColimits
  exact {
    modules := T.transport.modules
    additive := T.transport.forward.additive
    inverseAdditive := T.transport.backward.additive
    finiteLimits := T.transport.forward.finiteLimits
    finiteColimits := T.transport.forward.finiteColimits
    inverseFiniteLimits := T.transport.backward.finiteLimits
    inverseFiniteColimits := T.transport.backward.finiteColimits
    underlying := T.underlying
    unit := T.transport.forward.unit
    structural := T.structural
    pushforward := T.pushforward
    derived := T.transport.modules.mapDerivedCategory
    derivedFunctor := rfl
    derivedInverse := rfl }

private structure BinarySiteCore
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (U V : Sheaf J (Type u)) where
  E : Type u
  [category : SmallCategory E]
  [finiteLimits : HasFiniteLimits E]
  inclusion : E ⥤ Sheaf J (Type u)
  [full : inclusion.Full]
  [faithful : inclusion.Faithful]
  [preservesLimits : PreservesFiniteLimits inclusion]
  generators : ∀ X : C, ∃ Y : E,
    Nonempty (inclusion.obj Y ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj X))
  objects : Fin 4 → E
  terminal : inclusion.obj (objects 0) ≅ ⊤_ (Sheaf J (Type u))
  first : inclusion.obj (objects 1) ≅ U
  second : inclusion.obj (objects 2) ≅ V
  intersection : inclusion.obj (objects 3) ≅ U ⨯ V
  covers : Precoverage E
  site : covers.IsSiteForCoverings
  [subcanonical : covers.toGrothendieck.Subcanonical]
  epimorphic : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    P.presieve₀ ∈ covers X ↔
      ⟨X, P⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} inclusion
  representatives : Set (Σ X : E, PreZeroHypercover.{u} X)
  smallRepresentatives : Small.{u} representatives
  coveringClass : PreZeroHypercover.IsCoveringClass representatives
  representativeCovers : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    ⟨X, P⟩ ∈ representatives → P.presieve₀ ∈ covers X
  sameSupports : ∀ (X : E) (P : PreZeroHypercover.{u} X), P.presieve₀ ∈ covers X →
    ∃ Q : PreZeroHypercover.{u} X, ⟨X, Q⟩ ∈ representatives ∧ P.presieve₀ = Q.presieve₀
  binaryCover : ∀ X : E,
    Presieve.ofArrows (fun b : Bool ↦ X ⨯ objects (if b then 1 else 2))
      (fun _b ↦ prod.fst : ∀ b : Bool, X ⨯ objects (if b then 1 else 2) ⟶ X) ∈ covers X
  nerve : Sheaf J (Type u) ≌ Sheaf covers.toGrothendieck (Type u)
  nerveFormula : nerve.functor ⋙ sheafToPresheaf covers.toGrothendieck (Type u) ≅
    sheafSubcategoryNerve inclusion
  represented : ∀ X : E, Nonempty (nerve.functor.obj (inclusion.obj X) ≅
    covers.toGrothendieck.yoneda.obj X)

private theorem binaryFamily_epimorphic
    {C E : Type u} [SmallCategory C] [SmallCategory E] [HasFiniteLimits E]
    {J : GrothendieckTopology C} (F : E ⥤ Sheaf J (Type u))
    [PreservesFiniteLimits F] (U V : Sheaf J (Type u)) (a b : E)
    (ea : F.obj a ≅ U) (eb : F.obj b ≅ V)
    (hcover : ∀ X : C,
      Sieve.generate (fun (Y : C) (_ : Y ⟶ X) ↦
        Nonempty (U.obj.obj (op Y)) ∨ Nonempty (V.obj.obj (op Y))) ∈ J X) (X : E) :
    ∀ (B : Sheaf J (Type u)) (f g : F.obj X ⟶ B),
      (∀ c : Bool, F.map (prod.fst : X ⨯ (if c then a else b) ⟶ X) ≫ f =
        F.map prod.fst ≫ g) → f = g := by
  intro B f g hfg
  ext W x
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp B.property).isSeparated _
    (hcover W.unop)).ext
  intro Y t ht
  obtain ⟨Z, s, t', hz, rfl⟩ := ht
  have hy : Nonempty (U.obj.obj (op Y)) ∨ Nonempty (V.obj.obj (op Y)) := by
    rcases hz with ⟨⟨z⟩⟩ | ⟨⟨z⟩⟩
    · exact Or.inl ⟨U.obj.map s.op z⟩
    · exact Or.inr ⟨V.obj.map s.op z⟩
  have lift_agree (c : Bool) (z : (F.obj (if c then a else b)).obj.obj (op Y)) :
      f.hom.app (op Y) ((F.obj X).obj.map (s ≫ t').op x) =
        g.hom.app (op Y) ((F.obj X).obj.map (s ≫ t').op x) := by
    let H := F ⋙ sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj (op Y)
    let pair := Types.binaryProductIso (H.obj X) (H.obj (if c then a else b))
    let y := inv (prodComparison H X (if c then a else b))
      (pair.inv ((F.obj X).obj.map (s ≫ t').op x, z))
    have hy : (F.map (prod.fst : X ⨯ (if c then a else b) ⟶ X)).hom.app (op Y) y =
        (F.obj X).obj.map (s ≫ t').op x := by
      change (inv (prodComparison H X (if c then a else b)) ≫ H.map prod.fst)
        (pair.inv ((F.obj X).obj.map (s ≫ t').op x, z)) = _
      rw [inv_prodComparison_map_fst]
      change (pair.inv ≫ prod.fst) ((F.obj X).obj.map (s ≫ t').op x, z) = _
      rw [Types.binaryProductIso_inv_comp_fst]
      rfl
    have hh := congrArg (fun k ↦ k.hom.app (op Y) y) (hfg c)
    change f.hom.app (op Y) ((F.map prod.fst).hom.app (op Y) y) =
      g.hom.app (op Y) ((F.map prod.fst).hom.app (op Y) y) at hh
    rwa [hy] at hh
  change B.obj.map (s ≫ t').op (f.hom.app (op W.unop) x) =
    B.obj.map (s ≫ t').op (g.hom.app (op W.unop) x)
  rw [← NatTrans.naturality_apply f.hom, ← NatTrans.naturality_apply g.hom]
  rcases hy with ⟨⟨z⟩⟩ | ⟨⟨z⟩⟩
  · exact lift_agree true (ea.inv.hom.app (op Y) z)
  · exact lift_agree false (eb.inv.hom.app (op Y) z)

private theorem binarySiteCore_exists
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (U V : Sheaf J (Type u))
    (hcover : ∀ X : C,
      Sieve.generate (fun (Y : C) (_ : Y ⟶ X) ↦
        Nonempty (U.obj.obj (op Y)) ∨ Nonempty (V.obj.obj (op Y))) ∈ J X) :
    Nonempty (BinarySiteCore J U V) := by
  classical
  let Z : Fin 4 → Sheaf J (Type u) := ![⊤_ _, U, V, U ⨯ V]
  let family : C ⊕ Fin 4 → Sheaf J (Type u) := Sum.elim
    (fun X ↦ (presheafToSheaf J (Type u)).obj (yoneda.obj X)) Z
  obtain ⟨E, hE, hlim, F, hfull, hfaith, hpres, hgen⟩ := generators family
  choose obj e using fun i : Fin 4 ↦ hgen (.inr i)
  let iso (i : Fin 4) : F.obj (obj i) ≅ Z i := Classical.choice (e i)
  have hrep : ∀ X : C, ∃ Y : E,
      Nonempty (F.obj Y ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj X)) :=
    fun X ↦ hgen (.inl X)
  have hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g) := by
    intro A B T f g
    exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
      (IsPullback.of_hasPullback f g).map F⟩
  let K := epiPrecoverage F
  let hK := epiPrecoverage_subcanonical F hpb
  let hsite := epiPrecoverage_site F hpb
  let := nerveToSheaf_isEquivalence F hrep hpb
  let N := (nerveToSheaf F hpb).asEquivalence
  obtain ⟨Cov, hsmall, _, hsub, hclass, hsupp⟩ :=
    PreZeroHypercover.exists_small_coveringFamilies
      (sheafSubcategoryEpimorphicFamilies.{u, u, 0} F) (family_isCoveringClass F hpb)
      ∅ (by infer_instance) (by simp)
  have hepi : ∀ (X : E) (P : PreZeroHypercover.{u} X), P.presieve₀ ∈ K X ↔
      ⟨X, P⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F :=
    fun X P ↦ (family_epi_iff_cover F X P).symm
  refine ⟨{
    E := E
    inclusion := F
    generators := hrep
    objects := obj
    terminal := iso 0
    first := iso 1
    second := iso 2
    intersection := iso 3
    covers := K
    site := hsite
    epimorphic := hepi
    representatives := Cov
    smallRepresentatives := hsmall
    coveringClass := hclass
    representativeCovers := fun X P h ↦ (hepi X P).mpr (hsub h)
    sameSupports := fun X P h ↦ hsupp X P ((hepi X P).mp h)
    binaryCover := ?_
    nerve := N
    nerveFormula := Iso.refl _
    represented := ?_ }⟩
  · intro X B f g hfg
    apply binaryFamily_epimorphic F U V (obj 1) (obj 2) (iso 1) (iso 2) hcover X B f g
    intro c
    have hh := hfg _ _ (Presieve.ofArrows.mk
      (Y := fun c : Bool ↦ X ⨯ obj (if c then 1 else 2))
      (f := fun _ ↦ prod.fst) c)
    cases c <;> exact hh
  · intro X
    exact ⟨(nerve_representable_sheaf_iso F hpb).app X⟩

private theorem binarySliceNerve
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} (K : GrothendieckTopology E) [K.Subcanonical]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (n : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F) (X : E) :
    ∃ s : Over (F.obj X) ≌ Sheaf (K.over X) (Type u),
      Nonempty (s.functor ⋙ sheafToPresheaf (K.over X) (Type u) ≅
        yoneda ⋙ (Functor.whiskeringLeft (Over X)ᵒᵖ
          (Over (F.obj X))ᵒᵖ (Type u)).obj (Over.post F).op) := by
  classical
  let theta : N.functor.obj (F.obj X) ≅ K.yoneda.obj X :=
    (fullyFaithfulSheafToPresheaf K (Type u)).preimageIso
      (n.app (F.obj X) ≪≫ (nerve_representable_iso F).app X)
  have : IsIso (toSheafify K (yoneda.obj X)) := isIso_toSheafify _
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
  let y : K.yoneda.obj X ≅ (presheafToSheaf K (Type u)).obj (yoneda.obj X) :=
    (fullyFaithfulSheafToPresheaf K (Type u)).preimageIso
      (asIso (toSheafify K (yoneda.obj X)))
  let z := (Over.postEquiv (X := F.obj X) N).trans (Over.mapIso (theta ≪≫ y))
  let s := z.trans (sliceEquivalence K X).symm
  have htheta (P : Over (F.obj X)) (Y : Over X)
      (x : (N.functor.obj P.left).obj.obj (op Y.left)) :
      theta.hom.hom.app (op Y.left) ((N.functor.map P.hom).hom.app (op Y.left) x) =
        F.preimage ((n.hom.app P.left).app (op Y.left) x ≫ P.hom) := by
    change F.preimage ((n.hom.app (F.obj X)).app (op Y.left)
      ((N.functor.map P.hom).hom.app (op Y.left) x)) = _
    congr 1
    exact congrArg (fun t ↦ t.app (op Y.left) x) (n.hom.naturality P.hom)
  have hc (P : Over (F.obj X)) (Y : Over X)
      (x : (N.functor.obj P.left).obj.obj (op Y.left)) :
      (N.functor.map P.hom ≫ theta.hom ≫ y.hom).hom.app (op Y.left) x =
        (toSheafify K (yoneda.obj X)).app (op Y.left) Y.hom ↔
      (n.hom.app P.left).app (op Y.left) x ≫ P.hom = F.map Y.hom := by
    change y.hom.hom.app (op Y.left)
      (theta.hom.hom.app (op Y.left)
        ((N.functor.map P.hom).hom.app (op Y.left) x)) =
      y.hom.hom.app (op Y.left) Y.hom ↔ _
    rw [(ConcreteCategory.bijective_of_isIso (y.hom.hom.app (op Y.left))).injective.eq_iff,
      htheta]
    constructor
    · intro h
      simpa only [Functor.map_preimage] using congrArg F.map h
    · intro h
      rw [h, Functor.preimage_map]
  refine ⟨s, ⟨NatIso.ofComponents (fun P ↦ NatIso.ofComponents
    (fun Y ↦ (show (s.functor.obj P).obj.obj Y ≃
        ((Over.post F).obj Y.unop ⟶ P) from {
      toFun := fun x ↦ Over.homMk ((n.hom.app P.left).app (op Y.unop.left) x.val)
        ((hc P Y.unop x.val).mp x.property)
      invFun := fun f ↦ ⟨(n.inv.app P.left).app (op Y.unop.left) f.left, by
        apply (hc P Y.unop _).mpr
        have h := congrArg (fun t ↦ t.app (op Y.unop.left) f.left)
          (n.inv_hom_id_app P.left)
        change (n.hom.app P.left).app (op Y.unop.left)
          ((n.inv.app P.left).app (op Y.unop.left) f.left) = f.left at h
        rw [h]
        exact Over.w f⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact congrArg (fun t ↦ t.app (op Y.unop.left) x.val) (n.hom_inv_id_app P.left)
      right_inv := by
        intro f
        apply Over.OverMorphism.ext
        exact congrArg (fun t ↦ t.app (op Y.unop.left) f.left) (n.inv_hom_id_app P.left)
    }).toIso)
    (by
      intro Y Y' f
      ext x
      apply Over.OverMorphism.ext
      exact (n.hom.app P.left).naturality_apply f.unop.left.op x.val)) ?_⟩⟩
  intro P Q f
  ext Y x
  apply Over.OverMorphism.ext
  exact congrArg (fun t ↦ t.app (op Y.unop.left) x.val) (n.hom.naturality f.left)

set_option linter.unusedVariables false in
/-- A binary subterminal cover has one simultaneous small subcanonical site presentation,
with the nerve, its four slice nerves, exact module equivalences and ordinary derived
comparisons, preserving the adjunctions by their canonical mates.

Source: Stacks Sites, Tags 03A1 and 03CI, with the simultaneous ringed extension described
in the node; Tags 00Y1, 04GZ and 03EH for slices
(blueprint: lem-sp-binary-cover-site-presentation).

Proof:
1. Apply the proved finite-limit closure of a small family in a Grothendieck topos to the
   original sheafified representables and 1,U,V,U×V. This gives a small fully faithful
   finite-limit-preserving inclusion without changing the original sieve topology.
2. The arbitrary-topology subcategory comparison constructs its epimorphic precoverage,
   subcanonical topology and presenting nerve. Choose small covering representatives with
   the same supports. To check the binary covers, restrict a section to the covering sieve
   supplied by the local-union hypothesis. Each restriction lifts to one product with U
   or V. Two maps agreeing on both product projections therefore agree locally on every
   section; separatedness makes them equal.
3. Compose the nerve equivalence on arrow categories with the localized-site fibre
   equivalence. The explicit fibre bijection sends a section to its map into the source
   of an arrow, and identifies its fibre condition with commutativity over the base.
   Naturality gives precisely the required slice Hom formula.
4. Transport the whole ring along the nerve. Invert the supplied ring data with RingData.square
   to obtain inverse image in the required direction. Construct its induced module direct
   image and use the existing module-transport theorem. Construct the source element slices
   and their continuity proofs by the existing element-site results.
5. Apply lem-sp-ringed-nerve-slice-transport to these fixed whole and slice nerves. This
   separate localized ring/module calculation gives the ringed slice morphisms, their module
   transports, the restriction comparisons and all three normalization equations.
6. An additive exact equivalence induces the ordinary derived equivalence by its actual
   termwise functors. For every comparison square, the adjunction Hom bijections and full
   faithfulness of the two equivalences show that both actual adjunction mates are
   invertible. These arguments construct the derived and mate fields from the module data.
-/
theorem exists_binaryCoverSitePresentation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : Sheaf J (Type u))
    (hU : IsSubterminal U) (hV : IsSubterminal V)
    (hcover : ∀ X : C,
      Sieve.generate (fun (Y : C) (_ : Y ⟶ X) ↦
        Nonempty (U.obj.obj (op Y)) ∨ Nonempty (V.obj.obj (op Y))) ∈ J X) :
    Nonempty (BinaryCoverSitePresentation J R U V) := by
  classical
  obtain ⟨B⟩ := binarySiteCore_exists J U V hcover
  let := B.category
  let := B.finiteLimits
  let := B.full
  let := B.faithful
  let := B.preservesLimits
  let := B.subcanonical
  obtain ⟨S, g, hi, hd, hg, ⟨T⟩⟩ := binaryRingedEquivalence R B.nerve
  let : IsIso g.ringMap := hg
  let sourceSlice (X : B.E) := Classical.choice
    (ringed_sheaf_slice_adjunction (localCoefficientRings R) (B.inclusion.obj X))
  let continuous {X Y : B.E} (f : X ⟶ Y) :=
    (element_site_descent (B.inclusion.obj Y)).2.2.2 _ (B.inclusion.map f)
  choose slice hslice using fun X : B.E ↦
    binarySliceNerve B.covers.toGrothendieck B.inclusion B.nerve B.nerveFormula X
  let sliceFormula (X : B.E) := Classical.choice (hslice X)
  obtain ⟨L⟩ := exists_ringedNerveSliceTransport B.covers.toGrothendieck R S B.inclusion
    B.nerve B.nerveFormula g hi T sourceSlice slice sliceFormula continuous
  refine ⟨{
    E := B.E
    inclusion := B.inclusion
    generators := B.generators
    objects := B.objects
    terminal := B.terminal
    first := B.first
    second := B.second
    intersection := B.intersection
    covers := B.covers
    site := B.site
    epimorphic := B.epimorphic
    representatives := B.representatives
    smallRepresentatives := B.smallRepresentatives
    coveringClass := B.coveringClass
    representativeCovers := B.representativeCovers
    sameSupports := B.sameSupports
    binaryCover := B.binaryCover
    nerve := B.nerve
    nerveFormula := B.nerveFormula
    represented := B.represented
    ring := S
    ringed := g
    inverseNerve := hi
    directNerve := hd
    ringIsIso := hg
    wholeModules := binaryModulesOfPresentation T
    sourceSlice := fun i ↦ sourceSlice (B.objects i)
    slice := fun i ↦ slice (B.objects i)
    sliceFormula := fun i ↦ sliceFormula (B.objects i)
    sliceRinged := fun i ↦ L.ringed (B.objects i)
    sliceInverse := fun i ↦ L.inverse (B.objects i)
    sliceRingIsIso := fun i ↦ L.ringIsIso (B.objects i)
    sliceModules := fun i ↦ binaryModulesOfPresentation (L.modules (B.objects i))
    sourceContinuous := fun _ _ f ↦ continuous f
    restriction := fun i ↦ binaryAdjointSquare _ _ _ _ (L.restriction (B.objects i))
    further := fun _ _ f ↦ binaryAdjointSquare _ _ _ _ (L.further f)
    restrictionComposition := fun _ _ f M ↦ L.restrictionComposition f M
    furtherIdentity := fun i M ↦ L.furtherIdentity (B.objects i) M
    furtherComposition := fun _ _ _ f h M ↦ L.furtherComposition f h M }⟩

end CategoryTheory
