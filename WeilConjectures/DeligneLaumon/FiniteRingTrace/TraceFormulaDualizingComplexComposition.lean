/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CurrentCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData

/-! # Composition for dualizing complexes with arbitrary finite primary coefficients

Source: current DAG thm-trf-dualizing-complex-composition, generalized on 2026-11-01,
and literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-six/
thm-trf-dualizing-complex-composition.md and its .proof.md, both proof paragraphs
(blueprint: thm-trf-dualizing-complex-composition).

We use the current Brown adjunction and the recorded ordinary module-derived categories.
The compact-support compositor is the normalized proper/open comparison; its conjugate
is evaluated at the actual coefficient unit. No DVR-quotient presentation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteRingTrace

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)

/-- The finite discrete coefficient satisfies the existing coefficient predicate.
Source: current coefficient convention (blueprint: thm-trf-dualizing-complex-composition). -/
abbrev compositionCoefficient : IsLocalizingAdmissibleCoefficient ell (coefficient A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨hA.choose, hA.choose_spec.2⟩, ⟨Iso.refl _⟩⟩

variable {X Y Z : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The specified constructible adjunction, with its actual compactification lower functor.
Source: sk-thm-existence (3)--(4) and def-trf-admissibility
(blueprint: thm-trf-dualizing-complex-composition). -/
def compositionData (f : X ⟶ Y) : CurrentConstructibleExceptionalData (coefficient A) f := by
  let := fieldChar D
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  exact currentConstructibleExceptionalData (coefficient A) ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) f (compositionCoefficient A ell hA)

/-- The actual normalized ambient compositor restricted to a finite-Tor constructible input.
Source: sk-thm-sf-comp-composition, normalized proper/open compositor
(blueprint: thm-trf-dualizing-complex-composition). -/
def compositionAmbient (f : X ⟶ Y) (g : Y ⟶ Z) :
    (constantModelBoundedConstructible (coefficient A) X.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
      (rightDerivedLowerShriekOfCompactification (coefficient A) (compactificationOverField f) ⋙
        rightDerivedLowerShriekOfCompactification (coefficient A) (compactificationOverField g)) ≅
    (constantModelBoundedConstructible (coefficient A) X.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
      rightDerivedLowerShriekOfCompactification (coefficient A)
        (compactificationOverField (f ≫ g)) := by
  let h := compositionCoherence A D ell hell hA
  let i : (constantModelBoundedConstructible (coefficient A) X.left ⊓
      DerivedCategory.finiteTorAmplitude _).FullSubcategory ⥤
      (localizingClosureProEtale (coefficient A) X.left).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK P _ hP ↦ hP K hK)
  exact Functor.isoWhiskerLeft i
    (h.comp (SepFinType.homMk f) (SepFinType.homMk g)
      (compactificationOverField f) (compactificationOverField g)
      (compactificationOverField (f ≫ g)))

/-- Lift the same ambient compositor through the full constructible inclusion.
The two `lower_eq` identifications fix both objects and morphisms.
Source: composition proof, Step 1 (blueprint: thm-trf-dualizing-complex-composition). -/
def compositionSupport (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compositionData A D ell hell hA f).lower ⋙
      (compositionData A D ell hell hA g).lower ≅
        (compositionData A D ell hell hA (f ≫ g)).lower := by
  let F := compositionData A D ell hell hA f
  let G := compositionData A D ell hell hA g
  let H := compositionData A D ell hell hA (f ≫ g)
  apply ((constantModelBoundedConstructible (coefficient A) Z.left ⊓
    DerivedCategory.finiteTorAmplitude _).fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F.lower (eqToIso G.lower_eq) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso F.lower_eq) _ ≪≫
    Functor.associator _ _ _ ≪≫ compositionAmbient A D ell hell hA f g ≪≫
    (eqToIso H.lower_eq).symm

/-- The exceptional compositor is exactly the conjugate of inverse compact support.
Its counit is the pasted counit, so the normalization is part of its definition.
Source: composition proof, Steps 2 and 4; Mathlib conjugateIsoEquiv
(blueprint: thm-trf-dualizing-complex-composition). -/
def compositionExceptional (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compositionData A D ell hell hA g).right ⋙
      (compositionData A D ell hell hA f).right ≅
        (compositionData A D ell hell hA (f ≫ g)).right :=
  conjugateIsoEquiv
    ((compositionData A D ell hell hA f).adjunction.comp
      (compositionData A D ell hell hA g).adjunction)
    (compositionData A D ell hell hA (f ≫ g)).adjunction
    (compositionSupport A D ell hell hA f g).symm

/-- The existing dualizing object, retained in its full constructible subcategory.
Forgetting `.obj` is definitionally `dualizingComplex`, not a replacement complex.
Source: composition proof, Step 3 (blueprint: thm-trf-dualizing-complex-composition). -/
def compositionOmega (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom] : Ctf A W.left :=
  (exceptional A D ell hell hA W).obj
    ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
      constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩

/-- The functorial structure morphism lands in the actual terminal object over Spec k.
Source: composition proof, a_F = a_X d
(blueprint: thm-trf-dualizing-complex-composition). -/
abbrev compositionBase : Over (Spec (.of D.k)) := Over.mk (𝟙 (Spec (.of D.k)))

/-- The structure morphism of the terminal base is finite type and separated.
Source: the base identity (blueprint: thm-trf-dualizing-complex-composition). -/
instance compositionBase_lft : LocallyOfFiniteType (compositionBase D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))

/-- The structure morphism of the terminal base is quasi-compact.
Source: the base identity (blueprint: thm-trf-dualizing-complex-composition). -/
instance compositionBase_qc : QuasiCompact (compositionBase D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))

/-- The structure morphism of the terminal base is separated.
Source: the base identity (blueprint: thm-trf-dualizing-complex-composition). -/
instance compositionBase_sep : IsSeparated (compositionBase D).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))

/-- Evaluate the specified exceptional compositor at the coefficient unit and identify the
composite structure map by terminality. This is the canonical dualizing comparison itself.
Source: composition proof, Steps 2--3
(blueprint: thm-trf-dualizing-complex-composition). -/
def dualizingComposition (f : X ⟶ Y) :
    (compositionData A D ell hell hA f).right.obj (compositionOmega A D ell hell hA Y) ≅
      compositionOmega A D ell hell hA X := by
  let U : Ctf A (Spec (.of D.k)) :=
    ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
      constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩
  exact (compositionExceptional A D ell hell hA f
      (Over.mkIdTerminal.from Y : Y ⟶ compositionBase D)).app U ≪≫
    eqToIso (congrArg
      (fun t : X ⟶ compositionBase D ↦ (compositionData A D ell hell hA t).right.obj U)
      (Over.mkIdTerminal.hom_ext _ _))

/-- The normalized compact-support identity, restricted through the full inclusion.
Compare the chosen identity compactification to the proper identity model, and then use
its specified open/proper identity comparison. Source: composition proof, Step 6
(blueprint: thm-trf-dualizing-complex-composition). -/
def compositionSupportIdentity :
    (compositionData A D ell hell hA (𝟙 X)).lower ≅ 𝟭 (Ctf A X.left) := by
  let h := compositionCoherence A D ell hell hA
  let i : Ctf A X.left ⥤
      (localizingClosureProEtale (coefficient A) X.left).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK P _ hP ↦ hP K hK)
  apply ((constantModelBoundedConstructible (coefficient A) X.left ⊓
    DerivedCategory.finiteTorAmplitude _).fullyFaithfulι.whiskeringRight _).preimageIso
  exact eqToIso (compositionData A D ell hell hA (𝟙 X)).lower_eq ≪≫
    Functor.isoWhiskerLeft i
      (h.comparison (𝟙 (SepFinType.mk X)) (compactificationOverField (𝟙 X))
        (Compactification.ofIsProper (𝟙 X.left))) ≪≫
    Functor.isoWhiskerLeft
      (constantModelBoundedConstructible (coefficient A) X.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι
      (CompactSupportComposition.identity (coefficient A) X.left) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- The exceptional identity is the conjugate of the inverse compact-support unit.
This keeps its specified counit, even when that counit is not literally the identity.
Source: composition proof, Step 6 (blueprint: thm-trf-dualizing-complex-composition). -/
def compositionExceptionalIdentity :
    (compositionData A D ell hell hA (𝟙 X)).right ≅ 𝟭 (Ctf A X.left) :=
  conjugateIsoEquiv (compositionData A D ell hell hA (𝟙 X)).adjunction
    (Adjunction.id) (compositionSupportIdentity A D ell hell hA).symm

-- Keep the ambient functor folded while simplifying its dependent comparison maps.

private theorem compositionSupport_hom (f : X ⟶ Y) (g : Y ⟶ Z) (K : Ctf A X.left) :
    (constantModelBoundedConstructible (coefficient A) Z.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι.map
          ((compositionSupport A D ell hell hA f g).hom.app K) ≫
        (eqToIso (compositionData A D ell hell hA (f ≫ g)).lower_eq).hom.app K =
      (eqToIso (compositionData A D ell hell hA g).lower_eq).hom.app
          ((compositionData A D ell hell hA f).lower.obj K) ≫
        (rightDerivedLowerShriekOfCompactification (coefficient A)
          (compactificationOverField g)).map
            ((eqToIso (compositionData A D ell hell hA f).lower_eq).hom.app K) ≫
          (compositionAmbient A D ell hell hA f g).hom.app K := by
  simp only [compositionSupport,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom,
    Iso.trans_hom, Iso.symm_hom, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.id_comp]

private theorem compositionLower_transport (f g : X ⟶ Y) (h : f = g) (K : Ctf A X.left) :
    (constantModelBoundedConstructible (coefficient A) Y.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι.map
          (eqToHom (congrArg (fun t : X ⟶ Y ↦
            (compositionData A D ell hell hA t).lower.obj K) h)) ≫
        (eqToIso (compositionData A D ell hell hA g).lower_eq).hom.app K =
      (eqToIso (compositionData A D ell hell hA f).lower_eq).hom.app K ≫
        eqToHom (congrArg (fun t : X ⟶ Y ↦
          (rightDerivedLowerShriekOfCompactification (coefficient A)
            (compactificationOverField t)).obj K.obj) h) := by
  subst g
  simp

private theorem compositionComparison_transport_inv (f g : X ⟶ Y) (h : f = g)
    (K : (localizingClosureProEtale (coefficient A) X.left).FullSubcategory) :
    ((compositionCoherence A D ell hell hA).comparison (SepFinType.homMk f)
        ((compactificationOverField g).copy (congrArg Over.Hom.left h))
        (compactificationOverField f)).hom.app K =
      eqToHom (congrArg (fun t : X ⟶ Y ↦
        (rightDerivedLowerShriekOfCompactification (coefficient A)
          (compactificationOverField t)).obj K.obj) h.symm) := by
  subst g
  change ((compositionCoherence A D ell hell hA).comparison (SepFinType.homMk f)
    (compactificationOverField f) (compactificationOverField f)).hom.app K = 𝟙 _
  exact congrArg (fun e ↦ e.hom.app K)
    ((compositionCoherence A D ell hell hA).laws.2.1
      (SepFinType.homMk f) (compactificationOverField f))

private def compositionAmbientImage (f : X ⟶ Y) (K : Ctf A X.left) : Ctf A Y.left :=
  ⟨(rightDerivedLowerShriekOfCompactification (coefficient A)
      (compactificationOverField f)).obj K.obj,
    ((compositionCoherence A D ell hell hA).preserves (SepFinType.homMk f)
      (compactificationOverField f)).2 K.obj K.property⟩

private theorem compositionAmbient_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : Ctf A X.left) :
    (rightDerivedLowerShriekOfCompactification (coefficient A)
        (compactificationOverField h)).map
          ((compositionAmbient A D ell hell hA f g).hom.app K) ≫
        (compositionAmbient A D ell hell hA (f ≫ g) h).hom.app K ≫
          eqToHom (congrArg (fun t : X ⟶ W ↦
            (rightDerivedLowerShriekOfCompactification (coefficient A)
              (compactificationOverField t)).obj K.obj) (Category.assoc f g h)) =
      (compositionAmbient A D ell hell hA g h).hom.app
          (compositionAmbientImage A D ell hell hA f K) ≫
        (compositionAmbient A D ell hell hA f (g ≫ h)).hom.app K := by
  let H := compositionCoherence A D ell hell hA
  let i : Ctf A X.left ⥤
      (localizingClosureProEtale (coefficient A) X.left).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK P _ hP ↦ hP K hK)
  have ha := H.laws.2.2.2.2.2.2.2.1
    (SepFinType.homMk f) (SepFinType.homMk g) (SepFinType.homMk h)
    (compactificationOverField f) (compactificationOverField g)
    (compactificationOverField h) (compactificationOverField (f ≫ g))
    (compactificationOverField (g ≫ h)) (compactificationOverField ((f ≫ g) ≫ h))
    (i.obj K)
  have hi := H.laws.2.2.2.2.1 (SepFinType.homMk f)
    (SepFinType.homMk g ≫ SepFinType.homMk h)
    (compactificationOverField f) (compactificationOverField f)
    (compactificationOverField (g ≫ h)) (compactificationOverField (g ≫ h))
    ((compactificationOverField ((f ≫ g) ≫ h)).copy
      (Category.assoc f.left g.left h.left).symm)
    (compactificationOverField (f ≫ g ≫ h)) (i.obj K)
  rw [H.laws.2.1, H.laws.2.1] at hi
  simp only [Iso.refl_hom, NatTrans.id_app] at hi
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at hi
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at hi
  have ht := compositionComparison_transport_inv A D ell hell hA
    (f ≫ g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h).symm (i.obj K)
  erw [ht] at hi
  dsimp only [compositionAmbient, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, compositionAmbientImage]
  calc
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun v ↦ v ≫ _) ha
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (fun v ↦ _ ≫ v) hi

private theorem compositionSupport_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : Ctf A X.left) :
    (compositionData A D ell hell hA h).lower.map
        ((compositionSupport A D ell hell hA f g).hom.app K) ≫
      (compositionSupport A D ell hell hA (f ≫ g) h).hom.app K ≫
        eqToHom (congrArg (fun t : X ⟶ W ↦
          (compositionData A D ell hell hA t).lower.obj K) (Category.assoc f g h)) =
    (compositionSupport A D ell hell hA g h).hom.app
        ((compositionData A D ell hell hA f).lower.obj K) ≫
      (compositionSupport A D ell hell hA f (g ≫ h)).hom.app K := by
  let sf := (eqToIso (compositionData A D ell hell hA f).lower_eq).hom.app K
  let Mg := rightDerivedLowerShriekOfCompactification (coefficient A)
    (compactificationOverField g)
  let Mh := rightDerivedLowerShriekOfCompactification (coefficient A)
    (compactificationOverField h)
  let Mgh := rightDerivedLowerShriekOfCompactification (coefficient A)
    (compactificationOverField (g ≫ h))
  let Jz := (constantModelBoundedConstructible (coefficient A) Z.left ⊓
    DerivedCategory.finiteTorAmplitude _).ι
  let Jw := (constantModelBoundedConstructible (coefficient A) W.left ⊓
    DerivedCategory.finiteTorAmplitude _).ι
  have hn :
      Jw.map ((compositionData A D ell hell hA h).lower.map
          ((compositionSupport A D ell hell hA f g).hom.app K)) ≫
        (eqToIso (compositionData A D ell hell hA h).lower_eq).hom.app
          ((compositionData A D ell hell hA (f ≫ g)).lower.obj K) =
      (eqToIso (compositionData A D ell hell hA h).lower_eq).hom.app
          ((compositionData A D ell hell hA g).lower.obj
            ((compositionData A D ell hell hA f).lower.obj K)) ≫
        Mh.map (Jz.map ((compositionSupport A D ell hell hA f g).hom.app K)) :=
    (eqToIso (compositionData A D ell hell hA h).lower_eq).hom.naturality
      ((compositionSupport A D ell hell hA f g).hom.app K)
  have hn' : Mh.map (Mg.map sf) ≫
        (compositionAmbient A D ell hell hA g h).hom.app
          (compositionAmbientImage A D ell hell hA f K) =
      (compositionAmbient A D ell hell hA g h).hom.app
          ((compositionData A D ell hell hA f).lower.obj K) ≫ Mgh.map sf :=
    (compositionAmbient A D ell hell hA g h).hom.naturality
      (ObjectProperty.homMk sf :
        (compositionData A D ell hell hA f).lower.obj K ⟶
          compositionAmbientImage A D ell hell hA f K)
  apply Jw.map_injective
  rw [← cancel_mono
    ((eqToIso (compositionData A D ell hell hA (f ≫ g ≫ h)).lower_eq).hom.app K)]
  simp only [Functor.map_comp, Category.assoc]
  rw [compositionLower_transport A D ell hell hA ((f ≫ g) ≫ h) (f ≫ g ≫ h)
    (Category.assoc f g h) K]
  rw [reassoc_of% (compositionSupport_hom A D ell hell hA (f ≫ g) h K)]
  rw [compositionSupport_hom A D ell hell hA f (g ≫ h) K]
  rw [reassoc_of% hn]
  rw [reassoc_of% (compositionSupport_hom A D ell hell hA g h
    ((compositionData A D ell hell hA f).lower.obj K))]
  erw [← Functor.map_comp_assoc, compositionSupport_hom]
  simp only [Functor.map_comp, Category.assoc]
  have : IsIso (Mh.map ((eqToIso (compositionData A D ell hell hA g).lower_eq).hom.app
      ((compositionData A D ell hell hA f).lower.obj K))) := Functor.map_isIso _ _
  erw [cancel_epi, cancel_epi]
  rw [← reassoc_of% hn', compositionAmbient_assoc]

private theorem compositionExceptional_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : Ctf A W.left) :
    (compositionData A D ell hell hA f).right.map
        ((compositionExceptional A D ell hell hA g h).hom.app K) ≫
      (compositionExceptional A D ell hell hA f (g ≫ h)).hom.app K =
    (compositionExceptional A D ell hell hA f g).hom.app
        ((compositionData A D ell hell hA h).right.obj K) ≫
      (compositionExceptional A D ell hell hA (f ≫ g) h).hom.app K ≫
        eqToHom (congrArg (fun t : X ⟶ W ↦
          (compositionData A D ell hell hA t).right.obj K) (Category.assoc f g h)) := by
  have hL (M : Ctf A X.left) :
      (compositionSupport A D ell hell hA (f ≫ g) h).inv.app M ≫
        (compositionData A D ell hell hA h).lower.map
          ((compositionSupport A D ell hell hA f g).inv.app M) =
      eqToHom (congrArg (fun t : X ⟶ W ↦
          (compositionData A D ell hell hA t).lower.obj M) (Category.assoc f g h)) ≫
        (compositionSupport A D ell hell hA f (g ≫ h)).inv.app M ≫
          (compositionSupport A D ell hell hA g h).inv.app
            ((compositionData A D ell hell hA f).lower.obj M) := by
    let IL := (compositionData A D ell hell hA h).lower.mapIso
        ((compositionSupport A D ell hell hA f g).app M) ≪≫
      (compositionSupport A D ell hell hA (f ≫ g) h).app M ≪≫
        eqToIso (congrArg (fun t : X ⟶ W ↦
          (compositionData A D ell hell hA t).lower.obj M) (Category.assoc f g h))
    let IR := (compositionSupport A D ell hell hA g h).app
        ((compositionData A D ell hell hA f).lower.obj M) ≪≫
      (compositionSupport A D ell hell hA f (g ≫ h)).app M
    have hs : IL = IR := Iso.ext (compositionSupport_assoc A D ell hell hA f g h M)
    have hi := congrArg Iso.inv hs
    apply (cancel_epi (eqToHom (congrArg (fun t : X ⟶ W ↦
      (compositionData A D ell hell hA t).lower.obj M) (Category.assoc f g h).symm))).mp
    simpa only [IL, IR, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp] using hi
  have he := conjugateIsoEquiv_assoc_aux
    (fun t : X ⟶ W ↦ (compositionData A D ell hell hA t).lower)
    (fun t : X ⟶ W ↦ (compositionData A D ell hell hA t).right)
    (fun t ↦ (compositionData A D ell hell hA t).adjunction) (Category.assoc f g h)
    (compositionData A D ell hell hA f).adjunction
    (compositionData A D ell hell hA g).adjunction
    (compositionData A D ell hell hA h).adjunction
    (compositionData A D ell hell hA (f ≫ g)).adjunction
    (compositionData A D ell hell hA (g ≫ h)).adjunction
    (compositionSupport A D ell hell hA f g).symm
    (compositionSupport A D ell hell hA g h).symm
    (compositionSupport A D ell hell hA (f ≫ g) h).symm
    (compositionSupport A D ell hell hA f (g ≫ h)).symm hL K
  let IL := (compositionData A D ell hell hA f).right.mapIso
      ((compositionExceptional A D ell hell hA g h).app K) ≪≫
    (compositionExceptional A D ell hell hA f (g ≫ h)).app K
  let IR := (compositionExceptional A D ell hell hA f g).app
      ((compositionData A D ell hell hA h).right.obj K) ≪≫
    (compositionExceptional A D ell hell hA (f ≫ g) h).app K ≪≫
      eqToIso (congrArg (fun t : X ⟶ W ↦
        (compositionData A D ell hell hA t).right.obj K) (Category.assoc f g h))
  have hi : IR.inv = IL.inv := by
    dsimp only [IR, IL, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, eqToIso.inv]
    change (compositionExceptional A D ell hell hA (f ≫ g) h).inv.app K ≫
        (compositionExceptional A D ell hell hA f g).inv.app
          ((compositionData A D ell hell hA h).right.obj K) =
      eqToHom (congrArg (fun t : X ⟶ W ↦
          (compositionData A D ell hell hA t).right.obj K) (Category.assoc f g h)) ≫
        (compositionExceptional A D ell hell hA f (g ≫ h)).inv.app K ≫
          (compositionData A D ell hell hA f).right.map
            ((compositionExceptional A D ell hell hA g h).inv.app K) at he
    rw [Category.assoc, he]
    simp only [eqToHom_refl, Category.id_comp]
  exact (congrArg Iso.hom (Iso.ext_inv hi)).symm

private theorem compositionExceptional_terminalTransport (f : X ⟶ Y)
    (a b : Y ⟶ compositionBase D) (hab : a = b)
    (K : Ctf A (Spec (.of D.k))) :
    (compositionData A D ell hell hA f).right.map
        (eqToHom (congrArg (fun t : Y ⟶ compositionBase D ↦
          (compositionData A D ell hell hA t).right.obj K) hab)) ≫
      (compositionExceptional A D ell hell hA f b).hom.app K =
    (compositionExceptional A D ell hell hA f a).hom.app K ≫
      eqToHom (congrArg (fun t : Y ⟶ compositionBase D ↦
        (compositionData A D ell hell hA (f ≫ t)).right.obj K) hab) := by
  subst b
  simp

private theorem compositionComparison_transport (f g : X ⟶ Y) (h : f = g)
    (K : (localizingClosureProEtale (coefficient A) X.left).FullSubcategory) :
    ((compositionCoherence A D ell hell hA).comparison (SepFinType.homMk f)
        (compactificationOverField f)
        ((compactificationOverField g).copy (congrArg Over.Hom.left h))).hom.app K =
      eqToHom (congrArg (fun t : X ⟶ Y ↦
        (rightDerivedLowerShriekOfCompactification (coefficient A)
          (compactificationOverField t)).obj K.obj) h) := by
  subst g
  change ((compositionCoherence A D ell hell hA).comparison (SepFinType.homMk f)
    (compactificationOverField f) (compactificationOverField f)).hom.app K = 𝟙 _
  exact congrArg (fun e ↦ e.hom.app K)
    ((compositionCoherence A D ell hell hA).laws.2.1
      (SepFinType.homMk f) (compactificationOverField f))

private theorem compositionAmbient_unitLeft (f : X ⟶ Y) (K : Ctf A X.left) :
    (compositionAmbient A D ell hell hA (𝟙 X) f).hom.app K ≫
      eqToHom (congrArg (fun t : X ⟶ Y ↦
        (rightDerivedLowerShriekOfCompactification (coefficient A)
          (compactificationOverField t)).obj K.obj) (Category.id_comp f)) =
    (rightDerivedLowerShriekOfCompactification (coefficient A)
      (compactificationOverField f)).map
        (((compositionCoherence A D ell hell hA).comparison (𝟙 (SepFinType.mk X))
          (compactificationOverField (𝟙 X))
          (Compactification.ofIsProper (𝟙 X.left))).hom.app
            ((ObjectProperty.ιOfLE (fun K hK _P _ hP ↦ hP K hK)).obj K) ≫
          (CompactSupportComposition.identity (coefficient A) X.left).hom.app K.obj) := by
  let H := compositionCoherence A D ell hell hA
  let i : Ctf A X.left ⥤
      (localizingClosureProEtale (coefficient A) X.left).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK P _ hP ↦ hP K hK)
  have hi := H.laws.2.2.2.2.1 (𝟙 (SepFinType.mk X)) (SepFinType.homMk f)
    (compactificationOverField (𝟙 X)) (Compactification.ofIsProper (𝟙 X.left))
    (compactificationOverField f) (compactificationOverField f)
    (compactificationOverField (𝟙 X ≫ f))
    ((compactificationOverField f).copy (Category.id_comp f.left)) (i.obj K)
  rw [H.laws.2.1] at hi
  simp only [Iso.refl_hom, NatTrans.id_app] at hi
  rw [H.laws.2.2.2.2.2.1] at hi
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at hi
  simp only [Category.id_comp] at hi
  have hi' := hi.trans (Functor.map_comp _ _ _).symm
  have ht := compositionComparison_transport A D ell hell hA (𝟙 X ≫ f) f
    (Category.id_comp f) (i.obj K)
  erw [ht] at hi'
  exact hi'

private theorem compositionSupport_unitLeft (f : X ⟶ Y) (K : Ctf A X.left) :
    (compositionSupport A D ell hell hA (𝟙 X) f).hom.app K ≫
        eqToHom (congrArg (fun t : X ⟶ Y ↦
          (compositionData A D ell hell hA t).lower.obj K) (Category.id_comp f)) =
      (compositionData A D ell hell hA f).lower.map
        ((compositionSupportIdentity A D ell hell hA).hom.app K) := by
  apply (constantModelBoundedConstructible (coefficient A) Y.left ⊓
    DerivedCategory.finiteTorAmplitude _).ι.map_injective
  rw [← cancel_mono ((eqToIso (compositionData A D ell hell hA f).lower_eq).hom.app K)]
  rw [Functor.map_comp, Category.assoc,
    compositionLower_transport A D ell hell hA (𝟙 X ≫ f) f (Category.id_comp f) K]
  have hn := (eqToIso (compositionData A D ell hell hA f).lower_eq).hom.naturality
    ((compositionSupportIdentity A D ell hell hA).hom.app K)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  simp only [compositionSupport, compositionSupportIdentity,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
    ObjectProperty.FullSubcategory.id_hom,
    Iso.trans_hom, Iso.symm_hom, Category.id_comp, Category.comp_id]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [compositionAmbient_unitLeft]
  simp only [Functor.map_comp]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem compositionExceptional_transport (f g : X ⟶ Y) (h : f = g)
    (K : Ctf A Y.left) :
    (conjugateIsoEquiv (compositionData A D ell hell hA f).adjunction
      (compositionData A D ell hell hA g).adjunction
      (eqToIso (congrArg (fun t : X ⟶ Y ↦
        (compositionData A D ell hell hA t).lower) h.symm))).hom.app K =
      eqToHom (congrArg (fun t : X ⟶ Y ↦
        (compositionData A D ell hell hA t).right.obj K) h) := by
  subst g
  simp [conjugateIsoEquiv_apply_hom]

/-- Further-composition functoriality of the canonical dualizing comparisons.
Source: composition proof, Steps 4--5
(blueprint: thm-trf-dualizing-complex-composition).

Proof: the exceptional compositor is the adjunction conjugate of inverse compact support.
Mate pasting identifies the two displayed composites with the conjugates of the two
inverse compact-support compositors for f, g and a_Z. Their left mates agree by the
associativity equation in sk-thm-sf-comp-composition, so their right mates agree.
Terminality identifies the composite structure maps, and evaluation at the coefficient
unit gives this equation in the full constructible category. -/
theorem dualizingComposition_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compositionData A D ell hell hA f).right.map
        (dualizingComposition A D ell hell hA g).hom ≫
      (dualizingComposition A D ell hell hA f).hom =
    (compositionExceptional A D ell hell hA f g).hom.app
        (compositionOmega A D ell hell hA Z) ≫
      (dualizingComposition A D ell hell hA (f ≫ g)).hom := by
  let az : Z ⟶ compositionBase D := Over.mkIdTerminal.from Z
  let ay : Y ⟶ compositionBase D := Over.mkIdTerminal.from Y
  let ax : X ⟶ compositionBase D := Over.mkIdTerminal.from X
  let U : Ctf A (Spec (.of D.k)) :=
    ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
      constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩
  have ht := compositionExceptional_terminalTransport A D ell hell hA f
    (g ≫ az) ay (Over.mkIdTerminal.hom_ext _ _) U
  have hc := compositionExceptional_assoc A D ell hell hA f g az U
  dsimp only [dualizingComposition, Iso.trans_hom, Iso.app_hom, eqToIso.hom]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% ht, ← Category.assoc, hc]
  simp only [Category.assoc, eqToHom_trans_assoc]
  congr 1
  rw [eqToHom_trans]

/-- Identity functoriality with the actual unit-normalized exceptional identity.
Source: composition proof, Steps 6--8
(blueprint: thm-trf-dualizing-complex-composition).

Proof: conjugate the inverse compact-support unit under the specified identity
adjunction. Its component is the exceptional counit after the inverse left unit.
Substitute the two compact-support unit laws into the compositor's defining transpose;
counit naturality and injectivity of the adjunction Hom equivalence give the two
identity equations. Evaluate the source-identity equation at the coefficient unit and
use terminality for the structure map to obtain the displayed equality. -/
theorem dualizingComposition_id :
    dualizingComposition A D ell hell hA (𝟙 X) =
      (compositionExceptionalIdentity A D ell hell hA).app
        (compositionOmega A D ell hell hA X) := by
  let t : X ⟶ compositionBase D := Over.mkIdTerminal.from X
  let U : Ctf A (Spec (.of D.k)) :=
    ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
      constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩
  let e := eqToIso (congrArg (fun a : X ⟶ compositionBase D ↦
    (compositionData A D ell hell hA a).lower) (Category.id_comp t))
  have hc (K : Ctf A X.left) :
      (compositionSupport A D ell hell hA (𝟙 X) t).inv.app K ≫
          (compositionData A D ell hell hA t).lower.map
            ((compositionSupportIdentity A D ell hell hA).hom.app K) = e.hom.app K := by
    rw [← compositionSupport_unitLeft A D ell hell hA t K]
    simp only [Iso.inv_hom_id_app_assoc, e, eqToIso.hom, eqToHom_app]
  have he := conjugateIsoEquiv_comp_left_hom_app
    (compositionData A D ell hell hA (𝟙 X ≫ t)).adjunction
    (compositionData A D ell hell hA t).adjunction
    (compositionData A D ell hell hA (𝟙 X)).adjunction
    (compositionSupport A D ell hell hA (𝟙 X) t).symm
    (compositionSupportIdentity A D ell hell hA) e hc U
  have he' :
      (compositionExceptional A D ell hell hA (𝟙 X) t).inv.app U ≫
          (compositionExceptionalIdentity A D ell hell hA).hom.app
            ((compositionData A D ell hell hA t).right.obj U) =
        eqToHom (congrArg (fun a : X ⟶ compositionBase D ↦
          (compositionData A D ell hell hA a).right.obj U) (Category.id_comp t)) := by
    exact he.trans
      (compositionExceptional_transport A D ell hell hA (𝟙 X ≫ t) t
        (Category.id_comp t) U)
  apply Iso.ext
  dsimp only [dualizingComposition, Iso.trans_hom, Iso.app_hom, eqToIso.hom]
  rw [← he']
  change (compositionExceptional A D ell hell hA (𝟙 X) t).hom.app U ≫
      (compositionExceptional A D ell hell hA (𝟙 X) t).inv.app U ≫
        (compositionExceptionalIdentity A D ell hell hA).hom.app
          ((compositionData A D ell hell hA t).right.obj U) =
      (compositionExceptionalIdentity A D ell hell hA).hom.app
        ((compositionData A D ell hell hA t).right.obj U)
  rw [Iso.hom_inv_id_app_assoc]

/-- Canonical Rd! omega_X = omega_F for every finite commutative ell-primary ring.
The equality pins the ambient isomorphism to the explicitly constructed conjugate.
The preceding composition and identity equations give functoriality in d.
Source: current generalized node and latest blueprint, both proof paragraphs
(blueprint: thm-trf-dualizing-complex-composition).

Proof: (1) sk-thm-existence gives the three constructible adjunctions for d, a_X and a_F.
The normalized compact-support composition is sk-thm-sf-comp-composition (1), restricted
through the full inclusions using lower_eq. (2) Apply right-adjoint composition with its
pasted counit; conjugate the inverse compact-support isomorphism. This is precisely
compositionExceptional, rather than an arbitrary isomorphism of objects. (3) The constant
coefficient unit is free of rank one, hence constructible with Tor amplitude [0,0].
Evaluation gives dualizingComposition, whose target is the recorded dualizingComplex
by the equality a_F = a_X d. (4)--(5) Mate pasting and compact-support associativity give
dualizingComposition_comp. (6)--(8) Conjugating the inverse compact-support unit and using
its two unit laws gives dualizingComposition_id, with the specified exceptional counit.
Finally apply the full inclusion into the ordinary module-derived category. -/
theorem dualizingComplexComposition (d : X ⟶ Y) :
    ∃ e : ((compositionData A D ell hell hA d).right.obj
        (compositionOmega A D ell hell hA Y)).obj ≅ dualizingComplex A D ell hell hA X,
      e = (constantModelBoundedConstructible (coefficient A) X.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι.mapIso
          (dualizingComposition A D ell hell hA d) := by
  exact ⟨(constantModelBoundedConstructible (coefficient A) X.left ⊓
    DerivedCategory.finiteTorAmplitude _).ι.mapIso
      (dualizingComposition A D ell hell hA d), rfl⟩

end WeilConjectures.FiniteRingTrace
