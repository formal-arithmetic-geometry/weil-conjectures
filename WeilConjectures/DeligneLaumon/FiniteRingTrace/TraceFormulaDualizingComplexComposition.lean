/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CurrentCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates

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
  sorry

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
  sorry

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
  sorry

end WeilConjectures.FiniteRingTrace
