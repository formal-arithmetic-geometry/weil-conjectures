/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module
public import Sheaf.Paper.CondensedCoefficientComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.Paper.ProfinitePointPullback

/-! # Exact condensed coefficient changes and their derived tensor calculus

Source: archived master ModuleObject/Colimit/Compatibility.lean, A0.2 and Flat;
ModuleObject/Colimit/TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).

All modules below are the master internal module objects. The constructible categories
are `PadicSubfieldConstructible` and `PadicAlgClConstructible`, with no completeness
condition. The adjunctions are on the ambient unbounded derived categories.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

/-- Source: Compatibility.lean, A0.2 and Flat; ordinary module tensor adjunction;
TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: choose a finite field basis; its coordinate maps are continuous by the
finite-dimensional linear homeomorphism lemma. Continuous maps on profinite sets
therefore identify the finite coefficient module with the free module of that rank.
The exact strong monoidal inverse image from the point preserves this identification.
The tensor/restriction adjunction is given by `p ↦ 1 ⊗ p` and multiplication.
Restriction is exact because it only changes the action. Finite-stage tensor is exact
because its underlying module is a finite direct sum. For the algebraic closure, its
finite-stage coefficient cocone is a filtered colimit already on the finite-cover
basis of profinite sets; pullback preserves this colimit. Module sheaf filtered
colimits are exact and commute with tensor, giving flatness at the closure.
The exact-functor factorization and exact-derived-functor lemmas identify derivation
with termwise tensor on every complex, with its canonical shifts and cone triangles.
Descend the termwise unit and counit through localization; their triangle identities
are detected before localization, yielding the unbounded derived adjunction. -/
theorem condensedFiniteCoefficientCalculus
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (padicSubfieldRingObjMap T ℓ h)).obj (Mod.regular (padicSubfieldRingObj T ℓ
      F)) ≅
      Mod.finiteFree (padicSubfieldRingObj T ℓ E) (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) ∧
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ∧
    PreservesFiniteLimits
      (Mod.comap (padicSubfieldRingObjMap T ℓ h) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    PreservesFiniteColimits
      (Mod.comap (padicSubfieldRingObjMap T ℓ h) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ⊣ (Mod.comap
      (padicSubfieldRingObjMap T ℓ h))) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars (padicSubfieldRingObjMap T ℓ
      h)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).mapHomologicalComplex (ComplexShape.up ℤ)
        ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ⊣ (Mod.comap
      (padicSubfieldRingObjMap T ℓ h)).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).mapDerivedCategory) ∧
    (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))) n ⋙
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ≅ (Mod.extendScalars
        (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ⋙ shiftFunctor (DerivedCategory (Mod
        (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F))) n)) := by
  sorry

/-- Source: Compatibility.lean, A0.2 and Flat; ordinary module tensor adjunction;
TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: choose a finite field basis; its coordinate maps are continuous by the
finite-dimensional linear homeomorphism lemma. Continuous maps on profinite sets
therefore identify the finite coefficient module with the free module of that rank.
The exact strong monoidal inverse image from the point preserves this identification.
The tensor/restriction adjunction is given by `p ↦ 1 ⊗ p` and multiplication.
Restriction is exact because it only changes the action. Finite-stage tensor is exact
because its underlying module is a finite direct sum. For the algebraic closure, its
finite-stage coefficient cocone is a filtered colimit already on the finite-cover
basis of profinite sets; pullback preserves this colimit. Module sheaf filtered
colimits are exact and commute with tensor, giving flatness at the closure.
The exact-functor factorization and exact-derived-functor lemmas identify derivation
with termwise tensor on every complex, with its canonical shifts and cone triangles.
Descend the termwise unit and counit through localization; their triangle identities
are detected before localization, yielding the unbounded derived adjunction. -/
theorem condensedAlgClCoefficientCalculus
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ∧
    PreservesFiniteLimits
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    PreservesFiniteColimits
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ⊣ (Mod.comap
      (padicSubfieldRingObjToPadicAlgCl T ℓ E))) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ
      E)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ⊣
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapDerivedCategory) ∧
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))) n ⋙
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ≅
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ⋙
        shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj
        T ℓ))) n)) := by
  sorry

/-- Coherence of the canonical multiplication and unit comparisons.
Source: TwoColimit.lean, ExtendScalars; sheaf tensor coherence and localization
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: multiplication and its inverse are balanced and natural before sheafification.
The two associativity paths send `d ⊗ (c ⊗ (b ⊗ p))` to `dcb ⊗ p`.
Together with associativity of functor composition this gives the five-ring pentagon:
every path sends `h ⊗ (d ⊗ (c ⊗ (b ⊗ p)))` to `hdcb ⊗ p`.
The unit sends `a ⊗ p` to `ap`; either insertion of it in a multiplication comparison
has the same value. The same calculations hold with the last ring the closure.
These are equalities of maps from presheaf tensors and pass through the universal
property of sheafification, without asserting that global sections are pure tensors.
Apply these comparisons termwise. Shifts introduce the same differential sign on both
sides, and all coefficient factors have degree zero. Localization descends these
transformations and detects their equalities, proving the unit, associativity,
pentagon and shift compatibility laws. -/
theorem condensedCoefficientCoherence
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E F G H : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (h : E ≤ F) (k : F ≤ G) (l : G ≤ H),
      Functor.isoWhiskerRight (condensedCoefficientCompIso T ℓ h k) (derivedExtendScalarsSubfield T
        ℓ l) ≪≫
          (condensedCoefficientCompIso T ℓ (h.trans k) l) =
        Functor.associator (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsSubfield T ℓ k)
          (derivedExtendScalarsSubfield T ℓ l) ≪≫
          Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (condensedCoefficientCompIso T
            ℓ k l)
            ≪≫
          (condensedCoefficientCompIso T ℓ h (k.trans l))) ∧
    (∀ (E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F) (k : F ≤ G),
      Functor.isoWhiskerRight (condensedCoefficientCompIso T ℓ h k)
        (derivedExtendScalarsToPadicAlgCl T ℓ G)
        ≪≫ (derivedExtendScalarsCompIso T ℓ (h.trans k)) =
        Functor.associator (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsSubfield T ℓ k)
          (derivedExtendScalarsToPadicAlgCl T ℓ G) ≪≫
          Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsCompIso T
            ℓ k) ≪≫
            (derivedExtendScalarsCompIso T ℓ h)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      (condensedCoefficientCompIso T ℓ (le_refl E) h) =
        Functor.isoWhiskerRight (condensedCoefficientUnitIso T ℓ E) (derivedExtendScalarsSubfield T
          ℓ h) ≪≫
          Functor.leftUnitor (derivedExtendScalarsSubfield T ℓ h)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      (condensedCoefficientCompIso T ℓ h (le_refl F)) =
        Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (condensedCoefficientUnitIso T ℓ
          F) ≪≫
          Functor.rightUnitor (derivedExtendScalarsSubfield T ℓ h)) ∧
    (∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ),
      (derivedExtendScalarsCompIso T ℓ (le_refl E)) =
        Functor.isoWhiskerRight (condensedCoefficientUnitIso T ℓ E)
          (derivedExtendScalarsToPadicAlgCl T ℓ E)
          ≪≫ Functor.leftUnitor (derivedExtendScalarsToPadicAlgCl T ℓ E)) ∧
    (∀ (E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F) (k : F ≤ G),
      NatTrans.CommShift (condensedCoefficientCompIso T ℓ h k).hom ℤ) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      NatTrans.CommShift (derivedExtendScalarsCompIso T ℓ h).hom ℤ) ∧
    (∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ), NatTrans.CommShift
      (condensedCoefficientUnitIso T ℓ E).hom ℤ) := by
  sorry

/-- Tensor preserves the finite-coefficient colimit, in the category of modules over E.
Source: Compatibility.lean, RingObj; Stacks Tags 03DB, 03EP, 03EU
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
The parameters `D`, `e`, `hD`, `c`, `ec`, `hc` describe exactly the diagram of restricted
finite coefficient modules above E, with its inclusion cocone into the closure. This
allows any choices of the diagram and its colimit, without defining a second diagram.
`tensorRight P` is the internal relative tensor product over the E coefficient ring.
Preservation of this cocone says the canonical comparison is an isomorphism. Its
naturality in P follows from the functorial tensor and colimit comparison.
Proof: finite intermediate fields above E form a nonempty filtered poset. The union of
the continuous-function sheaves is already a sheaf, since a finite covering uses only
finitely many fields and hence their compositum. The inverse image from the point
preserves this colimit. The module forgetful functor creates it with the given action.
Tensor commutes with filtered colimits of module sheaves, so tensoring its universal
cocone by P remains a universal cocone, naturally in P. -/
theorem condensedCoefficientTensorColimit
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (D : Under E ⥤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)))
    (e : ∀ F : Under E, D.obj F ≅
      (Mod.comap (padicSubfieldRingObjMap T ℓ (leOfHom F.hom))).obj
        (Mod.regular (padicSubfieldRingObj T ℓ F.right)))
    (hD : ∀ (F G : Under E) (f : F ⟶ G),
      (D.map f).hom ≫ (e G).hom.hom =
        (e F).hom.hom ≫ padicSubfieldRingObjMap T ℓ (leOfHom f.right))
    (c : Cocone D)
    (ec : c.pt ≅ (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj (Mod.regular
      (padicAlgClRingObj T ℓ)))
    (hc : ∀ F : Under E, (c.ι.app F).hom ≫ ec.hom.hom =
      (e F).hom.hom ≫ padicSubfieldRingObjToPadicAlgCl T ℓ F.right)
    (hcolim : IsColimit c) :
    ∀ P : (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      Nonempty (IsColimit ((tensorRight P).mapCocone c)) := by
  sorry

end AlgebraicGeometry.ProEtale
