/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.FiniteSubextensionsDirected
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.DirectedRingSheafModuleColimit
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.Paper.ConstructibleExtContinuity
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# Finite descent of derived coefficient morphisms

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md and its proof
(blueprint: det-lem-coefficient-finite-descent-hom).

All coefficient maps, adjunctions, and tensor comparisons below are the recorded
constructions. The Hom-colimit assertion is expressed by surjectivity on finite
representatives and equality after passing to a common finite field.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vA uA vB uB vC uC

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Transport a shifted morphism by scalar extension and the given canonical tensor
comparison. Source: blueprint coefficient-finite-descent-hom, proof paragraph (1),
tensor transitivity (blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentDerivedHomMap
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {T : A ⥤ B} (S : B ⥤ V) [S.CommShift ℤ] {W : A ⥤ V}
    (α : T ⋙ S ≅ W) (C D : A) (r : ℤ)
    (f : T.obj C ⟶ (T.obj D)⟦r⟧) : W.obj C ⟶ (W.obj D)⟦r⟧ :=
  α.inv.app C ≫ S.map f ≫ (S.commShiftIso r).hom.app (T.obj D) ≫
    (α.hom.app D)⟦r⟧'

/-- The coefficient-inclusion map on restricted extensions is the adjunction mate
of tensor transitivity and the old counit. This fixes the actual transition map.
Source: blueprint coefficient-finite-descent-hom, proof paragraph (1), unit and counit
formulas (blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentDerivedRestrictionMap
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {T : A ⥤ B} {U : B ⥤ A} (a : T ⊣ U)
    (S : B ⥤ V) [S.CommShift ℤ]
    {W : A ⥤ V} {Z : V ⥤ A} (b : W ⊣ Z) (α : T ⋙ S ≅ W)
    (D : A) (r : ℤ) : U.obj ((T.obj D)⟦r⟧) ⟶ Z.obj ((W.obj D)⟦r⟧) :=
  b.homEquiv _ _
    (α.inv.app _ ≫ S.map (a.counit.app ((T.obj D)⟦r⟧)) ≫
      (S.commShiftIso r).hom.app (T.obj D) ≫ (α.hom.app D)⟦r⟧')

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The specified finite-field extension map on shifted derived Hom.
Source: blueprint coefficient-finite-descent-hom, clauses (1) and (3)
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentHomTransition
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (k : F ≤ G)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ)
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    (derivedExtendScalarsSubfield X ℓ (h.trans k)).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ (h.trans k)).obj D)⟦r⟧ :=
  coefficientDescentDerivedHomMap (derivedExtendScalarsSubfield X ℓ k)
    (condensedCoefficientCompIso X ℓ h k) C D r f

/-- The specified extension-to-algebraic-closure map on shifted derived Hom.
Source: blueprint coefficient-finite-descent-hom, clauses (1) and (3)
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentHomToAlgCl
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ)
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C ⟶
      ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D)⟦r⟧ :=
  coefficientDescentDerivedHomMap (derivedExtendScalarsToPadicAlgCl X ℓ F)
    (derivedExtendScalarsCompIso X ℓ h) C D r f

/-- The finite-stage transition on restricted shifted derived extensions.
Source: blueprint coefficient-finite-descent-hom, clause (1), transition identity
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentRestrictionTransition
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (k : F ≤ G)
    (D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) :
    (finiteCoefficientDerivedRestriction X ℓ h).obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) ⟶
      (finiteCoefficientDerivedRestriction X ℓ (h.trans k)).obj
        (((derivedExtendScalarsSubfield X ℓ (h.trans k)).obj D)⟦r⟧) :=
  coefficientDescentDerivedRestrictionMap (finiteCoefficientDerivedAdjunction X ℓ h)
    (derivedExtendScalarsSubfield X ℓ k)
    (finiteCoefficientDerivedAdjunction X ℓ (h.trans k))
    (condensedCoefficientCompIso X ℓ h k) D r

/-- The algebraic-closure transition on restricted shifted derived extensions.
Source: blueprint coefficient-finite-descent-hom, clause (1), transition identity
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentRestrictionToAlgCl
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) :
    (finiteCoefficientDerivedRestriction X ℓ h).obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) ⟶
      (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
        (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D)⟦r⟧) :=
  coefficientDescentDerivedRestrictionMap (finiteCoefficientDerivedAdjunction X ℓ h)
    (derivedExtendScalarsToPadicAlgCl X ℓ F)
    (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
    (derivedExtendScalarsCompIso X ℓ h) D r

/-- The poset of finite fields containing E, lifted to the coefficient universe.
Source: blueprint coefficient-finite-descent-hom, proof paragraph (2)
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentFields (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

/-- Derived coefficient Hom adjunction, its coefficient naturality, the uniformly
bounded-below coefficient tensor colimit, and bijectivity on finite representatives.
Source: blueprint main-20261015, sk-thm-sfb-qlbar-two-colimit,
sk-lem-coefficient-finite-descent-hom.md, clauses (1)--(3)
(blueprint: det-lem-coefficient-finite-descent-hom).

Proof, following the ten DAG steps:
1. On a small skeleton of the pro-etale site, sheaf tensor is closed and preserves
colimits (sk-def-sfb-sheaf-tensor). The extension/restriction adjunction of
sk-def-sfb-change-of-scalars has exact restriction; lem-sfb-subfield-flat and
lem-sfb-qlbar-flat make extension exact as well.
2. Lift this adjunction to complexes by lem-weil-pbc-termwise-adjunction-homotopy.
Exact functors preserve quasi-isomorphisms by
lem-weil-pbc-exact-functor-derived-factorization. Apply lem-sfb-adjunction-localization:
the Hom map is restriction followed by the unit, and its inverse is extension
followed by the counit. Restriction commutes with shifts.
3. Identify the recorded left-derived extensions with these termwise extensions
by the exact-functor clause of sk-def-sfb-derived-categories.
4. Tensor multiplication and insertion of 1 give inverse transitivity maps.
Their unit compatibility and lem-weil-pbc-conjugate-iso-unit-equation identify
them with def-sfb-derived-extend-comp-iso and the recorded finite comparison.
5. The inclusion map sends the old unit to the new one. Counit naturality gives
the two displayed Hom-naturality identities, also for the algebraic closure.
6. The finite fields containing E form a nonempty directed poset, by finite
composita (det-def-sfb-qlbar-condensed-subextensions). The ring cocone of
sk-prop-sfb-qlbar-colimit-x remains colimiting on this tail: extend a cocone on
the tail to every finite H via EH. All legs remain the actual inclusions.
7. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence and
lem-sfb-directed-ring-sheaf-module-colimit to identify this same cocone as a
colimit of E-module sheaves.
8. Tensor with each term of the representative preserves this colimit, by
lem-weil-pbc-independent-sheaf-tensor-colimits; its balancing maps are those of
def-sfb-modobj-relative-tensor. The comparisons commute with differentials.
Additivity preserves every zero term below the given lower bound.
9. The standing scheme is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
Bounded constructibility and lem-sfb-bounded-representative give a bounded
representative of D.
10. Apply sk-lem-constructible-ext-continuity with source C, the coefficient
diagram of steps 6--8, and degree r. The identities of step 5 identify its
comparison with coefficient extension on Hom. A filtered-colimit element is a
finite representative, and equality is equality at a common later stage. Thus
the last two clauses say exactly that this canonical comparison is bijective.
-/
theorem coefficient_finite_descent_hom
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      Function.Bijective (finiteCoefficientDerivedHomEquiv X ℓ h C.obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧))) ∧
    Function.Bijective (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj
      (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧)) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : F ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedHomEquiv X ℓ (h.trans j) C.obj _
          (coefficientDescentHomTransition X ℓ h j C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionTransition X ℓ h j D.obj r) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _
          (coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionToAlgCl X ℓ h D.obj r) ∧
    (∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ℤ)
      (_e : DerivedCategory.Q.obj K ≅ D.obj) (a b : ℤ)
      (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
      IsFiltered (AsSmall.{u + 1} (Under E)) ∧
        Nonempty (IsColimit (coefficientComplexCocone X ℓ K (coefficientDescentFields ℓ E)
          (fun i => leOfHom (ULift.down i).hom) (fun i => leOfHom (ULift.down i).hom))) ∧
        ∀ (i : AsSmall.{u + 1} (Under E)) (n : ℤ), n < a →
          IsZero (((coefficientComplexDiagram X ℓ K (coefficientDescentFields ℓ E)
            (fun j => leOfHom (ULift.down j).hom)
            (fun j => leOfHom (ULift.down j).hom)).obj i).X n)) ∧
    (∀ f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (g : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
        coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r g = f) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧)
      (g : (derivedExtendScalarsSubfield X ℓ j).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ j).obj D.obj)⟦r⟧),
      coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f =
        coefficientDescentHomToAlgCl X ℓ j C.obj D.obj r g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hF : F ≤ H) (hG : G ≤ H),
        coefficientDescentHomTransition X ℓ h hF C.obj D.obj r f =
          coefficientDescentHomTransition X ℓ j hG C.obj D.obj r g) := by
  sorry

end AlgebraicGeometry.ProEtale
