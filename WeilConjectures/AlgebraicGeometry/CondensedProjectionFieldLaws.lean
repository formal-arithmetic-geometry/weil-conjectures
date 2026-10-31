/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.AlgebraicGeometry.CondensedScalarProjectionCoherence
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension

/-! # Projection laws at the actual condensed field coefficients

Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).

The finite-extension and algebraic-closure assertions use the ordinary full bounded
constructible subcategories. The auxiliary definitions only restrict the existing
proper/open projection and transport the existing normalized compositors to arbitrary
compactifications. No projection law is assumed by these definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.FieldProjectionLaws

namespace Finite

variable (ell : ℕ) [Fact ell.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
variable (E : PadicAlgCl.FiniteIntermediateField ell)
variable {X Y Z W : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]

/-- Restriction of the actual proper-counit/open projection to the full subcategory.
Source: latest blueprint thm-sf-pf-field, canonical map, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws). -/
def projection (f : X ⟶ Y) (c : Compactification f.left)
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (L : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y.left)) :
    (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c).obj K ⊗ L ⟶
      (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c).obj
        (K ⊗ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell f).obj L) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification
      (Profinite.continuousMapRingObj E) c K.obj L.obj)

/-- The canonical support compositor, transported to any three compactifications.
Source: latest blueprint thm-sf-pf-field, canonical map, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws). -/
def composition (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.left) (d : Compactification g.left)
    (e : Compactification (f.left ≫ g.left)) :
    ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c ⋙
      ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E d ≅
      ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification
        ell E (f := f ≫ g) e :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso ell E c
        (compactificationOverField f)) _ ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekOfCompactificationIso ell E d
        (compactificationOverField g)) ≪≫
    (boundedConstructibleLowerShriekComp ell E f g).symm ≪≫
    boundedConstructibleLowerShriekOfCompactificationIso ell E
      (f := f ≫ g) (compactificationOverField (f ≫ g)) e

/-- Comparison with the identity-open compactification of a proper morphism.
Source: latest blueprint thm-sf-pf-field, canonical map, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws). -/
def properComparison (f : X ⟶ Y) [IsProper f.left]
    (c : Compactification f.left) :
    ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c ≅
      ContinuousMapRingObj.boundedConstructibleLowerStar ell E f :=
  boundedConstructibleLowerShriekOfCompactificationIso ell E c (.ofIsProper f.left) ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso
        (Profinite.continuousMapRingObj E) ell f) _ ≪≫
    Functor.leftUnitor _

end Finite

namespace Finite

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (_hell : ell ≠ D.p)
  [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
variable (E : PadicAlgCl.FiniteIntermediateField ell)
variable {X Y Z W : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
include _hell

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- Invertibility, two-input naturality, compactification independence, and proper coincidence.
Every second input is bounded constructible, with no Tor-amplitude hypothesis.
Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: the field projection theorem gives invertibility for the chosen compactification
on all bounded constructible inputs. Its canonical proper/open map is the one restricted
here. Naturality of each factor gives two-variable naturality. The comparison-equations
lemma identifies the maps under common dense refinements, so invertibility and naturality
pass to every compactification. Its composition, associativity and proper equations use
the same normalized support and pullback compositors. The field theorem identifies the
localization and scalar-extension maps; scalar comparison is independent of the chosen
compactification and hence transports these identities as well. -/
theorem laws (f : X ⟶ Y) (c : Compactification f.left)
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (L : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y.left)) :
    IsIso (projection ell E f c K L) ∧
    (∀ (K' : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
      (L' : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y.left))
      (a : K ⟶ K') (b : L ⟶ L'),
      ((ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c).map a
        ⊗ₘ b) ≫ projection ell E f c K' L' =
        projection ell E f c K L ≫
          (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c).map
            (a ⊗ₘ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell f).map b)) ∧
    (∀ d : Compactification f.left,
      projection ell E f c K L ≫
          (boundedConstructibleLowerShriekOfCompactificationIso ell E c d).hom.app
            (K ⊗ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell f).obj L) =
        ((boundedConstructibleLowerShriekOfCompactificationIso ell E c d).hom.app K ▷ L) ≫
          projection ell E f d K L) ∧
    (∀ [IsProper f.left],
      projection ell E f c K L ≫
          (properComparison ell E f c).hom.app
            (K ⊗ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell f).obj L) =
        ((properComparison ell E f c).hom.app K ▷ L) ≫
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction
            ell E f).projectionMorphism K L) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- Binary support/pullback composition for arbitrary compactifications.
Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: the field projection theorem gives invertibility for the chosen compactification
on all bounded constructible inputs. Its canonical proper/open map is the one restricted
here. Naturality of each factor gives two-variable naturality. The comparison-equations
lemma identifies the maps under common dense refinements, so invertibility and naturality
pass to every compactification. Its composition, associativity and proper equations use
the same normalized support and pullback compositors. The field theorem identifies the
localization and scalar-extension maps; scalar comparison is independent of the chosen
compactification and hence transports these identities as well. -/
theorem composition_law (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.left) (d : Compactification g.left)
    (e : Compactification (f.left ≫ g.left))
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (L : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z.left)) :
    ((composition ell E f g c d e).hom.app K ▷ L) ≫
        projection ell E (f ≫ g) e K L =
      projection ell E g d
          ((ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification
            ell E c).obj K) L ≫
        (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E d).map
          (projection ell E f c K
            ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell g).obj L)) ≫
        (composition ell E f g c d e).hom.app
          (K ⊗ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell f).obj
            ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ell g).obj L)) ≫
        (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification
        ell E (f := f ≫ g) e).map
          (K ◁ (boundedConstructibleUpperStarComp
            (Profinite.continuousMapRingObj E) ell f g).inv.app L) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- The associativity pentagon of the canonical compact-support compositors.
Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: the field projection theorem gives invertibility for the chosen compactification
on all bounded constructible inputs. Its canonical proper/open map is the one restricted
here. Naturality of each factor gives two-variable naturality. The comparison-equations
lemma identifies the maps under common dense refinements, so invertibility and naturality
pass to every compactification. Its composition, associativity and proper equations use
the same normalized support and pullback compositors. The field theorem identifies the
localization and scalar-extension maps; scalar comparison is independent of the chosen
compactification and hence transports these identities as well. -/
theorem pentagon (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : Compactification f.left) (d : Compactification g.left)
    (e : Compactification h.left)
    (cd : Compactification (f.left ≫ g.left))
    (de : Compactification (g.left ≫ h.left))
    (cde : Compactification ((f.left ≫ g.left) ≫ h.left))
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left)) :
    (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification
        ell E (f := h) e).map
        ((composition ell E f g c d cd).hom.app K) ≫
        (composition ell E (f ≫ g) h cd e cde).hom.app K =
      (composition ell E g h d e de).hom.app
          ((ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ell E c).obj K) ≫
        (composition ell E f (g ≫ h) c de
          (cde.copy (Category.assoc _ _ _).symm)).hom.app K := by
  sorry

end Finite

namespace Closure

variable (ell : ℕ) [Fact ell.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
variable {X Y Z W : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]

/-- Restriction of the actual proper-counit/open projection to the full subcategory.
Source: latest blueprint thm-sf-pf-field, canonical map, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws). -/
def projection (f : X ⟶ Y) (c : Compactification f.left)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (L : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) Y.left)) :
    (boundedConstructibleLowerShriekOfCompactification ell c).obj K ⊗ L ⟶
      (boundedConstructibleLowerShriekOfCompactification ell c).obj
        (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell f).obj L) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification
      (Profinite.padicAlgClRingObj ell) c K.obj L.obj)

/-- The canonical support compositor, transported to any three compactifications.
Source: latest blueprint thm-sf-pf-field, canonical map, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws). -/
def composition (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.left) (d : Compactification g.left)
    (e : Compactification (f.left ≫ g.left)) :
    boundedConstructibleLowerShriekOfCompactification ell c ⋙
      boundedConstructibleLowerShriekOfCompactification ell d ≅
      boundedConstructibleLowerShriekOfCompactification ell (f := f ≫ g) e :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ell c
        (compactificationOverField f)) _ ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ell d
        (compactificationOverField g)) ≪≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ell f g).symm ≪≫
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ell
      (f := f ≫ g) (compactificationOverField (f ≫ g)) e

/-- Comparison with the identity-open compactification of a proper morphism.
Source: latest blueprint thm-sf-pf-field, canonical map, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws). -/
def properComparison (f : X ⟶ Y) [IsProper f.left]
    (c : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification ell c ≅ boundedConstructibleLowerStar ell f :=
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ell c (.ofIsProper f.left) ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso
        (Profinite.padicAlgClRingObj ell) ell f) _ ≪≫
    Functor.leftUnitor _

end Closure

namespace Closure

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (_hell : ell ≠ D.p)
  [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
variable {X Y Z W : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
include _hell

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- Invertibility, two-input naturality, compactification independence, and proper coincidence.
Every second input is bounded constructible, with no Tor-amplitude hypothesis.
Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: the field projection theorem gives invertibility for the chosen compactification
on all bounded constructible inputs. Its canonical proper/open map is the one restricted
here. Naturality of each factor gives two-variable naturality. The comparison-equations
lemma identifies the maps under common dense refinements, so invertibility and naturality
pass to every compactification. Its composition, associativity and proper equations use
the same normalized support and pullback compositors. The field theorem identifies the
localization and scalar-extension maps; scalar comparison is independent of the chosen
compactification and hence transports these identities as well. -/
theorem laws (f : X ⟶ Y) (c : Compactification f.left)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (L : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) Y.left)) :
    IsIso (projection ell f c K L) ∧
    (∀ (K' : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
      (L' : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) Y.left))
      (a : K ⟶ K') (b : L ⟶ L'),
      ((boundedConstructibleLowerShriekOfCompactification ell c).map a ⊗ₘ b) ≫
        projection ell f c K' L' =
        projection ell f c K L ≫
          (boundedConstructibleLowerShriekOfCompactification ell c).map
            (a ⊗ₘ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell f).map b)) ∧
    (∀ d : Compactification f.left,
      projection ell f c K L ≫
          (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ell c d).hom.app
            (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell f).obj L) =
        ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ell c d).hom.app K ▷ L) ≫
          projection ell f d K L) ∧
    (∀ [IsProper f.left],
      projection ell f c K L ≫
          (properComparison ell f c).hom.app
            (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell f).obj L) =
        ((properComparison ell f c).hom.app K ▷ L) ≫
          (boundedConstructibleUpperStarLowerStarAdjunction ell f).projectionMorphism K L) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- Binary support/pullback composition for arbitrary compactifications.
Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: the field projection theorem gives invertibility for the chosen compactification
on all bounded constructible inputs. Its canonical proper/open map is the one restricted
here. Naturality of each factor gives two-variable naturality. The comparison-equations
lemma identifies the maps under common dense refinements, so invertibility and naturality
pass to every compactification. Its composition, associativity and proper equations use
the same normalized support and pullback compositors. The field theorem identifies the
localization and scalar-extension maps; scalar comparison is independent of the chosen
compactification and hence transports these identities as well. -/
theorem composition_law (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.left) (d : Compactification g.left)
    (e : Compactification (f.left ≫ g.left))
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (L : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) Z.left)) :
    ((composition ell f g c d e).hom.app K ▷ L) ≫
        projection ell (f ≫ g) e K L =
      projection ell g d ((boundedConstructibleLowerShriekOfCompactification ell c).obj K) L ≫
        (boundedConstructibleLowerShriekOfCompactification ell d).map
          (projection ell f c K
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell g).obj L)) ≫
        (composition ell f g c d e).hom.app
          (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell f).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell g).obj L)) ≫
        (boundedConstructibleLowerShriekOfCompactification ell (f := f ≫ g) e).map
          (K ◁ (boundedConstructibleUpperStarComp
            (Profinite.padicAlgClRingObj ell) ell f g).inv.app L) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- The associativity pentagon of the canonical compact-support compositors.
Source: latest blueprint fix-prop-projection-formula.proof, field transport and final
coherence sentences; thm-sf-pf-field and prop-sf-pf-coherence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: the field projection theorem gives invertibility for the chosen compactification
on all bounded constructible inputs. Its canonical proper/open map is the one restricted
here. Naturality of each factor gives two-variable naturality. The comparison-equations
lemma identifies the maps under common dense refinements, so invertibility and naturality
pass to every compactification. Its composition, associativity and proper equations use
the same normalized support and pullback compositors. The field theorem identifies the
localization and scalar-extension maps; scalar comparison is independent of the chosen
compactification and hence transports these identities as well. -/
theorem pentagon (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : Compactification f.left) (d : Compactification g.left)
    (e : Compactification h.left)
    (cd : Compactification (f.left ≫ g.left))
    (de : Compactification (g.left ≫ h.left))
    (cde : Compactification ((f.left ≫ g.left) ≫ h.left))
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)) :
    (boundedConstructibleLowerShriekOfCompactification ell (f := h) e).map
        ((composition ell f g c d cd).hom.app K) ≫
        (composition ell (f ≫ g) h cd e cde).hom.app K =
      (composition ell g h d e de).hom.app
          ((boundedConstructibleLowerShriekOfCompactification ell c).obj K) ≫
        (composition ell f (g ≫ h) c de
          (cde.copy (Category.assoc _ _ _).symm)).hom.app K := by
  sorry

end Closure


open AlgebraicGeometry.ProEtale.QuotientChange

section ScalarCompatibility


variable (D₀ : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (_hell : ell ≠ D₀.p)
  [Fact (ringChar D₀.k).Prime] [Fact (ringChar D₀.k ≠ ell)]
  {X Y : Over (Spec (.of D₀.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
include _hell

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- The projection square for the specified localization coefficient map.
The equation is in the ordinary ambient derived category and its inputs are the
full bounded constructible subcategory. A supplied pullback comparison is required
to have the universal K-flat normalization, which uniquely fixes it.
Source: latest blueprint thm-sf-pf-field, scalar compatibility, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: expand the proper counit mate, the inverse open projection and the pullback
compositor. The normalized scalar tensor square and preservation of adjunction mates
intertwine the proper factors. The open adjunction identifies the open square.
Naturality pastes the factors. Independence of compactification transports the
chosen-compactification identity to every c. -/
theorem localization (E : PadicAlgCl.FiniteIntermediateField ell)
    (a : latticeIntegralRing ell E ⟶ scalarSixFieldRing ell E)
    (_ha : a = scalarSixIntegralToField ell E)
    (f : X ⟶ Y) (c : Compactification f.left)
    (b : QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
      (Λ' := (scalarSixFieldRing ell E).X)
      a.hom.hom Y.left ⋙ QuotientChange.L (scalarSixFieldRing ell E).X f.left ≅
      QuotientChange.L (latticeIntegralRing ell E).X f.left ⋙
        QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
        (Λ' := (scalarSixFieldRing ell E).X)
        a.hom.hom X.left)
    (_hb : PullNormalized (Λ := (latticeIntegralRing ell E).X)
      (Λ' := (scalarSixFieldRing ell E).X)
      a.hom.hom f.left b)
    (K : BoundedConstructible (condensedRingObj (latticeIntegralRing ell E).X X.left))
    (L : BoundedConstructible (condensedRingObj (latticeIntegralRing ell E).X Y.left)) :
    scalarProjectionTensor (Λ := (latticeIntegralRing ell E).X)
      (Λ' := (scalarSixFieldRing ell E).X)
      a.hom.hom Y.left
        ((rightDerivedLowerShriekOfCompactification (latticeIntegralRing ell E).X c).obj K.obj)
        L.obj ≫
        (actualCompactScalarComparison a c K.obj ⊗ₘ
          𝟙 ((QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
            (Λ' := (scalarSixFieldRing ell E).X)
            a.hom.hom Y.left).obj L.obj)) ≫
        compactScalarProjection c ((QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
          (Λ' := (scalarSixFieldRing ell E).X)
          a.hom.hom X.left).obj K.obj)
          ((QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
            (Λ' := (scalarSixFieldRing ell E).X)
            a.hom.hom Y.left).obj L.obj) =
      (QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
        (Λ' := (scalarSixFieldRing ell E).X)
        a.hom.hom Y.left).map (compactScalarProjection c K.obj L.obj) ≫
        actualCompactScalarComparison a c
          (K.obj ⊗ (QuotientChange.L (latticeIntegralRing ell E).X f.left).obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell E).X c).map
          (scalarProjectionTensor (Λ := (latticeIntegralRing ell E).X)
            (Λ' := (scalarSixFieldRing ell E).X)
            a.hom.hom X.left K.obj
            ((QuotientChange.L (latticeIntegralRing ell E).X f.left).obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell E).X c).map
          (𝟙 ((QuotientChange.D (Λ := (latticeIntegralRing ell E).X)
            (Λ' := (scalarSixFieldRing ell E).X)
            a.hom.hom X.left).obj K.obj) ⊗ₘ b.inv.app L.obj) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- The projection square for the specified fieldExtension coefficient map.
The equation is in the ordinary ambient derived category and its inputs are the
full bounded constructible subcategory. A supplied pullback comparison is required
to have the universal K-flat normalization, which uniquely fixes it.
Source: latest blueprint thm-sf-pf-field, scalar compatibility, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: expand the proper counit mate, the inverse open projection and the pullback
compositor. The normalized scalar tensor square and preservation of adjunction mates
intertwine the proper factors. The open adjunction identifies the open square.
Naturality pastes the factors. Independence of compactification transports the
chosen-compactification identity to every c. -/
theorem fieldExtension (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
    (a : scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell F)
    (_ha : a = ⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩)
    (f : X ⟶ Y) (c : Compactification f.left)
    (b : QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
      (Λ' := (scalarSixFieldRing ell F).X)
      a.hom.hom Y.left ⋙ QuotientChange.L (scalarSixFieldRing ell F).X f.left ≅
      QuotientChange.L (scalarSixFieldRing ell E).X f.left ⋙
        QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
        (Λ' := (scalarSixFieldRing ell F).X)
        a.hom.hom X.left)
    (_hb : PullNormalized (Λ := (scalarSixFieldRing ell E).X)
      (Λ' := (scalarSixFieldRing ell F).X)
      a.hom.hom f.left b)
    (K : BoundedConstructible (condensedRingObj (scalarSixFieldRing ell E).X X.left))
    (L : BoundedConstructible (condensedRingObj (scalarSixFieldRing ell E).X Y.left)) :
    scalarProjectionTensor (Λ := (scalarSixFieldRing ell E).X)
      (Λ' := (scalarSixFieldRing ell F).X)
      a.hom.hom Y.left
        ((rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell E).X c).obj K.obj)
        L.obj ≫
        (actualCompactScalarComparison a c K.obj ⊗ₘ
          𝟙 ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (scalarSixFieldRing ell F).X)
            a.hom.hom Y.left).obj L.obj)) ≫
        compactScalarProjection c ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
          (Λ' := (scalarSixFieldRing ell F).X)
          a.hom.hom X.left).obj K.obj)
          ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (scalarSixFieldRing ell F).X)
            a.hom.hom Y.left).obj L.obj) =
      (QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
        (Λ' := (scalarSixFieldRing ell F).X)
        a.hom.hom Y.left).map (compactScalarProjection c K.obj L.obj) ≫
        actualCompactScalarComparison a c
          (K.obj ⊗ (QuotientChange.L (scalarSixFieldRing ell E).X f.left).obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell F).X c).map
          (scalarProjectionTensor (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (scalarSixFieldRing ell F).X)
            a.hom.hom X.left K.obj
            ((QuotientChange.L (scalarSixFieldRing ell E).X f.left).obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell F).X c).map
          (𝟙 ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (scalarSixFieldRing ell F).X)
            a.hom.hom X.left).obj K.obj) ⊗ₘ b.inv.app L.obj) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- The projection square for the specified closureExtension coefficient map.
The equation is in the ordinary ambient derived category and its inputs are the
full bounded constructible subcategory. A supplied pullback comparison is required
to have the universal K-flat normalization, which uniquely fixes it.
Source: latest blueprint thm-sf-pf-field, scalar compatibility, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: expand the proper counit mate, the inverse open projection and the pullback
compositor. The normalized scalar tensor square and preservation of adjunction mates
intertwine the proper factors. The open adjunction identifies the open square.
Naturality pastes the factors. Independence of compactification transports the
chosen-compactification identity to every c. -/
theorem closureExtension (E : PadicAlgCl.FiniteIntermediateField ell)
    (a : scalarSixFieldRing ell E ⟶ latticeClosureRing ell)
    (_ha : a = ⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩)
    (f : X ⟶ Y) (c : Compactification f.left)
    (b : QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
      (Λ' := (latticeClosureRing ell).X)
      a.hom.hom Y.left ⋙ QuotientChange.L (latticeClosureRing ell).X f.left ≅
      QuotientChange.L (scalarSixFieldRing ell E).X f.left ⋙
        QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
        (Λ' := (latticeClosureRing ell).X)
        a.hom.hom X.left)
    (_hb : PullNormalized (Λ := (scalarSixFieldRing ell E).X)
      (Λ' := (latticeClosureRing ell).X)
      a.hom.hom f.left b)
    (K : BoundedConstructible (condensedRingObj (scalarSixFieldRing ell E).X X.left))
    (L : BoundedConstructible (condensedRingObj (scalarSixFieldRing ell E).X Y.left)) :
    scalarProjectionTensor (Λ := (scalarSixFieldRing ell E).X)
      (Λ' := (latticeClosureRing ell).X)
      a.hom.hom Y.left
        ((rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell E).X c).obj K.obj)
        L.obj ≫
        (actualCompactScalarComparison a c K.obj ⊗ₘ
          𝟙 ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (latticeClosureRing ell).X)
            a.hom.hom Y.left).obj L.obj)) ≫
        compactScalarProjection c ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
          (Λ' := (latticeClosureRing ell).X)
          a.hom.hom X.left).obj K.obj)
          ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (latticeClosureRing ell).X)
            a.hom.hom Y.left).obj L.obj) =
      (QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
        (Λ' := (latticeClosureRing ell).X)
        a.hom.hom Y.left).map (compactScalarProjection c K.obj L.obj) ≫
        actualCompactScalarComparison a c
          (K.obj ⊗ (QuotientChange.L (scalarSixFieldRing ell E).X f.left).obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (latticeClosureRing ell).X c).map
          (scalarProjectionTensor (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (latticeClosureRing ell).X)
            a.hom.hom X.left K.obj
            ((QuotientChange.L (scalarSixFieldRing ell E).X f.left).obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (latticeClosureRing ell).X c).map
          (𝟙 ((QuotientChange.D (Λ := (scalarSixFieldRing ell E).X)
            (Λ' := (latticeClosureRing ell).X)
            a.hom.hom X.left).obj K.obj) ⊗ₘ b.inv.app L.obj) := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- Successive scalar extensions give the same compact-support comparison under the
specified tensor-transitivity isomorphism. Together with the projection squares,
this identifies projection transport along a tower with transport along its composite.
Source: latest blueprint thm-sf-pf-field, last sentence, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: extend scalars on K-flat representatives. Both routes send c tensor (b tensor m)
to cb tensor m. The proper comparison is its adjunction mate and the open comparison
is fixed by restriction to the open. Uniqueness of these comparisons, followed by
naturality and derivation, proves the equation. The pointwise coefficient inclusions
compose, so enlarging a finite coefficient presentation gives the same map. -/
theorem fieldTower (E F G : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F) (i : F ≤ G)
    (a : scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell F)
    (_ha : a = ⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩)
    (b : scalarSixFieldRing ell F ⟶ scalarSixFieldRing ell G)
    (_hb : b = ⟨⟨Profinite.padicSubfieldRingObjMap ell i⟩⟩)
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : BoundedConstructible (condensedRingObj (scalarSixFieldRing ell E).X X.left)) :
    (scalarSixChange b Y.left).map ((scalarCompactSupportMap a c.i c.g).app K.obj) ≫
        (scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj K.obj) ≫
        (rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell G).X c).map
          ((scalarSixTower a b X.left).hom.app K.obj) =
      (scalarSixTower a b Y.left).hom.app
          ((rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell E).X c).obj K.obj) ≫
        (scalarCompactSupportMap (a ≫ b) c.i c.g).app K.obj := by
  sorry

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the displayed derived-functor coherence equation.
/-- Successive scalar extensions give the same compact-support comparison under the
specified tensor-transitivity isomorphism. Together with the projection squares,
this identifies projection transport along a tower with transport along its composite.
Source: latest blueprint thm-sf-pf-field, last sentence, and
fix-prop-projection-formula.proof, field transport sentence
(blueprint: lem-sf-projection-field-stage-laws).
Proof: extend scalars on K-flat representatives. Both routes send c tensor (b tensor m)
to cb tensor m. The proper comparison is its adjunction mate and the open comparison
is fixed by restriction to the open. Uniqueness of these comparisons, followed by
naturality and derivation, proves the equation. The pointwise coefficient inclusions
compose, so enlarging a finite coefficient presentation gives the same map. -/
theorem closureTower (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
    (a : scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell F)
    (_ha : a = ⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩)
    (b : scalarSixFieldRing ell F ⟶ latticeClosureRing ell)
    (_hb : b = ⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell F⟩⟩)
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : BoundedConstructible (condensedRingObj (scalarSixFieldRing ell E).X X.left)) :
    (scalarSixChange b Y.left).map ((scalarCompactSupportMap a c.i c.g).app K.obj) ≫
        (scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj K.obj) ≫
        (rightDerivedLowerShriekOfCompactification (latticeClosureRing ell).X c).map
          ((scalarSixTower a b X.left).hom.app K.obj) =
      (scalarSixTower a b Y.left).hom.app
          ((rightDerivedLowerShriekOfCompactification (scalarSixFieldRing ell E).X c).obj K.obj) ≫
        (scalarCompactSupportMap (a ≫ b) c.i c.g).app K.obj := by
  sorry

end ScalarCompatibility

end AlgebraicGeometry.ProEtale.CondensedRing.FieldProjectionLaws
