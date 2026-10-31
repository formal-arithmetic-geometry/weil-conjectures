/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleData
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# Compact-support projection formula over finite coefficient fields and their algebraic closure

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-pf-proetale/
thm-sf-pf-field.md and thm-sf-pf-field.proof.md (blueprint: thm-sf-pf-field).

The morphism is the existing proper projection mate, followed by the inverse canonical open
projection comparison and the pullback compositor. All operations are ordinary and uncompleted.
The auxiliary predicates only package the clauses of this theorem; no operation is redefined.
The coefficient algebraic closure is the finite-subextension-valued condensed ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The isomorphism and naturality clauses for the specified compact-support projection map.
Both endpoints lie in the full bounded constructible category; its morphisms are ambient
morphisms. Naturality includes arbitrary isomorphisms between finite-stage presentations.
Source: thm-sf-pf-field.md, isomorphism and naturality (blueprint: thm-sf-pf-field). -/
def FieldProjectionFormulaAssertions (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  (∀ (K : BoundedConstructible (condensedRingObj Λ.X X))
    (L : BoundedConstructible (condensedRingObj Λ.X Y)),
    boundedConstructible (condensedRingObj Λ.X Y)
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K.obj ⊗ L.obj) ∧
      boundedConstructible (condensedRingObj Λ.X Y)
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj
          (K.obj ⊗ (upperStar Λ.X f).leftDerivedFunctor.obj L.obj)) ∧
      IsIso (exceptionalProjectionMorphismOfCompactification Λ.X c K.obj L.obj)) ∧
  (∀ (K K' : BoundedConstructible (condensedRingObj Λ.X X))
    (L L' : BoundedConstructible (condensedRingObj Λ.X Y))
    (a : K ⟶ K') (b : L ⟶ L'),
    ((rightDerivedLowerShriekOfCompactification Λ.X c).map a.hom ⊗ₘ b.hom) ≫
        exceptionalProjectionMorphismOfCompactification Λ.X c K'.obj L'.obj =
      exceptionalProjectionMorphismOfCompactification Λ.X c K.obj L.obj ≫
        (rightDerivedLowerShriekOfCompactification Λ.X c).map
          (a.hom ⊗ₘ (upperStar Λ.X f).leftDerivedFunctor.map b.hom))

/-- Equality with scalar extension under the canonical operation comparisons. The two
boundary maps are invertible, so the equality identifies the maps, and their inverses.
Source: thm-sf-pf-field.md, localization and scalar extension
(blueprint: thm-sf-pf-field). -/
def FieldProjectionScalarAssertions {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : BoundedConstructible (condensedRingObj Λ.X X))
    (L : BoundedConstructible (condensedRingObj Λ.X Y)) : Prop :=
  IsIso (condensedProjectionScalarSource a c K.obj L.obj) ∧
    IsIso (condensedProjectionScalarTarget a c K.obj L.obj) ∧
    condensedProjectionScalarSource a c K.obj L.obj ≫
        exceptionalProjectionMorphismOfCompactification Λ'.X c
          ((scalarSixChange a X).obj K.obj) ((scalarSixChange a Y).obj L.obj) =
      (scalarSixChange a Y).map
          (exceptionalProjectionMorphismOfCompactification Λ.X c K.obj L.obj) ≫
        condensedProjectionScalarTarget a c K.obj L.obj

/-- The two endpoint identifications respect successive scalar extensions. These are
explicit equations with the canonical scalar associator, rather than choices of comparisons.
Combined with the scalar square, they identify its direct and pasted versions.
Source: thm-sf-pf-field.md, successive field extensions
(blueprint: thm-sf-pf-field). -/
def FieldProjectionTowerAssertions {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : BoundedConstructible (condensedRingObj Λ₀.X X))
    (L : BoundedConstructible (condensedRingObj Λ₀.X Y)) : Prop :=
  ((scalarSixTower a b Y).hom.app
          ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K.obj ⊗ L.obj) ≫
        condensedProjectionScalarSource (a ≫ b) c K.obj L.obj =
      (scalarSixChange b Y).map (condensedProjectionScalarSource a c K.obj L.obj) ≫
        condensedProjectionScalarSource b c
          ((scalarSixChange a X).obj K.obj) ((scalarSixChange a Y).obj L.obj) ≫
        ((rightDerivedLowerShriekOfCompactification Λ₂.X c).map
              ((scalarSixTower a b X).hom.app K.obj) ▷
            (scalarSixChange b Y).obj ((scalarSixChange a Y).obj L.obj)) ≫
        ((rightDerivedLowerShriekOfCompactification Λ₂.X c).obj
              ((scalarSixChange (a ≫ b) X).obj K.obj) ◁
            (scalarSixTower a b Y).hom.app L.obj)) ∧
  ((scalarSixTower a b Y).hom.app
          ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj
            (K.obj ⊗ (upperStar Λ₀.X f).leftDerivedFunctor.obj L.obj)) ≫
        condensedProjectionScalarTarget (a ≫ b) c K.obj L.obj =
      (scalarSixChange b Y).map (condensedProjectionScalarTarget a c K.obj L.obj) ≫
        condensedProjectionScalarTarget b c
          ((scalarSixChange a X).obj K.obj) ((scalarSixChange a Y).obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification Λ₂.X c).map
          (((scalarSixTower a b X).hom.app K.obj ▷
              (upperStar Λ₂.X f).leftDerivedFunctor.obj
                ((scalarSixChange b Y).obj ((scalarSixChange a Y).obj L.obj))) ≫
            ((scalarSixChange (a ≫ b) X).obj K.obj ◁
              (upperStar Λ₂.X f).leftDerivedFunctor.map
                ((scalarSixTower a b Y).hom.app L.obj))))

/-- The compact-support projection formula over `E` and the finite-subextension-valued
condensed algebraic closure, with localization, scalar extension and presentation coherence.

Source: thm-sf-pf-field.md and thm-sf-pf-field.proof.md, with the explicit standing setting
of sk-def-sfb-dc-setting (blueprint: thm-sf-pf-field).

Proof, following the node's eight steps:
1. Choose c = compactificationOverField f. Pullback, tensor, open extension and proper
   pushforward preserve bounded constructible objects. The proper mate, inverse open
   comparison and pullback compositor define the displayed natural map. Fullness tests
   invertibility in the ambient category.
2. On integral inputs the ordinary integral proper projection theorem inverts the first
   factor; the canonical open tensor theorem inverts the second factor.
3. Localization is O_E to E. Proper scalar comparison on bounded-below inputs and the
   open, tensor and pullback comparisons give the invertible endpoint boundaries.
   Bounded constructible inputs are bounded below and have finite Tor amplitude here.
4. The proper counit mate equation and the balanced K-flat tensor normalization give
   the proper projection square. Open adjunct normalization gives the open square.
   Paste these squares to obtain the displayed scalar equality and transport inverses.
5. The proper projection map respects triangles and shifts in each variable. Exact open
   extension and its tensor comparison preserve those equations. Two-out-of-three makes
   the invertibility locus closed under cones and shifts in each variable.
6. Integral generation reduces first L and then K to localized integral generators.
   Steps 2--4 prove invertibility for those generators, hence for every pair over E.
7. Descend both algebraic-closure inputs to finite fields and then their compositum.
   The scalar square and naturality transport the E result to the given inputs.
8. The scalar associator and the proper, open, tensor and pullback cocycles give both
   boundary equations. Pasting the scalar squares therefore agrees with the composite
   square. Hom descent compares any two presentations at a further finite field;
   naturality at the presentation isomorphisms proves independence. Inverse uniqueness
   gives the same independence for inverses. This includes localization compatibility.
-/
theorem compactSupportProjectionFormulaField
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    (∀ E : PadicAlgCl.FiniteIntermediateField ell,
      FieldProjectionFormulaAssertions ⟨Profinite.continuousMapRingObj E.1⟩
        (compactificationOverField f)) ∧
    FieldProjectionFormulaAssertions ⟨Profinite.padicAlgClRingObj ell⟩
      (compactificationOverField f) ∧
    (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ'),
      ((∃ E : PadicAlgCl.FiniteIntermediateField ell,
          Λ = ⟨Profinite.padicIntegersRingObj ell E.1⟩) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ell,
          Λ = ⟨Profinite.continuousMapRingObj E.1⟩)) →
      ((∃ F : PadicAlgCl.FiniteIntermediateField ell,
          Λ' = ⟨Profinite.continuousMapRingObj F.1⟩) ∨
        Λ' = ⟨Profinite.padicAlgClRingObj ell⟩) →
      ListedCoefficientMap ell a →
      ∀ (K : BoundedConstructible (condensedRingObj Λ.X X.left))
        (L : BoundedConstructible (condensedRingObj Λ.X Y.left)),
        FieldProjectionScalarAssertions a (compactificationOverField f) K L) ∧
    (∀ {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}} (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂),
      ((∃ E : PadicAlgCl.FiniteIntermediateField ell,
          Λ₀ = ⟨Profinite.padicIntegersRingObj ell E.1⟩) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ell,
          Λ₀ = ⟨Profinite.continuousMapRingObj E.1⟩)) →
      (∃ F : PadicAlgCl.FiniteIntermediateField ell,
        Λ₁ = ⟨Profinite.continuousMapRingObj F.1⟩) →
      ((∃ G : PadicAlgCl.FiniteIntermediateField ell,
          Λ₂ = ⟨Profinite.continuousMapRingObj G.1⟩) ∨
        Λ₂ = ⟨Profinite.padicAlgClRingObj ell⟩) →
      ListedCoefficientMap ell a → ListedCoefficientMap ell b →
      ∀ (K : BoundedConstructible (condensedRingObj Λ₀.X X.left))
        (L : BoundedConstructible (condensedRingObj Λ₀.X Y.left)),
        FieldProjectionTowerAssertions a b (compactificationOverField f) K L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
