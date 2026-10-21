/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.ProEtaleConstantModuleEncoding
import Sheaf.Paper.CompletionTriangleComparison
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Triangle closure of the complete integral residue class

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md, paragraph (1).
(blueprint: lem-sfb-integral-residue-class-triangle-closure).

The ambient category is unbounded and uses the continuous condensed integral ring.
The first reduction retains its residue scalar action. Its finite-discrete encoding
is normalized on constant scalars; the ordinary origin predicate is the recorded one.

## Main definitions and statement

* `integralResidueEtaleOrigin`: bounded constructible etale origin of the first reduction.
* `integralResidueClass`: the predicate P in the source node.
* `integralResidueClass_triangle_closure`: zero, isomorphisms, shifts, and two out of three.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- Bounded constructible etale origin of the actual residue-module reduction.
The normalized encoding uses the existing section-action and constant-scalar restriction
functors. Its existence is a property, not a choice of new coefficient data. Realization
then enters the ordinary finite coefficient category of the recorded origin predicate.
Source: blueprint paragraph (1), exact reduction and finite etale origin
(blueprint: lem-sfb-integral-residue-class-triangle-closure). -/
def integralResidueEtaleOrigin (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X)) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 (Nat.le_refl 1)
  ∃ e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E 1) X,
    @isBoundedConstructibleFiniteCoefficient X
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) _ _ ⊥
      (discreteTopology_bot _)
      ((@finiteCoefficientRealization X
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) _ _ ⊥
        (discreteTopology_bot _)).mapDerivedCategory.obj
          (e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E X 0).obj K)))

/-- P(K) means derived completeness and bounded constructible etale origin of K modulo pi.
The pi used here is the recorded chosen uniformizer of the finite extension E/Q_l.
Source: blueprint paragraph (1), before the integral-model comparison
(blueprint: lem-sfb-integral-residue-class-triangle-closure). -/
def integralResidueClass (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) :=
  fun K ↦ IsDerivedComplete l E X K ∧ integralResidueEtaleOrigin l E X K

/-- The complete integral residue class contains zero and is stable under isomorphisms,
all integer shifts, and any two vertices of an ambient distinguished triangle.
In particular, if its first and third vertices belong, the middle vertex is complete
and its reduction has bounded constructible etale origin. No geometric hypothesis on X
or invertibility assumption on l is imposed.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md, paragraph (1)
(blueprint: lem-sfb-integral-residue-class-triangle-closure).

Proof (the node's seven steps):
1. lem-pe-completion-triangle-comparison supplies the additive completion functor and
its canonical unit. Completeness is invertibility of that unit, hence holds at zero,
is invariant under isomorphisms by naturality, and is invariant under shifts by its
invertible shift comparison.
2. Apply lem-sf-triangle-morphism-iso to its morphism of distinguished triangles.
Invertibility of two unit components implies invertibility of the third.
3. lem-pur-derived-change-of-rings makes residue scalar extension exact, with its
residue-module structure. It preserves zero, isomorphisms, shifts and triangles.
lem-sf-module-object-ordinary-coefficient-equivalence identifies these finite discrete
coefficients with ordinary coefficient sheaves. Constant functions identify the
coefficient sheaf of def-weil-pbc-proetale-modules by sheafification.
4. lem-weil-pbc-proetale-constant-module-encoding identifies the ordinary and fixed-scalar
module conventions. lem-sf-exact-functor-derived-triangulated and
lem-weil-pbc-exact-functor-complex-cohomology transport the exact equivalence termwise,
without changing scalar-linear maps, bounds or global finite stratifications.
5. lem-weil-pbc-fixed-module-constructible-origin and
lem-weil-pbc-fixed-module-bounded-constructible-origin identify bounded constructible
etale origin with bounded globally constructible residue cohomology.
6. lem-weil-proetale-dbc-triangulated gives zero, isomorphism, shift and extension
closure of that residue condition. Rotate a distinguished triangle once or twice
using def-weil-triangulated-category to obtain its other two closure implications.
7. Combine completeness and residue-origin closure, then unpack the middle vertex.
The argument uses neither boundedness of K nor any finiteness assumption on X. -/
theorem integralResidueClass_triangle_closure (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    integralResidueClass l E X (0 : DerivedCategory (AdicCompletion.Modules l E X)) ∧
    (∀ (K L : DerivedCategory (AdicCompletion.Modules l E X)) (e : K ≅ L),
      integralResidueClass l E X K ↔ integralResidueClass l E X L) ∧
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℤ),
      integralResidueClass l E X (K⟦n⟧) ↔ integralResidueClass l E X K) ∧
    (∀ T : Triangle (DerivedCategory (AdicCompletion.Modules l E X)),
      T ∈ distTriang (DerivedCategory (AdicCompletion.Modules l E X)) →
        (integralResidueClass l E X T.obj₁ → integralResidueClass l E X T.obj₂ →
          integralResidueClass l E X T.obj₃) ∧
        (integralResidueClass l E X T.obj₁ → integralResidueClass l E X T.obj₃ →
          integralResidueClass l E X T.obj₂) ∧
        (integralResidueClass l E X T.obj₂ → integralResidueClass l E X T.obj₃ →
          integralResidueClass l E X T.obj₁) ∧
        (integralResidueClass l E X T.obj₁ → integralResidueClass l E X T.obj₃ →
          IsDerivedComplete l E X T.obj₂ ∧ integralResidueEtaleOrigin l E X T.obj₂)) := by
  sorry

end AlgebraicGeometry.ProEtale
