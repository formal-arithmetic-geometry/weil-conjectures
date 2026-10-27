/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sober
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Nonconstant proper curve morphisms and function fields

Source: Stacks Project, Curves, Theorem 0BY1 (theorem-curves-rational-maps),
the fully faithful functor in the third proof paragraph
(blueprint: lem-sfb-proper-curve-function-field-morphisms).

The correspondence is stated by its graph: every base-compatible field homomorphism
is the generic stalk map of a unique nonconstant morphism over the base field.
The forward clause identifies the actual generic stalk map and its finite extension.
The identity and composition clauses use the same existing `Scheme.Hom.functionFieldMap`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical scalar map to the generic stalk, obtained by pulling back constants
and taking their germs. This is the base-field map used in the curve correspondence.
Source: Stacks Project, Curves, Theorem 0BY1, third proof paragraph;
Morphisms, Definition 01RW (blueprint: lem-sfb-proper-curve-function-field-morphisms). -/
noncomputable def Scheme.Hom.curveFunctionFieldBaseMap
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) : k →+* X.functionField :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom

/-- Nonconstant morphisms between smooth proper integral dimension-one curves over an
algebraically closed field correspond bijectively to base-compatible function-field
embeddings. Both function fields are finitely generated of transcendence degree one;
the generic stalk map of every such morphism induces a finite extension.

Source: Stacks Project, Curves, Theorem 0BY1, third proof paragraph
(blueprint: lem-sfb-proper-curve-function-field-morphisms).

Proof plan, following steps 1--8 of the node:
1. Integrality implies connectedness. Apply lem-sc-smooth-connected-curve-local-rings:
   nongeneric points are closed, local rings are fields or DVRs, hence valuation rings,
   and sections on nonempty opens inject into the function field.
2. A finite-type affine chart has a finitely generated coordinate algebra. Its fraction
   field is the curve's function field by lem-sc-integral-function-field-affine-fraction,
   hence is finitely generated as a field. Apply lem-sc-closed-irreducible-dimension-trdeg
   to the whole curve to obtain transcendence degree one.
3. If the image of the generic point were nongeneric, it would be closed and continuity
   would make the whole image that point. By lem-wf-affine-nullstellensatz-vanishing its
   residue field is k. Its inclusion is a closed immersion, so reduced-source factorization
   (lem-weil-pbc-reduced-source-factors-through-closed-subscheme) contradicts nonconstancy.
4. Taking the actual stalk map at the generic point gives an injective field map.
   The over-k equation makes it compatible with the two scalar maps below.
5. The transcendence-degree tower (lem-kun-transcendence-degree-tower) makes the extension
   over the embedded target field algebraic. Finite field generators remain generators
   over that field, so lem-weil-pbc-algebraic-generators-finite-extension makes it finite.
6. Conversely, an embedding composed with the germ injection of an affine target chart
   gives Spec k(X) to Y by the affine-spectrum correspondence. It induces the given map
   on generic stalks, since this holds on each fraction a/b.
7. Extend that generic map using lem-sfb-valuation-stalk-proper-target-extension:
   the local rings are valuation rings and Y is proper. The extension is nonconstant,
   since a k-point at the generic point of Y would embed k(Y) into k, contradicting step 2.
8. If two morphisms induce the same embedding, they agree on Spec k(X). Their equalizer
   is closed, by properness and base-change permanence of closed immersions. It contains
   the generic point, so has all of X as its image. Reduced-source factorization gives
   a section of the equalizer inclusion, and hence equality of the two morphisms.
   Thus every embedding arises exactly once, as asserted in the final clause. -/
theorem proper_curve_function_field_morphisms
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Scheme.{u}) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [IsCurve sX] [IsCurve sY]
    [Smooth sX] [Smooth sY] [IsProper sX] [IsProper sY]
    (hXdim : topologicalKrullDim X = 1) (hYdim : topologicalKrullDim Y = 1) :
    (@IntermediateField.FG k _ X.functionField _ sX.curveFunctionFieldBaseMap.toAlgebra ⊤ ∧
      @Algebra.trdeg k X.functionField _ _ sX.curveFunctionFieldBaseMap.toAlgebra = 1) ∧
    (@IntermediateField.FG k _ Y.functionField _ sY.curveFunctionFieldBaseMap.toAlgebra ⊤ ∧
      @Algebra.trdeg k Y.functionField _ _ sY.curveFunctionFieldBaseMap.toAlgebra = 1) ∧
    (∀ (f : X ⟶ Y) (_ : f ≫ sY = sX)
      (_ : ¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sX ≫ y = f),
      ∃ hf : f (genericPoint X) = genericPoint Y,
        Function.Injective (f.functionFieldMap hf).hom ∧
        (f.functionFieldMap hf).hom.comp sY.curveFunctionFieldBaseMap =
          sX.curveFunctionFieldBaseMap ∧
        @Module.Finite Y.functionField X.functionField _ _
          (@Algebra.toModule _ _ _ _ (f.functionFieldMap hf).hom.toAlgebra)) ∧
    (∀ φ : Y.functionField →+* X.functionField,
      φ.comp sY.curveFunctionFieldBaseMap = sX.curveFunctionFieldBaseMap →
      ∃! f : {f : X ⟶ Y // f ≫ sY = sX ∧
        ¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sX ≫ y = f},
        ∃ hf : f.val (genericPoint X) = genericPoint Y,
          (f.val.functionFieldMap hf).hom = φ) := by
  sorry

/-- The identity curve morphism is nonconstant and its generic stalk map is the identity.
Source: Stacks Project, Curves, Theorem 0BY1, third proof paragraph
(blueprint: lem-sfb-proper-curve-function-field-morphisms).

Proof (node step 9): if the identity factored through a k-point, that point would be
at the generic point, giving a k-embedding of the transcendence-degree-one function
field into k, which is impossible by the tower formula. The stalk map of the identity
sends each germ to itself, so its function-field map is the identity. -/
theorem proper_curve_function_field_identity
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsCurve sX] [Smooth sX] [IsProper sX]
    (hXdim : topologicalKrullDim X = 1) :
    (¬ ∃ x : Spec (.of k) ⟶ X, x ≫ sX = 𝟙 _ ∧ sX ≫ x = 𝟙 X) ∧
    ∀ h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X,
      ((𝟙 X : X ⟶ X).functionFieldMap h).hom = RingHom.id X.functionField := by
  sorry

/-- The composite of two nonconstant curve morphisms is nonconstant, and its function-field
map is the composite of their function-field maps in the reverse order.
Source: Stacks Project, Curves, Theorem 0BY1, third proof paragraph
(blueprint: lem-sfb-proper-curve-function-field-morphisms).

Proof (node step 9): by the forward correspondence, both morphisms send the generic point
to the generic point, hence so does their composite. A factorization through a rational
point would embed the target function field into k, contradicting its transcendence
degree one by lem-kun-transcendence-degree-tower. On a germ represented near the target
generic point, pullback along the composite is successive pullback. Taking stalks gives
the claimed equality for every germ. -/
theorem proper_curve_function_field_composition
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y Z : Scheme.{u})
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsCurve sX] [IsCurve sY] [IsCurve sZ]
    [Smooth sX] [Smooth sY] [Smooth sZ] [IsProper sX] [IsProper sY] [IsProper sZ]
    (hXdim : topologicalKrullDim X = 1) (hYdim : topologicalKrullDim Y = 1)
    (hZdim : topologicalKrullDim Z = 1)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
    (hf_nonconstant : ¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sX ≫ y = f)
    (hg_nonconstant : ¬ ∃ z : Spec (.of k) ⟶ Z, z ≫ sZ = 𝟙 _ ∧ sY ≫ z = g) :
    (¬ ∃ z : Spec (.of k) ⟶ Z, z ≫ sZ = 𝟙 _ ∧ sX ≫ z = f ≫ g) ∧
    ∃ (hfg : (f ≫ g) (genericPoint X) = genericPoint Z)
      (hfη : f (genericPoint X) = genericPoint Y)
      (hgη : g (genericPoint Y) = genericPoint Z),
      ((f ≫ g).functionFieldMap hfg).hom =
        (f.functionFieldMap hfη).hom.comp (g.functionFieldMap hgη).hom := by
  sorry

end AlgebraicGeometry
