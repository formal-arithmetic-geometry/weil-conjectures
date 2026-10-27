/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealPowerQuotients
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.ReesAlgebra

/-! # The specified Rees action on ideal-power cohomology

Source: Stacks Project, Spaces Cohomology, Situation 08AV and Lemma 08AW
(blueprint: def-sfb-space-ideal-power-rees-cohomology-data).

The power subsheaves are specified by their local sections, and multiplication by its
sectionwise inclusion formula. Cohomology is the existing additive-sheaf cohomology on
the equivalent small affine etale model. Neither a replacement cohomology theory nor an
arbitrary action is supplied. The action formula determines all finite-support inputs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

namespace AlgebraicGeometry.AlgebraicSpace

/-- Additive-sheaf cohomology on the equivalent small affine etale site.
Source: Stacks, Cohomology on Sites, Section 01FT, and Spaces Cohomology, Situation 08AV
(blueprint: def-sfb-space-ideal-power-rees-cohomology-data).
Ext is taken in the section universe u, given by the Grothendieck abelian structure of
sheaves on the small model, as in lem-sfb-space-graded-cohomology-finite; this adds no
size assumption on the space. -/
def idealPowerCohomologyFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) (q : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  X.smallModuleRestriction ⋙ SheafOfModules.toSheaf X.smallStructureRings ⋙
    Sheaf.functorH X.smallEtaleModelTopology q

open Classical in
/-- The ideal-power subsheaves and their prescribed homogeneous action on cohomology.
Source: Stacks, Spaces Cohomology, Situation 08AV and the graded action of Lemma 08AW
(blueprint: def-sfb-space-ideal-power-rees-cohomology-data).

The range condition is local generation by base ideal powers, so also specifies the
zeroth power as F. Inclusions are injective on sections. The multiplication formula
therefore uniquely determines each map. The scalar normalization specifies the A-module
structures; the double finite sum specifies the Rees-module structure. -/
structure IdealPowerReesCohomologyData {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (F : X.Modules) (q : ℕ)
    where
  /-- The actual locally generated power subsheaves. -/
  obj (r : ℕ) : X.Modules
  /-- Their inclusions in the original module. -/
  inclusion (r : ℕ) : obj r ⟶ F
  /-- The inclusions are injective on every etale chart. -/
  injective (r : ℕ) (T : X.EtaleSite) : Function.Injective ((inclusion r).val.app (op T))
  /-- Exactly the sections locally in the span of products a s with a in I^r. -/
  range_eq (r : ℕ) (T : X.EtaleSite) :
    Set.range ((inclusion r).val.app (op T)) =
      {s | ∃ R : Sieve T, R ∈ X.etaleTopology T ∧
        ∀ (V : X.EtaleSite) (g : V ⟶ T), R g →
          F.val.map g.op s ∈ Submodule.span (X.structureSheaf.obj.obj (op V))
            {z | ∃ a : A, a ∈ I ^ r ∧ ∃ t : F.val.obj (op V),
              z = idealPowerChartScalar X V a • t}}
  /-- Multiplication by a homogeneous coefficient. -/
  multiply (k r : ℕ) (a : ↥(I ^ k)) : obj r ⟶ obj (r + k)
  /-- The multiplication map is the restriction of ordinary scalar multiplication. -/
  multiply_inclusion (k r : ℕ) (a : ↥(I ^ k)) (T : X.EtaleSite)
      (s : (obj r).val.obj (op T)) :
    (inclusion (r + k)).val.app (op T) ((multiply k r a).val.app (op T) s) =
      idealPowerChartScalar X T a.val • (inclusion r).val.app (op T) s
  /-- Scalar structures on the actual additive cohomology groups. -/
  scalarModule (r : ℕ) : Module A ((idealPowerCohomologyFunctor X q).obj (obj r))
  /-- Degree-zero multiplication is exactly the specified scalar action. -/
  scalar_normalization (r : ℕ) (a : ↥(I ^ 0))
      (x : (idealPowerCohomologyFunctor X q).obj (obj r)) :
    HEq ((idealPowerCohomologyFunctor X q).map (multiply 0 r a) x)
      (@SMul.smul _ _ (scalarModule r).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        a.val x)
  /-- All induced cohomology maps are A-linear. -/
  linear (k r : ℕ) (a : ↥(I ^ k)) (b : A)
      (x : (idealPowerCohomologyFunctor X q).obj (obj r)) :
    (idealPowerCohomologyFunctor X q).map (multiply k r a)
      (@SMul.smul _ _ (scalarModule r).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        b x) =
      @SMul.smul _ _
        (scalarModule (r + k)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul b
        ((idealPowerCohomologyFunctor X q).map (multiply k r a) x)
  /-- The Rees module structure on the additive direct sum. -/
  reesModule : Module (reesAlgebra I)
    (⨁ r : ℕ, ((idealPowerCohomologyFunctor X q).obj (obj r) : Type u))
  /-- The convolution formula, for every pair of finite-support inputs. -/
  convolution (b : reesAlgebra I)
      (x : ⨁ r : ℕ, ((idealPowerCohomologyFunctor X q).obj (obj r) : Type u)) :
    @SMul.smul _ _ reesModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b x =
      ∑ k ∈ b.val.support, ∑ r ∈ x.support,
        DirectSum.of (fun n : ℕ ↦
          ((idealPowerCohomologyFunctor X q).obj (obj n) : Type u)) (r + k)
            ((idealPowerCohomologyFunctor X q).map
              (multiply k r ⟨b.val.coeff k, b.property k⟩) (x r))
  /-- The degree-zero A-action agrees on each summand. -/
  degree_zero (a : A) (r : ℕ)
      (x : (idealPowerCohomologyFunctor X q).obj (obj r)) :
    @SMul.smul _ _ reesModule.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      (algebraMap A (reesAlgebra I) a)
      (DirectSum.of (fun n : ℕ ↦
        ((idealPowerCohomologyFunctor X q).obj (obj n) : Type u)) r x) =
      DirectSum.of (fun n : ℕ ↦
        ((idealPowerCohomologyFunctor X q).obj (obj n) : Type u)) r
          (@SMul.smul _ _
            (scalarModule r).toDistribMulAction.toMulAction.toSemigroupAction.toSMul a x)

end AlgebraicGeometry.AlgebraicSpace
