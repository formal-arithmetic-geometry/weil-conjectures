/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Sheaf.Paper.SheavesKilledByNZmodModules
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.ProjectiveCurveConstant

/-!
# Constructible higher direct images of finite constant groups on curve families

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
cor-fin-projective-curve-finite-group (blueprint: cor-fin-projective-curve-finite-group).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a projective family of schemes of finite type over a field, with geometric
fibres of dimension at most one, all higher direct images of a finite constant abelian
sheaf of invertible order are constructible.

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
cor-fin-projective-curve-finite-group (blueprint: cor-fin-projective-curve-finite-group).

Proof:
1. Enough injectives and left exact additive direct image give additive derived functors
and a long exact sequence (lem-weil-pbc-module-sheaves-enough-injectives,
lem-weil-pbc-direct-image-left-exact, lem-weil-pbc-horseshoe-delta-functor).
Induct simultaneously in all degrees on the order of the finite group; the zero group
has zero, hence constructible, higher images.
2. Choose a prime-order cyclic subgroup H of a nonzero group N. The quotient Q has
smaller order, and both orders divide the original order. The prime is invertible on S.
3. Exact abelian sheafification makes 0 → H → N → Q → 0 an exact sequence of constant
sheaves (lem-weil-pbc-sheafification-exact).
4. Apply thm-fin-projective-curve-constant to H and the induction hypothesis to Q.
5. All these sheaves and higher images are killed by n = |M|. The unique Z/n-module
structures and linearity of abelian maps are supplied by
lem-weil-pbc-sheaves-killed-by-n-zmod-modules. Finite constant abelian local models
become finite constant module local models: inverse image preserves n-annihilation
(prop-weil-pbc-inverse-image-exact), and geometric stalks identify the groups
(lem-weil-pbc-constant-sheaf-geometric-stalk). Module restriction has the same underlying
abelian inverse image (prop-weil-pbc-inverse-image-modules-exact).
6. The long exact sequence (lem-weil-pbc-derived-functor-long-exact) expresses each
higher image of N as an extension of a cokernel by a kernel of maps between the
constructible images of H and Q. In degree zero use zero for the preceding term.
Module kernels and cokernels have these underlying abelian objects
(def-weil-sheaf-of-modules-category).
7. Apply kernel, cokernel and extension closure (thm-constructible-serre), and forget
scalars in the finite constant models. This completes the induction. Negative-degree
images vanish since the injective resolution is concentrated in nonnegative degrees. -/
theorem isConstructibleAbelianSheaf_higherDirectImage_constant_of_projective_curve
    (k : Type u) [Field k] (X S : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] (f : X ⟶ S) [IsProjective f.left]
    (hdim : ∀ s : S.left,
      topologicalKrullDim (pullback f.left
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.left.residueField s) (AlgebraicClosure (S.left.residueField s)))) ≫
          S.left.fromSpecResidueField s) : Scheme.{u}) ≤ 1)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (horder : IsUnit (Nat.card M : Γ(S.left, ⊤))) (q : ℤ) :
    Scheme.IsConstructibleAbelianSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.left.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f.left).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)))) := by
  sorry

end AlgebraicGeometry
