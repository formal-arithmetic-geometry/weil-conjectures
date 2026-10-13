/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.PQFCohomology
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.Algebra.Homology.HomologySequence
import Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts
import Sheaf.AlgebraicGeometry.CechH1MapNatural
import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor

import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # The Leibniz identity for a fixed quotient action and horseshoe boundary

Source: Stacks Project, Cohomology, Lemma 0B8S, local-lift computation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The connecting map obeys Leibniz for any sheaf action agreeing with multiplication
by local lifts. The action is input; no action, cohomology action, or boundary is chosen.
Source: Stacks Project, Cohomology, Lemma 0B8S, local-lift computation.
(blueprint: lem-sc-square-zero-horseshoe-boundary-leibniz)

Proof:
1. For global f and g, the sheaf epimorphism p gives a common open cover with lifts
b_a and c_a (intersect covers for f and g). Their products lift fg. Kernel exactness
identifies overlap differences with unique sections z_f, z_g, z_fg of I; the triple
differences telescope, so these are Cech cocycles.
2. On each overlap, b_a*c_a - b_b*c_b = (b_a-b_b)*c_a + b_b*(c_a-c_b).
The lift-action hypothesis identifies the two terms with the images under i of
(mu g)(z_f) and (mu f)(z_g). Injectivity of i on sections therefore identifies z_fg
with their sum. Square-zero guarantees that replacing any lift gives the same action.
3. Apply boundary_cech_local_lifts and cechH1Map_natural. The comparison is additive
and commutes with mu f and mu g, so the preceding cocycle identity yields the same
identity on H1 for the canonical connecting classes. Either uniform convention for
Cech differences gives this identity, since changing all three signs preserves it.
4. The displayed snake map is that connecting map: compare the compatible resolutions
with a horseshoe using exists_horseshoe_rightDerived_deltaFunctor and resolution
comparison. Naturality for the identity ladder makes the transported boundaries equal;
the degree-zero augmentation identifies the section f with its H0 class through
 toRightDerivedZero. Thus the same identity holds for the specified boundary d.
For I = 0 it is the zero identity; for a split extension the boundary vanishes. -/
theorem square_zero_horseshoe_boundary_leibniz (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0)
    (IA : InjectiveResolution I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map i ≫ IB.ι)
    (hιB : IB.ι ≫ β =
      (CochainComplex.single₀ _).map ((commAlgebraSheafModuleFunctor X.sheaf).map p) ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact)
    (μ : C.right.obj.obj (op ⊤) →+* End I)
    (hlift : ∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens)
      (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
      p.right.hom.app (op U) b = C.right.obj.map (homOfLE le_top).op f →
      @id (B.right.obj.obj (op U)) (i.val.app (op U) ((μ f).val.app (op U) x)) =
        b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) :
    let d :=
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
          (commAlgebraSheafModule X.sheaf C) ≫
        (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
        hΓ.δ 0 1 rfl ≫
        (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv
    ∀ f g : C.right.obj.obj (op ⊤), d.hom (f * g) =
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ f)).hom (d.hom g) +
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ g)).hom (d.hom f) := by
  sorry

end AlgebraicGeometry
