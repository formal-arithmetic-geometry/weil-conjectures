module

public import Sheaf.Geometry.Complex.DolbeaultSheafData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives

/-!
# The Dolbeault acyclic resolution

Source: Demailly, Complex Analytic and Differential Geometry, I §3.C, §3.E Lemma (3.29),
and IV §6 Example (6.13) (blueprint: lem-sfb-dolbeault-acyclic-resolution).

The atlas admits varying finite dimensions. Hausdorffness and second countability are
imposed on the whole space; no nonemptiness, fixed dimension, or compactness is imposed.
The resolution and its cohomology are in sheaves of complex vector spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.SmoothAnalytic

/-- The canonical type components of exterior differentiation give an acyclic resolution
of every holomorphic form sheaf. The single-complex augmentation is a quasi-isomorphism,
which states exactness as sheaves, without claiming exactness on global sections.
All coefficient categories remain complex vector spaces, including in the derived functor.

Source: Demailly I §3.C, formulas (3.14)--(3.17), I §3.E Lemma (3.29), pp.28--29,
and IV §6 Example (6.13), pp.215--216
(blueprint: lem-sfb-dolbeault-acyclic-resolution).

Proof plan from the five DAG steps:
1. In each chart, the usual coordinate formulas split exterior differentiation into
   its two types. Holomorphic transition maps and the chain rule glue these operators
   and make them commute with restriction. The pointwise identity
   extDeriv_extDeriv_apply (lem-sfb-chart-exterior-derivative-square-zero) splits into
   the three identities below. On functions the holomorphic component is d_hol.
2. In degree zero of the augmented complex, write a (p,0)-form as a sum of dz_I f_I.
   Its dbar vanishes exactly when all f_I are holomorphic, by the degree-zero clause
   of lem-sfb-local-scalar-dolbeault. The inclusion uses the identical tensors and is mono.
3. For a dbar-closed (p,q)-form, q>0, write it as a sum of dz_I wedged with scalar
   (0,q)-forms. Apply lem-sfb-local-scalar-dolbeault to their finitely many coefficients
   on a common neighborhood. Multiply their primitives by (-1)^p to account for
   passing dbar across dz_I. This proves exactness of sheaves and the quasi-isomorphism.
4. The smooth form sheaves are modules over smooth complex-valued functions. Apply
   lem-sfb-smooth-function-modules-acyclic to their underlying abelian sheaves.
   The constant-complex-ring module comparison module_derived_evaluation_slice and
   moduleSheaves_abelian_enoughInjectives identify this with derived global sections
   in complex-vector-space sheaves. Zero underlying additive group means zero module.
5. These are local arguments in each chart dimension. Negative and excessive degrees
   have zero tensors; dimension zero has only functions. Finite disjoint unions retain
   the stated separation and countability properties, and the empty space has zero
   sections on its only open. Thus every listed edge case is included. -/
theorem dolbeault_acyclic_resolution (M : Type u) [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] (A : Atlas M) :
    ∃ (D : DolbeaultSheafData A)
      (sq : ∀ p q : ℤ, D.dbar p q ≫ D.dbar p (q + 1) = 0),
      (∀ p q : ℤ, D.del p q ≫ D.del (p + 1) q = 0) ∧
      (∀ p q : ℤ,
        D.dbar p q ≫ D.del p (q + 1) + D.del p q ≫ D.dbar (p + 1) q = 0) ∧
      (∀ p : ℕ, ∃ i :
        (HomologicalComplex.single (ComplexSheaves M) (ComplexShape.up ℤ) 0).obj
          (D.omega p) ⟶ CochainComplex.of (D.smooth p) (D.dbar p) (sq p),
        (HomologicalComplex.singleObjXSelf (V := ComplexSheaves M) (ComplexShape.up ℤ)
          0 (D.omega p)).inv ≫ i.f 0 = D.inclusion p ∧ QuasiIso i) ∧
      (∀ (p q : ℤ) (r : ℕ), 0 < r →
        IsZero (((complexGlobalSections (M := M)).rightDerived r).obj (D.smooth p q))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero (D.smooth p q)) ∧
      D.inclusion 0 ≫ D.del 0 0 = D.holomorphicDerivative ≫ D.inclusion 1 := by
  sorry

end AlgebraicGeometry.SmoothAnalytic
