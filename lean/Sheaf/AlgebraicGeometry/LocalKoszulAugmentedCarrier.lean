/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.KoszulComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # A locally augmented Koszul carrier

Source: Stacks Project, Tags 0BQY and 068C.
(blueprint: new-s1-local-koszul-augmented-carrier). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A specified algebraic Koszul resolution gives a local K-flat resolution whose
restricted tensor pullback has bounded finite-free terms and zero differential.

Source: Stacks Project, Tag 068C, finite-free Koszul resolution; Tag 0BQY,
proof's local Koszul construction and quotient calculation.
(blueprint: new-s1-local-koszul-augmented-carrier).

Proof: Put A = Gamma(Y,U) and I = ker(i)(U). The closed immersion on U identifies
its source with Spec(A/I). Apply exists_affine_quotient_sheafified_resolution to
Q.complex and Q.pi using that quotient identification. Replace Q.complex by the
Koszul complex using hQ and reindex degree n as -n, with zero terms in positive
cochain degrees. This gives a complex B on U and a quasi-isomorphism to the
restriction of i_*O_Z in degree zero. Each exterior basis makes B^{-n} free of
rank binomial(m,n); exterior powers vanish for n > m. Thus B is bounded and
termwise flat, hence K-flat by the finite filtration by its single-degree terms.
Take K to be the termwise module pushforward of B along U.ι. The restriction of
this pushforward back to U is naturally isomorphic to B: sections over an open
of U are unchanged by the pushforward and restriction. Transport the augmentation
and K-flatness along this isomorphism. This construction needs no exactness or
K-flatness of the pushforward on all of Y.
On W = V intersect i^{-1}(U), restriction of i^*K is the tensor pullback of B
along the restricted immersion, followed by restriction to W's over site.
This follows termwise from the inverse-image and extension-of-scalars formula
for tensorPullback. Every generator f_j has zero image in the quotient, by hf,
so the pulled-back contraction differential is zero. Scalar extension and open
restriction take each displayed exterior basis to a basis over the new ring
sheaf. The bounds [-m,0] are preserved. For m=0 this is the degree-zero unit
complex; for an empty open or zero quotient the same bases describe zero
modules over the zero ring. No arbitrary choice of a zero model is used. -/
theorem exists_local_koszul_augmented_carrier
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (V : Z.Opens) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (Q : ProjectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
      ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)))
    (hQ : Q.complex = ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) m f) :
    let F := (Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex (.up ℤ)
    let S := (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    let G := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
      moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))
    ∃ (K : CochainComplex Y.Modules ℤ) (b : F.obj K ⟶ F.obj S),
      CochainComplex.IsKFlatResolution (R := U.1.toScheme.sheaf) b ∧
      (∀ x y : ℤ, (G.obj K).d x y = 0) ∧
      (∃ x y : ℤ, ∀ k : ℤ, k < x ∨ y < k → IsZero ((G.obj K).X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ, Nonempty ((G.obj K).X k ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf.over
          (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) (ULift.{u} (Fin r)))) := by sorry

end AlgebraicGeometry
