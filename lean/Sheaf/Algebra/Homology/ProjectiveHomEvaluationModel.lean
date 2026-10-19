/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.ModuleHomComplexQuotient
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-! # Projective Hom complexes and the derived evaluation

Source: Stacks Project, More on Algebra, Tags 0A66, 0A5W, 0A5Y, 0GWQ and 0FNG
(blueprint: lem-pod-projective-hom-evaluation-model).

The Hom complex here has differential d_N f - (-1)^q f d_P, using the recorded
module-valued Hom complex. The tensor and internal Hom on the derived category are
its existing derived closed monoidal structure. The canonical lax tensorator of Q
compares derived tensor with the ordinary direct-sum total tensor of complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CochainComplex

/-- The projective Hom model, natural in both complexes, with its signed evaluation.
Source: Stacks Project, Tags 0A66 (projective Hom model), 0A5W (derived internal Hom),
0A5Y and 0GWQ (tensor-Hom adjunction), and 0FNG (Koszul signs).
(blueprint: lem-pod-projective-hom-evaluation-model)

The witnesses H and ev are uniquely specified chain maps: H is pre- and post-composition
on every homogeneous coordinate, and ev is signed evaluation on every total-tensor
summand. The comparison e is specified by its counit square, equivalently as the
adjoint transpose of Q(ev) after the canonical tensorator. Thus neither the comparison
nor the tensor model is an arbitrary isomorphism. Boundedness and projectivity enter
only the derived comparison; no finite generation or bound on N is assumed.

Proof:
1. Projective modules are flat (lem-weil-pbc-projective-module-flat). The bounded-above
flat-complex theorem (lem-pc-module-bounded-flat-kflat) therefore makes P K-flat.
2. The Hom-complex quotient theorem (lem-sc-module-hom-complex-quotient), applied in
all shifted degrees, identifies Hom cohomology with homotopy maps. Bounded-above
projectivity makes the localization map bijective
(lem-pc-ring-derived-map-representative). The defining derived Hom identity then
shows that the canonical comparison is an isomorphism in every cohomological degree.
Equivalently, compare N with a K-injective resolution; Hom(P,-) preserves that
quasi-isomorphism, by precisely the preceding Hom-cohomology computation.
3. The K-flat tensor computation (lem-pc-source-kflat-module-tensor-model) makes the
canonical tensorator QP tensor QD to Q(P tensor D) invertible for this P and arbitrary D.
4. On bidegree (p,q), evaluate x tensor f as (-1)^(p*q) f(x). The two terms involving
f(d_P x) cancel against those from the Hom differential; the remaining term is the
signed d_N(f(x)). This gives a chain map. Ordinary tensor-Hom adjunction identifies
it with the identity of the Hom complex. Deriving the adjunction identifies its
localization, after the tensor comparison, with the counit, giving the displayed square.
5. Pre- and post-composition commute with these constructions and with signed evaluation.
This gives the mixed naturality square for e, contravariant in P and covariant in N.
The same formulas apply to zero complexes, shifted free modules, arbitrary projective
modules, and unbounded N; no finite-generation hypothesis is used. -/
theorem projective_hom_evaluation_model (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] :
    ∃ H : ∀ {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ},
        (P' ⟶ P) → (N ⟶ N') → (moduleHomComplex P N ⟶ moduleHomComplex P' N'),
      ∃ ev : ∀ (P N : CochainComplex (ModuleCat.{u} R) ℤ),
          P ⊗ moduleHomComplex P N ⟶ N,
        (∀ (P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ)
          (a : P' ⟶ P) (b : N ⟶ N') (q p s : ℤ) (h : p + q = s)
          (f : (moduleHomComplex P N).X q),
          ((H a b).f q f).v p s h = a.f p ≫ f.v p s h ≫ b.f s) ∧
        (∀ (P N : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ)
          (x : P.X p) (f : (moduleHomComplex P N).X q),
          (ev P N).f (p + q)
              ((HomologicalComplex.ιTensorObj P (moduleHomComplex P N) p q (p + q) rfl)
                (x ⊗ₜ[R] f)) =
            (p * q).negOnePow • (f.v p (p + q) rfl) x) ∧
        ∃ e : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
            (_hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (_hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (N : CochainComplex (ModuleCat.{u} R) ℤ),
            DerivedCategory.Q.obj (moduleHomComplex P N) ≅
              (ihom (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N),
          (∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
            (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (N : CochainComplex (ModuleCat.{u} R) ℤ),
            IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N)) ∧
            Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N) ≫
                DerivedCategory.Q.map (ev P N) =
              DerivedCategory.Q.obj P ◁ (e P hb hp N).hom ≫
                (ihom.ev (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)) ∧
          (∀ (P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ)
            (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (hb' : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P'.X i))
            (hp' : ∀ i : ℤ, Module.Projective R (P'.X i))
            (a : P' ⟶ P) (b : N ⟶ N'),
            DerivedCategory.Q.map (H a b) ≫ (e P' hb' hp' N').hom =
              (e P hb hp N).hom ≫
                (MonoidalClosed.pre (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj N) ≫
                (ihom (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map b)) := by
  sorry

end CochainComplex
