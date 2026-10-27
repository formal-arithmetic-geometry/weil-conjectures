/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # A signed first-quadrant Hom model for a module target

Source: Stacks Project, Tags 0G1Z, 013K, 070J, 0A8H and 012Z.
(blueprint: lem-trf-source-hom-double-complex-model).

The double complex is specified by term isomorphisms and its two differential formulas.
The translation is specified by term isomorphisms with unchanged differential, so it
uses no convention for signed shifts. The inverse comparison is fixed on every total
coprojection by a single homogeneous cochain. All Hom objects retain their A-actions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- The signed Hom double complex and its translated total compute ordinary derived Hom.
Source: Stacks Project, Injectives Tag 0G1Z, Derived Categories Tags 013K and 070J,
More on Algebra Tag 0A8H, Homology Tag 012Z.
(blueprint: lem-trf-source-hom-double-complex-model).

Proof:
1. Modules have enough injectives (lem-weil-pbc-ring-modules-enough-injectives).
Apply clause (1) of lem-weil-pbc-left-exact-injective-resolution-degree-zero to N,
and extend its nonnegative resolution by zero to integer degrees. Fix any such I.
2. In the quadrant take Hom_A(M^(u-b), I^i), postcomposition by d_I and
(-1)^(b-u+1) times precomposition by d_M. Take zero terms outside the quadrant.
The two squares vanish by d_I squared and d_M squared. The mixed composites agree
because the second sign is independent of i. This is def-sp-double-complex-total.
3. By def-pur-hom-complex, presented for ordinary modules by
 def-sc-module-total-hom-complex, degree t is the product over a of
Hom_A(M^a,I^(a+t)). Only -t <= a <= u can contribute. The substitution
(i,b)=(a+t,u-a) identifies this finite product with the diagonal finite coproduct.
The inverse sends each coprojection to its single homogeneous cochain. For t+u<0
both sides are zero. This specifies the comparison without any choice of coordinates.
4. The second total differential has coefficient
(-1)^i (-1)^(b-u+1)=(-1)^(t+1). The two contributions are therefore exactly
 d_I f - (-1)^t f d_M. Thus the comparison is a complex isomorphism. Translation
retains the total differential, including when u is odd or negative.
5. By lem-weil-pbc-bounded-below-injectives-kinjective, I is K-injective.
The ordinary-module presentation of def-pur-derived-internal-hom identifies
Hom_A(M,I) with RHom_A(M,N[0]). On the one-object identity-covering ringed site
these are precisely the module Hom and product Hom complex. Localize the complex
isomorphism by def-weil-abstract-derived-category and compose its inverse with this
identification to obtain the displayed isomorphism in D(A). No other bound on M,
projectivity, finite generation, or Noetherian hypothesis enters the argument. -/
theorem source_hom_double_complex_model
    (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (u₀ : ℤ)
    (hM : ∀ a : ℤ, u₀ < a → IsZero (M.X a)) (N : ModuleCat.{u} A) :
    (∃ I : CochainComplex (ModuleCat.{u} A) ℤ,
      ∃ s : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N ⟶ I,
        QuasiIso s ∧ (∀ i : ℤ, Injective (I.X i)) ∧
          (∀ i : ℤ, i < 0 → IsZero (I.X i))) ∧
    (∀ (I : CochainComplex (ModuleCat.{u} A) ℤ)
      (s : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N ⟶ I),
      QuasiIso s → (∀ i : ℤ, Injective (I.X i)) →
      (∀ i : ℤ, i < 0 → IsZero (I.X i)) →
      ∃ D : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
        (∀ i b : ℤ, i < 0 ∨ b < 0 → IsZero ((D.X i).X b)) ∧
        ∃ e : ∀ (i b : ℤ) (_hi : 0 ≤ i) (_hb : 0 ≤ b),
          ((D.X i).X b ≅ ModuleCat.of A (M.X (u₀ - b) →ₗ[A] I.X i)),
          (∀ (i b : ℤ) (hi : 0 ≤ i) (hb : 0 ≤ b)
            (f : M.X (u₀ - b) →ₗ[A] I.X i),
            (e (i + 1) b (by omega) hb).hom
              (((D.d i (i + 1)).f b) ((e i b hi hb).inv f)) =
              (I.d i (i + 1)).hom.comp f) ∧
          (∀ (i b : ℤ) (hi : 0 ≤ i) (hb : 0 ≤ b)
            (f : M.X (u₀ - b) →ₗ[A] I.X i),
            (e i (b + 1) hi (by omega)).hom
              (((D.X i).d b (b + 1)) ((e i b hi hb).inv f)) =
              (b - u₀ + 1).negOnePow •
                (f.comp (M.d (u₀ - (b + 1)) (u₀ - b)).hom)) ∧
          ∃ Q : CochainComplex (ModuleCat.{u} A) ℤ,
            ∃ q : ∀ t : ℤ, Q.X t ≅ (D.total (ComplexShape.up ℤ)).X (t + u₀),
              (∀ t : ℤ,
                Q.d t (t + 1) ≫ (q (t + 1)).hom =
                  (q t).hom ≫ (D.total (ComplexShape.up ℤ)).d
                    (t + u₀) ((t + 1) + u₀)) ∧
              ∃ φ : moduleHomComplex M I ≅ Q,
                (∀ (t i b : ℤ) (hi : 0 ≤ i) (hb : 0 ≤ b)
                  (h : i + b = t + u₀) (f : (D.X i).X b),
                  (φ.inv.f t) ((q t).inv
                    ((D.ιTotal (ComplexShape.up ℤ) i b (t + u₀) h) f)) =
                    HomComplex.Cochain.single (ModuleCat.ofHom ((e i b hi hb).hom f)) t) ∧
                Nonempty (DerivedCategory.Q.obj Q ≅
                  (ordinaryModuleDerivedInternalHom A).obj
                    (op (DerivedCategory.Q.obj M),
                      DerivedCategory.Q.obj
                        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)))) := by
  sorry

end CochainComplex
