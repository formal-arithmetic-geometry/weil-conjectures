/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.PNat.Basic

/-! # The simultaneous-root diagram indexed by divisibility

Source: the explicit construction in Step 1 of
`lem-sfb-flat-root-tower-nonzerodivisor`; Stacks Project, Algebra, polynomial quotient
universal properties, and Categories, Tags 002F and 04AX.
(blueprint: def-sfb-simultaneous-root-tower).

Finite stages use the existing `Algebra.pthRootAlgebra`, whose exponent parameter
does not require primality. All maps are specified polynomial evaluations descended
through the displayed ideals. Their well-definedness and functor laws follow from
the quotient relations and polynomial extensionality.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- A set of positive root orders, endowed below with divisibility rather than numerical order.
Source: Step 1 of the flat-root-tower lemma; Stacks, Categories, Tag 04AX.
(blueprint: def-sfb-simultaneous-root-tower). -/
def RootTowerIndex (I : Set ℕ+) : Type := I

/-- The divisibility preorder on the actual set of root orders.
Source: Step 1 of the flat-root-tower lemma; Stacks, Categories, Tag 04AX.
(blueprint: def-sfb-simultaneous-root-tower). -/
instance rootTowerIndexPreorder (I : Set ℕ+) : Preorder (RootTowerIndex I) where
  le n m := (n.1 : ℕ) ∣ (m.1 : ℕ)
  le_refl n := dvd_refl (n.1 : ℕ)
  le_trans _ _ _ := dvd_trans

/-- The quotient map to the existing simultaneous-root algebra.
Source: the displayed quotient in the flat-root-tower lemma; Stacks, Algebra, quotients.
(blueprint: def-sfb-simultaneous-root-tower). -/
def simultaneousRootQuotient {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ+) :
    MvPolynomial (Fin r) R →ₐ[R] pthRootAlgebra (n : ℕ) r R t :=
  Ideal.Quotient.mkₐ R _

/-- The class of the d-th polynomial variable at the specified root order.
Source: the displayed quotient in the flat-root-tower lemma; Stacks, Algebra, quotients.
(blueprint: def-sfb-simultaneous-root-tower). -/
def simultaneousRoot {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ+) (d : Fin r) : pthRootAlgebra (n : ℕ) r R t :=
  simultaneousRootQuotient t n (MvPolynomial.X d)

/-- Polynomial substitution x_d ↦ x_d^(m/n) into the stage of order m.
Source: Step 1 of the flat-root-tower lemma; Stacks, Algebra, polynomial evaluation.
(blueprint: def-sfb-simultaneous-root-tower). -/
def simultaneousRootEval {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : ℕ+) :
    MvPolynomial (Fin r) R →ₐ[R] pthRootAlgebra (m : ℕ) r R t :=
  MvPolynomial.aeval (fun d ↦ simultaneousRoot t m d ^ ((m : ℕ) / (n : ℕ)))

/-- The specified evaluation kills the source root relations, hence their generated ideal.
Source: Step 1 of the flat-root-tower lemma; polynomial quotient universal property.
(blueprint: def-sfb-simultaneous-root-tower).

Proof: for a generator X_d^n-C(t_d), evaluation is
(x_(d,m)^(m/n))^n-t_d = x_(d,m)^m-t_d = 0. The first equality uses n | m
and n > 0, and the second is the target quotient relation. The kernel of an algebra
map is an ideal, so vanishing on these generators gives vanishing on their span.
The argument also applies to zero coefficient rings and the empty family of generators. -/
theorem simultaneousRootEval_kills {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) :
    ∀ f : MvPolynomial (Fin r) R,
      f ∈ Ideal.span (Set.range (fun d : Fin r ↦
        MvPolynomial.X d ^ (n : ℕ) - MvPolynomial.C (t d))) →
      simultaneousRootEval t n m f = 0 := by
  have hker : Ideal.span (Set.range (fun d : Fin r ↦
      MvPolynomial.X d ^ (n : ℕ) - MvPolynomial.C (t d))) ≤
      RingHom.ker (simultaneousRootEval t n m).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨d, rfl⟩
    change simultaneousRootEval t n m
      (MvPolynomial.X d ^ (n : ℕ) - MvPolynomial.C (t d)) = 0
    simp only [simultaneousRootEval, map_sub, map_pow, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, ← pow_mul, Nat.div_mul_cancel h]
    have hrel : simultaneousRootQuotient t m
        (MvPolynomial.X d ^ (m : ℕ) - MvPolynomial.C (t d)) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_range_self d))
    simpa [map_sub, map_pow, simultaneousRoot, simultaneousRootQuotient,
      MvPolynomial.algebraMap_eq] using hrel
  intro f hf
  exact hker hf

/-- The canonical transition, obtained by descending the specified polynomial evaluation.
Source: Step 1 of the flat-root-tower lemma; Stacks, Algebra, quotient universal property.
(blueprint: def-sfb-simultaneous-root-tower). -/
def simultaneousRootTransition {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) :
    pthRootAlgebra (n : ℕ) r R t →ₐ[R] pthRootAlgebra (m : ℕ) r R t :=
  Ideal.Quotient.liftₐ _ (simultaneousRootEval t n m) (simultaneousRootEval_kills t h)

/-- The transition at equal positive orders is the identity.
Source: Step 1 of the flat-root-tower lemma; polynomial and quotient extensionality.
(blueprint: def-sfb-simultaneous-root-tower).

Proof: n/n = 1 since n is positive. Thus the descended evaluation fixes every root
class and every coefficient. Precompose with the surjective quotient map and use
MvPolynomial.algHom_ext to obtain equality on every polynomial class. -/
theorem simultaneousRootTransition_id {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ+) :
    simultaneousRootTransition t (dvd_refl (n : ℕ)) =
      AlgHom.id R (pthRootAlgebra (n : ℕ) r R t) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro d
  simp [simultaneousRootTransition, simultaneousRootEval, simultaneousRoot,
    simultaneousRootQuotient]

/-- The canonical root transitions compose along divisibility.
Source: Step 1 of the flat-root-tower lemma; polynomial and quotient extensionality.
(blueprint: def-sfb-simultaneous-root-tower).

Proof: for n | m | k, both maps fix coefficients and send x_(d,n) to
x_(d,k)^((k/m)*(m/n)) = x_(d,k)^(k/n). For the exponent identity write m=n*a
and k=m*b, using positivity to cancel n and m in natural-number division.
Polynomial extensionality followed by quotient surjectivity gives equality of maps.
No transition is assumed injective. -/
theorem simultaneousRootTransition_comp {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) {n m k : ℕ+}
    (h : (n : ℕ) ∣ (m : ℕ)) (h' : (m : ℕ) ∣ (k : ℕ)) :
    (simultaneousRootTransition t h').comp (simultaneousRootTransition t h) =
      simultaneousRootTransition t (dvd_trans h h') := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro d
  simp [simultaneousRootTransition, simultaneousRootEval, simultaneousRoot,
    simultaneousRootQuotient, ← pow_mul, Nat.div_mul_div h' h]

/-- The actual simultaneous-root diagram of commutative rings.
Source: Step 1 of the flat-root-tower lemma; Stacks, Categories, Tags 002F and 04AX.
(blueprint: def-sfb-simultaneous-root-tower). -/
def simultaneousRootDiagram {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (I : Set ℕ+) : RootTowerIndex I ⥤ CommRingCat.{u} where
  obj n := .of (pthRootAlgebra (n.1 : ℕ) r R t)
  map h := CommRingCat.ofHom (simultaneousRootTransition t (leOfHom h)).toRingHom
  map_id n := congrArg (fun f ↦ CommRingCat.ofHom (AlgHom.toRingHom f))
    (simultaneousRootTransition_id t n.1)
  map_comp f g := (congrArg (fun h ↦ CommRingCat.ofHom (AlgHom.toRingHom h))
    (simultaneousRootTransition_comp t (leOfHom f) (leOfHom g))).symm

/-- The coefficient map to the ring colimit, using the stage of order one.
Source: Step 1 of the flat-root-tower lemma; Stacks, Categories, colimit coprojections.
(blueprint: def-sfb-simultaneous-root-tower). -/
def simultaneousRootColimitMap {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (I : Set ℕ+) (h1 : (1 : ℕ+) ∈ I) :
    R →+* ↥(colimit (simultaneousRootDiagram t I)) :=
  ((colimit.ι (simultaneousRootDiagram t I) (⟨1, h1⟩ : RootTowerIndex I)).hom).comp
    (algebraMap R (pthRootAlgebra 1 r R t))

end Algebra
