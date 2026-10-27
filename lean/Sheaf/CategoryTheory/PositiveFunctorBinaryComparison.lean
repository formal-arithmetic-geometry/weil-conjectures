/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.CategoryTheory.NaturalTransportInduction

/-! # Binary compatibility of positive functor comparisons

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, categorical expansion
of the iterate assertion (blueprint: lem-trf-positive-functor-binary-comparison).

The family index `n` denotes the positive exponent `n + 1`. Functor composition
is diagrammatic, so `P b ⋙ P a` denotes the source's `P_a ∘ P_b`.
The plain powers are the recorded `NaturalTransport.power`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.PositiveFunctorComparison

/-- Canonical reassociation of the recorded powers, with identity components.
Source: categorical expansion of the blueprint iterate assertion, proof step 1
(blueprint: lem-trf-positive-functor-binary-comparison). -/
def powerReassoc {C : Type u} [Category.{v} C] (T : C ⥤ C) :
    (a b : ℕ) → NaturalTransport.power T b ⋙ NaturalTransport.power T a ≅
      NaturalTransport.power T (b + a)
  | 0, b => Functor.rightUnitor (NaturalTransport.power T b)
  | a + 1, b =>
      (Functor.associator _ _ T).symm ≪≫ Functor.isoWhiskerRight (powerReassoc T a b) T

/-- The specified recursion `d_1 = id`, `d_(r+1) = T(d_r) ∘ C_(1,r)`.
It constructs natural isomorphisms directly; no invertibility of `T` is assumed.
Source: categorical expansion of the blueprint iterate assertion, proof step 2
(blueprint: lem-trf-positive-functor-binary-comparison). -/
def comparison {C : Type u} [Category.{v} C] (P : ℕ → C ⥤ C)
    (μ : ∀ a b : ℕ, P (b + a + 1) ≅ P b ⋙ P a) :
    (n : ℕ) → P n ≅ NaturalTransport.power (P 0) (n + 1)
  | 0 => Iso.refl _
  | n + 1 => μ 0 n ≪≫ Functor.isoWhiskerRight (comparison P μ n) (P 0)

/-- The recursive comparisons respect every binary positive decomposition.
The cocycle and conclusion are equalities of natural isomorphisms, equivalently
equalities of their forward natural transformations. The `eqToIso` factors only
transport equal sums of indices; `powerReassoc` inserts canonical associators.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, categorical expansion
of the iterate assertion (blueprint: lem-trf-positive-functor-binary-comparison).

Proof plan (the explicit componentwise argument supplied by the DAG):
1. Induct on the first exponent to identify iterated powers on objects and
   morphisms. The reassociations have identity components; use category laws
   (def-nagata-category) and the recorded powers (def-trf-endofunctor-powers).
2. The recursion starts with the identity. Naturality of each successor follows
   from naturality of its comparison factors and functoriality of T. Its inverse
   is C_(1,r)^(-1) composed with T(d_r^(-1)); the inverse laws and naturality
   follow by functoriality and cancellation. This is built into `comparison`.
3. Fix the second positive exponent and induct on the first. At exponent one,
   binary compatibility is exactly the successor recursion, including b = 1.
4. Expand the successor recursion and the induction hypothesis componentwise.
   Functoriality separates T applied to each factor. The cocycle at (1,a,b)
   replaces T(C_(a,b)) composed with C_(1,a+b) by C_(1,a)P_b composed with
   C_(a+1,b). Combine T(d_a P_b) with C_(1,a)P_b using the recursion at P_b M.
   The result is precisely the binary formula for the successor exponent.
5. Equality at every object is equality of natural transformations. Naturality
   of the factors and preservation of composition give compatibility with every
   morphism, without assuming that the endofunctor is an equivalence. -/
theorem binary_compatibility {C : Type u} [Category.{v} C] (P : ℕ → C ⥤ C)
    (μ : ∀ a b : ℕ, P (b + a + 1) ≅ P b ⋙ P a)
    (hμ : ∀ a b c : ℕ,
      μ a (c + b + 1) ≪≫ Functor.isoWhiskerRight (μ b c) (P a) ≪≫
          Functor.associator (P c) (P b) (P a) =
        eqToIso (congrArg P
          (congrArg (fun n : ℕ => n + 1)
            ((Nat.add_right_comm (c + b) 1 a).trans
              ((congrArg (fun n : ℕ => n + 1) (Nat.add_assoc c b a)).trans
                (Nat.add_assoc c (b + a) 1))))) ≪≫
          μ (b + a + 1) c ≪≫ Functor.isoWhiskerLeft (P c) (μ a b)) :
    ∀ a b : ℕ,
      comparison P μ (b + a + 1) =
        μ a b ≪≫
          Functor.isoWhiskerLeft (P b) (comparison P μ a) ≪≫
          Functor.isoWhiskerRight (comparison P μ b)
            (NaturalTransport.power (P 0) (a + 1)) ≪≫
          powerReassoc (P 0) (a + 1) (b + 1) ≪≫
          eqToIso (congrArg (NaturalTransport.power (P 0))
            (congrArg (fun n : ℕ => n + 1) (Nat.add_right_comm b 1 a))) := by
  intro a
  induction a with
  | zero =>
    intro b
    ext X
    simp [comparison, powerReassoc, NaturalTransport.power]
  | succ a ih =>
    intro b
    erw [comparison, ih b]
    ext X
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_comp]
    have hc := congrArg (fun e ↦ e.hom.app X) (hμ 0 a b)
    simp only [Nat.add_zero, Functor.comp_obj, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, eqToIso_refl, Iso.refl_trans, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app] at hc
    simp only [comparison, powerReassoc, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      NaturalTransport.power, Functor.comp_map, Functor.map_comp,
      eqToIso.hom, eqToHom_app, eqToHom_map, Category.assoc]
    simp only [Iso.symm_hom, Functor.associator_inv_app, Functor.map_id,
      Category.id_comp]
    erw [← Category.assoc, hc]
    simp only [Category.assoc]
    erw [Category.id_comp]

end CategoryTheory.PositiveFunctorComparison
