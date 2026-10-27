/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Composition of equivariant finite generically etale covers

Source: de Jong, Families of curves and alterations (1997), Remarks 2.3(iii), p. 602,
Situation 5.3, p. 613, and the induction in Lemma 5.7, p. 615; the exact kernel-fixed-field
strengthening and elementary proof in the DAG
(blueprint: lem-sfb-equivariant-finite-cover-composition).

Function fields are generic stalks. Their inclusions are the canonical
`Scheme.Hom.functionFieldMap`, and fixed elements use `Scheme.functionFieldAut`.
Inverse pullback on constants expresses the compatibility of the left scheme actions
with the left action on the base field. Taking fixed elements is unchanged by replacing
every group member by its inverse.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Two finite surjective generically etale equivariant covers compose, with the exact
fixed field of the composite kernel. No action is required to be faithful. The terminal
base is the same scheme `T` with its given structure map, so its geometric properties
are retained.

Source: de Jong (1997), Remarks 2.3(iii), Situation 5.3 and Lemma 5.7 induction;
the exact fixed-field strengthening is the elementary argument recorded in the DAG
(blueprint: lem-sfb-equivariant-finite-cover-composition).

Proof:
1. Finite morphisms compose (lem-weil-pbc-finite-composition); successive lifts of points
prove surjectivity. Choose dense target opens V0 and W0 for the two etale restrictions.
2. The image of the generic point of W is generic by dominance. The generic fibre of a
has only that point: on affine domain charts, finiteness implies integrality
(pqf-lem-finite-integral-lft), and incomparability (pqf-lem-incomparability) makes every
prime above zero equal to zero.
3. Put Z = W minus W0. Its image under a is closed
(lem-weil-pbc-finite-closed-map-finite-fibres) and misses the generic point of V.
Thus U = V0 minus a(Z) is dense open, and its inverse image lies in W0.
4. Both restricted maps over U are base changes of the given etale restrictions
(lem-weil-pbc-etale-scheme-base-change). Compose them using
lem-weil-pbc-etale-composition-cancellation to get an etale restriction of c followed by a.
5. Paste the equivariance squares; successive lifts prove that sigma composed with tau
is surjective. Pullback of generic germs gives compatibility of the field inclusions
with these induced automorphisms.
6. Write Q for ker(sigma composed with tau) and N for ker(tau). Since N is contained in Q,
a Q-fixed element of k(T) comes from k(W). Lift every element of ker(sigma) through tau:
its lifts belong to Q, so the element of k(W) is ker(sigma)-fixed and comes from k(V).
Conversely, every element from k(V) is fixed by Q, by the two given fixed-field equalities
and compatibility of the generic stalk maps. This uses no faithfulness assumption. -/
theorem equivariant_finite_cover_composition
    (k : Type u) [Field k] (V W T : Scheme.{u})
    (pV : V ⟶ Spec (.of k)) (pW : W ⟶ Spec (.of k)) (pT : T ⟶ Spec (.of k))
    [IsIntegral V] [IsIntegral W] [IsIntegral T]
    [IsHProjective pV] [IsHProjective pW] [IsHProjective pT]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    [LocallyOfFiniteType pW] [QuasiCompact pW]
    [LocallyOfFiniteType pT] [QuasiCompact pT]
    (hnormalV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (hnormalW : ∀ x : W, IsDomain (W.presheaf.stalk x) ∧
      IsIntegrallyClosed (W.presheaf.stalk x))
    (hnormalT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.presheaf.stalk x))
    (G : Type v) (J : Type w) (L : Type z)
    [Group G] [Group J] [Group L] [Finite G] [Finite J] [Finite L]
    (σ : J →* G) (τ : L →* J)
    (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (ρk : G →* (k ≃+* k)) (ρV : G →* Aut V)
    (ρW : J →* Aut W) (ρT : L →* Aut T)
    (hV : ∀ g : G, (ρV g).hom ≫ pV =
      pV ≫ Spec.map (CommRingCat.ofHom (ρk g⁻¹).toRingHom))
    (hW : ∀ j : J, (ρW j).hom ≫ pW =
      pW ≫ Spec.map (CommRingCat.ofHom (ρk (σ j⁻¹)).toRingHom))
    (hT : ∀ l : L, (ρT l).hom ≫ pT =
      pT ≫ Spec.map (CommRingCat.ofHom (ρk (σ (τ l⁻¹))).toRingHom))
    (a : W ⟶ V) (c : T ⟶ W) [IsFinite a] [Surjective a] [IsFinite c] [Surjective c]
    (ha : ∀ j : J, (ρW j).hom ≫ a = a ≫ (ρV (σ j)).hom)
    (hc : ∀ l : L, (ρT l).hom ≫ c = c ≫ (ρW (τ l)).hom)
    (haet : ∃ U : V.Opens, Dense (U : Set V) ∧ Etale (a ∣_ U))
    (hcet : ∃ U : W.Opens, Dense (U : Set W) ∧ Etale (c ∣_ U))
    (hMa : ∀ y : W.functionField,
      (∃ x : V.functionField, a.functionFieldMap a.apply_genericPoint_of_isDominant x = y) ↔
        ∀ j : σ.ker, (Scheme.functionFieldAut (ρW j.val)).hom y = y)
    (hFc : ∀ y : T.functionField,
      (∃ x : W.functionField, c.functionFieldMap c.apply_genericPoint_of_isDominant x = y) ↔
        ∀ l : τ.ker, (Scheme.functionFieldAut (ρT l.val)).hom y = y) :
    IsFinite (c ≫ a) ∧ Surjective (c ≫ a) ∧
      (∃ U : V.Opens, Dense (U : Set V) ∧ Etale ((c ≫ a) ∣_ U)) ∧
      Function.Surjective (σ.comp τ) ∧
      (∀ l : L, (ρT l).hom ≫ (c ≫ a) = (c ≫ a) ≫ (ρV ((σ.comp τ) l)).hom) ∧
      ∀ y : T.functionField,
        (∃ x : V.functionField,
          (c ≫ a).functionFieldMap (c ≫ a).apply_genericPoint_of_isDominant x = y) ↔
          ∀ l : (σ.comp τ).ker, (Scheme.functionFieldAut (ρT l.val)).hom y = y := by
  sorry

end AlgebraicGeometry
