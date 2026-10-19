/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Normalization and completion away from the special fibre

Source: Stacks Project, Resolution of Surfaces, Tag 0BG9,
`resolve-lemma-normalization-completion`
(blueprint: lem-per-normalization-completion-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

/-- If a scheme locally of finite type over a Noetherian local ring becomes normal away
from the special fibre after completing the base, its componentwise normalization is finite
and commutes with that completion. The two equations express that the isomorphism is over
`Y = X ×[Spec A] Spec Â`, by its two projections.

Source: Stacks Project, Resolution of Surfaces, Tag 0BG9,
`resolve-lemma-normalization-completion`
(blueprint: lem-per-normalization-completion-base-change).

Proof:
1. Choose an affine cover of `X` by opens `Spec B` with `B` a finite-type `A`-algebra, as
   supplied by local finite type, and work on one such open; put `C = B ⊗[A] Â` and
   `I = m B`. The affine fibre-product formula gives the corresponding open `Spec C ⊆ Y`.
   The completion `Â` is Noetherian and local, its maximal ideal is `m Â`, and it is
   complete: apply module-completion completeness to `M = A`, noting that
   `m^n Â = (m Â)^n`. Thus the complete-local Nagata theorem makes `Â` Nagata. Local
   completion is faithfully flat, so its base change `B → C` is faithfully flat. Both `B`
   and `C` are Noetherian by finite-type Noetherianity. Moreover `B/I ≅ C/IC`, by
   tensoring the completion residue-field isomorphism with `B`. The special fibre in this
   chart is exactly `V(IC)`.
2. Write `ν : Spec C^ν → Spec C` for normalization. It is finite: the quotient `C_red` is
   Noetherian by finite-type Noetherianity, and the affine-chart description applied to
   `(Spec C)_red` (normalization does not change on removing nilpotents, by its
   componentwise definition) gives `C^ν = ∏_{j=1}^r (C/q_j)‾`, where `q_j` are the finitely
   many minimal primes and the bars are integral closures in the fraction fields. Each
   domain `C/q_j` is of finite type over the Nagata ring `Â`, hence N-2 by the
   universally-Japanese theorem; for the degree-one extension of its fraction field this
   makes each integral closure a finite `C/q_j`-module. Its finitely many generators also
   generate over `C`, and their union, inserted in the factors, generates the finite
   product. Thus `C^ν` is finite over `C`. By the normalization-properties node it is
   normal and `C → C^ν` is an isomorphism over the assumed normal open
   `Spec C ∖ V(IC)`.
3. Choose generators `f_1, …, f_t` of `I` (they exist because `B` is Noetherian). On each
   `D(f_i)` the map `C_{f_i} → (C^ν)_{f_i}` is an isomorphism. Form the finite-algebra
   gluing datum with prime algebra `E' = C^ν`, chart algebras `E_i = B_{f_i}`, transitions
   `(C^ν)_{f_i} ≅ C_{f_i} = B_{f_i} ⊗_B C` and the usual identifications
   `(B_{f_i})_{f_j} ≅ (B_{f_j})_{f_i}`. The overlap and cocycle identities are the
   equalities `x/(f_i^a f_j^b) = x/(f_j^b f_i^a)` and their three-denominator versions; the
   prime transitions are the inverses of the same structural isomorphism `C → C^ν` after
   localization, so satisfy them too. The hypotheses of finite-algebra formal gluing hold:
   `B → C` is flat, `B/I ≅ C/IC`, `C^ν` is finite, and each chart algebra is generated as
   a module by `1`. It gives a finite `B`-algebra `D` with compatible algebra isomorphisms
   `D ⊗_B C ≅ C^ν` and `D_{f_i} ≅ B_{f_i}`. Hence `Spec D → Spec B` is finite and is an
   isomorphism away from `V(I)`.
4. The base-change map `D → D ⊗_B C` is faithfully flat and its target is the normal ring
   `C^ν`, so normality descent (the ring version, not the field-extension statement)
   makes `D` normal. A finite algebra is of finite type, so `D` is Noetherian. Thus
   `Z = Spec D` is normal and locally Noetherian.
5. Every minimal prime `t` of `D` contracts to a minimal prime of `B`: faithful flatness of
   `D → C^ν` gives a prime above `t`; choose a minimal prime `u` inside it, whose
   contraction is still `t` by minimality. The normalization-properties node says that
   `u ∩ C` is minimal in `C`, and a minimal prime under the flat map `B → C` contracts to
   a minimal prime by going down. This holds even for components inside the special fibre.
6. Fix a minimal prime `p` of `B`. Faithful flatness gives a prime of `C` over it, and a
   minimal prime `q` inside that prime still contracts to `p`. Put `K = κ(p)`, `L = κ(q)`
   and `E = D ⊗_B K`, a finite `K`-algebra. The generic-fibre assertion for normalization
   gives, as `L`-algebras, `E ⊗_K L = D ⊗_B L ≅ C^ν ⊗_C L ≅ L`. Hence `K → E` is an
   isomorphism (a nonzero kernel or cokernel would survive the field extension), so
   `E = K`. Primes of this fibre are the primes of `D` over `p`, so there is exactly one,
   with residue field `K`; it is minimal, since a minimal prime beneath it contracts to a
   minimal prime of `B` by step 5, necessarily `p`. With step 5 this is a bijection of
   generic points and isomorphisms of their residue fields.
7. The finite morphism `Z → Spec B` is integral, `Z` is normal and locally Noetherian, and
   steps 5 and 6 are exactly the generic-point and residue-field hypotheses of
   normalization recognition. Its recognition clause gives a unique isomorphism
   `Z ≅ (Spec B)^ν` over `Spec B`. So this normalization is finite and its base change is
   `Spec C^ν`, with the prescribed structural map to `Spec C`. No reducedness of `B` is
   assumed: recognition applies to the reductions at the generic points.
8. Normalization restricts to normalization on open subschemes, so the finite maps of step 7
   on affine opens of `X` are restrictions of `X^ν → X`, which is finite since finiteness
   is local on the target. The comparison isomorphisms on the corresponding opens of `Y`
   agree on overlaps by the uniqueness in normalization recognition (each identifies the
   componentwise normalization and is the identity on generic residue fields). They glue,
   with their inverses, by the sheaf axiom, giving `X^ν ×_{Spec A} Spec Â ≅ Y^ν` over `Y`,
   i.e. the isomorphism compatible with both projections asserted below. -/
theorem normalization_completion_base_change
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (hnormal : ∀ y : (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (maximalIdeal A) A)))) : Scheme.{u}),
      (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A))))) y ≠
          closedPoint (AdicCompletion (maximalIdeal A) A) →
      IsDomain ((pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A))))).presheaf.stalk y) ∧
      IsIntegrallyClosed ((pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A))))).presheaf.stalk y)) :
    IsFinite X.fromReducedNormalization ∧
      ∃ e : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (maximalIdeal A) A))))).reducedNormalization ≅
        pullback (X.fromReducedNormalization ≫ f)
          (Spec.map (CommRingCat.ofHom
            (algebraMap A (AdicCompletion (maximalIdeal A) A)))),
        (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
          (pullback f (Spec.map (CommRingCat.ofHom
            (algebraMap A (AdicCompletion (maximalIdeal A) A))))).fromReducedNormalization ≫
              pullback.fst f (Spec.map (CommRingCat.ofHom
                (algebraMap A (AdicCompletion (maximalIdeal A) A))))) ∧
        (e.hom ≫ pullback.snd _ _ =
          (pullback f (Spec.map (CommRingCat.ofHom
            (algebraMap A (AdicCompletion (maximalIdeal A) A))))).fromReducedNormalization ≫
              pullback.snd f (Spec.map (CommRingCat.ofHom
                (algebraMap A (AdicCompletion (maximalIdeal A) A))))) := by
  sorry

end AlgebraicGeometry.Scheme
