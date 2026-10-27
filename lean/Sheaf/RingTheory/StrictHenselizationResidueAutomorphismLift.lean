/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.RingTheory.StrictHenselizationFiniteLifts
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Sheaf.RingTheory.HenselianFiniteEtaleMapBijective
import Mathlib.FieldTheory.Normal.Basic

/-!
# Lifting residue automorphisms through a strict henselization

Source: Stacks Project, Tag 0BSW, proof of lemma-identify-inertia; Tag 0BSL,
remark-construct-sh-from-h; Tag 04GK, lemma-henselian-cat-finite-etale.
(blueprint: lem-dl-a1-strict-henselization-residue-automorphism-lift).

The finite-stage assertion quantifies over every diagram of finite local etale lifts
and residue-compatible colimit identification, indexed by finite Galois residue fields.
-/

@[expose] public section
set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- A residue Galois automorphism lifts through the strict henselization and its fraction
field to an automorphism of the ambient separable closure. The fraction-field embedding
is characterized on the original ring, so it extends the given embedding, not a new choice.
The final clause includes uniqueness at each finite Galois stage, compatibility with all
transition maps, and the characterization of the induced colimit automorphism.

Source: Stacks Project, Tag 0BSW (lemma-identify-inertia, automorphism paragraph),
Tag 0BSL (remark-construct-sh-from-h), Tag 04GK (lemma-henselian-cat-finite-etale),
and Tag 0BME(2) (lemma-lift-maps).
(blueprint: lem-dl-a1-strict-henselization-residue-automorphism-lift).

Proof:
1. Regard the henselian base H as its own henselization, by the identity universal
property in def-weil-pbc-henselization-at-prime. The theorem
lem-wf-strict-henselization-finite-lifts supplies finite local etale lifts and their
residue-compatible colimit presentation of R, also after restriction to Galois stages.
2. Every finite Galois residue subfield e is preserved by tau: its minimal polynomials
split in e, so tau and its inverse send every element back into e. Restrictions of tau
therefore commute with inclusions of such subfields.
3. The Hom bijection lem-weil-pbc-henselian-finite-etale-map-bijective lifts these
restrictions uniquely to H-maps of the finite etale lifts. Lift tau inverse too;
injectivity of reduction makes the two composites identities. The same injectivity
makes the lifts commute with every transition, since their reductions commute.
4. The colimit universal property def-weil-pbc-category-colimit descends the compatible
lifts and their inverses. Their composites are identities on each coprojection and
hence on R. Testing the residue maps on the coprojections gives q t = tau q. This
argument works for every diagram and residue-compatible colimit identification in
the final clause, not only the system chosen in step 1.
5. Extend t by a/b mapping to t(a)/t(b). Injectivity preserves nonzero denominators,
and preservation of cross products proves well-definedness. The inverse comes from
t inverse. Since t fixes H, this extension fixes F. Extend the given embedding into
Omega by the same fraction formula; it is uniquely characterized on R.
6. By lem-weil-pbc-separable-closure-exists-galois, Omega/F is algebraic normal.
Apply lem-sfb-normal-intermediate-isomorphism-lifts to the image of Frac(R) in Omega
and its conjugated automorphism. The resulting F-automorphism restricts to t_L.
No normality of Frac(R)/F is needed. -/
theorem strictHenselization_residue_automorphism_lift
    (H K R : Type u) [CommRing H] [HenselianLocalRing H]
    [IsDomain H] [IsIntegrallyClosed H]
    [Field K] [Algebra (IsLocalRing.ResidueField H) K]
    [IsSepClosure (IsLocalRing.ResidueField H) K]
    [Algebra H K] [IsScalarTower H (IsLocalRing.ResidueField H) K]
    [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra H R]
    (P : StrictHenselizationPresentationIn.{u, u} H K R)
    (F : Type v) [Field F] [Algebra H F] [IsFractionRing H F]
    (L : Type w) [Field L] [Algebra R L] [IsFractionRing R L]
    [Algebra H L] [IsScalarTower H R L]
    [Algebra F L] [IsScalarTower H F L]
    (Ω : Type z) [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
    [Algebra H Ω] [IsScalarTower H F Ω]
    (j : R →ₐ[H] Ω) (_hj : Function.Injective j)
    (τ : K ≃ₐ[IsLocalRing.ResidueField H] K) :
    ∃ (t : R ≃ₐ[H] R) (tL : L ≃ₐ[F] L) (jL : L →ₐ[F] Ω) (g : Ω ≃ₐ[F] Ω),
      (∀ r : R, P.residueMap (t r) = τ (P.residueMap r)) ∧
      (∀ r : R, tL (algebraMap R L r) = algebraMap R L (t r)) ∧
      (∀ r : R, jL (algebraMap R L r) = j r) ∧
      (∀ x : L, g (jL x) = jL (tL x)) ∧
      ∀ (D : ObjectProperty.FullSubcategory
          (fun e : finiteResidueLiftIndex H K ↦
            Normal (IsLocalRing.ResidueField H) e.val) ⥤ CommAlgCat.{u} H)
        (_local : ∀ e, IsLocalRing (D.obj e))
        (_finite : ∀ e, Module.Finite H (D.obj e))
        (_etale : ∀ e, Etale H (D.obj e))
        (q : ∀ e, D.obj e →+* e.obj.val),
        (∀ e, Function.Surjective (q e)) →
        (∀ e, RingHom.ker (q e) =
          (IsLocalRing.maximalIdeal H).map (algebraMap H (D.obj e))) →
        (∀ e h, q e (algebraMap H (D.obj e) h) =
          algebraMap (IsLocalRing.ResidueField H) e.obj.val (IsLocalRing.residue H h)) →
        ∀ c : Cocone D, IsColimit c → ∀ i : c.pt ≅ CommAlgCat.of H R,
        (∀ e b, P.residueMap (i.hom.hom ((c.ι.app e).hom b)) = (q e b : K)) →
        ∃ ts : ∀ e, D.obj e ≃ₐ[H] D.obj e,
          (∀ e b, (q e (ts e b) : K) = τ (q e b : K)) ∧
          (∀ e (s : D.obj e ≃ₐ[H] D.obj e),
            (∀ b, (q e (s b) : K) = τ (q e b : K)) → s = ts e) ∧
          (∀ (e f : ObjectProperty.FullSubcategory
              (fun e : finiteResidueLiftIndex H K ↦
                Normal (IsLocalRing.ResidueField H) e.val)) (a : e ⟶ f) b,
            ts f ((D.map a).hom b) = (D.map a).hom (ts e b)) ∧
          (∀ e b, t (i.hom.hom ((c.ι.app e).hom b)) =
            i.hom.hom ((c.ι.app e).hom (ts e b))) := by
  sorry

end Algebra
