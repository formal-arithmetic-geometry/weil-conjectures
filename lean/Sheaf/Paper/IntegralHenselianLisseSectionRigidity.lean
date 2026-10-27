/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.WStrictLisseComponentCohomology
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.RingTheory.IndfiniteContractibleBaseWStrict
import Sheaf.RingTheory.HenselianWStrictLocalInvariance
import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import Sheaf.Paper.ProfinitePointPullback

/-!
# Integral henselian lisse section rigidity

Source: Hemo--Richarz--Scholbach, Corollary 4.4(1), Lemma 4.1, Proposition 4.3,
equation (4.2) and Corollary 4.7; Bhatt--Scholze, Lemma 2.2.13; Stacks Project,
Tags 02JK, 09XK, 0817 and 01ID.
(blueprint: lem-sfb-integral-henselian-lisse-section-rigidity).

The restriction map is the existing actual derived-adjunction-unit map in D(Ab).
The tensor ideal and two affine maps below are explicit canonical constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ideal ID in D = B tensor_A C. By compatibility of the tensor structure maps,
this is also the extension of IC along C -> D.
Source: Stacks Tags 02JK and 09XK, extended ideals under base change.
(blueprint: lem-sfb-integral-henselian-lisse-section-rigidity). -/
abbrev integralHenselianTensorIdeal
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A) : Ideal (B ⊗[A] C) :=
  I.map (algebraMap A (B ⊗[A] C))

/-- The quotient closed immersion a : Spec(D/ID) -> Spec D, for D = B tensor_A C.
Source: HRS Corollary 4.4(1), applied to the tensor algebra and its extended ideal.
(blueprint: lem-sfb-integral-henselian-lisse-section-rigidity). -/
def integralHenselianClosedFibre
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A) :
    Spec (.of ((B ⊗[A] C) ⧸ integralHenselianTensorIdeal A B C I)) ⟶
      Spec (.of (B ⊗[A] C)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (integralHenselianTensorIdeal A B C I)))

/-- The projection b : Spec(B tensor_A C) -> Spec B, induced by b |-> b tensor 1.
Source: Stacks Tag 02JK, affine integral base change, and HRS Proposition 4.3.
(blueprint: lem-sfb-integral-henselian-lisse-section-rigidity). -/
def integralHenselianTensorProjection
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] :
    Spec (.of (B ⊗[A] C)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom)

/-- Integral base change over a henselian w-contractible test ring gives henselian
w-strictly local source and closed fibre, the actual component homeomorphism, and
invertibility of the actual restriction of ordinary derived lisse sections.
Source: HRS Corollary 4.4(1), Lemma 4.1, Proposition 4.3, (4.2), Corollary 4.7;
BS Lemma 2.2.13; Stacks Tags 02JK, 09XK, 0817 and 01ID.
(blueprint: lem-sfb-integral-henselian-lisse-section-rigidity).

Proof for stage 3, following the five DAG steps:
1. Integral base change (lem-weil-pbc-integral-base-change), followed by the tensor
flip, makes D integral over C. Integral permanence of henselian pairs
(lem-weil-pbc-integral-over-henselian-pair) makes (D,ID) henselian. Ideal.map_map
identifies ID with (IC)D; no structural map has to be injective or finite.
2. Spec C is qcqs (lem-weil-pbc-affine-scheme-qcqs). Form the associated algebra
using lem-weil-pbc-spec-module-tilde-sections, with multiplication of fractions.
The affine restriction formula (lem-weil-pbc-quasi-coherent-algebra-affine-inclusion)
and integral base change make it integral on every affine open. Apply
lem-weil-pbc-integral-algebra-directed-colimit-finite, clause (2), and take affine
sections with lem-weil-pbc-quasi-coherent-algebra-colimit. This expresses D as a
nonempty directed colimit of finite, finitely presented C-algebras; transition
maps need not be injective.
3. Apply lem-sfb-indfinite-contractible-base-wstrict to get w-strict locality of D.
Then lem-zl-henselian-wstrict-local-invariance gives it for D/ID as well. This
makes no claim that D is w-contractible.
4. The unconditional first clause of lem-zl-condensed-henselian-lisse-rigidity,
HRS Corollary 4.4(1), identifies the actual pi_0(a) as a homeomorphism, with
ConnectedComponents carrying its quotient topology.
5. Pull back a pro-etale cover trivializing L along b, and use the canonical
coefficient comparison (lem-weil-pbc-profinite-point-pullback) to get lisseness
of b*L. Apply lem-sfb-wstrict-lisse-component-cohomology to a and b*L using steps
3 and 4. Its map is precisely componentLisseSectionsPullback: the actual derived
adjunction unit, followed by the canonical derived composition comparison and
the exact degree-zero pullback comparison. Sections are terminal evaluation,
forgetting scalars, derived on K-injectives. Rank zero, varying ranks and empty
spectra are allowed. There is no Noetherianity, finiteness, coefficient completeness
or coefficient discreteness assumption. -/
theorem integral_henselian_lisse_section_rigidity
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A)
    [Algebra.IsIntegral A B] [IsWContractibleRing C]
    [HenselianRing C (I.map (algebraMap A C))] :
    (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom.IsIntegral ∧
      HenselianRing (B ⊗[A] C) (integralHenselianTensorIdeal A B C I) ∧
      IsWStrictlyLocalRing (B ⊗[A] C) ∧
      IsWStrictlyLocalRing ((B ⊗[A] C) ⧸ integralHenselianTensorIdeal A B C I) ∧
      IsHomeomorph (integralHenselianClosedFibre A B C I).continuous.connectedComponentsMap ∧
      ∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
        (L : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of B))) Ab.{u + 1})
          (condensedRingObj Λ.X (Spec (.of B)))),
        IsLisseCoefficientModule Λ.X L →
          IsLisseCoefficientModule Λ.X
            ((upperStar Λ.X (integralHenselianTensorProjection A B C)).obj L) ∧
          IsIso ((componentLisseSectionsPullback Λ (integralHenselianClosedFibre A B C I)).app
            ((upperStar Λ.X (integralHenselianTensorProjection A B C)).obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
