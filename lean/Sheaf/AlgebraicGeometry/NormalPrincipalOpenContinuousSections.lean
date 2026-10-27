/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence

import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic
import Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism
import Sheaf.Paper.ContinuousRingUniverseRealization

/-! # Continuous coefficient sections across a normal principal open

Source: Stacks Project, Algebra, Tags 034M and 00EE; Bhatt--Scholze,
The pro-etale topology for schemes, Lemma 4.2.12; Hemo--Richarz--Scholbach,
Constructible sheaves on schemes, Example 3.1.
(blueprint: lem-sfb-normal-principal-open-continuous-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The actual morphism Spec Q[1/s] → Spec Q induced by localization.
Source: Stacks Project, Algebra, Tag 00EE, localization of clopens
(blueprint: lem-sfb-normal-principal-open-continuous-sections). -/
noncomputable abbrev normalPrincipalOpenInclusion (Q : Type u) [CommRing Q] (s : Q) :
    Spec (.of (Localization.Away s)) ⟶ Spec (.of Q) :=
  Spec.map (CommRingCat.ofHom (algebraMap Q (Localization.Away s)))

/-- Evaluate the existing section-ring reconstruction on the actual pulled-back coefficient
ring object. This only packages its section carrier and its tensor-induced ring operations.
Source: Hemo--Richarz--Scholbach, Example 3.1; Stacks Project, Tag 00YV
(blueprint: lem-sfb-normal-principal-open-continuous-sections). -/
noncomputable def principalContinuousCoefficientSections (E : Type u) [NormedField E]
    (X : Scheme.{u}) (U : X.ProEt) : RingCat.{u + 1} := by
  letI : MonObj (condensedRingObj (Profinite.continuousCoefficientRingObj E) X).obj :=
    (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).monObjObj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)
  exact (InternalAbelianSheafModule.presheafRings
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) X).obj).obj (Opposite.op U)

/-- Actual restriction of the pulled-back coefficient sheaf on a fixed site's objects.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme-pullback paragraph
(blueprint: lem-sfb-normal-principal-open-continuous-sections). -/
noncomputable def principalContinuousCoefficientObjectRestriction (E : Type u) [NormedField E]
    {Z : Scheme.{u}} {U V : Z.ProEt} (f : V ⟶ U) :
    principalContinuousCoefficientSections E Z U →
      principalContinuousCoefficientSections E Z V :=
  (condensedRingObj (Profinite.continuousCoefficientRingObj E) Z).obj.map f.op

/-- The canonical map on global coefficient sections: evaluate the mate of the specified
point-pullback comparison at the terminal object and restrict along the canonical map
X → Y ×_Y X. Thus its target is evaluation at the actual terminal object of X_proet.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme-pullback paragraph
(blueprint: lem-sfb-normal-principal-open-continuous-sections). -/
noncomputable def principalContinuousCoefficientGlobalRestriction (E : Type u) [NormedField E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    principalContinuousCoefficientSections E Y (Scheme.ProEt.mk (𝟙 Y)) →
      principalContinuousCoefficientSections E X (Scheme.ProEt.mk (𝟙 X)) :=
  fun a ↦
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) X).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift f (𝟙 X) (by simp)) (by simp)).op
      ((condensedPushforwardHom (Profinite.continuousCoefficientRingObj E) f).hom.app
        (Opposite.op (Scheme.ProEt.mk (𝟙 Y))) a)

/-- The canonical continuous-function coordinates of actual coefficient sections.
Source: Hemo--Richarz--Scholbach, Example 3.1, normalized comparison
(blueprint: lem-sfb-normal-principal-open-continuous-sections). -/
noncomputable def principalContinuousCoefficientRealization (E : Type u) [NormedField E]
    [IsUltrametricDist E] (X : Scheme.{u}) (U : X.ProEt) :
    principalContinuousCoefficientSections E X U → C(U.left, E) :=
  fun a ↦ ((condensedFieldContinuousMapIso E X).hom.hom.hom.app (Opposite.op U) a).down

/-- Clopen inverse images are bijective and the normalized component map is a homeomorphism.
Source: Stacks Project, Algebra, Tags 034M and 00EE, and Topology, Tag 0906
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof (node steps 1--3): regularity embeds Q and Q[1/s] in the total fraction ring.
Every localized idempotent satisfies the monic polynomial T²-T. The theorem
`integral_totalFraction_mem_range_of_normal` (normal-ring-integrally-closed-total)
therefore puts it uniquely in Q, and injectivity shows the lift is idempotent.
The clopen-idempotent correspondence (spec-clopen-idempotent) identifies this bijection
with actual inverse image. Both affine spectra are qcqs (affine-scheme-qcqs), hence
spectral (qcqs-scheme-spectral). Apply spectral-clopen-component-homeomorphism to obtain
h and its normalization. For Q=0 both component spaces are empty and both clopen sets
are singletons. For s=1 the same construction is the identity. -/
theorem normal_principal_open_clopen_components (Q : Type u) [CommRing Q]
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (hs : Function.Injective (fun x : Q ↦ s * x)) :
    Function.Bijective
      (fun U : Clopens (Spec (.of Q)) ↦
        (⟨(normalPrincipalOpenInclusion Q s) ⁻¹' (U : Set (Spec (.of Q))),
          U.isClopen.preimage (normalPrincipalOpenInclusion Q s).continuous⟩ :
          Clopens (Spec (.of (Localization.Away s))))) ∧
    ∃ h : ConnectedComponents (Spec (.of (Localization.Away s))) ≃ₜ
        ConnectedComponents (Spec (.of Q)),
      ∀ x : Spec (.of (Localization.Away s)),
        h (ConnectedComponents.mk x) =
          ConnectedComponents.mk (normalPrincipalOpenInclusion Q s x) := by
  sorry

/-- Actual restriction is a ring bijection, with the stated component-factor inverse.
Source: Bhatt--Scholze, Lemma 4.2.12; Stacks Project, Tags 034M, 00EE and 0906
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof (node steps 1--4): first obtain the normalized component homeomorphism from
normal_principal_open_clopen_components. Ultrametric balls are clopen and separate any
two points of E; hence E is totally disconnected. Every continuous function factors
uniquely and continuously through the connected-component quotient. The result
ultrametric-component-map-extension gives extension by the inverse homeomorphism and
q_X, inverse to actual precomposition with i. Pointwise addition and multiplication
make this a ring isomorphism. No compactness or completeness of E is used; for the
empty spectra all function rings are singleton rings. -/
theorem normal_principal_open_continuous_sections (Q : Type u) [CommRing Q]
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (hs : Function.Injective (fun x : Q ↦ s * x))
    (E : Type u) [NormedField E] [IsUltrametricDist E] :
    ∃ h : ConnectedComponents (Spec (.of (Localization.Away s))) ≃ₜ
        ConnectedComponents (Spec (.of Q)),
      ∃ r : C(Spec (.of Q), E) ≃+* C(Spec (.of (Localization.Away s)), E),
        (∀ x : Spec (.of (Localization.Away s)),
          h (ConnectedComponents.mk x) =
            ConnectedComponents.mk (normalPrincipalOpenInclusion Q s x)) ∧
        (∀ a : C(Spec (.of Q), E),
          r a = a.comp (normalPrincipalOpenInclusion Q s).base.hom) ∧
        (∀ a : C(Spec (.of (Localization.Away s)), E),
          ∃! b : C(ConnectedComponents (Spec (.of (Localization.Away s))), E),
            a = b.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) ∧
        (∀ (a : C(Spec (.of (Localization.Away s)), E)) (x : Spec (.of Q)),
          r.symm a x = a.continuous.connectedComponentsLift
            (h.symm (ConnectedComponents.mk x))) := by
  sorry

/-- The actual coefficient restriction is a ring bijection, and the canonical realization
identifies it with precomposition of continuous functions.
Source: Hemo--Richarz--Scholbach, Example 3.1 and the following scheme-pullback paragraph
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof (node step 5): the ultrametric topology is totally disconnected. Apply
condensed-field-continuous-realization on both schemes. The adjoint normalization
f ↦ f composed with profiniteTestProjection is the continuous-ring-canonical-comparison.
The scheme-pullback square of normalized-continuous-set-comparison-coherence identifies
the mate of the point-pullback comparison with precomposition, including its ring
operations. Evaluation at the terminal objects and the canonical terminal pullback map
gives precisely principalContinuousCoefficientGlobalRestriction. Conjugate the ring
bijection from normal_principal_open_continuous_sections by these realizations.
This yields the displayed equality as well as bijectivity. Empty spectra give singleton
section rings and the unit open gives identity restrictions. -/
theorem normal_principal_open_coefficient_sections (Q : Type u) [CommRing Q]
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (hs : Function.Injective (fun x : Q ↦ s * x))
    (E : Type u) [NormedField E] [IsUltrametricDist E] :
    ∃ c : principalContinuousCoefficientSections E (Spec (.of Q))
          (Scheme.ProEt.mk (𝟙 (Spec (.of Q)))) ≃+*
        principalContinuousCoefficientSections E (Spec (.of (Localization.Away s)))
          (Scheme.ProEt.mk (𝟙 (Spec (.of (Localization.Away s))))),
      (∀ a, c a = principalContinuousCoefficientGlobalRestriction E
        (normalPrincipalOpenInclusion Q s) a) ∧
      (∀ a, principalContinuousCoefficientRealization E
          (Spec (.of (Localization.Away s)))
          (Scheme.ProEt.mk (𝟙 (Spec (.of (Localization.Away s))))) (c a) =
        (principalContinuousCoefficientRealization E (Spec (.of Q))
          (Scheme.ProEt.mk (𝟙 (Spec (.of Q)))) a).comp
            (normalPrincipalOpenInclusion Q s).base.hom) := by
  sorry

/-- On any ambient pro-etale site, evaluation at the normal affine pair gives the same
coefficient ring bijection and the same continuous-function restriction.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof (node step 5): evaluate condensed-field-continuous-realization for Z at the objects
Spec Q → Z and Spec Q[1/s] → Z. Naturality of this ring-sheaf isomorphism identifies its
actual restriction with function precomposition. The ring bijection from
normal_principal_open_continuous_sections therefore transports to the stated ring
bijection of evaluations. There is no condition on Z. The empty object is included. -/
theorem normal_principal_open_coefficient_object_sections (Q : Type u) [CommRing Q]
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (hs : Function.Injective (fun x : Q ↦ s * x))
    (E : Type u) [NormedField E] [IsUltrametricDist E]
    (Z : Scheme.{u}) (t : Spec (.of Q) ⟶ Z) [WeaklyEtale t] :
    ∃ c : principalContinuousCoefficientSections E Z (Scheme.ProEt.mk t) ≃+*
        principalContinuousCoefficientSections E Z
          (Scheme.ProEt.mk (normalPrincipalOpenInclusion Q s ≫ t)),
      (∀ a, c a = principalContinuousCoefficientObjectRestriction E
        (MorphismProperty.Over.homMk (normalPrincipalOpenInclusion Q s)) a) ∧
      (∀ a, principalContinuousCoefficientRealization E Z
          (Scheme.ProEt.mk (normalPrincipalOpenInclusion Q s ≫ t)) (c a) =
        (principalContinuousCoefficientRealization E Z (Scheme.ProEt.mk t) a).comp
          (normalPrincipalOpenInclusion Q s).base.hom) := by
  sorry

/-- Restriction and its inverse commute with every morphism of normal affine pairs.
The quantified ring equivalences are exactly those normalized by actual restriction.
Source: the elementary composition and uniqueness argument of node step 6
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof: v composed with i' equals i composed with v_s. Associativity of precomposition
gives the forward square. For an a on X_s, both extensions appearing in the inverse
square restrict on X'_{s'} to a composed with v_s. Injectivity of restriction for Q'
(normal_principal_open_continuous_sections) makes the extensions equal. The open
preimage condition says exactly that v is a morphism of the specified pairs; empty pairs
and identity opens satisfy the same composition and uniqueness argument. -/
theorem normal_principal_open_continuous_sections_natural
    (Q Q' : Type u) [CommRing Q] [CommRing Q']
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hnormal' : ∀ (p : Ideal Q') [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (s' : Q')
    (hs : Function.Injective (fun x : Q ↦ s * x))
    (hs' : Function.Injective (fun x : Q' ↦ s' * x))
    (E : Type u) [NormedField E] [IsUltrametricDist E]
    (v : Spec (.of Q') ⟶ Spec (.of Q))
    (vs : Spec (.of (Localization.Away s')) ⟶ Spec (.of (Localization.Away s)))
    (hv : normalPrincipalOpenInclusion Q' s' ≫ v = vs ≫ normalPrincipalOpenInclusion Q s)
    (hopen : v ⁻¹' Set.range (normalPrincipalOpenInclusion Q s) =
      Set.range (normalPrincipalOpenInclusion Q' s'))
    (r : C(Spec (.of Q), E) ≃+* C(Spec (.of (Localization.Away s)), E))
    (r' : C(Spec (.of Q'), E) ≃+* C(Spec (.of (Localization.Away s')), E))
    (hr : ∀ a, r a = a.comp (normalPrincipalOpenInclusion Q s).base.hom)
    (hr' : ∀ a, r' a = a.comp (normalPrincipalOpenInclusion Q' s').base.hom) :
    (∀ a, r' (a.comp v.base.hom) = (r a).comp vs.base.hom) ∧
    (∀ a, (r.symm a).comp v.base.hom = r'.symm (a.comp vs.base.hom)) := by
  sorry

/-- Global coefficient restriction and its inverse are natural for the same affine pairs.
Source: Hemo--Richarz--Scholbach, Example 3.1; node steps 5--6
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof: the normalized continuous realization intertwines each of the four actual
coefficient maps with function precomposition (node step 5). Apply
normal_principal_open_continuous_sections_natural to the function restrictions.
Transport both its forward and inverse equalities back along the canonical realizations.
Equivalently, the forward square is point-pullback composition coherence and the inverse
square follows by injectivity of restriction for Q'. No choice of a different coefficient
map is made: hc and hc' specify exactly the actual mates on global sections. -/
theorem normal_principal_open_coefficient_sections_natural
    (Q Q' : Type u) [CommRing Q] [CommRing Q']
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hnormal' : ∀ (p : Ideal Q') [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (s' : Q')
    (hs : Function.Injective (fun x : Q ↦ s * x))
    (hs' : Function.Injective (fun x : Q' ↦ s' * x))
    (E : Type u) [NormedField E] [IsUltrametricDist E]
    (v : Spec (.of Q') ⟶ Spec (.of Q))
    (vs : Spec (.of (Localization.Away s')) ⟶ Spec (.of (Localization.Away s)))
    (hv : normalPrincipalOpenInclusion Q' s' ≫ v = vs ≫ normalPrincipalOpenInclusion Q s)
    (hopen : v ⁻¹' Set.range (normalPrincipalOpenInclusion Q s) =
      Set.range (normalPrincipalOpenInclusion Q' s'))
    (c : principalContinuousCoefficientSections E (Spec (.of Q))
          (Scheme.ProEt.mk (𝟙 (Spec (.of Q)))) ≃+*
        principalContinuousCoefficientSections E (Spec (.of (Localization.Away s)))
          (Scheme.ProEt.mk (𝟙 (Spec (.of (Localization.Away s))))))
    (c' : principalContinuousCoefficientSections E (Spec (.of Q'))
          (Scheme.ProEt.mk (𝟙 (Spec (.of Q')))) ≃+*
        principalContinuousCoefficientSections E (Spec (.of (Localization.Away s')))
          (Scheme.ProEt.mk (𝟙 (Spec (.of (Localization.Away s'))))))
    (hc : ∀ a, c a = principalContinuousCoefficientGlobalRestriction E
      (normalPrincipalOpenInclusion Q s) a)
    (hc' : ∀ a, c' a = principalContinuousCoefficientGlobalRestriction E
      (normalPrincipalOpenInclusion Q' s') a) :
    (∀ a, c' (principalContinuousCoefficientGlobalRestriction E v a) =
      principalContinuousCoefficientGlobalRestriction E vs (c a)) ∧
    (∀ a, principalContinuousCoefficientGlobalRestriction E v (c.symm a) =
      c'.symm (principalContinuousCoefficientGlobalRestriction E vs a)) := by
  sorry

/-- Evaluation bijections and their inverses are natural inside every ambient site's normal
principal-open pairs. The over-morphisms f and fs are the given maps of pairs over Z.
Source: Hemo--Richarz--Scholbach, Example 3.1; node steps 5--6
(blueprint: lem-sfb-normal-principal-open-continuous-sections).

Proof: naturality of the actual sheaf restrictions gives the forward square from hv.
For a section on X_s, the two inverse-square sections on X' restrict to the same section
on X'_{s'}. Injectivity of the evaluation restriction, from
normal_principal_open_coefficient_object_sections for Q', makes them equal.
The normalized comparison identifies this with the same function argument as for global
sections. Both arguments include empty objects and identity principal opens. -/
theorem normal_principal_open_coefficient_object_sections_natural
    (Q Q' : Type u) [CommRing Q] [CommRing Q']
    (hnormal : ∀ (p : Ideal Q) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hnormal' : ∀ (p : Ideal Q') [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : Q) (s' : Q')
    (hs : Function.Injective (fun x : Q ↦ s * x))
    (hs' : Function.Injective (fun x : Q' ↦ s' * x))
    (E : Type u) [NormedField E] [IsUltrametricDist E]
    (Z : Scheme.{u}) (t : Spec (.of Q) ⟶ Z) (t' : Spec (.of Q') ⟶ Z)
    [WeaklyEtale t] [WeaklyEtale t']
    (f : Scheme.ProEt.mk t' ⟶ Scheme.ProEt.mk t)
    (fs : Scheme.ProEt.mk (normalPrincipalOpenInclusion Q' s' ≫ t') ⟶
      Scheme.ProEt.mk (normalPrincipalOpenInclusion Q s ≫ t))
    (hv : normalPrincipalOpenInclusion Q' s' ≫ f.left =
      fs.left ≫ normalPrincipalOpenInclusion Q s)
    (hopen : f.left ⁻¹' Set.range (normalPrincipalOpenInclusion Q s) =
      Set.range (normalPrincipalOpenInclusion Q' s'))
    (c : principalContinuousCoefficientSections E Z (Scheme.ProEt.mk t) ≃+*
      principalContinuousCoefficientSections E Z
        (Scheme.ProEt.mk (normalPrincipalOpenInclusion Q s ≫ t)))
    (c' : principalContinuousCoefficientSections E Z (Scheme.ProEt.mk t') ≃+*
      principalContinuousCoefficientSections E Z
        (Scheme.ProEt.mk (normalPrincipalOpenInclusion Q' s' ≫ t')))
    (hc : ∀ a, c a = principalContinuousCoefficientObjectRestriction E
      (MorphismProperty.Over.homMk (normalPrincipalOpenInclusion Q s)) a)
    (hc' : ∀ a, c' a = principalContinuousCoefficientObjectRestriction E
      (MorphismProperty.Over.homMk (normalPrincipalOpenInclusion Q' s')) a) :
    (∀ a, c' (principalContinuousCoefficientObjectRestriction E f a) =
      principalContinuousCoefficientObjectRestriction E fs (c a)) ∧
    (∀ a, principalContinuousCoefficientObjectRestriction E f (c.symm a) =
      c'.symm (principalContinuousCoefficientObjectRestriction E fs a)) := by
  sorry

end AlgebraicGeometry.ProEtale
