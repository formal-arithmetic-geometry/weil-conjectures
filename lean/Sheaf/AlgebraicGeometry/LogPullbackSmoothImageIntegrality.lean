/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.AlgebraicGeometry.SmoothTraitCurveLocalProperties
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.AlgebraicGeometry.SmoothSectionAffineCoordinates
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # Integral logarithmic pullback at smooth images

Source: Stacks, Morphisms, Tags 054L and 01UV; Algebra, Tags 00PD and 00IQ;
Duality, Tag 0E9Z; the nine-step local logarithmic-integrality argument of the DAG
(blueprint: lem-sfb-log-pullback-smooth-image-integrality).

The generic section lives in the actual dual-tensor line. Its evaluation uses the
existing dual-tensor-to-Hom map. Integrality is expressed by a neighbourhood section
with the same generic restriction, equivalently membership in the localized stalk image.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The actual coefficient homomorphism on an open chart, obtained from the structure map.
Source: Stacks, Morphisms, Tag 01UV
(blueprint: lem-sfb-log-pullback-smooth-image-integrality). -/
def nodalLogChartScalar (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The coefficient map to the actual local ring, with no arbitrary algebra structure.
Source: Stacks, Schemes, Tag 0HA1
(blueprint: lem-sfb-log-pullback-smooth-image-integrality). -/
def nodalLogStalkScalar (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The generic open of a trait family is the inverse image of D(pi).
Source: Stacks, Algebra, Tag 00PD
(blueprint: lem-sfb-log-pullback-smooth-image-integrality). -/
def nodalLogGenericOpen (R : Type u) [CommRing R] (π : R) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) : X.Opens :=
  f ⁻¹ᵁ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π)

/-- Evaluate a dual-tensor section on a smaller open using the canonical Hom comparison.
Source: Stacks, Modules, tensor-Hom evaluation, and Morphisms, Tag 01UV
(blueprint: lem-sfb-log-pullback-smooth-image-integrality). -/
def nodalLogSectionValue {X : Scheme.{u}} (L N : X.Modules)
    (U V : X.Opens) (h : V ≤ U) (s : Γ(Lᵛ ⊗ₘ N, U)) (v : Γ(L, V)) : Γ(N, V) :=
  (((Scheme.Modules.dualTensorHom L N).app U s).app (op (Over.mk (homOfLE h)))) v

/-- The explicit local algebra conclusion. The algebra structures are the specified
coefficient map and its canonical localization. The displayed logarithmic differential
is in the canonical fraction field, and is the image of the indicated integral differential.
Source: Stacks, Algebra, Tags 00PD, 00IQ, 07BK and 00RO
(blueprint: lem-sfb-log-pullback-smooth-image-integrality). -/
def NodalLogDvrDifferentials (R A : Type u) [CommRing R] [CommRing A]
    [IsLocalRing A] (r : R →+* A) (π : R) : Prop :=
  letI : Algebra R A := r.toAlgebra
  ∃ hdom : IsDomain A,
    letI : IsDomain A := hdom
    IsDiscreteValuationRing A ∧ IsLocalRing.maximalIdeal A = Ideal.span {r π} ∧
      r π ≠ 0 ∧ IsFractionRing A (Localization.Away (r π)) ∧
      IsField (Localization.Away (r π)) ∧
      ∀ a : A, a ≠ 0 → ∃ (m : ℕ) (w : Aˣ),
        a = r π ^ m * (w : A) ∧
        (algebraMap A (FractionRing A) a)⁻¹ •
            KaehlerDifferential.D R (FractionRing A) (algebraMap A (FractionRing A) a) =
          KaehlerDifferential.map R R A (FractionRing A)
            ((↑(w⁻¹) : A) • KaehlerDifferential.D R A (w : A))

/-- At a component generic point with smooth image the canonical generic logarithmic
pullback section is integral. All the local DVR, logarithmic differential and centred
marked-coordinate clauses are included. The marking may be empty, and a special-fibre
component may map into a marking. The section normalization is the equation on actual
pulled-back differentials; its Hom morphism is an isomorphism on the generic open.

Source: Stacks, Morphisms, Tags 054L and 01UV; Algebra, Tags 00PD and 00IQ; Duality,
Tag 0E9Z. This is the agent local argument, not a verbatim assertion of Tag 054L
(blueprint: lem-sfb-log-pullback-smooth-image-integrality).

Proof, following the node's nine steps:
1. Finite presentation over the Noetherian trait makes the models Noetherian. Generic
   fibre-point smoothness and the smooth-trait local dimension formula make A regular
   local of dimension one at the component generic point.
2. The fibre-stalk quotient is reduced and zero-dimensional local, hence a field.
   Its kernel is pi A, so the maximal ideal is pi A; flatness makes pi regular.
3. Krull intersection bounds the pi-divisibility of every nonzero a. Extract the largest
   power pi^m to obtain a unit w. Taking the least order in each nonzero ideal makes
   every ideal principal. Thus A is a DVR and A[1/pi] is its fraction field.
4. Relative derivations kill pi, so d(pi^m w)=pi^m dw and da/a=dw/w, in every characteristic.
5. A section meets the special fibre in a closed rational point, never a component generic
   point. The marking twist is therefore trivial at eta; the normalized fundamental class
   identifies its dualizing line there with relative differentials, including stalks.
6. At an unmarked smooth image the canonical map of relative differentials is integral;
   adjunction normalization identifies its generic restriction with the prescribed section.
7. A centred etale coordinate generates precisely the section ideal. Etale differential
   comparison makes dt a basis, so the Cartier twist has its unique frame dt/t.
8. Its pulled-back germ a is nonzero: otherwise the generic isomorphism would force the
   generic point of Spec A into the closed source marking, hence also eta, a contradiction.
   Factor a=pi^m w. The same normalized comparison sends dt/t to da/a=dw/w.
9. These regular differentials define a homomorphism of the two lines at eta, equivalently
   a germ in their dual-tensor line. Represent it on a neighbourhood and shrink until its
   generic restriction equals s. For n=0 only the unmarked case occurs; contraction to a
   marking allows m>0 and still gives a regular logarithmic differential. -/
theorem log_pullback_smooth_image_integrality
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (P Q : MultipointedCurve (Spec (.of R))) [IsHProjective P.x] [IsHProjective Q.x]
    (n : ℕ) (a : (∐ fun _ : Fin n ↦ Spec (.of R)) ≅ P.D)
    (b : (∐ fun _ : Fin n ↦ Spec (.of R)) ≅ Q.D)
    (ha : a.hom ≫ P.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of R))))
    (hb : b.hom ≫ Q.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of R))))
    (hPsmooth : ∀ z : P.D, P.i z ∈ P.x.smoothLocus)
    (hQsmooth : ∀ z : Q.D, Q.i z ∈ Q.x.smoothLocus)
    (hPnodal : HasNodalGeometricFibres P.x) (hQnodal : HasNodalGeometricFibres Q.x)
    (hPgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback P.x t) ∧ (pullback P.x t).IsPureDimension 1)
    (hQgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback Q.x t) ∧ (pullback Q.x t).IsPureDimension 1)
    (DP : MarkedNodalDualizingDegreesData P) (DQ : MarkedNodalDualizingDegreesData Q)
    (p : Q.Hom P) (hmarks : b.hom ≫ p.marking = a.hom)
    (hiso : IsIso (p.curveBaseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (s : Γ(((Scheme.Modules.tensorPullback p.curve).obj
      (markedNodalLine P DP.omega))ᵛ ⊗ₘ markedNodalLine Q DQ.omega,
        nodalLogGenericOpen R π Q.x))
    (hsiso : IsIso ((Scheme.Modules.dualTensorHom
      ((Scheme.Modules.tensorPullback p.curve).obj (markedNodalLine P DP.omega))
      (markedNodalLine Q DQ.omega)).app (nodalLogGenericOpen R π Q.x) s))
    (hs : ∀ (W : P.X.Opens) (V : Q.X.Opens) (hVW : V ≤ p.curve ⁻¹ᵁ W)
        (hVG : V ≤ nodalLogGenericOpen R π Q.x) (r : Γ(P.X, W)),
      nodalLogSectionValue
          ((Scheme.Modules.tensorPullback p.curve).obj (markedNodalLine P DP.omega))
          (markedNodalLine Q DQ.omega) (nodalLogGenericOpen R π Q.x) V hVG s
          (((Scheme.Modules.tensorPullback p.curve).obj
              (markedNodalLine P DP.omega)).presheaf.map (homOfLE hVW).op
            (((Scheme.Modules.tensorPullback p.curve).map
                (nodalLogFundamental P DP.omega DP.dualizing)).app (p.curve ⁻¹ᵁ W)
              (P.x.relativeDifferentialsPullbackGenerator p.curve W r))) =
        (markedNodalLine Q DQ.omega).presheaf.map (homOfLE hVW).op
          ((nodalLogFundamental Q DQ.omega DQ.dualizing).app (p.curve ⁻¹ᵁ W)
            (Q.x.relativeDifferentialsDerivation.d (X := op (p.curve ⁻¹ᵁ W))
              (p.curve.app W r))))
    (C : Set (Q.x.fiber (IsLocalRing.closedPoint R)))
    (hC : C ∈ irreducibleComponents (Q.x.fiber (IsLocalRing.closedPoint R)))
    (z : Q.x.fiber (IsLocalRing.closedPoint R)) (hz : IsGenericPoint z C)
    (himage : p.curve (Q.x.fiberι (IsLocalRing.closedPoint R) z) ∈ P.x.smoothLocus) :
    Q.x.fiberι (IsLocalRing.closedPoint R) z ∈ Q.x.smoothLocus ∧
      Q.x.fiberι (IsLocalRing.closedPoint R) z ∉ Set.range Q.i ∧
      NodalLogDvrDifferentials R
        (Q.X.presheaf.stalk (Q.x.fiberι (IsLocalRing.closedPoint R) z))
        (nodalLogStalkScalar R Q.x (Q.x.fiberι (IsLocalRing.closedPoint R) z)) π ∧
      (∃ (U : Q.X.Opens), Q.x.fiberι (IsLocalRing.closedPoint R) z ∈ U ∧
        ∃ e : Γ(((Scheme.Modules.tensorPullback p.curve).obj
            (markedNodalLine P DP.omega))ᵛ ⊗ₘ markedNodalLine Q DQ.omega, U),
          (((Scheme.Modules.tensorPullback p.curve).obj
              (markedNodalLine P DP.omega))ᵛ ⊗ₘ markedNodalLine Q DQ.omega).presheaf.map
              (homOfLE (inf_le_left : U ⊓ nodalLogGenericOpen R π Q.x ≤ U)).op e =
            (((Scheme.Modules.tensorPullback p.curve).obj
                (markedNodalLine P DP.omega))ᵛ ⊗ₘ markedNodalLine Q DQ.omega).presheaf.map
              (homOfLE (inf_le_right : U ⊓ nodalLogGenericOpen R π Q.x ≤
                nodalLogGenericOpen R π Q.x)).op s) ∧
      ∀ (j : Fin n) (W : P.X.affineOpens)
        (hW : W.1 ≤ P.x.smoothLocus)
        (hx : p.curve (Q.x.fiberι (IsLocalRing.closedPoint R) z) ∈ W.1)
        (hmarked : p.curve (Q.x.fiberι (IsLocalRing.closedPoint R) z) ∈
          Set.range (Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) j ≫ a.hom ≫ P.i))
        (t : Γ(P.X, W.1)),
        (Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) j ≫ a.hom ≫ P.i).ker.ideal W =
          Ideal.span {t} →
        (∀ i : Fin n, i ≠ j → Disjoint (W.1 : Set P.X)
          (Set.range (Sigma.ι (fun _ : Fin n ↦ Spec (.of R)) i ≫ a.hom ≫ P.i))) →
        Etale (W.1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
          (Polynomial.eval₂RingHom (nodalLogChartScalar R P.x W.1) t))) →
        (p.curve.stalkMap (Q.x.fiberι (IsLocalRing.closedPoint R) z))
          (P.X.presheaf.germ W.1 _ hx t) ≠ 0 ∧
        ∃ e : Γ(markedNodalLine P DP.omega, W.1),
          t • e = (nodalLogFundamental P DP.omega DP.dualizing).app W.1
            (P.x.relativeDifferentialsDerivation.d (X := op W.1) t) ∧
          (∀ (T : P.X.Opens) (hTW : T ≤ W.1),
            Function.Bijective (fun r : Γ(P.X, T) ↦
              r • (markedNodalLine P DP.omega).presheaf.map (homOfLE hTW).op e)) ∧
          ∀ (V : Q.X.Opens) (hVW : V ≤ p.curve ⁻¹ᵁ W.1)
            (hVG : V ≤ nodalLogGenericOpen R π Q.x) (v : Γ(Q.X, V)),
            v * Q.X.presheaf.map (homOfLE hVW).op (p.curve.app W.1 t) = 1 →
            nodalLogSectionValue
                ((Scheme.Modules.tensorPullback p.curve).obj (markedNodalLine P DP.omega))
                (markedNodalLine Q DQ.omega) (nodalLogGenericOpen R π Q.x) V hVG s
                (((Scheme.Modules.tensorPullback p.curve).obj
                    (markedNodalLine P DP.omega)).presheaf.map (homOfLE hVW).op
                  (Scheme.Modules.tensorPullbackSection p.curve
                    (markedNodalLine P DP.omega) W.1 e)) =
              (nodalLogFundamental Q DQ.omega DQ.dualizing).app V
                (v • Q.x.relativeDifferentialsDerivation.d (X := op V)
                  (Q.X.presheaf.map (homOfLE hVW).op (p.curve.app W.1 t))) := by
  sorry

end AlgebraicGeometry
