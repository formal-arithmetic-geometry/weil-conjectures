/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CanonicalAffineTowerCounitTransition
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness

/-! # Root transition of the ordered affine counit

Source: affine-space top trace, affine-line restriction and ordered tower induction.
(blueprint: lem-pur-ordered-affine-trace-exponent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The ordered affine counit commutes with the root transition conjugated by the
specified coefficient descents. There is no vector bundle or inverse-frame exchange.
Source: blueprint affine-space top trace, affine-line open triangle and ordered tower;
integration-exponent-transpose-transport, Steps 6--9; Stacks 03PK.
(blueprint: lem-pur-ordered-affine-trace-exponent).

Proof: form the morphism of Kummer sequences for ell^(s+1) and ell^(r+1), with
power ell^(s-r) on the first units term and identity on the second units term.
Boundary naturality identifies the scalar Kummer Chern classes. The normalized root
transition therefore sends the second component of the projective decomposition at
s to the component at r. Its first component commutes by adjunction-unit naturality
and normalized Tate pullback. The biproduct universal property gives the decomposition
square. Invert it and compose with the second projection to obtain the projective
trace equation. The counit normalization and naturality of the coefficient-first
projection map extend it to each input complex. Naturality of the open-extension
counit gives the affine-line counit equation. Induct along the ordered coordinate
tower: the zero counit and transition are identities. At a successor use the formula
for the composite counit, apply the previous left functor to the last line equation,
and use the induction hypothesis and counit naturality. Canonical tensor and pullback
comparisons identify the resulting transition with coefficient descent at s, then
pullback of baseExponentComparison, then inverse coefficient descent at r, exactly
as displayed. The normalization of each chosen transport and projective datum fixes
all these arrows, so arbitrary tr, Dr, ts, Ds are permitted. Empty bases, zero rank,
equal exponents and ramified coefficients need no exception or flatness assumption.
In Lean: uniqueness of normalized twist transports and projective-line data replaces
tr, ts, Dr, Ds by the canonical choices; the canonical equation is
`canonicalAffineTowerCounitTransition` (blueprint:
lem-pur-canonical-affine-tower-counit-transition), which carries the line equation and
tower induction above. -/
theorem affineTraceCounit_exponentTransition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (Dr : ∀ (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum _ (l ^ (r + 1)) hr tr Y hY)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs)
    (Ds : ∀ (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit ((l ^ (s + 1) : ℕ) : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum _ (l ^ (s + 1)) hs ts Y hY) (d : ℕ) :
    (Etale.affineTraceLeft (Scheme.finiteTateCoefficient l E n) T d).map
      ((Etale.affineLinearCoefficientDescent _ (l ^ (s + 1)) hs ts T
          (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) d).hom ≫
        (Etale.ordinaryFinitePullback _ (affineTraceProjection T d)).map
          (baseExponentComparison l E n T hT r s hrs hr hs d).hom ≫
        (Etale.affineLinearCoefficientDescent _ (l ^ (r + 1)) hr tr T
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d).inv) ≫
      Etale.affineTraceCounit _ (l ^ (r + 1)) hr tr Dr T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d =
    Etale.affineTraceCounit _ (l ^ (s + 1)) hs ts Ds T
      (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) d := by
  have htr : tr = Etale.projectiveLineTraceTransport (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hr :=
    _root_.AlgebraicGeometry.Etale.ordinaryFiniteTwistTransport_unique _ _ _ tr _
  have hts : ts = Etale.projectiveLineTraceTransport (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hs :=
    _root_.AlgebraicGeometry.Etale.ordinaryFiniteTwistTransport_unique _ _ _ ts _
  subst tr
  subst ts
  have hDr : Dr = (fun (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit ((l ^ (r + 1) : ℕ) : Γ(Y, ⊤))) =>
      Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hr Y hY) := by
    funext Y inst hY
    exact _root_.AlgebraicGeometry.Etale.ordinaryFiniteP1Datum_unique _ _ _ _ Y hY
      (Dr Y hY) _
  have hDs : Ds = (fun (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit ((l ^ (s + 1) : ℕ) : Γ(Y, ⊤))) =>
      Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hs Y hY) := by
    funext Y inst hY
    exact _root_.AlgebraicGeometry.Etale.ordinaryFiniteP1Datum_unique _ _ _ _ Y hY
      (Ds Y hY) _
  subst Dr
  subst Ds
  exact canonicalAffineTowerCounitTransition l E n T hT r s hrs hr hs d

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
