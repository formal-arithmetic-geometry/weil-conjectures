/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.OrderedTateExponentPullback
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.OrderedAffineTraceExponent

/-! # Root transport of the trace on the affine-space coefficient

Source: the normalized affine trace calculation in projection purity agreement.
(blueprint: lem-pur-affine-base-trace-exponent)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The actual affine trace with its ordered coefficient expressed on the total
space. This is inverse coefficient descent, inverse compact-support comparison,
and the ordered counit, in that order.
Source: normalized ordinary affine trace.
(blueprint: lem-pur-affine-base-trace-exponent) -/
def affineBaseTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :=
  let tr := Etale.projectiveLineTraceTransport N hN A hA
  let Dr := Etale.projectiveLineTraceDatum N hN A hA
  let e := Etale.affineLinearCoefficientDescent A N hA tr T hT d ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback A N hA tr
      (affineTraceProjection T d) hT d
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
    (affineTraceProjection T d)).map e.inv ≫
  (Etale.affineLinearCompactComparison N hN A hA T hT d).inv ≫
    Etale.affineTraceCounit A N hA tr Dr T hT d

set_option maxHeartbeats 800000 in
-- Expanding the two specified coefficient comparisons requires additional reduction.
/-- The trace on the coefficient over the total affine space commutes with the
ordered root-power transition. This is an equation before taking any exceptional
adjunct or site comparison.

Source: the exponent-normalization step of
blueprint, sec-smooth-purity/sk-thm-smooth-purity,
`lem-pur-projection-purity-agreement.proof.md`.
(blueprint: lem-pur-affine-base-trace-exponent)

Proof: coefficient pullback commutes with the normalized root transition, so
conjugating the coefficient transition by the two total-space descents gives
the transition between the two tower coefficients. Naturality of the bounded
compact-support comparison moves it past the inverse comparison. The ordered
affine-counit exponent equation then identifies the two traces. The tower
coefficients are bounded below by affine-space top trace, which supplies the
domain needed for that naturality square. Rank zero and empty bases are included.
The algebra is the pre-adjunction part of the proof of
`VectorIntegrationChart.affineTransposeRaw_transition`; that private lemma's
module imports the parent purity agreement and cannot be imported here. -/
theorem affineBaseTrace_exponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (affineTraceProjection T d)).map
          (baseExponentComparison l E n (affineTraceTower T d)
            (by simpa using hT.map (affineTraceProjection T d).appTop.hom)
            r s hrs hr hs d).hom ≫
      affineBaseTrace _ (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hr T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d =
    affineBaseTrace _ (l ^ (s + 1)) (pow_pos (Fact.out : l.Prime).pos _) hs T
      (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) d := by
  let A := Scheme.finiteTateCoefficient l E n
  let Nr := l ^ (r + 1)
  let Ns := l ^ (s + 1)
  have hNr : 0 < Nr := pow_pos (Fact.out : l.Prime).pos _
  have hNs : 0 < Ns := pow_pos (Fact.out : l.Prime).pos _
  have hTr : IsUnit (Nr : Γ(T, ⊤)) := by
    simpa only [Nr, Nat.cast_pow] using hT.pow (r + 1)
  have hTs : IsUnit (Ns : Γ(T, ⊤)) := by
    simpa only [Ns, Nat.cast_pow] using hT.pow (s + 1)
  let tr := Etale.projectiveLineTraceTransport Nr hNr A hr
  let ts := Etale.projectiveLineTraceTransport Ns hNs A hs
  let Dr : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (Nr : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum A Nr hr tr Y hY :=
    fun Y _ hY ↦ Etale.projectiveLineTraceDatum Nr hNr A hr Y hY
  let Ds : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (Ns : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum A Ns hs ts Y hY :=
    fun Y _ hY ↦ Etale.projectiveLineTraceDatum Ns hNs A hs Y hY
  let f := affineTraceProjection T d
  let U := Etale.ordinaryFinitePullback A f
  let R := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let L := Etale.affineTraceLeft A T d
  let br := Etale.vectorIntegrationBaseCoefficientPullback A Nr hr tr f hTr d
  let bs := Etale.vectorIntegrationBaseCoefficientPullback A Ns hs ts f hTs d
  let cr := Etale.affineLinearCoefficientDescent A Nr hr tr T hTr d
  let cs := Etale.affineLinearCoefficientDescent A Ns hs ts T hTs d
  let v := (baseExponentComparison l E n T hT r s hrs hr hs d).hom
  let w := (baseExponentComparison l E n (affineTraceTower T d)
    (by simpa using hT.map f.appTop.hom) r s hrs hr hs d).hom
  let z := cs.hom ≫ U.map v ≫ cr.inv
  let er := Etale.affineLinearCompactComparison Nr hNr A hr T hTr d
  let es := Etale.affineLinearCompactComparison Ns hNs A hs T hTs d
  have hb : U.map v ≫ br.hom = bs.hom ≫ w :=
    baseExponentComparison_pullback l E n f hT r s hrs hr hs tr ts d
  have hz : w ≫ br.inv ≫ cr.inv = (bs.inv ≫ cs.inv) ≫ z := by
    calc
      w ≫ br.inv ≫ cr.inv = bs.inv ≫ (bs.hom ≫ w) ≫ br.inv ≫ cr.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = bs.inv ≫ (U.map v ≫ br.hom) ≫ br.inv ≫ cr.inv := by rw [hb]
      _ = (bs.inv ≫ cs.inv) ≫ z := by
        dsimp only [z]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have hk : R.map z ≫ er.inv = es.inv ≫ L.map z := by
    let Kr : DerivedCategory.Plus
        (Sheaf (affineTraceTower T d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨_, Exists.elim (Etale.exists_affineSpaceTopTrace Nr hNr A hr) (fun _ ht ↦
        Exists.elim ht (fun _ hD ↦ (hD.2 T hTr d).2.1))⟩
    let Ks : DerivedCategory.Plus
        (Sheaf (affineTraceTower T d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨_, Exists.elim (Etale.exists_affineSpaceTopTrace Ns hNs A hs) (fun _ ht ↦
        Exists.elim ht (fun _ hD ↦ (hD.2 T hTs d).2.1))⟩
    let c := (Etale.affineTracePlusCompatibility A T d).symm ≪≫
      Functor.isoWhiskerRight (Etale.affineTraceCompactSupportComparison A T d)
        DerivedCategory.Plus.ι ≪≫
      Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f
    change R.map z ≫ c.inv.app Kr = c.inv.app Ks ≫ L.map z
    exact c.inv.naturality (ObjectProperty.homMk (X := Ks) (Y := Kr) z)
  have ht : L.map z ≫ Etale.affineTraceCounit A Nr hr tr Dr T hTr d =
      Etale.affineTraceCounit A Ns hs ts Ds T hTs d :=
    affineTraceCounit_exponentTransition l E n T hT r s hrs hr hs tr Dr ts Ds d
  unfold affineBaseTrace
  change R.map w ≫ (R.map (br.inv ≫ cr.inv) ≫ er.inv ≫
      Etale.affineTraceCounit A Nr hr tr Dr T hTr d) =
    R.map (bs.inv ≫ cs.inv) ≫ es.inv ≫
      Etale.affineTraceCounit A Ns hs ts Ds T hTs d
  rw [← R.map_comp_assoc, hz, R.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hk, ht]

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
