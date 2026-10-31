/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationUnitTranspose
public import WeilConjectures.AlgebraicGeometry.FiniteSiteCoordinates
import WeilConjectures.AlgebraicGeometry.OrderedTateExponentPullback
import WeilConjectures.AlgebraicGeometry.OrderedAffineTraceExponent

/-! # Root-power naturality of the ordinary affine integration transpose

Source: blueprint latest, sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, ordinary affine-counit adjunct;
ordinary ordered-affine counit transition in integration-exponent-transpose-transport,
Steps 6--9, and adjunction source naturality in Step 11.
(blueprint: lem-pur-affine-transpose-exponent-transition)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart

open AffineLinePurity AffineSpacePurity VectorIntegrationSite

set_option maxHeartbeats 800000 in
-- Elaborating the two geometric trace presentations needs a larger local allowance.
private theorem affineTransposeRaw_transition (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    (d r s : ℕ) (hrs : r ≤ s)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0) :
    (comparison (Ring P) (affineTraceTower T d)).map
        (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
          (affineTraceTower T d) (primeUnit P _ (affineTraceProjection T d ≫ aT))
          r s hrs hr hs d).hom ≫ affineTransposeRaw P T aT d r hr =
      affineTransposeRaw P T aT d s hs := by
  let A := Ring P
  let Nr := P.coefficients.l ^ (r + 1)
  let Ns := P.coefficients.l ^ (s + 1)
  have hNr : 0 < Nr := pow_pos P.coefficients.prime.out.pos _
  have hNs : 0 < Ns := pow_pos P.coefficients.prime.out.pos _
  let hT := primeUnit P T aT
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
  let v := (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
    T hT r s hrs hr hs d).hom
  let w := (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
    (affineTraceTower T d) (primeUnit P _ (f ≫ aT)) r s hrs hr hs d).hom
  let z := cs.hom ≫ U.map v ≫ cr.inv
  let er := Etale.affineLinearCompactComparison Nr hNr A hr T hTr d
  let es := Etale.affineLinearCompactComparison Ns hNs A hs T hTs d
  have hb : U.map v ≫ br.hom = bs.hom ≫ w :=
    baseExponentComparison_pullback P.coefficients.l P.extension (P.level - 1)
      f hT r s hrs hr hs tr ts d
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
    affineTraceCounit_exponentTransition P.coefficients.l P.extension (P.level - 1)
      T hT r s hrs hr hs tr Dr ts Ds d
  have he : R.map w ≫
        (R.map (br.inv ≫ cr.inv) ≫ er.inv ≫
          Etale.affineTraceCounit A Nr hr tr Dr T hTr d) =
      R.map (bs.inv ≫ cs.inv) ≫ es.inv ≫
        Etale.affineTraceCounit A Ns hs ts Ds T hTs d := by
    rw [← R.map_comp_assoc, hz, R.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hk, ht]
  unfold affineTransposeRaw
  dsimp only
  rw [← Functor.map_comp, ← Adjunction.homEquiv_naturality_left]
  apply congrArg
  apply congrArg
  exact he

private theorem transport_transition {I : Type*} (C : I → Type*)
    [∀ i, Category (C i)] (A B Z : ∀ i, C i) (v : ∀ i, A i ⟶ B i)
    {i j : I} (h : i = j) {a : B i ⟶ Z i} {b : A i ⟶ Z i}
    {a' : B j ⟶ Z j} {b' : A j ⟶ Z j}
    (ha : HEq a' a) (hb : HEq b' b) (w : v i ≫ a = b) : v j ≫ a' = b' := by
  cases h
  cases eq_of_heq ha
  cases eq_of_heq hb
  exact w

set_option maxHeartbeats 800000 in
-- Transporting the geometric dependent morphism families needs a larger local allowance.
/-- Root-power transition of the ordinary ordered affine integration adjunct.
Source: blueprint thm-amb-vector-bundle-purity.proof.md, ordinary affine-counit
adjunct, and integration-exponent-transpose-transport, Steps 6--9 and 11.
(blueprint: lem-pur-affine-transpose-exponent-transition).

Proof: apply affineTraceCounit_exponentTransition to the canonical normalized
projective data. The coefficient pullback equation baseExponentComparison_pullback
identifies the conjugated tower transition with the coefficient transition on the
tower. Naturality of the bounded-below compact-support comparison moves that
transition through its inverse. After applying the fixed exceptional adjunction's
Hom bijection, source naturality and comparison.map_comp give the raw transpose
equation. Induction identifies the dependent pairs of tower and projection in the
two affine presentations. Transport this equation along their equality; the HEq
specifications of affineTranspose identify the two transported arrows uniquely.
The zero tower and the empty base are included, and no flatness is needed. -/
theorem affineTranspose_exponent_transition (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (d r r' : ℕ) (h : r ≤ r')
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0) :
    (comparison (Ring P) (iteratedAffineLine T d)).map
        (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
          (iteratedAffineLine T d) (primeUnit P _ (towerBase aT d))
          r r' h hA hA' d).hom ≫
      affineTranspose P T aT d r hA = affineTranspose P T aT d r' hA' := by
  let := (projection_geometry T d).2
  let I := Σ X : Scheme.{u}, {f : X ⟶ T // HasCompactification f}
  let i : I := ⟨affineTraceTower T d, affineTraceProjection T d, inferInstance⟩
  let j : I := ⟨iteratedAffineLine T d, iteratedAffineLineProj T d, inferInstance⟩
  have ht (Y : Scheme.{u}) (n : ℕ) :
      (⟨affineTraceTower Y n, affineTraceProjection Y n⟩ : Σ X : Scheme.{u}, X ⟶ Y) =
        ⟨iteratedAffineLine Y n, iteratedAffineLineProj Y n⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ Y)) ih
  have lift (X X' : Scheme.{u}) (f : X ⟶ T) (f' : X' ⟶ T)
      (hf : HasCompactification f) (hf' : HasCompactification f')
      (hh : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ T) = ⟨X', f'⟩) :
      (⟨X, f, hf⟩ : I) = ⟨X', f', hf'⟩ := by
    cases hh
    rfl
  have hij : i = j := lift _ _ _ _ _ _ (ht T d)
  let C := fun q : I ↦ DerivedCategory
    (Sheaf (Scheme.ProEt.topology q.1) (ModuleCat.{u + 1} (Ring P)))
  let B := fun (e : ℕ) (he : ((P.coefficients.l ^ (e + 1) : ℕ) : Ring P) = 0)
      (q : I) ↦ (comparison (Ring P) q.1).obj
        (Etale.affineLinearBaseCoefficient (Ring P) (P.coefficients.l ^ (e + 1)) he q.1 d)
  let Z := fun q : I ↦
    letI : HasCompactification q.2.val := q.2.property
    (comparison (Ring P) q.1).obj
      ((Etale.rightDerivedUpperShriek (Ring P) q.2.val).obj
        (Etale.ordinaryFiniteUnit (Ring P) T))
  let v := fun q : I ↦ (comparison (Ring P) q.1).map
    (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
      q.1 (primeUnit P q.1 (q.2.val ≫ aT)) r r' h hA hA' d).hom
  exact transport_transition C (B r' hA') (B r hA) Z v hij
    (affineTranspose_existsUnique P T aT d r hA).exists.choose_spec
    (affineTranspose_existsUnique P T aT d r' hA').exists.choose_spec
    (affineTransposeRaw_transition P T aT d r r' h hA hA')

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
