module

public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Sheaf.AlgebraicGeometry.AssociatedPoints
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Uncontracted normalized tower recovery tests

Source: ILO, Travaux de Gabber, VIII 2.1.18--2.1.20, 2.2.5--2.2.12 and proof of
3.4.15, printed pp.89--91,114; Stacks Tag 04HX for the pointed strict local ring.
(blueprint: def-per-normalized-tower-recovery-tests).

These are comparison data, not a choice of a normalized blowup or a base-change theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Monoscheme.NormalizedTower

/-- The union of images of associated points of the actual closed center schemes.
Their local rings are precisely the quotients by the ideal-center stalks.
Source: ILO VIII 2.1.19 and 2.2.12
(blueprint: def-per-normalized-tower-recovery-tests). -/
def associatedCenterImages {n : ℕ} (T : NormalizedTower.{u} n) : Set (T.level 0) :=
  ⋃ i : Fin n, (fun z : (T.center i).subscheme ↦
    T.toFirst i.castSucc ((T.center i).subschemeι z)) ''
      AlgebraicGeometry.associatedPoints (T.center i).subscheme

/-- Equality of uncontracted centered towers over a base includes equality of their
lengths and a center-preserving isomorphism over that base. The transport only changes
finite index types; it never contracts a stage.
Source: ILO VIII 2.2.3--2.2.5, 2.2.12
(blueprint: def-per-normalized-tower-recovery-tests). -/
def SameOver {X : Scheme.{u}} {n m : ℕ}
    (T : NormalizedTower.{u} n) (S : NormalizedTower.{u} m)
    (bT : T.level 0 ⟶ X) (bS : S.level 0 ⟶ X) : Prop :=
  ∃ h : n = m, ∃ E : CenterIso T (h.symm ▸ S),
    (E.iso 0).hom ≫ eqToHom (by cases h; rfl) ≫ bS = bT

/-- A scheme-theoretic uncontracted pullback, with all centers extended along the
cartesian comparison and its base identification fixed over the prescribed map.
Source: ILO VIII 2.2.7--2.2.8
(blueprint: def-per-normalized-tower-recovery-tests). -/
structure PullbackOver {X Y : Scheme.{u}} {n : ℕ} (T : NormalizedTower.{u} n)
    (b : T.level 0 ⟶ X) (f : Y ⟶ X) where
  tower : NormalizedTower.{u} n
  baseIso : tower.level 0 ≅ Y
  comparison : CenterMap tower T
  cartesian : comparison.IsCartesian
  overBase : comparison.map 0 ≫ b = baseIso.hom ≫ f

end AlgebraicGeometry.Monoscheme.NormalizedTower

namespace AlgebraicGeometry.Scheme

/-- The completion of the recorded geometric strict local ring at the kernel of its
canonical geometric evaluation. That kernel is its maximal ideal (Stacks Tag 04HX).
This presentation avoids choosing a second local-ring structure on the colimit.
Source: ILO VIII proof of 3.4.15, p.114; Stacks Tag 04HX
(blueprint: def-per-normalized-tower-recovery-tests). -/
def towerTestCompletedStrictRing {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) : Type u :=
  AdicCompletion (RingHom.ker (strictHenselizationPointEvaluation s))
    (strictHenselizationRing s)

/-- The ring structure is the ordinary componentwise ring structure of adic completion.
Source: ILO VIII proof of 3.4.15, p.114
(blueprint: def-per-normalized-tower-recovery-tests). -/
instance towerTestCompletedStrictRingCommRing {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    CommRing (towerTestCompletedStrictRing s) :=
  inferInstanceAs (CommRing (AdicCompletion
    (RingHom.ker (strictHenselizationPointEvaluation s)) (strictHenselizationRing s)))

/-- The actual completed strict local scheme maps to X by Spec of the completion map
followed by the already recorded structural map of the strict henselization.
Source: ILO VIII proof of 3.4.15, p.114
(blueprint: def-per-normalized-tower-recovery-tests). -/
def towerTestCompletedStrictMap {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Spec (.of (towerTestCompletedStrictRing s)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (strictHenselizationRing s)
    (AdicCompletion (RingHom.ker (strictHenselizationPointEvaluation s))
      (strictHenselizationRing s)))) ≫ strictHenselizationStructuralMap s

/-- The structural map to Spec Z, with an explicit universe lift of Z.
Source: ILO VIII proof of 3.4.15, p.114
(blueprint: def-per-normalized-tower-recovery-tests). -/
def towerTestIntegerMap (X : Scheme.{u}) : X ⟶ Spec (.of (ULift.{u} ℤ)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((Int.castRingHom Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom))

/-- The rational localization projection, defined as a scheme pullback over Spec Z.
It is not replaced by an open subscheme.
Source: ILO VIII proof of 3.4.15, p.114
(blueprint: def-per-normalized-tower-recovery-tests). -/
def towerTestRationalMap (X : Scheme.{u}) :
    pullback (towerTestIntegerMap X)
      (Spec.map (CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Int.castRingHom ℚ).comp ULift.ringEquiv.toRingHom)))) ⟶ X :=
  pullback.fst _ _

end AlgebraicGeometry.Scheme
