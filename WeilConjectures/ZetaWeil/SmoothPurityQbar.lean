/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit

/-! # Smooth purity with condensed algebraically closed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-sp-qbar/
_section.md (blueprint: sk-thm-sp-qbar).
The coefficient is the native condensed algebraic closure; the adjunction is
supplied by the native coefficient family and its closure component.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Residue-field invertibility for the condensed coefficient constructions.
Source: blueprint sk-thm-sp-qbar, global coefficient hypotheses (blueprint: sk-thm-sp-qbar).
Proof: l is a unit of the base field k by `primeUnit` (characteristic p, l ≠ p);
its image along the residue-field algebra map is a unit. -/
@[instance_reducible] def smoothQbarResidueInvertible
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
    ∀ x, Invertible (l : T.residueField x) :=
  fun x ↦ (by
    simpa only [map_natCast] using
      (primeUnit D l hl).map ((T ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
      IsUnit (l : T.residueField x)).invertible

/-- The `SmoothDatum` record attached to ordinary scheme morphism data. -/
private def smoothQbarDatum
    (D : FiniteFieldDatum.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) : SmoothDatum D := by
  let Xo : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
  let Yo : Over (Spec (.of D.k)) := Over.mk (Y ↘ Spec (.of D.k))
  letI : LocallyOfFiniteType Xo.hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k)); infer_instance
  letI : QuasiCompact Xo.hom := by
    change QuasiCompact (X ↘ Spec (.of D.k)); infer_instance
  letI : IsSeparated Xo.hom := by
    change IsSeparated (X ↘ Spec (.of D.k)); infer_instance
  letI : LocallyOfFiniteType Yo.hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of D.k)); infer_instance
  letI : QuasiCompact Yo.hom := by
    change QuasiCompact (Y ↘ Spec (.of D.k)); infer_instance
  letI : IsSeparated Yo.hom := by
    change IsSeparated (Y ↘ Spec (.of D.k)); infer_instance
  exact { X := Xo, Y := Yo, map := f, dim := d, compactification := c }

/-- The native condensed pullback, positive Tate twist, and shift by twice the dimension.
Source: current blueprint `sk-thm-sp-qbar` (blueprint: sk-thm-sp-qbar). -/
def smoothQbarPurityRightFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :=
  Coefficient.closure.smoothSource l f d

include hl in
private theorem smoothQbar_ctf_eq_bc (T : Scheme.{u})
    [T.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] :
    property l (.closure) T =
      boundedConstructible (condensedRingObj (Coefficient.closure.obj l) T) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have h := (finiteCoefficientDescentTwoColimit D.k D.p l D.prime.pos hl.symm T).2.2.2
  exact h.2.1.2.trans h.2.1.1

include hl in
/-- The compact-support and twisted-pullback adjunction on all bounded constructible
complexes over the native condensed algebraic closure.
Source: current blueprint `sk-thm-sp-qbar` (blueprint: sk-thm-sp-qbar).

Proof: specialize the existing native coefficient family to its closure component.
The finite-descent theorem identifies the finite-Tor constructible predicate with
bounded constructibility at this coefficient. Transport both membership certificates
and the resulting restricted adjunction along that equality. The ambient functors
remain the literal proper/open compact-support functor and pullback/Tate/shift.
-/
theorem smoothPurityQbar
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) :
    ∃ (hF : ∀ K,
        boundedConstructible (condensedRingObj (Coefficient.closure.obj l) X) K →
        boundedConstructible (condensedRingObj (Coefficient.closure.obj l) Y)
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (Coefficient.closure.obj l) c).obj K))
      (hG : ∀ K,
        boundedConstructible (condensedRingObj (Coefficient.closure.obj l) Y) K →
        boundedConstructible (condensedRingObj (Coefficient.closure.obj l) X)
          ((smoothQbarPurityRightFunctor l f d).obj K)),
      Nonempty (
        (boundedConstructible (condensedRingObj (Coefficient.closure.obj l) Y)).lift
          ((boundedConstructible (condensedRingObj (Coefficient.closure.obj l) X)).ι ⋙
            CondensedRing.rightDerivedLowerShriekOfCompactification
              (Coefficient.closure.obj l) c) (fun K ↦ hF K.obj K.property) ⊣
        (boundedConstructible (condensedRingObj (Coefficient.closure.obj l) X)).lift
          ((boundedConstructible (condensedRingObj (Coefficient.closure.obj l) Y)).ι ⋙
            smoothQbarPurityRightFunctor l f d) (fun K ↦ hG K.obj K.property)) := by
  obtain ⟨N, _hBrown, _hScalar, _hBase, _hComp, _hAffine⟩ :=
    smooth_purity_transport l D hl
  let A := N .closure (smoothQbarDatum D f d c)
  have hX := smoothQbar_ctf_eq_bc D l hl X
  have hY := smoothQbar_ctf_eq_bc D l hl Y
  let adjunctionOn (PX : ObjectProperty (Coefficient.closure.derived l X))
      (PY : ObjectProperty (Coefficient.closure.derived l Y)) : Prop :=
    ∃ (hF : ∀ K, PX K → PY
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (Coefficient.closure.obj l) c).obj K))
      (hG : ∀ K, PY K → PX
        ((smoothQbarPurityRightFunctor l f d).obj K)),
      Nonempty (
        (PY).lift ((PX).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification
            (Coefficient.closure.obj l) c) (fun K ↦ hF K.obj K.property) ⊣
        (PX).lift ((PY).ι ⋙
          smoothQbarPurityRightFunctor l f d) (fun K ↦ hG K.obj K.property))
  have hA : adjunctionOn (property l (.closure) X) (property l (.closure) Y) := by
    exact ⟨A.support_closed, A.source_closed, ⟨A.adjunction⟩⟩
  exact (congrArg₂ adjunctionOn hX hY).mp hA

end WeilConjectures
