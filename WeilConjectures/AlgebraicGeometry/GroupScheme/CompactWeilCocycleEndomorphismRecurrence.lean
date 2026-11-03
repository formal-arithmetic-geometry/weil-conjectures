/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CompactFrobeniusTransport.CompactFrobeniusTransportComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilComplex

/-! # The compact-support Weil endomorphism recurrence

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-correspondences/sk-lem-tf-frobenius-convention/
lem-trf-frobenius-operator-compact-description.proof.md,
application of the iterated Weil map to the direct compact-support transport.
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence).

We use the ordinary finite-discrete module-sheaf presentation, as does the recorded
transport-composition dependency. Its direct transport is evaluated separately at each
power, with the same base-changed compactification throughout. No homology is applied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ)

/-- The coefficient convention's quotient, canonically lifted to the module universe.
Source: coefficient conventions, positive finite level.
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence). -/
abbrev compactWeilCoefficientRing : Type (u + 1) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing C.l E.val (n + 1))

local notation "A" => compactWeilCoefficientRing D C E n

/-- Reuse finiteness of the positive coefficient quotient, with its canonical size lift.
Source: coefficient conventions, A = O_E / varpi_E^(n+1).
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence). -/
local instance compactWeilCoefficientFinite : Finite A :=
  letI := Padic.finite_coefficientExtensionRing C.l E.val (n + 1) (Nat.succ_pos n)
  inferInstance

variable (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (c₀ : Compactification X₀.hom)
  (K : StrictWeilComplex (ModuleCat.{u + 1} A) (D.geometricFrobenius X₀))

/-- U_r is direct power transport followed by compact cohomology of the specified
Weil iterate. The representative is the base change of the retained c₀ at every r.
Only the canonical comparison between the two notations for the scheme power is inserted.
Source: compact-description proof, coefficient-complex composite.
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence). -/
def compactWeilCocycleEndomorphism (r : ℕ) (_hr : 1 ≤ r) :
    End ((CompactFrobeniusTransport.cohomology A D X₀
      (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).obj
        ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} A) _).obj K.obj)) :=
  let c := c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let M := (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} A) _).obj K.obj
  CompactFrobeniusTransport.transport A D X₀ c r M K.obj.property ≫
    (CompactFrobeniusTransport.cohomology A D X₀ c).map
      ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
        (show ((D.geometricFrobenius X₀) ^ r).hom =
          iterateHom (D.geometricFrobenius X₀).hom r from
            (Aut.toEnd _).map_pow (D.geometricFrobenius X₀) r)).hom.app M ≫
        weilDatumIterate K.frobenius.hom r)

/-- Degree one and U_(r+1) = U_1 composed with U_r, on coefficient complexes.
Degree-one transport is the same direct insertion/exchange recipe at r = 1.
The coefficient index n represents every positive level n+1.
Source: compact-description proof, application of the iterated Weil map;
steps 1--5 of this DAG node.
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence).

Proof: (1) the first Weil iterate is phi and the first direct transport is tau_c.
(2) Direct transport composition at r, using the retained c₀ and its base change c,
gives tau_r, then tau_1 at P_r K, then H(b_r), where b_r is the inverse compositor.
(3) The Weil cocycle at (1,r) identifies b_r followed by phi^[r+1] with
T(phi^[r]) followed by phi, using precisely this canonical compositor.
(4) Naturality at phi^[r] moves H(T(phi^[r])) across degree-one transport.
(5) Functoriality of H and associativity give U_r followed by U_1. Every arrow
is in the ordinary derived category of coefficient modules, before cohomology. -/
theorem compact_weil_cocycle_endomorphism_recurrence :
    compactWeilCocycleEndomorphism D C E n X₀ c₀ K 1 (Nat.le_refl 1) =
      CompactFrobeniusTransport.transport A D X₀
        (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) 1
        ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} A) _).obj K.obj) K.obj.property ≫
      (CompactFrobeniusTransport.cohomology A D X₀
        (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).map
          K.frobenius.hom ∧
    ∀ (r : ℕ) (hr : 1 ≤ r),
      compactWeilCocycleEndomorphism D C E n X₀ c₀ K (r + 1)
          (Nat.le_trans hr (Nat.le_succ r)) =
        compactWeilCocycleEndomorphism D C E n X₀ c₀ K r hr ≫
          compactWeilCocycleEndomorphism D C E n X₀ c₀ K 1 (Nat.le_refl 1) :=
  sorry

end WeilConjectures
