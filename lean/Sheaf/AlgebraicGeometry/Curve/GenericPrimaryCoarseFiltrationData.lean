/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

public import Mathlib.GroupTheory.PGroup

import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.RepresentationTheory.SylowModuleFiltration
import Sheaf.FieldTheory.OpenSubgroupFixedField
import Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore
import Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator

/-! # Generic primary filtration with its terminal identification

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.
(blueprint: lem-sc-generic-primary-coarse-filtration-data)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace AlgebraicGeometry.IsConnectedCurve

/-- Construct the filtration together with the generic cover it filters.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.
Proof: identify M with its finite primary discrete Galois module by the abelian
sheaf/stalk equivalence. The Sylow filtration supplies an open subgroup H of
index d coprime to ell, and a full H-stable chain with trivial quotients killed
by ell. Its fixed field L is finite separable of degree d. Transport restriction
of the module and its chain to Spec L; finite bases of the quotient ZMod ell
vector spaces identify their sheaves with the displayed binary biproducts.
Extend the chain constantly after its last index. For the zero module take
n = 0, so its terminal sheaf really is zero.

Apply hmodel to L and take D to be the normalization, with pi its canonical map.
Normalization in a field is integral. The supplied isomorphism e from Spec L to
Spec D.functionField transports the entire chain, including the terminal term.
Define q by e.inv followed by Spec L -> Spec C.functionField. The compatibility
in hmodel and the normalization diagram give the displayed commuting square.
Isomorphism transport preserves finiteness, etaleness and degree d of q, and
identifies the terminal sheaf with q^* M. No retraction is asserted here.
Finally, each element of the finite primary stalk is killed by an ell power;
take the maximum of these exponents. The faithful stalk equivalence then gives
ell^e times the identity of M equal to zero. Repeated terms have dimension-zero
quotients, and the zero sheaf may use exponent zero.
(blueprint: lem-sc-generic-primary-coarse-filtration-data) -/
theorem exists_generic_primary_coarse_filtration_data
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup ℓ (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (D : Scheme.{u}) (π : D ⟶ C), IsFinite π ∧
      IsConnectedCurve (π ≫ f) ∧ Smooth (π ≫ f) ∧ IsAffine D ∧
      ∃ hIntegral : IsIntegral D,
      letI : IsIntegral D := hIntegral;
      ∃ (n : ℕ) (F : ℕ → Sheaf (Spec D.functionField).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        IsZero (F 0) ∧
        (∀ (a : ℕ), a < n →
          ∃ (S : ShortComplex (Sheaf (Spec D.functionField).smallEtaleTopology
              AddCommGrpCat.{u + 1})) (d : ℕ),
            S.ShortExact ∧ Nonempty (S.X₁ ≅ F a) ∧
              Nonempty (S.X₂ ≅ F (a + 1)) ∧
              Nonempty (S.X₃ ≅ Nat.rec (0 : _)
                (fun _ A ↦ A ⊞ (Spec D.functionField).constantZMod ℓ) d)) ∧
        ∃ (q : Spec D.functionField ⟶ Spec C.functionField),
          q ≫ C.fromSpecFunctionField = D.fromSpecFunctionField ≫ π ∧
          Etale q ∧
          ∃ (d : ℕ), q.IsFiniteLocallyFreeOfDegree d ∧ d.Coprime ℓ ∧
          ∃ (e : ℕ), (ℓ ^ e) • 𝟙 M = 0 ∧
            Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} q).obj M ≅ F n) := by
  obtain ⟨D, π, hπ, hconn, hsmooth, haff, hIntegral, n, F, hzero, hchain,
    q, hsquare, hqetale, d, hdegree, hcop, hterm⟩ :=
    exists_generic_primary_coarse_filtration_core f hmodel M ℓ hℓ hfinite hprimary
  obtain ⟨e, hkill⟩ := exists_primary_annihilator f M ℓ hℓ hfinite hprimary
  exact ⟨D, π, hπ, hconn, hsmooth, haff, hIntegral, n, F, hzero, hchain,
    q, hsquare, hqetale, d, hdegree, hcop, e, hkill, hterm⟩

end AlgebraicGeometry.IsConnectedCurve
