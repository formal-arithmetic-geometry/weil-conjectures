/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import Mathlib.Algebra.Category.ModuleCat.Biproducts
/-! # Finite native lisse fibres and their local Frobenius modules

Source: the local finite-rank calculation in lem-wf-envelope-real.
(blueprint: lem-wf-envelope-real-native-fibre-finite)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeEnvelope
/-- Native scalar fibres of lisse coefficient modules are finite dimensional.
Source: lem-wf-envelope-real, finite-rank local calculation;
lem-zl-condensed-lisse-fibres-finite, finite-free-cover proof.
(blueprint: lem-wf-envelope-real-native-fibre-finite).

Proof: lift the algebraically closed point through a member of a finite-free
trivializing pro-etale cover. Pull the chosen free model to the point, using the
pullback composition isomorphism. Actual unit sections are additive, so preserve the
finite biproduct of coefficient units. Identify each unit's sections with the lifted
coefficient field. This gives coordinates K^r on the native fibre and transports
finite dimensionality. This includes r = 0. -/
theorem native_fibre_finite
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (L : NativeCondensedModule.Modules l T)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L)
    (z : Spec (.of D.k) ⟶ T) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D L z) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨U, hU⟩ := hL
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale z
  subst z
  have hfree := (hU i).map
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l) g)
  have hcomp := hfree.of_iso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g (U.f i)).app L).symm
  obtain ⟨r, ⟨e⟩⟩ := hcomp
  let H := NativeCondensedModule.pointSections l D.k
  have : H.Additive := by
    dsimp [H, NativeCondensedModule.pointSections]
    infer_instance
  let R := condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k))
  let eV := H.mapIso e ≪≫ H.mapBiproduct (fun _ : Fin r => Mod.regular R) ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin r => H.obj (Mod.regular R))
  let d := eV.toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun _ : Fin r =>
      (NativeCondensedModule.pointSectionsUnitIso l D.k).symm.toLinearEquiv)
  exact LinearEquiv.finiteDimensional d.symm

/-- The native transport used as the local Frobenius field.
Source: the local Frobenius operator definition
(blueprint: def-wf-envelope-real-native-local-transport). -/
def localFrobeniusTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    NativeCondensedModule.fibre l D M.carrier
      (NativeCondensedModule.localClosedPoint D X₀ x i hi) ≅
      NativeCondensedModule.fibre l D M.carrier
        (NativeCondensedModule.localClosedPoint D X₀ x i hi) :=
  NativeCondensedModule.transport l D (D.geometricFrobenius X₀).hom M.carrier M.str
    (NativeCondensedModule.localClosedPoint D X₀ x i hi)
    (NativeCondensedModule.localClosedPoint D X₀ x i hi)
    (NativeCondensedModule.localClosedPointDegree D X₀ x - 1)
    (NativeCondensedModule.localClosedPoint_return D X₀ x i hi)

/-- The concrete Frobenius module on the native scalar fibre of a lisse Weil module.
Finite dimensionality is a proved property, and the automorphism is the existing
native transport. No vector space or automorphism is selected by existence.
Source: local-factor calculation of lem-wf-envelope-real.
(blueprint: def-wf-envelope-real-native-local-module). -/
def localFrobeniusModule
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    FrobeniusModule.{u + 1, u + 1} (ULift.{u + 1} (PadicAlgCl l)) := by
  let V := NativeCondensedModule.fibre l D M.carrier
    (NativeCondensedModule.localClosedPoint D X₀ x i hi)
  letI : AddCommGroup V :=
    (NativeCondensedModule.fibre l D M.carrier
      (NativeCondensedModule.localClosedPoint D X₀ x i hi)).isAddCommGroup
  letI : Module (ULift.{u + 1} (PadicAlgCl l)) V :=
    (NativeCondensedModule.fibre l D M.carrier
      (NativeCondensedModule.localClosedPoint D X₀ x i hi)).isModule
  exact {
    carrier := V
    finiteDimensional := native_fibre_finite l D M.carrier hM _
    frobenius := (localFrobeniusTransport D l X₀ M x i hi).toLinearEquiv }


/-- The concrete module uses exactly the native transport as its Frobenius isomorphism.
This transport-level equality is the cheap bridge used by the reality proof; the
irreducible public `closedOperator` wrapper is unfolded only at its final goal.
Source: the local Frobenius operator definition
(blueprint: def-weil-local-frobenius-trace). -/
private theorem localFrobeniusModule_frobenius_transport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (localFrobeniusModule D l X₀ M hM x i hi).frobenius =
      (NativeCondensedModule.transport l D (D.geometricFrobenius X₀).hom
        M.carrier M.str (NativeCondensedModule.localClosedPoint D X₀ x i hi)
        (NativeCondensedModule.localClosedPoint D X₀ x i hi)
        (NativeCondensedModule.localClosedPointDegree D X₀ x - 1)
        (NativeCondensedModule.localClosedPoint_return D X₀ x i hi)).toLinearEquiv := by
  rfl

/-- Eigenvalues of the concrete Frobenius module are eigenvalues of its native transport.
The explicit fibre instances in `localFrobeniusModule` make this conversion a direct
rewrite, with no cross-instance transfer in downstream proofs.
Source: the local Frobenius operator definition
(blueprint: lem-wf-envelope-real-native-local-module-frobenius-transport). -/
theorem localFrobeniusModule_hasEigenvalue_transport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    {α : ULift.{u + 1} (PadicAlgCl l)}
    (hα : (localFrobeniusModule D l X₀ M hM x i hi).frobeniusEnd.HasEigenvalue α) :
    Module.End.HasEigenvalue
      (ModuleCat.Hom.hom ((NativeCondensedModule.transport l D
        (D.geometricFrobenius X₀).hom M.carrier M.str
        (NativeCondensedModule.localClosedPoint D X₀ x i hi)
        (NativeCondensedModule.localClosedPoint D X₀ x i hi)
        (NativeCondensedModule.localClosedPointDegree D X₀ x - 1)
        (NativeCondensedModule.localClosedPoint_return D X₀ x i hi)).hom)) α := by
  change Module.End.HasEigenvalue
    ((localFrobeniusModule D l X₀ M hM x i hi).frobenius.toLinearMap) α at hα
  rw [localFrobeniusModule_frobenius_transport D l X₀ M hM x i hi] at hα
  simpa only [CategoryTheory.Iso.toLinearMap_toLinearEquiv] using hα

/-- The transport eigenvalue is the eigenvalue of the published closed operator.
Only the two named operator wrappers are unfolded, so this bridge is independent of
the Frobenius-module record reduction.
Source: the local Frobenius operator definition
(blueprint: lem-wf-envelope-real-native-local-module-closed-operator-bridge). -/
theorem localTransport_hasEigenvalue_closedOperator
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    {α : ULift.{u + 1} (PadicAlgCl l)}
    (hα : Module.End.HasEigenvalue
      (ModuleCat.Hom.hom (localFrobeniusTransport D l X₀ M x i hi).hom) α) :
    Module.End.HasEigenvalue (NativeL2.closedOperator D l X₀ M x i hi).hom α := by
  rw [NativeL2.closedOperator, NativeCondensedModule.operator]
  exact hα

end WeilConjectures.NativeEnvelope
