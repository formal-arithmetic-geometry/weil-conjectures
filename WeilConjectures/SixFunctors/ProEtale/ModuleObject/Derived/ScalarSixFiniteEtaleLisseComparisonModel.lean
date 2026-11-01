/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin

/-! # Scalar models of finite projective constant modules

Source: blueprint scalar-six-ctf (1), finite projective local models.
(blueprint: lem-sfb-finite-projective-constant-scalar-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- The specified finite comparison of a constant finite projective module is the
finite scalar extension of a retract of a finite free scalar module.

Source: blueprint scalar-six-ctf (1), finite ring generators; Stacks 00NX and 099Y.
(blueprint: lem-sfb-finite-projective-constant-scalar-model).

Proof: split a finite free surjection onto P using projectivity. Encode ordinary
modules as internal modules in abelian groups, then identify the scalar ring at the
one-point profinite set with the given finite coefficient ring. Both equivalences
preserve the regular module and finite sums; full faithfulness lifts the splitting
to scalar modules. The normalized constant-sheaf comparison identifies its scalar
extension with the specified finite comparison realization. Restriction along e.hom
preserves finite sums and identifies regular modules, and hence preserves the
splitting. This includes the zero ring, rank zero and the empty scheme. -/
theorem finiteProjectiveConstantScalarModel
    (T : Scheme.{u})
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (hfin : Module.Finite (ULift.{u + 1} A) P)
    (hproj : Module.Projective (ULift.{u + 1} A) P) :
    ∃ (Q : Mod Ab.{u + 1} (scalarRingObj Λ.X)) (n : ℕ),
      Nonempty (Retract Q (Mod.finiteFree (scalarRingObj Λ.X) n)) ∧
      Nonempty ((Mod.comap (coefficientMap e.hom.hom T)).obj
        ((finiteComparisonRealization A T eR).obj
          ((constantSheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)) ≅
        (finiteConstantScalarExtension Λ.X T).obj Q) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
