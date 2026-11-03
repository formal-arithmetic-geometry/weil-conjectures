/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison

/-! # Scalar-perfect stratifications under coefficient isomorphisms -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Ω] [IsCommMonObj Ω]

/-- Scalar restriction along a coefficient isomorphism preserves locally
constant perfect scalar complexes.
Source: blueprint internal-Hom proof, coefficient identifications in paragraph 1
(blueprint: lem-sfb-scalar-perfect-coefficient-iso).

Proof: use the same trivializing cover. Apply point scalar restriction
to the entire complex, including its differentials. Exactness preserves its bounds;
regular-module comparison and finite sums carry each finite-free retract to a finite-free
retract. The natural pullback/scalar-restriction comparison identifies the realized complex
on every chart. Zero rings, zero complexes and empty schemes are included. -/
theorem scalarPerfect_comap (φ : Ω ⟶ Λ) [IsMonHom φ] [IsIso φ]
    (X : Scheme.{u}) (K : DerivedCategory (supportModules Λ X))
    (hK : IsLocallyConstantPerfectComplex Λ X K) :
    IsLocallyConstantPerfectComplex Ω X
      ((Mod.comap (coefficientMap φ X)).mapDerivedCategory.obj K) := by
  obtain ⟨U, hU⟩ := hK
  let C := Mod.comap (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) φ
  have : C.IsEquivalence := (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨F, ⟨b, c, hb⟩, hF, hG, ⟨eF⟩⟩ := hU i
  let G := upperStarFromPointMod Λ (U.X i)
  let H := upperStarFromPointMod Ω (U.X i)
  have : ((upperStarFromPoint (U.X i)).mapMod Λ).Additive := inferInstanceAs G.Additive
  have : PreservesFiniteLimits ((upperStarFromPoint (U.X i)).mapMod Λ) :=
    inferInstanceAs (PreservesFiniteLimits G)
  have : PreservesFiniteColimits ((upperStarFromPoint (U.X i)).mapMod Λ) :=
    inferInstanceAs (PreservesFiniteColimits G)
  have : ((upperStarFromPoint (U.X i)).mapMod Ω).Additive := inferInstanceAs H.Additive
  have : PreservesFiniteLimits ((upperStarFromPoint (U.X i)).mapMod Ω) :=
    inferInstanceAs (PreservesFiniteLimits H)
  have : PreservesFiniteColimits ((upperStarFromPoint (U.X i)).mapMod Ω) :=
    inferInstanceAs (PreservesFiniteColimits H)
  let D := Mod.comap (D := Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
    (coefficientMap φ (U.X i))
  have : G.PreservesZeroMorphisms := hG
  let P := (C.mapHomologicalComplex (.up ℤ)).obj F
  refine ⟨P, ⟨b, c, fun n hn ↦ C.map_isZero (hb n hn)⟩, ?_, inferInstance, ⟨?_⟩⟩
  · intro n
    obtain ⟨m, j, p, hjp⟩ := hF n
    let r : Retract (F.X n) (Mod.finiteFree Λ m) := ⟨j, p, hjp⟩
    let t := (r.map C).trans (Retract.ofIso (Mod.finiteFreeIsoComap φ m))
    exact ⟨m, t.i, t.r, t.retract⟩
  · exact ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (comapUpperStarIso φ (U.f i)).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
      D.mapDerivedCategory.mapIso eF ≪≫
      D.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app F).symm ≪≫
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso ((upperStarFromPoint (U.X i)).mapModComapIso φ).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _).app (DerivedCategory.Q.obj F) ≪≫
      H.mapDerivedCategory.mapIso (C.mapDerivedCategoryFactors.app F) ≪≫
      H.mapDerivedCategoryFactors.app P


end AlgebraicGeometry.ProEtale.CondensedRing
