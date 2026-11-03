/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PointTatePullback.SignedTatePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.LinearAlgebra.Basis.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison

/-! # A basis trivializes a condensed point Tate twist

Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality,
prop-pod-degree-of-the-pairing.proof.md, final sentence, point-line sub-step.
The coefficients and signed lines are those of the condensed Poincare conventions.
The pullback arrow uses the existing root-normalized signed comparison.
(blueprint: lem-pod-point-twist-trivialization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.PurityTransport
open Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace WeilConjectures.PointTwistTrivialization

/-- The selected actual condensed ring, not a discrete substitute.
Source: coefficient list in def-pod-conventions
(blueprint: lem-pod-point-twist-trivialization). -/
abbrev coefficient (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :=
  (P.presentation c).obj P.ell

/-- The recorded signed Tate sheaf, with positive tensor powers and negative sheaf duals.
Source: sk-def-sp-tate-twist, signed powers paragraph
(blueprint: lem-pod-point-twist-trivialization). -/
abbrev line (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) (m : ℤ) :=
  CondensedRing.StrictWeilCondensed.tateLine P.ell (P.presentation c) T m

/-- Actual terminal sections of the point twist, restricted along the canonical
scalar map from Lambda(*). This is H^0 of the sheaf placed in degree zero.
Source: point sections clause and def-weil-finite-coefficient-point
(blueprint: lem-pod-point-twist-trivialization). -/
abbrev sections (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (m : ℤ) :=
  (CondensedRing.CohomologyTransport.sections (coefficient P c) P.s).obj (line P c P.s m)

/-- The morphism sending the coefficient unit to the specified global section.
The terminal-section and regular-module Hom equivalences fix its restrictions
on every object of the small pro-etale site.
Source: the map 1 maps to xi_m in the node
(blueprint: lem-pod-point-twist-trivialization). -/
def pointArrow (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (m : ℤ) (t : sections P c m) :
    Mod.regular (condensedRingObj (coefficient P c) P.s) ⟶ line P c P.s m :=
  (Mod.regularHomAddEquiv (line P c P.s m)).symm
    ((Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId P.s)
      (line P c P.s m).X).symm t)

/-- Prime invertibility inherited from the finite-field datum, for any scheme over s.
It is constructed from ell != p and the scalar map, rather than an added hypothesis.
Source: prime convention in def-pod-conventions
(blueprint: lem-pod-point-twist-trivialization). -/
@[instance_reducible] def primeInvertible (P : CondensedPoincareDualityConventions.{u})
    {T : Scheme.{u}} (a : T ⟶ P.s) (x : T) : Invertible (P.ell : T.residueField x) := by
  apply IsUnit.invertible
  simpa using (primeUnit P.datum P.ell P.different).map (a.residueFieldAlgebraMap x)

/-- The canonical identification from the recorded internal signed line to its
native root/tensor presentation.
Source: signed powers in sk-def-sp-tate-twist
(blueprint: lem-pod-point-twist-trivialization). -/
@[irreducible] def lineIdentification (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (T : Scheme.{u}) (m : ℤ) :
    CondensedRing.StrictWeilCondensed.tateLine ell c T m ≅
      CondensedRing.StrictWeilCondensed.presentationLine ell c T m :=
  CondensedRing.StrictWeilCondensed.tateLine_identification ell c T m

/-- Transport the published root-normalized comparison to the actual internal
signed Tate lines. The negative branch retains the evaluation-transpose comparison.
Source: sk-prop-sfb-cartesian-coefficients, clause (1)
(blueprint: lem-pod-point-twist-trivialization). -/
@[irreducible] def lineComparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (ell : X.residueField x)]
    [hY : ∀ y : Y, Invertible (ell : Y.residueField y)] (m : ℤ) :
    (CondensedRing.upperStar (c.obj ell) f).obj
        (CondensedRing.StrictWeilCondensed.tateLine ell c Y m) ⟶
      CondensedRing.StrictWeilCondensed.tateLine ell c X m :=
  (CondensedRing.upperStar (c.obj ell) f).map (lineIdentification ell c Y m).hom ≫
    @PointTatePullback.comparison ell _ c X Y f hX hY m ≫
      (lineIdentification ell c X m).inv

/-- Pull a unit-to-Tate-line morphism back using the canonical coefficient-unit
identification and the normalized signed-line comparison.
Source: sk-prop-sfb-cartesian-coefficients, clause (1)
(blueprint: lem-pod-point-twist-trivialization). -/
@[irreducible] def pullbackTateArrow (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (ell : X.residueField x)]
    [hY : ∀ y : Y, Invertible (ell : Y.residueField y)] (m : ℤ)
    (t : Mod.regular (condensedRingObj (c.obj ell) Y) ⟶
      CondensedRing.StrictWeilCondensed.tateLine ell c Y m) :
    Mod.regular (condensedRingObj (c.obj ell) X) ⟶
      CondensedRing.StrictWeilCondensed.tateLine ell c X m :=
  (CondensedRing.upperStarObjRegularIso (c.obj ell) f).inv ≫
    (CondensedRing.upperStar (c.obj ell) f).map t ≫
      @lineComparison ell _ c X Y f hX hY m

/-- Pull back the point morphism, identify the pulled-back coefficient unit, and
compose the canonical root-normalized signed Tate comparison. Its negative part
is the transpose of evaluation; its zeroth part is the coefficient-unit comparison.
Source: sk-prop-sfb-cartesian-coefficients, clause (1)
(blueprint: lem-pod-point-twist-trivialization). -/
@[irreducible] def pullbackArrow (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (m : ℤ) (t : sections P c m) :
    Mod.regular (condensedRingObj (coefficient P c) P.X) ⟶ line P c P.X m :=
  @pullbackTateArrow P.ell _ (P.presentation c) P.X P.s P.structureMap
    (primeInvertible P P.structureMap) (primeInvertible P (𝟙 P.s)) m (pointArrow P c m t)

attribute [local implicit_reducible] Mod.regular

-- Pullback along a section descends a local trivialization of any internal module.
private theorem splitLocalTrivial
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage (Spec (.of k)))
    (hU : ∀ i : U.I₀, Nonempty
      (((upperStar Ab.{u + 1} (U.f i)).mapMod
        (condensedRingObj Λ (Spec (.of k)))).obj M ≅ 𝟙_ _)) :
    Nonempty (M ≅ Mod.regular (condensedRingObj Λ (Spec (.of k)))) := by
  let X := Spec (.of k)
  obtain ⟨i, y, _⟩ := Scheme.Cover.exists_eq
    (U.weaken (inf_le_right : Scheme.proetalePrecoverage ≤
      Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u})))
    (IsLocalRing.closedPoint k)
  have : WeaklyEtale (U.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ ⟨i⟩
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (U.f i) y
  obtain ⟨e⟩ := hU i
  let e' : (CondensedRing.upperStar Λ (U.f i)).obj M ≅
      Mod.regular (condensedRingObj Λ (U.X i)) :=
    (Mod.extendScalars (condensedPullbackHom Λ (U.f i))).mapIso e ≪≫
      Mod.extendScalarsObjRegularIso (condensedPullbackHom Λ (U.f i))
  exact ⟨((CondensedRing.upperStarId Λ X).app _).symm ≪≫
    (CondensedRing.upperStarCongr Λ hσ.symm).app _ ≪≫
    (CondensedRing.upperStarComp Λ σ (U.f i)).app _ ≪≫
    (CondensedRing.upperStar Λ σ).mapIso e' ≪≫
    CondensedRing.upperStarObjRegularIso Λ σ⟩

-- Split a local integral basis over a geometric point, then extend coefficients.
private theorem integralTrivial (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime]
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)] :
    Nonempty (tateModule (Spec (.of k)) ell ≅
      Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell])
        (Spec (.of k)))) := by
  let X := Spec (.of k)
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[ell]
  have hunit : IsUnit (ell : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (ell : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : X.residueField x)
  obtain ⟨U, hU⟩ := tateModule_locally_trivial X ell hunit
  exact splitLocalTrivial Λ k (tateModule X ell) U hU

private theorem powerTrivial (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)]
    (n : ℕ) : Nonempty (c.line ell (Spec (.of k)) n ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := integralTrivial k ell
  let e₁ : c.firstLine ell (Spec (.of k)) ≅ 𝟙_ _ :=
    (Mod.extendScalars (coefficientMap (c.integralMap ell) (Spec (.of k)))).mapIso e ≪≫
      Mod.extendScalarsObjRegularIso _
  induction n with
  | zero => exact ⟨Iso.refl _⟩
  | succ n ih =>
      obtain ⟨v⟩ := ih
      exact ⟨tensorIso v e₁ ≪≫ λ_ _⟩

private theorem signedTrivial (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)]
    (m : ℤ) : Nonempty
      (CondensedRing.StrictWeilCondensed.tateLine ell c (Spec (.of k)) m ≅ 𝟙_ _) := by
  refine ⟨CondensedRing.StrictWeilCondensed.tateLine_identification ell c _ m ≪≫ ?_⟩
  cases m with
  | ofNat n => exact (powerTrivial k ell c n).some
  | negSucc n =>
      let e := (powerTrivial k ell c (n + 1)).some
      exact (MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ _) ≪≫
        MonoidalClosed.unitIsoSelf _

private theorem comparison_isIso (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)]
    (m : ℤ) : IsIso (PointTatePullback.comparison ell c f m) := by
  let F := CondensedRing.upperStar (c.obj ell) f
  let : F.Monoidal := CondensedRing.monoidal_upperStar (c.obj ell) f
  cases m with
  | ofNat n =>
      change IsIso ((PointTatePullback.coordinates ell c f).power n).hom
      infer_instance
  | negSucc n =>
      obtain ⟨e⟩ := powerTrivial k ell c (n + 1)
      have hcmp : IsIso ((Functor.LaxMonoidal.ihomComparison F
          (c.line ell (Spec (.of k)) (n + 1))).natTrans.app (𝟙_ _)) :=
        (Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_left F e (𝟙_ _)).mpr
          (Functor.LaxMonoidal.isIso_ihomComparison_app_unit F (𝟙_ _))
      change IsIso (_ ≫ _ ≫ _)
      refine IsIso.comp_isIso' hcmp (IsIso.comp_isIso' ?_ ?_)
      · exact ((ihom (F.obj (c.line ell (Spec (.of k)) (n + 1)))).mapIso
          (Functor.Monoidal.εIso F).symm).isIso_hom
      · exact ((MonoidalClosed.internalHom.mapIso
          ((PointTatePullback.coordinates ell c f).power (n + 1)).symm.op).app
            (𝟙_ _)).isIso_hom

private abbrev Modules
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

private abbrev Scalar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :=
  condensedScalarRing Λ

private abbrev Sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) :=
  (CondensedRing.CohomologyTransport.sections Λ X).obj L

private theorem scalarMap_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Bijective (CondensedRing.CohomologyTransport.scalarMap Λ (Spec (.of k))) := by
  let := Functor.additive_of_preserves_binary_products (upperStarFromPoint (Spec (.of k)))
  exact (InternalAbelianSheafModule.sectionGlobalEval_bijective
    (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))
    (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
    (Scheme.ProEt.isTerminalMkId _)).comp
      ((InternalAbelianSheafModule.globalMapFunctor_bijective
        (upperStarFromPoint (Spec (.of k))) (Functor.FullyFaithful.ofFullyFaithful _) Λ).comp
        (InternalAbelianSheafModule.sectionGlobalEquiv (coherentTopology Profinite.{u}) Λ
          (⊤_ Profinite.{u}) terminalIsTerminal).symm.bijective)

set_option maxHeartbeats 2000000 in
-- Comparing internal actions with concrete section modules needs additional reduction.
private theorem globalSmul_eval
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (s : Scheme.{u})
    (L : Modules Λ s)
    (σ : MonObj.Γ (condensedRingObj Λ s)) (V : s.ProEtᵒᵖ)
    (x : L.X.obj.obj V) :
    (Mod.globalSmul σ.hom L).hom.app V x =
      (InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u}
        (Scheme.ProEt.topology s) (condensedRingObj Λ s) V.unop σ) •
        (show ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology s)
          (condensedRingObj Λ s)).functor.obj L).val.obj V from x) := by
  let F := sheafToPresheaf (Scheme.ProEt.topology s) Ab.{u + 1}
  change (F.map (Mod.globalSmul σ.hom L)).app V x = _
  rw [← Mod.globalSmul_mapMod F]
  rfl

private def pointScalars
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (s : Scheme.{u}) :
    Scalar Λ →+* MonObj.Γ (condensedRingObj Λ s) := by
  letI : PreservesFiniteLimits (upperStarFromPoint s) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : (upperStarFromPoint s).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (MonObj.Γ.mapFunctor (upperStarFromPoint s)).comp
    (InternalAbelianSheafModule.sectionGlobalEquiv
      (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal).symm.toRingHom

private def arrowSectionsEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) :
    (Mod.regular (condensedRingObj Λ X) ⟶ L) ≃+ Sections Λ X L :=
  (Mod.regularHomAddEquiv L).trans
    (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId X) L.X)

set_option maxHeartbeats 2000000 in
-- Comparing internal actions with concrete section modules needs additional reduction.
private theorem arrowSectionsEquiv_smul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) :
    let := Mod.linearOfRingHom (pointScalars Λ X)
    ∀ (r : Scalar Λ) (f : Mod.regular (condensedRingObj Λ X) ⟶ L),
      arrowSectionsEquiv Λ X L (r • f) = r • arrowSectionsEquiv Λ X L f := by
  let := Mod.linearOfRingHom (pointScalars Λ X)
  dsimp only
  intro r f
  change Sheaf.unitHomEval (Scheme.ProEt.mk (𝟙 X)) (η[condensedRingObj Λ X] ≫ (r • f).hom) = _
  rw [Mod.linearOfRingHom_smul_hom]
  change (Mod.globalSmul ((pointScalars Λ X) r).hom L).hom.app
    (op (Scheme.ProEt.mk (𝟙 X))) (arrowSectionsEquiv Λ X L f) = _
  rw [globalSmul_eval]
  rfl

private theorem arrowSectionsEquiv_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {L N : Modules Λ X} (f : Mod.regular (condensedRingObj Λ X) ⟶ L) (g : L ⟶ N) :
    arrowSectionsEquiv Λ X N (f ≫ g) =
      ((CondensedRing.CohomologyTransport.sections Λ X).map g).hom
        (arrowSectionsEquiv Λ X L f) := by
  change Sheaf.unitHomEval _ (η[condensedRingObj Λ X] ≫ (f ≫ g).hom) = _
  rw [Mod.comp_hom']
  rfl

private theorem arrowSectionsEquiv_id
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    arrowSectionsEquiv Λ X (Mod.regular (condensedRingObj Λ X)) (𝟙 _) =
      (1 : CondensedRing.Evaluation.A (Scheme.ProEt.topology X)
        (condensedRingObj Λ X) (Scheme.ProEt.mk (𝟙 X))) := by
  change Sheaf.unitHomEval (Scheme.ProEt.mk (𝟙 X)) (η[condensedRingObj Λ X]) = _
  exact (InternalAbelianSheafModule.sectionGlobalEval (Scheme.ProEt.topology X)
    (condensedRingObj Λ X) (Scheme.ProEt.mk (𝟙 X))).map_one

private def regularSectionsEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    Scalar Λ ≃ₗ[Scalar Λ] Sections Λ (Spec (.of k))
      (Mod.regular (condensedRingObj Λ (Spec (.of k)))) := by
  let f : Scalar Λ →ₗ[Scalar Λ] Sections Λ (Spec (.of k))
      (Mod.regular (condensedRingObj Λ (Spec (.of k)))) :=
    { toFun := CondensedRing.CohomologyTransport.scalarMap Λ (Spec (.of k))
      map_add' := map_add _
      map_smul' := fun r s ↦ by
        change CondensedRing.CohomologyTransport.scalarMap Λ _ (r * s) =
          CondensedRing.CohomologyTransport.scalarMap Λ _ r *
            CondensedRing.CohomologyTransport.scalarMap Λ _ s
        exact map_mul _ r s }
  exact LinearEquiv.ofBijective f (scalarMap_bijective Λ k)

private theorem basisArrow_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (L : Modules Λ (Spec (.of k)))
    (v : L ≅ Mod.regular (condensedRingObj Λ (Spec (.of k))))
    (b : Module.Basis (Fin 1) (Scalar Λ) (Sections Λ (Spec (.of k)) L)) :
    IsIso ((arrowSectionsEquiv Λ (Spec (.of k)) L).symm (b 0)) := by
  let X := Spec (.of k)
  let := Mod.linearOfRingHom (pointScalars Λ X)
  let e := (regularSectionsEquiv Λ k).trans
    ((CondensedRing.CohomologyTransport.sections Λ X).mapIso v).toLinearEquiv.symm
  let r : Scalar Λ := e.symm (b 0)
  let a : Scalar Λ := b.repr (e 1) 0
  have ha : a • b 0 = e 1 := by
    simpa [a, Fin.sum_univ_succ] using b.sum_repr (e 1)
  have har : a * r = 1 := by
    have h := congrArg e.symm ha
    simpa [r, map_smul, smul_eq_mul] using h
  have he (x : Scalar Λ) :
      arrowSectionsEquiv Λ X L (x • v.inv) = e x := by
    rw [arrowSectionsEquiv_smul]
    have h := arrowSectionsEquiv_comp Λ X (𝟙 _) v.inv
    simp only [Category.id_comp, arrowSectionsEquiv_id] at h
    rw [h]
    change x • ((CondensedRing.CohomologyTransport.sections Λ X).map v.inv).hom
        (1 : CondensedRing.Evaluation.A (Scheme.ProEt.topology X)
          (condensedRingObj Λ X) (Scheme.ProEt.mk (𝟙 X))) =
      ((CondensedRing.CohomologyTransport.sections Λ X).map v.inv).hom
        (CondensedRing.CohomologyTransport.scalarMap Λ X x)
    rw [← map_smul]
    congr 1
    change CondensedRing.CohomologyTransport.scalarMap Λ X x * 1 = _
    exact mul_one _
  have ht : (arrowSectionsEquiv Λ X L).symm (b 0) = r • v.inv := by
    apply (arrowSectionsEquiv Λ X L).injective
    rw [(arrowSectionsEquiv Λ X L).apply_symm_apply, he]
    exact (e.apply_symm_apply (b 0)).symm
  let w : Mod.regular (condensedRingObj Λ X) ≅ L :=
    { hom := r • v.inv
      inv := a • v.hom
      hom_inv_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, v.inv_hom_id]
        rw [har, one_smul]
      inv_hom_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, v.hom_inv_id]
        rw [mul_comm r a, har, one_smul] }
  rw [ht]
  exact w.isIso_hom

-- Check the basis construction for an abstract ring object and module.
private theorem basisTrivialization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (L : Modules Λ (Spec (.of k)))
    (v : L ≅ Mod.regular (condensedRingObj Λ (Spec (.of k)))) :
    Nonempty (Module.Basis (Fin 1) (Scalar Λ) (Sections Λ (Spec (.of k)) L)) ∧
      ∀ b : Module.Basis (Fin 1) (Scalar Λ) (Sections Λ (Spec (.of k)) L),
        IsIso ((arrowSectionsEquiv Λ (Spec (.of k)) L).symm (b 0)) := by
  let ev := (CondensedRing.CohomologyTransport.sections Λ (Spec (.of k))).mapIso v
  let e := (regularSectionsEquiv Λ k).trans ev.toLinearEquiv.symm
  exact ⟨⟨(Module.Basis.singleton (Fin 1) (Scalar Λ)).map e⟩,
    fun b ↦ basisArrow_isIso Λ k L v b⟩

private theorem pullbackTateArrow_isIso (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)] (m : ℤ)
    (t : Mod.regular (condensedRingObj (c.obj ell) (Spec (.of k))) ⟶
      CondensedRing.StrictWeilCondensed.tateLine ell c (Spec (.of k)) m)
    (ht : IsIso t) : IsIso (pullbackTateArrow ell c f m t) := by
  have := ht
  have := comparison_isIso k ell c f m
  unfold pullbackTateArrow lineComparison
  infer_instance

/-- Every signed point Tate line has free rank-one global sections. Every basis
trivializes that sheaf, and its specified canonical pullback trivializes the line on X.

Source: latest blueprint, prop-pod-degree-of-the-pairing.proof.md, final sentence,
point-line trivialization sub-step (blueprint: lem-pod-point-twist-trivialization).

Proof.
1. Compatible roots give a pro-etale cover trivializing the first Tate line, hence
   its tensor powers and sheaf duals. At the algebraically closed point a member
   of a covering of the final object has a section. Restrict a local trivialization
   and its inverse along this section to obtain a point-sheaf isomorphism.
2. The canonical point coefficient identification gives Gamma(s,Lambda_s)=Lambda(*).
   Taking sections of this isomorphism and its inverse gives a basis e of the
   section module, indexed by Fin 1.
3. For any other basis xi, write xi=u e and e=v xi. Uniqueness of coordinates
   gives uv=vu=1. Multiplication by u followed by the original trivialization,
   and its inverse using v, are inverse sheaf-module maps. On each object they
   send 1 to the restriction of xi, so the forward map is exactly pointArrow.
4. The positive pullback comparison is the power-coordinate isomorphism. For a
   negative degree, transport its internal-Hom comparison along the positive
   point-line trivialization to the unit, where it is invertible. Its other
   factors are images of isomorphisms. Pull the basis inverse pair back along a_X
   and compose with this signed comparison and the coefficient-unit isomorphism.
   Their composite is precisely pullbackArrow, and is therefore an isomorphism.
   The argument includes m=0 and m<0 and uses no properness assumption on X.
-/
theorem pointTwistTrivialization (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (m : ℤ) :
    Nonempty (Module.Basis (Fin 1) (condensedScalarRing (coefficient P c)) (sections P c m)) ∧
      ∀ b : Module.Basis (Fin 1) (condensedScalarRing (coefficient P c)) (sections P c m),
        IsIso (pointArrow P c m (b 0)) ∧ IsIso (pullbackArrow P c m (b 0)) := by
  let : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
  let := primeInvertible P (𝟙 P.s)
  let := primeInvertible P P.structureMap
  obtain ⟨v⟩ := signedTrivial P.datum.k P.ell (P.presentation c) m
  have hb :
      Nonempty (Module.Basis (Fin 1) (condensedScalarRing (coefficient P c)) (sections P c m)) ∧
        ∀ b : Module.Basis (Fin 1) (condensedScalarRing (coefficient P c)) (sections P c m),
          IsIso (pointArrow P c m (b 0)) := by
    exact @basisTrivialization (coefficient P c) _ _ P.datum.k _ _ (line P c P.s m) v
  refine ⟨hb.1, fun b ↦ ⟨hb.2 b, ?_⟩⟩
  unfold pullbackArrow
  exact pullbackTateArrow_isIso P.datum.k P.ell (P.presentation c) P.structureMap m
    (pointArrow P c m (b 0)) (hb.2 b)

end WeilConjectures.PointTwistTrivialization
