/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import Sheaf.Paper.ProEtaleConstantModuleEncoding
import all Sheaf.Paper.ProEtaleFiniteModelStalks
import WeilConjectures.CategoryTheory.Sites.Point.Flat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Tor amplitude of exact sections on the geometric point

Source: blueprint thm-pod-point-perfectness, Step 1; Stacks Tags 07A4, 08FZ.
(blueprint: lem-sf-point-sections-tor-amplitude).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

local instance (priority := 10000) point_siteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _

local instance point_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  inferInstance

private theorem point_evaluation_flat (k : Type u) [Field k] [IsAlgClosed k]
    (R : Type (u + 1)) [CommRing R]
    (M : Sheaf (ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} R))
    (hM : ObjectProperty.flat M) :
    ObjectProperty.flat (M.obj.obj (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  let : (ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      (ModuleCat.{u + 1} R) := inferInstance
  let x := 𝟙 (Spec (.of k))
  let I : ProEtaleGeometricNeighbourhood x :=
    StructuredArrow.mk (Y := ProEt.mk (𝟙 (Spec (.of k))))
      (𝟙 (Over.mk (𝟙 (Spec (.of k)))))
  have hI : IsInitial I := StructuredArrow.mkIdInitial
  let D := proEtaleGeometricStalkDiagram x M
  have : IsIso (colimit.ι D (op I)) := isIso_ι_of_isTerminal hI.op D
  let e : M.obj.obj (op (ProEt.mk (𝟙 (Spec (.of k))))) ≅
      ((ProEtale.geometricPoint x).sheafFiber (A := ModuleCat.{u + 1} R)).obj M :=
    asIso (colimit.ι D (op I)) ≪≫ ProEtale.geometricStalkIsoFiber x R M
  have hf : ObjectProperty.flat
      (((ProEtale.geometricPoint x).sheafFiber (A := ModuleCat.{u + 1} R)).obj M) :=
    GrothendieckTopology.Point.flat_sheafFiber_obj.{u + 2, u, u + 1}
      (A := ModuleCat.{u + 1} R) (FA := fun X Y ↦ X →ₗ[R] Y)
      (CA := fun X ↦ X) (ProEtale.geometricPoint x) hM
  exact (ObjectProperty.flat (A := ModuleCat.{u + 1} R)).prop_of_iso e.symm hf

/-- Exact final-object sections preserve the Tor interval. Test modules are arbitrary;
no constructibility or finite-generation hypothesis is imposed on K or on test modules.

Source: blueprint thm-pod-point-perfectness.proof.md, Step 1, geometric-point passage;
Stacks Tags 07A4 and 08FZ.
(blueprint: lem-sf-point-sections-tor-amplitude).

Proof: Transport the input Tor bound to the equivalent intrinsic constant-module
sheaf category. Its bounded flat-model theorem gives a flat-term representative
supported in [a,b]. After realization, restriction recovers each original term by
the counit isomorphism. Final-object evaluation preserves its flatness: the pointed
final neighbourhood is initial, so evaluation identifies with the geometric stalk,
and geometric stalks preserve flat objects. The scalar-restricted section module
has exactly this module structure. Exact sections therefore produce a flat-term
complex with the same support; the bounded flat-model Tor theorem proves the
claimed interval. Derived comparison isomorphisms transport this conclusion to K.
No finite-generation condition on terms or test modules is needed. Equal endpoints
and the zero complex are included. -/
theorem point_sections_torAmplitude (F : FiniteFieldDatum.{u})
    (A : Type u) [CommRing A] [Finite A] (K : proEtaleDerivedCategory (Spec (.of F.k)) A)
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude (Spec (.of F.k)) A K a b) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a b
      ((pointFiniteSections F.k A).mapDerivedCategory.obj K)  := by
  classical
  let Y := Spec (.of F.k)
  let R := ULift.{u + 1, u} A
  let T := pointFiniteSections F.k A
  let V := ProEtale.finiteCoefficientIntrinsicRealization Y A
  have : V.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact Y A).1
  let K₀ := V.mapDerivedCategory.objPreimage K
  let e₀ : V.mapDerivedCategory.obj K₀ ≅ K := V.mapDerivedCategory.objObjPreimageIso K
  have ht : HasProEtaleTorAmplitude Y A (V.mapDerivedCategory.obj K₀) a b := by
    refine ⟨hTor.1, ?_⟩
    intro L P hL f hf hP M i hi
    exact hTor.2 L P ⟨hL.some ≪≫ e₀⟩ f hf hP M i hi
  have ht₀ := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A Y a b hTor.1 K₀).mp ht
  obtain ⟨P, ha, hb, hp, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht₀
  let VP := (V.mapHomologicalComplex (.up ℤ)).obj P
  let ev : DerivedCategory.Q.obj VP ≅ K :=
    (V.mapDerivedCategoryFactors.app P).symm ≪≫ V.mapDerivedCategory.mapIso e ≪≫ e₀
  let Ps : CochainComplex (ModuleCat.{u + 1} R) ℤ :=
    (T.mapHomologicalComplex (.up ℤ)).obj VP
  let es : DerivedCategory.Q.obj Ps ≅ T.mapDerivedCategory.obj K :=
    (T.mapDerivedCategoryFactors.app VP).symm ≪≫ T.mapDerivedCategory.mapIso ev
  have hps (i : ℤ) : ObjectProperty.flat (Ps.X i) := by
    let U := proEtaleModuleRestriction Y A
    let q : U.obj (V.obj (P.X i)) ≅ P.X i :=
      V.preimageIso (asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)).counit.app (V.obj (P.X i))))
    have hf : ObjectProperty.flat (U.obj (V.obj (P.X i))) :=
      ObjectProperty.prop_of_iso _ q.symm (hp i)
    have he := point_evaluation_flat F.k R (U.obj (V.obj (P.X i))) hf
    let s : (U.obj (V.obj (P.X i))).obj.obj (op (ProEt.mk (𝟙 Y))) ≅ Ps.X i :=
      (show (U.obj (V.obj (P.X i))).obj.obj (op (ProEt.mk (𝟙 Y))) ≃ₗ[R] Ps.X i from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }).toModuleIso
    exact (ObjectProperty.flat (A := ModuleCat.{u + 1} R)).prop_of_iso s he
  have : Ps.IsStrictlyGE a := (Ps.isStrictlyGE_iff a).2
    (fun i hi ↦ T.map_isZero (V.map_isZero (P.isZero_of_isStrictlyGE a i hi)))
  have : Ps.IsStrictlyLE b := (Ps.isStrictlyLE_iff b).2
    (fun i hi ↦ T.map_isZero (V.map_isZero (P.isZero_of_isStrictlyLE b i hi)))
  exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso es
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat Ps a b hps)

end WeilConjectures
