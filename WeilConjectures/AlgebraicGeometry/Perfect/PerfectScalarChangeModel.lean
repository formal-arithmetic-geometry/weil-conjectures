/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Perfect scalar models under arbitrary coefficient change

Source: blueprint sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md (2), displayed scalar-change formula.
(blueprint: lem-sfb-perfect-scalar-change-model).

The scalar ring and constant-sheaf extension are the existing local-model API.
Finite projectivity is expressed by a splitting off a finite free scalar module,
including rank zero. The derived functor is ordinary and uncompleted.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance 0] CompleteLattice.hasFiniteColimits_of_semilatticeSup_orderBot
  Preorder.instHasColimitsOfShape

attribute [local instance 2000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint pointUpperStar
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

private theorem flat_of_retract_unit_sum
    {D : Type*} [Category D] [Preadditive D] [MonoidalCategory D]
    [(ObjectProperty.flat (A := D)).IsStableUnderRetracts]
    {n : ℕ} [HasBiproductsOfShape (Fin n) D]
    [(ObjectProperty.flat (A := D)).IsClosedUnderLimitsOfShape (Discrete (Fin n))]
    {M : D} (r : Retract M (⨁ fun _ : Fin n ↦ 𝟙_ D)) : ObjectProperty.flat M := by
  apply ObjectProperty.prop_of_retract ObjectProperty.flat r
  exact ObjectProperty.flat.prop_of_isLimit
    (biproduct.isLimit (fun _ : Fin n ↦ 𝟙_ D))
    (fun _ ↦ ObjectProperty.prop_unit ObjectProperty.flat)

/-- The termwise scalar model, using the canonical constant-to-coefficient map.
Source: blueprint scalar-six proof (2)
(blueprint: lem-sfb-perfect-scalar-change-model). -/
noncomputable def sfbScalarModelComplex (X : Scheme.{u})
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) :
    CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ :=
  letI : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits (scalarConstant X) :=
    inferInstanceAs (PreservesFiniteColimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
        (pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X))))
  letI : PreservesFiniteColimits (finiteConstantScalarExtension Λ X) :=
    inferInstanceAs (PreservesFiniteColimits
      ((scalarConstant X).mapMod (scalarRingObj Λ) ⋙
        Mod.extendScalars (scalarCoefficientHom Λ X)))
  ((finiteConstantScalarExtension Λ X).mapHomologicalComplex (.up ℤ)).obj C

/-- Termwise scalar change along the map on sections at the point.
Source: blueprint scalar-six proof (2)
(blueprint: lem-sfb-perfect-scalar-change-model). -/
noncomputable def sfbScalarChangedComplex
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) :
    CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ')) ℤ :=
  ((Mod.extendScalars (scalarSections.map a)).mapHomologicalComplex (.up ℤ)).obj C

/-- Ordinary, uncompleted coefficient change of the scalar model.
Source: blueprint scalar-six proof (2)
(blueprint: lem-sfb-perfect-scalar-change-model). -/
noncomputable def sfbExtendedScalarModelComplex (X : Scheme.{u})
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) :
    CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) ℤ :=
  ((Mod.extendScalars (coefficientMap a X)).mapHomologicalComplex (.up ℤ)).obj
    (sfbScalarModelComplex X C)

private instance scalarConstant_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (scalarConstant X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  unfold scalarConstant upperStarFromPoint
  infer_instance

private instance scalarExtension_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteConstantScalarExtension Λ X) := by
  unfold finiteConstantScalarExtension
  infer_instance

private instance scalarExtension_additive (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).Additive := by
  have : PreservesBinaryBiproducts (finiteConstantScalarExtension Λ X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable def scalarFreeIso (X : Scheme.{u}) (n : ℕ) :
    (finiteConstantScalarExtension Λ X).obj (Mod.finiteFree (scalarRingObj Λ) n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  (finiteConstantScalarExtension Λ X).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (scalarRingObj Λ)) ≪≫
    biproduct.mapIso (fun _ ↦
      (Mod.extendScalars (scalarCoefficientHom Λ X)).mapIso
        (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
      Mod.regularExtensionIso (scalarCoefficientHom Λ X))

private noncomputable def changedFreeIso (n : ℕ) :
    (Mod.extendScalars (scalarSections.map a)).obj
        (Mod.finiteFree (scalarRingObj Λ) n) ≅
      Mod.finiteFree (scalarRingObj Λ') n :=
  (Mod.extendScalars (scalarSections.map a)).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (scalarRingObj Λ)) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso (scalarSections.map a))

private theorem scalarModel_flat (X : Scheme.{u})
    (M : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hp : ∃ n : ℕ, Nonempty (Retract M (Mod.finiteFree (scalarRingObj Λ) n))) :
    (∃ n : ℕ, Nonempty (Retract ((finiteConstantScalarExtension Λ X).obj M)
      (Mod.finiteFree (condensedRingObj Λ X) n))) ∧
    ObjectProperty.flat ((finiteConstantScalarExtension Λ X).obj M) := by
  obtain ⟨n, ⟨r⟩⟩ := hp
  let t := (r.map (finiteConstantScalarExtension Λ X)).trans
    (Retract.ofIso (scalarFreeIso (Λ := Λ) X n))
  refine ⟨⟨n, ⟨t⟩⟩, ?_⟩
  let : (ObjectProperty.flat (A := Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))).IsStableUnderRetracts :=
    CochainComplex.instIsStableUnderRetractsFlat
  exact flat_of_retract_unit_sum t

/-- Scalar change preserves bounded finite-projective complexes and gives flat,
K-flat coefficient models, without a global object or cover.
Source: blueprint scalar-six proof (2)
(blueprint: lem-sfb-perfect-scalar-change-model).

Proof: split each finite projective scalar term off a finite free module, using
[def-weil-pbc-projective-module]. Tensoring preserves this split identity, and
extension of a free module is free of the same finite rank. Zero terms remain zero.
Apply the constant-sheaf functor and [def-pur-sheaf-tensor-product] to these splittings.
Tensor with a finite-free sheaf is a finite sum of the identity, hence exact;
its retract is exact, proving [def-pc-flat-sheaf-modules]. The same argument over
Λ' applies to the changed scalar complex. Both models are bounded, so
[lem-pc-bounded-above-flat-kflat-site] proves [def-pc-kflat-complex]. No scalar
or sheaf ring map is assumed flat. -/
theorem sfbPerfectScalarChangeModels (X : Scheme.{u})
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) (l h : ℤ)
    (hl : C.IsStrictlyGE l) (hh : C.IsStrictlyLE h)
    (hp : ∀ q : ℤ, ∃ n : ℕ,
      Nonempty (Retract (C.X q) (Mod.finiteFree (scalarRingObj Λ) n))) :
    (sfbScalarChangedComplex a C).IsStrictlyGE l ∧
    (sfbScalarChangedComplex a C).IsStrictlyLE h ∧
    (∀ q : ℤ, ∃ n : ℕ, Nonempty (Retract ((sfbScalarChangedComplex a C).X q)
      (Mod.finiteFree (scalarRingObj Λ') n))) ∧
    (∀ q : ℤ,
      (∃ n : ℕ, Nonempty (Retract ((sfbScalarModelComplex X C).X q)
        (Mod.finiteFree (condensedRingObj Λ X) n))) ∧
      ObjectProperty.flat ((sfbScalarModelComplex X C).X q) ∧
      (∃ n : ℕ, Nonempty (Retract
        ((sfbScalarModelComplex X (sfbScalarChangedComplex a C)).X q)
        (Mod.finiteFree (condensedRingObj Λ' X) n))) ∧
      ObjectProperty.flat ((sfbScalarModelComplex X (sfbScalarChangedComplex a C)).X q)) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (sfbScalarModelComplex X C) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (sfbScalarModelComplex X (sfbScalarChangedComplex a C)) := by
  let := hl
  let := hh
  have hge : (sfbScalarChangedComplex a C).IsStrictlyGE l := by
    unfold sfbScalarChangedComplex
    infer_instance
  have hle : (sfbScalarChangedComplex a C).IsStrictlyLE h := by
    unfold sfbScalarChangedComplex
    infer_instance
  have hp' (q : ℤ) : ∃ n : ℕ,
      Nonempty (Retract ((sfbScalarChangedComplex a C).X q)
        (Mod.finiteFree (scalarRingObj Λ') n)) := by
    obtain ⟨n, ⟨r⟩⟩ := hp q
    exact ⟨n, ⟨(r.map (Mod.extendScalars (scalarSections.map a))).trans
      (Retract.ofIso (changedFreeIso a n))⟩⟩
  have hf := fun q ↦ scalarModel_flat X (C.X q) (hp q)
  have hf' := fun q ↦ scalarModel_flat X ((sfbScalarChangedComplex a C).X q) (hp' q)
  refine ⟨hge, hle, hp', fun q ↦ ⟨(hf q).1, (hf q).2, (hf' q).1, (hf' q).2⟩,
    ?_, ?_⟩
  · have : (sfbScalarModelComplex X C).IsStrictlyGE l := by
      unfold sfbScalarModelComplex
      infer_instance
    have : (sfbScalarModelComplex X C).IsStrictlyLE h := by
      unfold sfbScalarModelComplex
      infer_instance
    exact CochainComplex.kFlat_of_bounded_of_flat _ l h (fun q ↦ (hf q).2)
  · let := hge
    let := hle
    have : (sfbScalarModelComplex X (sfbScalarChangedComplex a C)).IsStrictlyGE l := by
      unfold sfbScalarModelComplex
      infer_instance
    have : (sfbScalarModelComplex X (sfbScalarChangedComplex a C)).IsStrictlyLE h := by
      unfold sfbScalarModelComplex
      infer_instance
    exact CochainComplex.kFlat_of_bounded_of_flat _ l h (fun q ↦ (hf' q).2)

attribute [local irreducible] Mod.extendScalars scalarConstant finiteConstantScalarExtension
attribute [local irreducible] ObjectProperty.flat HomologicalComplex.quasiIso
  MorphismProperty.kFlat

private noncomputable def scalarRightAdjoint (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar) ⋙
    (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (Opposite.op (Profinite.of PUnit.{u + 1}))

private noncomputable def scalarAdjunction (X : Scheme.{u}) :
    scalarConstant X ⊣ scalarRightAdjoint X := by
  simpa only [scalarConstant, upperStarFromPoint, scalarRightAdjoint] using
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).comp (pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)))

private noncomputable def scalarMapExtensionIso (X : Scheme.{u}) :
    (scalarConstant X).mapMod (scalarRingObj Λ) ⋙
        Mod.extendScalars ((scalarConstant X).map (scalarSections.map a)) ≅
      Mod.extendScalars (scalarSections.map a) ⋙
        (scalarConstant X).mapMod (scalarRingObj Λ') := by
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction ((scalarConstant X).map (scalarSections.map a)))
    (Mod.extendRestrictAdjunction (scalarSections.map a))
    ((scalarAdjunction X).mapModAdjunction (scalarRingObj Λ))
    ((scalarAdjunction X).mapModAdjunction (scalarRingObj Λ'))
    (Mod.comapMapModComapIso (scalarRightAdjoint X)
      ((scalarConstant X).map (scalarSections.map a)) (scalarSections.map a)
      ((scalarAdjunction X).unitAlgHom (scalarRingObj Λ))
      ((scalarAdjunction X).unitAlgHom (scalarRingObj Λ'))
      ((scalarAdjunction X).unit.naturality (scalarSections.map a)))

private theorem scalarCoefficientSquare (X : Scheme.{u}) :
    scalarCoefficientHom Λ X ≫ coefficientMap a X =
      (scalarConstant X).map (scalarSections.map a) ≫ scalarCoefficientHom Λ' X := by
  unfold scalarConstant
  change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map a =
    (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (upperStarFromPoint X).map
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.naturality a).symm

private noncomputable def scalarModelExtensionIso (X : Scheme.{u}) :
    finiteConstantScalarExtension Λ X ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (scalarSections.map a) ⋙ finiteConstantScalarExtension Λ' X := by
  unfold finiteConstantScalarExtension
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.extendScalarsComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoOfEq (scalarCoefficientSquare a X)) ≪≫
    Functor.isoWhiskerLeft _ (Mod.extendScalarsComp _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarMapExtensionIso a X) _ ≪≫
    Functor.associator _ _ _

private noncomputable def extendedModelIso (X : Scheme.{u})
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) :
    sfbExtendedScalarModelComplex a X C ≅
      sfbScalarModelComplex X (sfbScalarChangedComplex a C) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (finiteConstantScalarExtension Λ X ⋙
        Mod.extendScalars (coefficientMap a X))) (.up ℤ)).app C ≪≫
    (NatIso.mapHomologicalComplex (scalarModelExtensionIso a X) (.up ℤ)).app C ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (Mod.extendScalars (scalarSections.map a) ⋙
        finiteConstantScalarExtension Λ' X)) (.up ℤ)).app C).symm

private noncomputable def derivedModelIso (X : Scheme.{u})
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (sfbScalarModelComplex X C)) :
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj
        (DerivedCategory.Q.obj (sfbScalarModelComplex X C)) ≅
      DerivedCategory.Q.obj (sfbExtendedScalarModelComplex a X C) := by
  let E := Mod.extendScalars (coefficientMap a X)
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat _ hC
  exact E.leftDerivedFunctor.mapIso
      ((DerivedCategory.quotientCompQhIso _).app (sfbScalarModelComplex X C)).symm ≪≫
    asIso (E.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (sfbScalarModelComplex X C))) ≪≫
    (DerivedCategory.quotientCompQhIso _).app (sfbExtendedScalarModelComplex a X C)

/-- On each specified chart the ordinary derived coefficient change is represented
by ordinary tensor of the old scalar model, equivalently by the changed scalar model.
Source: blueprint scalar-six proof (2), displayed scalar-change formula
(blueprint: lem-sfb-perfect-scalar-change-model).

Proof:
1. [lem-sfb-coefficient-sections-localization] identifies chart pullback with slice
restriction. [def-sfb-pullback-from-point-comp-iso] identifies restricted coefficients
with Λ_W and Λ'_W; [sk-def-sfb-coefficient-change] gives the compatible square.
The scalar maps of [det-def-sfb-constructible-local-model] commute with this square.
2. Splitting finite projective scalar terms and tensoring the splitting proves
finite projectivity after scalar change, without flatness.
3. Applying constant sheaves and coefficient extension to the splitting gives
finite-free retracts; tensoring their finite-free ambient sheaves is exact, so the
retracts are flat [def-pc-flat-sheaf-modules].
4. Boundedness and [lem-pc-bounded-above-flat-kflat-site] give K-flatness of both
models, as stated separately in sfbPerfectScalarChangeModels.
5. Resolve P by [lem-pc-kflat-resolution]. Restriction remains a K-flat resolution
by [lem-sfb-ringed-site-restriction-kflat], and
[lem-sfb-localized-site-tensor-restriction] commutes ordinary tensor with restriction.
Thus [lem-pur-derived-change-of-rings] identifies restricted derived extension
with extension of the restricted derived object.
6. Apply derived extension to the specified chart isomorphism. K-flatness of its
scalar model allows the identity resolution in [lem-pur-derived-change-of-rings],
giving the first displayed isomorphism.
7. The balanced maps b tensor (c tensor m) ↦ bc tensor m and
b tensor (r' tensor m) ↦ br' tensor m, with inverses inserting 1, identify both
ordinary expressions with B tensor_R M. They commute with differentials and
restrictions, hence give the second isomorphism in the new coefficient derived
category. Zero complexes, zero rings, and rank zero obey the same identities. -/
theorem sfbPerfectScalarChangeModel (S : Scheme.{u})
    (P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (C : ∀ i : 𝒰.I₀, CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ)
    (hb : ∀ i : 𝒰.I₀, ∃ l h : ℤ, (C i).IsStrictlyGE l ∧ (C i).IsStrictlyLE h)
    (hp : ∀ (i : 𝒰.I₀) (q : ℤ), ∃ n : ℕ,
      Nonempty (Retract ((C i).X q) (Mod.finiteFree (scalarRingObj Λ) n)))
    (e : ∀ i : 𝒰.I₀,
      (CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory.obj P ≅
        DerivedCategory.Q.obj (sfbScalarModelComplex (𝒰.X i) (C i))) :
    ∀ i : 𝒰.I₀,
      Nonempty ((CondensedRing.upperStar Λ' (𝒰.f i)).mapDerivedCategory.obj
        ((Mod.extendScalars (coefficientMap a S)).leftDerivedFunctor.obj P) ≅
          DerivedCategory.Q.obj (sfbExtendedScalarModelComplex a (𝒰.X i) (C i))) ∧
      Nonempty (DerivedCategory.Q.obj (sfbExtendedScalarModelComplex a (𝒰.X i) (C i)) ≅
        DerivedCategory.Q.obj
          (sfbScalarModelComplex (𝒰.X i) (sfbScalarChangedComplex a (C i)))) := by
  intro i
  obtain ⟨l, h, hl, hh⟩ := hb i
  have hk := (sfbPerfectScalarChangeModels a (𝒰.X i) (C i) l h hl hh (hp i)).2.2.2.2.1
  have := FreeParameterEvaluation.scalarPullComparison_isIso
    (Mon.mk Λ) (Mon.mk Λ') a (𝒰.f i) P
  exact ⟨⟨(asIso (FreeParameterEvaluation.scalarPullComparison
      (Mon.mk Λ) (Mon.mk Λ') a (𝒰.f i) P)).symm ≪≫
    (Mod.extendScalars (coefficientMap a (𝒰.X i))).leftDerivedFunctor.mapIso (e i) ≪≫
    derivedModelIso a (𝒰.X i) (C i) hk⟩,
    ⟨DerivedCategory.Q.mapIso (extendedModelIso a (𝒰.X i) (C i))⟩⟩

omit [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] [IsMonHom a] in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
end AlgebraicGeometry.ProEtale
