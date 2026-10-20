/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import all Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.RegularExtensionComparison
import all Sheaf.Paper.InternalModuleAbEquivalence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ULift
import all Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank
import all Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Normed
import all Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

/-!
# Finite constant local models for condensed coefficients

Source: blueprint main-20261015, `sk-def-sfb-constructible-local-model.md`
(blueprint: det-def-sfb-constructible-local-model).

Scalars are encoded as a ring object of abelian groups, and scalar modules as internal
modules in abelian groups. These are precisely ordinary modules over the scalar ring.
The constant sheaf on the profinite point is formed before inverse image to a scheme;
only this constant sheaf, rather than an arbitrary condensed module, is called constant.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Sections at the one-point profinite set. Source: blueprint local-model definition,
first paragraph (blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarSections :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (op (Profinite.of PUnit.{u + 1}))

/-- The sections functor has the lax monoidal structure right adjoint to the monoidal
constant sheaf functor. Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable instance scalarSections_laxMonoidal : scalarSections.{u}.LaxMonoidal :=
  (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).rightAdjointLaxMonoidal

@[instance_reducible]
private noncomputable def constantScalarSheaf_laxBraided :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided := by
  let : (Functor.const Profinite.{u}ᵒᵖ :
      Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}).LaxBraided :=
    { braided := by intros; ext; simp [Functor.LaxMonoidal.μ]; rfl }
  exact inferInstanceAs (Functor.const Profinite.{u}ᵒᵖ ⋙
    presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided

@[instance_reducible]
private noncomputable def scalarSections_laxBraided : scalarSections.{u}.LaxBraided := by
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : F.LaxBraided := constantScalarSheaf_laxBraided
  let : F.Braided := { toMonoidal := inferInstance, braided := Functor.LaxBraided.braided }
  let adj : F ⊣ scalarSections.{u} := constantSheafAdj
    (coherentTopology Profinite.{u}) Ab.{u + 1} Profinite.isTerminalPUnit
  refine { toLaxMonoidal := scalarSections_laxMonoidal, braided := ?_ }
  intro A B
  change adj.homEquiv _ _ _ ≫ scalarSections.map (β_ A B).hom =
    (β_ _ _).hom ≫ adj.homEquiv _ _ _
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  rw [Functor.map_braiding]
  dsimp only [F]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [BraidedCategory.braiding_naturality]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]

/-- The scalar ring Λ(*), encoded as a ring object of abelian groups. Its underlying
abelian group is literally evaluation at *. Source: blueprint local-model definition,
first paragraph (blueprint: det-def-sfb-constructible-local-model). -/
noncomputable abbrev scalarRingObj : Ab.{u + 1} := scalarSections.obj Λ

/-- The scalar ring is commutative. Source: blueprint local-model proof, Step 1.
Proof: evaluation's multiplication is induced from the sheaf tensor comparison; the
symmetry and the commutativity of Λ give commutativity on sections.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarRingObj_comm : IsCommMonObj (scalarRingObj Λ) := by
  let := scalarSections_laxBraided.{u}
  exact Functor.isCommMonObj_obj (F := scalarSections.{u}) (M := Λ)

attribute [instance] scalarRingObj_comm

/-- Sheafified constant abelian groups pulled to X. This is the constant-sheaf functor
on X: inverse image preserves colimits and the integer tensor unit, hence preserves
constant abelian sheaves, which are presentations by coproducts of that unit.
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarConstant (X : Scheme.{u}) :
    Ab.{u + 1} ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

/-- The constant-sheaf construction followed by inverse image is monoidal.
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable instance scalarConstant_monoidal (X : Scheme.{u}) :
    (scalarConstant X).Monoidal :=
  inferInstanceAs (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    upperStarFromPoint X).Monoidal

/-- The composed constant construction agrees monoidally with the sheafification of
constant presheaves on X. This records that P_X here really is a constant sheaf.
Source: blueprint local-model definition, first paragraph, and proof, Step 1.
Proof: both functors are additive left adjoints and preserve the tensor unit ℤ.
Present any abelian group by coproducts of ℤ and transport the presentation through
both functors. The unit comparison gives compatible maps on the free presentations
and hence an isomorphism on their cokernels, independent of the presentation.
The resulting isomorphism is natural; checking its unit and tensor compatibility
on free generators gives the monoidal clauses.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarConstant_iso_constantSheaf (X : Scheme.{u}) :
    ∃ e : scalarConstant X ≅ constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1},
      NatTrans.IsMonoidal e.hom := by
  refine ⟨(AlgebraicGeometry.ProEtale.constantSchemeIso X).symm, ?_⟩
  change NatTrans.IsMonoidal (AlgebraicGeometry.ProEtale.constantSchemeIso X).inv
  infer_instance

/-- The scalar map R_X → Λ_X is the inverse image of the constant-sheaf counit at Λ.
Thus a scalar is pulled back from Λ(*) rather than chosen in Γ(X,Λ_X).
Source: blueprint local-model proof, Step 1
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarCoefficientHom (X : Scheme.{u}) :
    (scalarConstant X).obj (scalarRingObj Λ) ⟶ condensedRingObj Λ X :=
  (upperStarFromPoint X).map
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ)

/-- The scalar map preserves multiplication and unit. Source: blueprint local-model
proof, Step 1. Proof: the constant-sheaf adjunction is monoidal, so its counit is a
ring morphism, and the monoidal inverse image preserves ring morphisms.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarCoefficientHom_isMonHom (X : Scheme.{u}) :
    IsMonHom (scalarCoefficientHom Λ X) := by
  let _ := ‹IsCommMonObj Λ›
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (op (Profinite.of PUnit.{u + 1}))
  let : G.LaxMonoidal := scalarSections_laxMonoidal
  let adj : F ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  have : adj.IsMonoidal := inferInstance
  have hc : @IsMonHom _ _ _ (F.obj (G.obj Λ)) Λ
      (F.monObjObj (G.obj Λ)) ‹MonObj Λ› (adj.counit.app Λ) :=
    adj.isMonHom_counitAlgHom Λ
  have hm : @IsMonHom _ _ _ ((upperStarFromPoint X).obj (F.obj (G.obj Λ)))
      ((upperStarFromPoint X).obj Λ)
      ((upperStarFromPoint X).monObjObj (F.obj (G.obj Λ)))
      ((upperStarFromPoint X).monObjObj Λ)
      ((upperStarFromPoint X).map (adj.counit.app Λ)) :=
    Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _ _
  dsimp only [scalarConstant_monoidal, scalarConstant]
  exact IsMonHom.of_eq
    (h₁ := (upperStarFromPoint X).monObjObj (F.obj (G.obj Λ)))
    (h₂ := (upperStarFromPoint X).monObjObj Λ) (scalarCoefficientHom Λ X)
    (Functor.monObjObj_comp F (upperStarFromPoint X) (G.obj Λ)).symm rfl (hf := hm)

attribute [instance] scalarCoefficientHom_isMonHom

/-- The constant scalar ring on X is commutative. Source: blueprint local-model proof,
Step 1. Proof: the constant presheaf functor, sheafification and inverse image are
symmetric monoidal and transport commutative ring objects to commutative ring objects.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem scalarConstant_comm (X : Scheme.{u}) :
    IsCommMonObj ((scalarConstant X).obj (scalarRingObj Λ)) := by
  dsimp only [scalarConstant_monoidal, scalarConstant]
  let := constantScalarSheaf_laxBraided.{u}
  change IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    upperStarFromPoint X).obj (scalarRingObj Λ))
  infer_instance

attribute [instance] scalarConstant_comm

/-- E_X(P) = Λ_X ⊗_{R_X} P_X, using actual scalar extension along the canonical map.
This functor starts with ordinary scalar modules and takes values in module sheaves.
Source: blueprint local-model definition and proof, Steps 1–2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def finiteConstantScalarExtension (X : Scheme.{u}) :
    Mod Ab.{u + 1} (scalarRingObj Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (scalarConstant X).mapMod (scalarRingObj Λ) ⋙ Mod.extendScalars (scalarCoefficientHom Λ X)

/-- A scalar section on X, with the unit comparison included explicitly.
Source: blueprint local-model proof, Steps 1–2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarSection (X : Scheme.{u}) (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X :=
  Functor.LaxMonoidal.ε (scalarConstant X) ≫
    (scalarConstant X).map a ≫ scalarCoefficientHom Λ X

/-- The finite matrix with scalar entries, acting on finite free Λ_X-modules.
The first index is the source column and the second is the target row.
A map ℤ → Λ(*) encodes its value at 1, so these entries are exactly elements of Λ(*).
Source: blueprint local-model definition, Lemma (2), and proof, Step 2
(blueprint: det-def-sfb-constructible-local-model). -/
noncomputable def scalarMatrix (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    Mod.finiteFree (condensedRingObj Λ X) m ⟶
      Mod.finiteFree (condensedRingObj Λ X) n :=
  biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X (A j k))

private noncomputable def scalarRegularIso (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).obj (Mod.regular (scalarRingObj Λ)) ≅
      Mod.regular (condensedRingObj Λ X) :=
  (Mod.extendScalars (scalarCoefficientHom Λ X)).mapIso
      (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
    Mod.regularExtensionIso (scalarCoefficientHom Λ X)

private theorem scalarRegular_entry (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (finiteConstantScalarExtension Λ X).map
        (Mod.regularLift (Mod.regular (scalarRingObj Λ)) a) ≫
      (scalarRegularIso Λ X).hom =
    (scalarRegularIso Λ X).hom ≫
      Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X a) := by
  let F := scalarConstant X
  let R := scalarRingObj Λ
  let S := condensedRingObj Λ X
  let φ := scalarCoefficientHom Λ X
  have hm : (F.mapMod R).map (Mod.regularLift (Mod.regular R) a) ≫
      (Mod.isoMk (Iso.refl _) (by simp) :
        (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R)).hom =
      (Mod.isoMk (Iso.refl _) (by simp) :
        (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R)).hom ≫
      Mod.regularLift (Mod.regular (F.obj R)) (Functor.LaxMonoidal.ε F ≫ F.map a) := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
        (F.map (Mod.regularLift (Mod.regular R) a).hom ≫ 𝟙 _) =
      (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫ (𝟙 _ ≫ _)
    simp only [Category.comp_id, Category.id_comp]
    rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
      ← F.map_comp, Mod.one_comp_regularLift]
  have h : Mod.regularLift (Mod.regular (F.obj R))
        (Functor.LaxMonoidal.ε F ≫ F.map a) ≫ Mod.regularCoefficientMap φ =
      Mod.regularCoefficientMap φ ≫ (Mod.comap φ).map
        (Mod.regularLift (Mod.regular S) (scalarSection Λ X a)) := by
    apply Mod.regular_hom_ext
    change MonObj.one ≫ (_ ≫ φ) = MonObj.one ≫ (φ ≫ _)
    change (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
        ((Mod.regularLift (Mod.regular (F.obj R))
          (Functor.LaxMonoidal.ε F ≫ F.map a)).hom ≫ φ) =
      (MonObj.one : 𝟙_ _ ⟶ F.obj R) ≫
        (φ ≫ (Mod.regularLift (Mod.regular S) (scalarSection Λ X a)).hom)
    rw [← Category.assoc, Mod.one_comp_regularLift, ← Category.assoc,
      IsMonHom.one_hom φ, Mod.one_comp_regularLift]
    rfl
  have he := Mod.regularExtensionIso_naturality φ
    (Mod.regularLift (Mod.regular (F.obj R)) (Functor.LaxMonoidal.ε F ≫ F.map a))
    (Mod.regularLift (Mod.regular S) (scalarSection Λ X a)) (congrArg Mod.Hom.hom h)
  dsimp only [finiteConstantScalarExtension, scalarRegularIso, Functor.comp_map,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← (Mod.extendScalars φ).map_comp, hm,
    (Mod.extendScalars φ).map_comp, Category.assoc, he]
  exact (Category.assoc _ _ _).symm

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
    biproduct.mapIso (fun _ ↦ scalarRegularIso Λ X)

private theorem scalarMatrix_map (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (scalarFreeIso Λ X m).inv ≫ (finiteConstantScalarExtension Λ X).map
        (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (scalarRingObj Λ))
          (A j k)) ≫ (scalarFreeIso Λ X n).hom = scalarMatrix Λ X A := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simp only [scalarFreeIso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π,
    scalarMatrix, biproduct.matrix]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
    biproduct.lift_π]
  simp only [Category.assoc]
  rw [scalarRegular_entry, Iso.inv_hom_id_assoc]

omit [IsCommMonObj Λ] in
private theorem scalarMatrix_reconstruct {m n : ℕ}
    (f : Mod.finiteFree (scalarRingObj Λ) m ⟶ Mod.finiteFree (scalarRingObj Λ) n) :
    (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (scalarRingObj Λ))
      ((MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
        (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom)) = f := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  erw [biproduct.ι_matrix, biproduct.lift_π]
  apply Mod.regular_hom_ext
  simpa only [Category.assoc] using Mod.one_comp_regularLift (A := scalarRingObj Λ) _ _

/-- Finite constant local models on a specified pro-étale cover: the model on each
member is extension of a finitely presented scalar module, with no uniform rank bound.
Source: blueprint local-model definition, second paragraph and Lemma (1)
(blueprint: det-def-sfb-constructible-local-model). -/
def HasFiniteConstantLocalModelOnCover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : Prop :=
  ∀ i : 𝒰.I₀, ∃ P : Mod Ab.{u + 1} (scalarRingObj Λ),
    Mod.IsFinitelyPresented (scalarRingObj Λ) P ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
        (finiteConstantScalarExtension Λ (𝒰.X i)).obj P)

/-- Scalar finite-presentation matrices on a specified pro-étale cover.
Source: blueprint local-model definition, Lemma (2)
(blueprint: det-def-sfb-constructible-local-model). -/
def HasScalarMatrixPresentationOnCover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : Prop :=
  ∀ i : 𝒰.I₀, ∃ (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)),
    Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
      cokernel (scalarMatrix Λ (𝒰.X i) A))

private noncomputable def pointScalarSection
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ :=
  Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem pointScalarSection_surjective :
    Function.Surjective (pointScalarSection Λ) := by
  intro b
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  refine ⟨adj.homEquiv _ _ (Functor.OplaxMonoidal.η F ≫ b), ?_⟩
  change Functor.LaxMonoidal.ε F ≫
    (F.map (adj.homEquiv _ _ _) ≫ adj.counit.app Λ) = b
  have h := (adj.homEquiv _ _).symm_apply_apply (Functor.OplaxMonoidal.η F ≫ b)
  rw [adj.homEquiv_counit] at h
  calc
    _ = Functor.LaxMonoidal.ε F ≫ (Functor.OplaxMonoidal.η F ≫ b) :=
      congrArg (fun f ↦ Functor.LaxMonoidal.ε F ≫ f) h
    _ = b := by rw [← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem scalarSection_point (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    scalarSection Λ X a = Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map (pointScalarSection Λ a) := by
  simp only [scalarSection, scalarCoefficientHom, pointScalarSection,
    Functor.map_comp]
  rfl

private instance pointMod_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits ((upperStarFromPoint X).mapMod Λ) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  infer_instance

private instance pointMod_additive (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).Additive := by
  have : PreservesBinaryBiproducts ((upperStarFromPoint X).mapMod Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable def pointRegularIso (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) :=
  Mod.isoMk (Iso.refl _) (by simp)

private noncomputable def pointFreeIso (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  ((upperStarFromPoint X).mapMod Λ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ pointRegularIso Λ X)

omit [IsCommMonObj Λ] in
private theorem pointRegular_entry (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    ((upperStarFromPoint X).mapMod Λ).map
        (Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ a)) ≫
      (pointRegularIso Λ X).hom =
    (pointRegularIso Λ X).hom ≫
      Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X a) := by
  apply Mod.regular_hom_ext
  change (MonObj.one : 𝟙_ _ ⟶ (upperStarFromPoint X).obj Λ) ≫
      ((upperStarFromPoint X).map
        (Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ a)).hom ≫ 𝟙 _) =
    (MonObj.one : 𝟙_ _ ⟶ (upperStarFromPoint X).obj Λ) ≫ (𝟙 _ ≫ _)
  simp only [Category.comp_id, Category.id_comp]
  rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
    ← Functor.map_comp, Mod.one_comp_regularLift, scalarSection_point]

omit [IsCommMonObj Λ] in
private theorem pointMatrix_map (X : Scheme.{u}) {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (pointFreeIso Λ X m).inv ≫ ((upperStarFromPoint X).mapMod Λ).map
        (biproduct.matrix fun j k ↦
          Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))) ≫
      (pointFreeIso Λ X n).hom = scalarMatrix Λ X A := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simp only [pointFreeIso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π,
    scalarMatrix, biproduct.matrix]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
    biproduct.lift_π]
  simp only [Category.assoc]
  rw [pointRegular_entry, Iso.inv_hom_id_assoc]

omit [IsCommMonObj Λ] in
private theorem pointMatrix_reconstruct {m n : ℕ}
    (f : Mod.finiteFree Λ m ⟶ Mod.finiteFree Λ n) :
    (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular Λ)
      ((MonObj.one : 𝟙_ _ ⟶ Λ) ≫
        (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom)) = f := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  erw [biproduct.ι_matrix, biproduct.lift_π]
  apply Mod.regular_hom_ext
  simpa only [Category.assoc] using Mod.one_comp_regularLift (A := Λ) _ _

/-- Constant finite scalar models and finite scalar matrices are equivalent on the
same given cover. Source: blueprint local-model lemma, and proof, Steps 1–3.
Proof: the constant-sheaf adjunction and extension/restriction adjunction identify maps
from E_U(P) to N with scalar-linear maps P → N(U). For P = R^k this identifies E_U(P)
with Λ_U^k, preserving each scalar matrix entry. For a scalar matrix A, maps from
E_U(coker A) to N are exactly maps from Λ_U^n killing A, so E_U(coker A) is its cokernel;
no flatness is used. Apply a finite presentation of each P_i for the forward direction.
Conversely take P_i to be the cokernel of the given scalar matrix over R.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem finiteConstantLocalModelOnCover_iff_scalarMatrix {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    HasFiniteConstantLocalModelOnCover Λ M 𝒰 ↔
      HasScalarMatrixPresentationOnCover Λ M 𝒰 := by
  constructor
  · intro h i
    obtain ⟨P, ⟨n, m, f, ⟨ef⟩⟩, ⟨eP⟩⟩ := h i
    let A (j : Fin m) (k : Fin n) : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ :=
      (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
        (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom
    let E := finiteConstantScalarExtension Λ (𝒰.X i)
    have he : (scalarFreeIso Λ (𝒰.X i) m).inv ≫ E.map f ≫
        (scalarFreeIso Λ (𝒰.X i) n).hom = scalarMatrix Λ (𝒰.X i) A := by
      rw [← scalarMatrix_map, scalarMatrix_reconstruct]
    refine ⟨m, n, A, ⟨eP ≪≫ E.mapIso ef ≪≫ PreservesCokernel.iso E f ≪≫ ?_⟩⟩
    exact cokernel.mapIso (E.map f) (scalarMatrix Λ (𝒰.X i) A)
      (scalarFreeIso Λ (𝒰.X i) m) (scalarFreeIso Λ (𝒰.X i) n)
      (by rw [← he]; simp)
  · intro h i
    obtain ⟨m, n, A, ⟨e⟩⟩ := h i
    let f : Mod.finiteFree (scalarRingObj Λ) m ⟶ Mod.finiteFree (scalarRingObj Λ) n :=
      biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)
    let E := finiteConstantScalarExtension Λ (𝒰.X i)
    refine ⟨cokernel f, ⟨n, m, f, ⟨Iso.refl _⟩⟩, ⟨e ≪≫ ?_⟩⟩
    refine (cokernel.mapIso (E.map f) (scalarMatrix Λ (𝒰.X i) A)
      (scalarFreeIso Λ (𝒰.X i) m) (scalarFreeIso Λ (𝒰.X i) n) ?_).symm ≪≫
        (PreservesCokernel.iso E f).symm
    rw [← scalarMatrix_map]
    simp only [f, E, Iso.hom_inv_id_assoc]


/-- The existing finite constant local model predicate is exactly the scalar-extension
formulation. Source: blueprint local-model definition and proof, Steps 1–3.
Proof: a finite presentation by regular condensed modules is a finite scalar matrix,
since maps from the regular module are maps from the integer unit, hence sections
at the terminal profinite set. Its cokernel is extension of the corresponding
finitely presented scalar module by the adjunction and cokernel calculation of
Steps 1–3. Conversely present a scalar module by a finite matrix and take the
same matrix of regular condensed modules before inverse image. Inverse image and
extension of scalars preserve these cokernels. The same cover and its members
are used in both directions.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem finiteConstantLocalModel_iff_exists_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ X M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        HasFiniteConstantLocalModelOnCover Λ M 𝒰 := by
  classical
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, (finiteConstantLocalModelOnCover_iff_scalarMatrix Λ M 𝒰).mpr ?_⟩
    intro i
    obtain ⟨P, ⟨n, m, f, ⟨ef⟩⟩, ⟨eP⟩⟩ := h𝒰 i
    let b (j : Fin m) (k : Fin n) : 𝟙_ _ ⟶ Λ :=
      (MonObj.one : 𝟙_ _ ⟶ Λ) ≫ (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom
    choose A hA using fun j k ↦ pointScalarSection_surjective Λ (b j k)
    let F := (upperStarFromPoint (𝒰.X i)).mapMod Λ
    have hf : (biproduct.matrix fun j k ↦
        Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))) = f := by
      simp_rw [hA]
      exact pointMatrix_reconstruct Λ f
    have he : (pointFreeIso Λ (𝒰.X i) m).inv ≫ F.map f ≫
        (pointFreeIso Λ (𝒰.X i) n).hom = scalarMatrix Λ (𝒰.X i) A := by
      rw [← pointMatrix_map, hf]
    refine ⟨m, n, A, ⟨eP ≪≫ F.mapIso ef ≪≫ PreservesCokernel.iso F f ≪≫ ?_⟩⟩
    exact cokernel.mapIso (F.map f) (scalarMatrix Λ (𝒰.X i) A)
      (pointFreeIso Λ (𝒰.X i) m) (pointFreeIso Λ (𝒰.X i) n)
      (by rw [← he]; simp)
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨m, n, A, ⟨e⟩⟩ :=
      (finiteConstantLocalModelOnCover_iff_scalarMatrix Λ M 𝒰).mp h𝒰 i
    let f : Mod.finiteFree Λ m ⟶ Mod.finiteFree Λ n :=
      biproduct.matrix fun j k ↦
        Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))
    let F := (upperStarFromPoint (𝒰.X i)).mapMod Λ
    refine ⟨cokernel f, ⟨n, m, f, ⟨Iso.refl _⟩⟩, ⟨e ≪≫ ?_⟩⟩
    refine (cokernel.mapIso (F.map f) (scalarMatrix Λ (𝒰.X i) A)
      (pointFreeIso Λ (𝒰.X i) m) (pointFreeIso Λ (𝒰.X i) n) ?_).symm ≪≫
        (PreservesCokernel.iso F f).symm
    rw [← pointMatrix_map]
    simp only [f, F, Iso.hom_inv_id_assoc]



private theorem map_finitePresentation
    {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    (R : C) (S : D) [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]
    (F : Mod C R ⥤ Mod D S) [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    (M : Mod C R) (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := F.additive_of_preservesBinaryBiproducts
  obtain ⟨n, m, f, ⟨h⟩⟩ := hM
  let b (k : ℕ) : F.obj (Mod.finiteFree R k) ≅ Mod.finiteFree S k :=
    F.mapBiproduct (fun _ : Fin k ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ e)
  let g := (b m).inv ≫ F.map f ≫ (b n).hom
  refine ⟨n, m, g, ⟨F.mapIso h ≪≫ PreservesCokernel.iso F f ≪≫ ?_⟩⟩
  exact cokernel.mapIso (F.map f) g (b m) (b n) (by simp [g])

/-- Finite constant local models imply local finite presentation.
Source: blueprint local-model final paragraph and proof, Step 4.
Proof: replace each constant scalar model by its scalar matrix presentation using
finiteConstantLocalModelOnCover_iff_scalarMatrix. This is a finite free presentation
over Λ_U. Transport along the canonical coefficient isomorphism α_u to the
u^*Λ_X-module category used by IsLocallyFinitelyPresented. Restriction along α_u and
its inverse preserve regular modules, finite sums and cokernel presentations, so the
same cover witnesses local finite presentation.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem HasFiniteConstantLocalModel.isLocallyFinitelyPresented {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := h𝒰 i
  let F := (upperStarFromPoint (𝒰.X i)).mapMod Λ
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint (𝒰.X i)) := by
    unfold upperStarFromPoint
    infer_instance
  have : PreservesFiniteColimits F := by
    dsimp only [F]
    infer_instance
  have hF : Mod.IsFinitelyPresented (condensedRingObj Λ (𝒰.X i)) (F.obj P) :=
    map_finitePresentation Λ _ F (Mod.isoMk (Iso.refl _) (by simp)) P hP
  let φ := condensedPullbackHom Λ (𝒰.f i)
  let E := Mod.comapEquivalenceOfIsIso φ
  have : (Mod.comap φ).IsEquivalence := E.isEquivalence_functor
  let er : (Mod.comap φ).obj (Mod.regular (condensedRingObj Λ (𝒰.X i))) ≅
      Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj (condensedRingObj Λ X)) := by
    exact (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  have hG := map_finitePresentation _ _ (Mod.comap φ) er (F.obj P) hF
  obtain ⟨n, m, f, ⟨hf⟩⟩ := hG
  refine ⟨n, m, f, ⟨?_ ≪≫ hf⟩⟩
  let N := ((upperStar Ab.{u + 1} (𝒰.f i)).mapMod (condensedRingObj Λ X)).obj M
  exact ((Mod.comapId _).app N).symm ≪≫
    (Mod.comapCongr (IsIso.hom_inv_id φ).symm).app N ≪≫
    (Mod.comapComp φ (inv φ)).app N ≪≫
    (Mod.comap φ).mapIso ((Mod.extendScalarsIsoComapInv φ).app N).symm ≪≫
    (Mod.comap φ).mapIso e


attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension

private theorem locallyFinitelyPresented_of_finitelyPresented {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : Mod.IsFinitelyPresented R M) : IsLocallyFinitelyPresented R M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (𝟙 X)
  exact map_finitePresentation R (F.obj R) (F.mapMod R)
    (Mod.isoMk (Iso.refl _) (by simp)) M hM

private theorem locallyConstant_of_cover_constants {X : Scheme.{u}}
    [CompactSpace X] [T2Space X] {A : Type*} (d : X → A)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, ∃ a, ∀ x : C.X i, d (C.f i x) = a) : IsLocallyConstant d := by
  classical
  obtain ⟨V, q, hfin, ho⟩ := QuasiCompactCover.exists_hom C.forgetQc
  have : Finite V.cover.I₀ := hfin
  choose a ha using h
  have hc (i : V.cover.I₀) : IsClosed (Set.range (V.cover.f i)) := by
    have : IsAffine (V.cover.X i) := by change IsAffine (Spec (V.X i)); infer_instance
    exact (isCompact_range (V.cover.f i).continuous).isClosed
  have hv (i : V.cover.I₀) (x : V.cover.X i) :
      d (V.cover.f i x) = a (q.s₀ i) := by
    rw [← q.w₀ i]
    exact ha _ _
  have hf (b : A) : IsClosed {x | d x = b} := by
    have he : {x | d x = b} = ⋃ i : {i : V.cover.I₀ // a (q.s₀ i) = b},
        Set.range (V.cover.f i.val) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨i, v, hvx⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mp
          V.cover.mem₀).1 x
        subst x
        exact ⟨⟨i, (hv i v).symm.trans hx⟩, v, rfl⟩
      · rintro ⟨⟨i, hi⟩, v, rfl⟩
        exact (hv i v).trans hi
    rw [he]
    exact isClosed_iUnion_of_finite fun i ↦ hc i.val
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro b
  have he : {x | d x = b}ᶜ = ⋃ i : {i : V.cover.I₀ // a (q.s₀ i) ≠ b},
      Set.range (V.cover.f i.val) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨i, v, hvx⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mp
        V.cover.mem₀).1 x
      subst x
      exact ⟨⟨i, fun he ↦ hx ((hv i v).trans he)⟩, v, rfl⟩
    · rintro ⟨⟨i, hi⟩, v, rfl⟩ he
      exact hi ((hv i v).symm.trans he)
  exact isClosed_compl_iff.mp (he ▸ isClosed_iUnion_of_finite fun i ↦ hc i.val)

private theorem scalarSections_monoidal_eq :
    scalarSections_laxMonoidal.{u} =
      sectionsMonoidal (A := Ab.{u + 1}) (coherentTopology Profinite.{u})
        (T := Profinite.of PUnit.{u + 1}) := by
  let := sectionsMonoidal (A := Ab.{u + 1}) (coherentTopology Profinite.{u})
    (T := Profinite.of PUnit.{u + 1})
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  have : adj.IsMonoidal := inferInstance
  apply Functor.LaxMonoidal.ext
  · exact (Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj)).symm
  · funext X Y
    exact (Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj) X Y).symm

private theorem scalarField_monObj (E : Type u) [NormedField E] :
    (scalarSections.{u}).monObjObj (condensedFieldCoefficientRingObj E) =
      AddCommGrpCat.ringMonObj (ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, E)) := by
  have he := scalarSections_monoidal_eq.{u}
  change @Functor.monObjObj _ _ _ _ _ _ scalarSections scalarSections_laxMonoidal _ _ = _
  rw [he]
  apply MonObj.ext
  let R := Profinite.continuousCoefficientRingSheaf E
  let : MonObj ((condensedFieldCoefficientRingObj E).obj) := R.obj.monObjCompForget₂
  have hm := congr_app (Sheaf.μ_comp_map_mul (condensedFieldCoefficientRingObj E))
    (op (Profinite.of PUnit.{u + 1}))
  exact hm

private noncomputable def scalarFieldConstants (E : Type u) [NormedField E] :
    ULift.{u + 1} E ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, E) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext y
    exact congrArg f.down (Subsingleton.elim PUnit.unit y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def scalarFieldHom (E : Type u) [NormedField E] :
    AddCommGrpCat.of (ULift.{u + 1} E) ⟶
      scalarRingObj (condensedFieldCoefficientRingObj E) :=
  (scalarFieldConstants E).toAddEquiv.toAddCommGrpIso.hom

private instance scalarFieldHom_isIso (E : Type u) [NormedField E] :
    IsIso (scalarFieldHom E) := by
  unfold scalarFieldHom
  infer_instance

private instance scalarFieldHom_isMonHom (E : Type u) [NormedField E] :
    IsMonHom (scalarFieldHom E) := by
  change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj _) _
  rw [scalarField_monObj E]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (scalarFieldConstants E).toRingHom

private noncomputable def internalRegularCoordinates (K : Type*) [Ring K] :
    (internalToModule K).obj (Mod.regular (AddCommGrpCat.of K)) ≃ₗ[K] K where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalarField_finitelyPresented_isFree
    (E : Type u) [NormedField E]
    (P : Mod Ab.{u + 1} (scalarRingObj (condensedFieldCoefficientRingObj E)))
    (hP : Mod.IsFinitelyPresented (scalarRingObj (condensedFieldCoefficientRingObj E)) P) :
    Mod.IsFree (scalarRingObj (condensedFieldCoefficientRingObj E)) P := by
  classical
  let K := ULift.{u + 1} E
  let R := scalarRingObj (condensedFieldCoefficientRingObj E)
  let φ := scalarFieldHom E
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular R) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular R) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans
    (internalRegularCoordinates K)
  let c (n : ℕ) := finiteFreeEvaluationCoords (Mod.regular R) Q b n
  obtain ⟨n, m, f, ⟨e⟩⟩ := hP
  let eQ : Q.obj P ≅ cokernel (Q.map f) :=
    Q.mapIso e ≪≫ PreservesCokernel.iso Q f
  have : Module.Finite K (Q.obj (Mod.finiteFree R n)) :=
    Module.Finite.of_injective (c n).toLinearMap (c n).injective
  have : Module.Finite K (cokernel (Q.map f) : ModuleCat K) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (Q.map f)).toLinearEquiv.symm
  have : Module.Finite K (Q.obj P) := Module.Finite.equiv eQ.toLinearEquiv.symm
  let B := Module.finBasis K (Q.obj P)
  refine ⟨Module.finrank K (Q.obj P), ⟨Q.preimageIso ?_⟩⟩
  exact (B.equivFun.trans (c _).symm).toModuleIso

@[irreducible] private noncomputable def plainPullback
    {X Y : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (p : Y ⟶ X) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj L X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj L Y) :=
  (upperStar Ab.{u + 1} p).mapMod (condensedRingObj L X) ⋙
    Mod.comap (inv (condensedPullbackHom L p))

@[irreducible] private noncomputable def plainPullbackIso
    {X Y : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (p : Y ⟶ X) : CondensedRing.upperStar L p ≅ plainPullback L p := by
  unfold plainPullback CondensedRing.upperStar
  exact Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} p).mapMod _)
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom L p))

@[irreducible] private noncomputable def plainRegularIso
    {X Y : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (p : Y ⟶ X) :
    (plainPullback L p).obj (Mod.regular (condensedRingObj L X)) ≅
      Mod.regular (condensedRingObj L Y) := by
  unfold plainPullback
  exact (Mod.comap (inv (condensedPullbackHom L p))).mapIso
      (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
    Mod.regularIsoOfIsIso (condensedPullbackHom L p)

set_option backward.isDefEq.respectTransparency false in
private theorem plainRegular_map
    {X Y : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (p : Y ⟶ X)
    (f : Mod.regular (condensedRingObj L X) ⟶ Mod.regular (condensedRingObj L X)) :
    ((plainRegularIso L p).inv ≫ (plainPullback L p).map f ≫
      (plainRegularIso L p).hom).hom =
      inv (condensedPullbackHom L p) ≫ (upperStar Ab.{u + 1} p).map f.hom ≫
        condensedPullbackHom L p := by
  unfold plainRegularIso plainPullback
  change (inv (condensedPullbackHom L p) ≫ 𝟙 _) ≫
      (upperStar Ab.{u + 1} p).map f.hom ≫ (𝟙 _ ≫ condensedPullbackHom L p) = _
  simp

private instance plainPullback_additive
    {X Y : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (p : Y ⟶ X) : (plainPullback L p).Additive :=
  Functor.additive_of_iso (plainPullbackIso L p)

private instance plainPullback_finiteColimits
    {X Y : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (p : Y ⟶ X) : PreservesFiniteColimits (plainPullback L p) :=
  preservesFiniteColimits_of_natIso (plainPullbackIso L p)

@[irreducible] private noncomputable def plainPullbackComp
    {X Y Z : Scheme.{u}}
    (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj L] [IsCommMonObj L]
    (a : Z ⟶ Y) (p : Y ⟶ X) :
    plainPullback L (a ≫ p) ≅ plainPullback L p ⋙ plainPullback L a :=
  (plainPullbackIso L (a ≫ p)).symm ≪≫ CondensedRing.upperStarComp L a p ≪≫
    Functor.isoWhiskerRight (plainPullbackIso L p) _ ≪≫
      Functor.isoWhiskerLeft _ (plainPullbackIso L a)

@[irreducible] private noncomputable def evaluationCoordinates
    {C D : Type*} [Category C] [Category D]
    {K : Type*} [Field K] (P : C ⥤ D) (H : D ⥤ ModuleCat.{u + 1} K)
    (A : C) (B : D) (r : P.obj A ≅ B) (b₀ : H.obj B ≃ₗ[K] K) :
    (P ⋙ H).obj A ≃ₗ[K] K :=
  (H.mapIso r).toLinearEquiv.trans b₀

set_option backward.isDefEq.respectTransparency true in
private theorem plainPointScalar
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X : Scheme.{u}} (Ω : Type u) [Field Ω]
    (q : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω))
    (f : Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
      Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X)) :
    condensedFieldPointCoefficient E Ω z
      ((plainRegularIso (condensedFieldCoefficientRingObj E) q).inv ≫
        (plainPullback (condensedFieldCoefficientRingObj E) q).map f ≫
        (plainRegularIso (condensedFieldCoefficientRingObj E) q).hom) =
      ringScalar E X (q z) f.hom := by
  exact pointCoefficient_from_hom E Ω z q f.hom
    ((plainRegularIso (condensedFieldCoefficientRingObj E) q).inv ≫
      (plainPullback (condensedFieldCoefficientRingObj E) q).map f ≫
      (plainRegularIso (condensedFieldCoefficientRingObj E) q).hom)
    (plainRegular_map (condensedFieldCoefficientRingObj E) q f)

set_option backward.isDefEq.respectTransparency true in
private theorem exists_evaluation_at_point
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X : Scheme.{u}} (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (q : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω)) :
    ∃ H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
        (condensedRingObj (condensedFieldCoefficientRingObj E) (Spec (.of Ω))) ⥤
        ModuleCat.{u + 1} E,
      H.Additive ∧ PreservesFiniteColimits H ∧
      CondensedFieldPointScalarProperty E Ω z H ∧
      ∃ b : (plainPullback (condensedFieldCoefficientRingObj E) q ⋙ H).obj
        (Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X)) ≃ₗ[E] E,
        ∀ f : Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
            Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X),
          b ((plainPullback (condensedFieldCoefficientRingObj E) q ⋙ H).map f
          (b.symm 1)) = ringScalar E X (q z) f.hom := by
  obtain ⟨H, ha, hc, hHs⟩ := exists_condensedField_point_evaluation E Ω z
  refine ⟨H, ha, hc, hHs, ?_⟩
  obtain ⟨b₀, hb₀⟩ := hHs
  let t := plainRegularIso (condensedFieldCoefficientRingObj E) q
  let h := H.mapIso t
  let b := h.toLinearEquiv.trans b₀
  refine ⟨b, fun f ↦ ?_⟩
  change b₀ (H.map t.hom
    (H.map ((plainPullback (condensedFieldCoefficientRingObj E) q).map f)
      (H.map t.inv (b₀.symm 1)))) = _
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, hb₀]
  exact plainPointScalar E Ω q z f

private theorem models_free_cover
    {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hf : ∀ P : Mod Ab.{u + 1} (scalarRingObj Λ),
      Mod.IsFinitelyPresented (scalarRingObj Λ) P → Mod.IsFree (scalarRingObj Λ) P)
    (hM : HasFiniteConstantLocalModel Λ X M) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree (condensedRingObj Λ (C.X i))
        ((CondensedRing.upperStar Λ (C.f i)).obj M) := by
  obtain ⟨C, hC⟩ := (finiteConstantLocalModel_iff_exists_cover Λ M).mp hM
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hC i
  obtain ⟨n, ⟨a⟩⟩ := hf P hP
  exact ⟨n, ⟨e ≪≫ (finiteConstantScalarExtension Λ (C.X i)).mapIso a ≪≫
    scalarFreeIso Λ (C.X i) n⟩⟩

private theorem finrank_scalar_cokernel {K : Type*} [Field K] [DecidableEq K]
    {A : ModuleCat.{u + 1} K} (b : A ≃ₗ[K] K) (f : A ⟶ A) :
    Module.finrank K (cokernel f : ModuleCat.{u + 1} K) =
      if b (f (b.symm 1)) = 0 then 1 else 0 := by
  classical
  let a := b (f (b.symm 1))
  have h (v : A) : b (f v) = b v * a := by
    have hv : v = (b v) • b.symm 1 := by
      apply b.injective
      simp
    calc
      b (f v) = b ((b v) • f (b.symm 1)) := by
        conv_lhs => rw [hv, map_smul]
      _ = b v * a := b.map_smul (b v) (f (b.symm 1))
  by_cases ha : a = 0
  · have hf : f = 0 := by
      ext v
      apply b.injective
      change b (f v) = b 0
      simpa only [ha, mul_zero, map_zero] using h v
    rw [if_pos ha, hf]
    calc
      _ = Module.finrank K A := (cokernelZeroIsoTarget).toLinearEquiv.finrank_eq
      _ = 1 := b.finrank_eq.trans (Module.finrank_self K)
  · have hs : Function.Surjective f := by
      intro v
      refine ⟨b.symm (b v / a), b.injective ?_⟩
      rw [h, b.apply_symm_apply, div_mul_cancel₀ _ ha]
    have : Epi f := (ModuleCat.epi_iff_surjective f).mpr hs
    have : Subsingleton (cokernel f : ModuleCat.{u + 1} K) :=
      ModuleCat.subsingleton_of_isZero (isZero_cokernel_of_epi f)
    rw [if_neg ha]
    exact Module.finrank_zero_of_subsingleton

private theorem evaluation_free_finrank
    {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    {K : Type*} [Field K] (G : C ⥤ ModuleCat.{u + 1} K) [G.Additive]
    (A : C) (b : G.obj A ≃ₗ[K] K) (n : ℕ) :
    Module.finrank K (G.obj (⨁ fun _ : Fin n ↦ A)) = n := by
  calc
    _ = Module.finrank K (Fin n → K) :=
      (finiteFreeEvaluationCoords A G b n).finrank_eq
    _ = n := by simp

private theorem evaluation_cokernel_finrank
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts D] [HasCokernels C]
    {K : Type*} [Field K]
    (F : C ⥤ ModuleCat.{u + 1} K) [F.Additive] [PreservesFiniteColimits F]
    (G : D ⥤ ModuleCat.{u + 1} K) [G.Additive]
    (A : C) (B : D) (b : G.obj B ≃ₗ[K] K) (f : A ⟶ A) (n : ℕ)
    (e : F.obj (cokernel f) ≅ G.obj (⨁ fun _ : Fin n ↦ B)) :
    Module.finrank K (cokernel (F.map f) : ModuleCat.{u + 1} K) = n :=
  (PreservesCokernel.iso F f).toLinearEquiv.finrank_eq.symm.trans
    (e.toLinearEquiv.finrank_eq.trans (evaluation_free_finrank G B b n))

private theorem evaluated_cokernel_rank
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts D] [HasCokernels C]
    {K : Type*} [Field K] [DecidableEq K]
    (F : C ⥤ ModuleCat.{u + 1} K) [F.Additive] [PreservesFiniteColimits F]
    (G : D ⥤ ModuleCat.{u + 1} K) [G.Additive]
    (A : C) (B : D) (b : F.obj A ≃ₗ[K] K) (c : G.obj B ≃ₗ[K] K)
    (f : A ⟶ A) (n : ℕ)
    (e : F.obj (cokernel f) ≅ G.obj (⨁ fun _ : Fin n ↦ B))
    (k : K) (hk : b (F.map f (b.symm 1)) = k) :
    (if k = 0 then 1 else 0) = n := by
  have h := finrank_scalar_cokernel b (F.map f)
  rw [hk] at h
  exact h.symm.trans (evaluation_cokernel_finrank F G A B c f n e)

set_option backward.isDefEq.respectTransparency true in
private theorem rank_at_geometric_point
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E] [DecidableEq E]
    {X V : Scheme.{u}} (p : V ⟶ X)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ V)
    (z : Spec (.of Ω))
    (f : Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
      Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X))
    (n : ℕ)
    (e : (CondensedRing.upperStar (condensedFieldCoefficientRingObj E) p).obj (cokernel f) ≅
      Mod.finiteFree (condensedRingObj (condensedFieldCoefficientRingObj E) V) n) :
    (if ringScalar E X (p (a z)) f.hom = 0 then 1 else 0) = n := by
  classical
  obtain ⟨H, ha, hc, ⟨b₀, hb₀⟩, b, hb⟩ := exists_evaluation_at_point E Ω (a ≫ p) z
  let := ha
  let := hc
  let F := plainPullback (condensedFieldCoefficientRingObj E) (a ≫ p) ⋙ H
  let G := plainPullback (condensedFieldCoefficientRingObj E) a ⋙ H
  let bG := evaluationCoordinates (plainPullback (condensedFieldCoefficientRingObj E) a) H _ _
    (plainRegularIso (condensedFieldCoefficientRingObj E) a) b₀
  let e₁ := H.mapIso
    ((plainPullbackComp (condensedFieldCoefficientRingObj E) a p).app (cokernel f))
  let e₂ := (plainPullbackIso (condensedFieldCoefficientRingObj E) p).symm.app
    (cokernel f) ≪≫ e
  let e₃ := (plainPullback (condensedFieldCoefficientRingObj E) a ⋙ H).mapIso e₂
  let eG := e₁ ≪≫ e₃
  exact evaluated_cokernel_rank F G _ _ b bG f n eG _ (hb f)

set_option backward.isDefEq.respectTransparency true in
private theorem rankIndicator_constant_on_free_cover
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E] [DecidableEq E]
    {X : Scheme.{u}}
    (f : Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
      Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hC : ∀ i, Mod.IsFree
      (condensedRingObj (condensedFieldCoefficientRingObj E) (C.X i))
      ((CondensedRing.upperStar (condensedFieldCoefficientRingObj E) (C.f i)).obj
        (cokernel f))) :
    ∀ i, ∃ n : ℕ, ∀ v : C.X i,
      (if ringScalar E X (C.f i v) f.hom = 0 then 1 else 0) = n := by
  classical
  intro i
  obtain ⟨n, ⟨e⟩⟩ := hC i
  refine ⟨n, fun v ↦ ?_⟩
  let Ω := AlgebraicClosure ((C.X i).residueField v)
  let a : Spec (.of Ω) ⟶ C.X i :=
    Spec.map (CommRingCat.ofHom (algebraMap ((C.X i).residueField v) Ω)) ≫
      (C.X i).fromSpecResidueField v
  let z : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have haz : a z = v := Scheme.fromSpecResidueField_apply v
    ((Spec.map (CommRingCat.ofHom (algebraMap ((C.X i).residueField v) Ω))) z)
  have h := rank_at_geometric_point E (C.f i) Ω a z f n e
  rw [haz] at h
  exact h


private theorem cokernel_regular_finitelyPresented
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (f : Mod.regular R ⟶ Mod.regular R) : Mod.IsFinitelyPresented R (cokernel f) := by
  let e : Mod.finiteFree R 1 ≅ Mod.regular R := biproductUniqueIso _
  let g := e.hom ≫ f ≫ e.inv
  exact ⟨1, 1, g, ⟨cokernel.mapIso f g e.symm e.symm (by simp [g])⟩⟩

@[instance_reducible] private noncomputable def counterexampleNormedField :
    NormedField (ULift.{u} ℚ_[2]) :=
  NormedField.induced _ ℚ_[2] ULift.ringEquiv ULift.down_injective

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_endMul
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) (t : C(X, E)) (x : X) :
    ringScalar E X x
      (endMul (condensedFieldContinuousMapIso E X).hom.hom t).hom = t x := by
  have h := congrArg (fun g : C(X, E) ↦ g x)
    (endFun_endMul (condensedFieldContinuousMapIso E X).hom.hom t)
  change ringScalar E X x _ = _
  unfold ringScalar coefficientValue condensedFieldContinuousCoefficientMap
  have hi : inv (condensedFieldContinuousMapIso E X).hom.hom =
      (condensedFieldContinuousMapIso E X).inv.hom := by
    simpa only [IsIso.Iso.inv_hom, Mon.forget] using
      (Functor.map_inv (Mon.forget _) (condensedFieldContinuousMapIso E X).hom).symm
  simpa only [endFun, coeffEndFun, regConj, Mod.comp_hom', Mod.comap,
    Mod.regularIsoOfIsIso_inv_hom, Mod.regularIsoOfIsIso_hom_hom,
    IsIso.Iso.inv_hom, hi] using h

private theorem scalar_zeroIndicator_locallyConstant
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E] [DecidableEq E]
    (X : Scheme.{u}) [T2Space X] [CompactSpace X] (t : C(X, E))
    (hall : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (condensedFieldCoefficientRingObj E) X),
      IsLocallyFinitelyPresented (condensedRingObj (condensedFieldCoefficientRingObj E) X) M →
        HasFiniteConstantLocalModel (condensedFieldCoefficientRingObj E) X M) :
    IsLocallyConstant (fun x : X ↦ if t x = 0 then (1 : ℕ) else 0) := by
  classical
  let f : Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
      Mod.regular (condensedRingObj (condensedFieldCoefficientRingObj E) X) :=
    endMul (condensedFieldContinuousMapIso E X).hom.hom t
  have hM := locallyFinitelyPresented_of_finitelyPresented
    (condensedRingObj (condensedFieldCoefficientRingObj E) X) (cokernel f)
    (cokernel_regular_finitelyPresented
      (condensedRingObj (condensedFieldCoefficientRingObj E) X) f)
  obtain ⟨C, hC⟩ := models_free_cover (condensedFieldCoefficientRingObj E) (cokernel f)
    (scalarField_finitelyPresented_isFree E) (hall (cokernel f) hM)
  have h := locallyConstant_of_cover_constants
    (fun x ↦ if ringScalar E X x f.hom = 0 then 1 else 0)
    C (rankIndicator_constant_on_free_cover E f C hC)
  simpa only [f, scalar_endMul] using h

private theorem counterexample_of_zeroIndicator
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E] [DecidableEq E]
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] (t : C(S, E))
    (ht : ¬ IsLocallyConstant (fun s : S ↦ if t s = 0 then (1 : ℕ) else 0)) :
    ¬ ∀ (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj L] [IsCommMonObj L] (X : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj L X)),
      IsLocallyFinitelyPresented (condensedRingObj L X) M →
        HasFiniteConstantLocalModel L X M := by
  intro hall
  let K := ULift.{u} ℚ
  let X : Scheme.{u} := Spec (.of (LocallyConstant S K))
  let e : X ≃ₜ S :=
    (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := K)).symm.trans
      (Homeomorph.prodUnique S (PrimeSpectrum K))
  have : T2Space X := e.symm.t2Space
  let tX : C(X, E) := t.comp ⟨e, e.continuous⟩
  have h := scalar_zeroIndicator_locallyConstant E X tX
    (fun M hM ↦ hall (condensedFieldCoefficientRingObj E) X M hM)
  apply ht
  have hS := h.comp_continuous e.symm.continuous
  simpa only [Function.comp_def, tX, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    e.apply_symm_apply] using hS

/-- Local finite presentation does not imply finite constant local models for all
commutative condensed coefficients.
Source: blueprint local-model final sentence and node proof, Steps 5–7.
Proof: take continuous 2-adic coefficients and X = Spec LC(S,ℚ), using universe lifts,
where S = ℕ ∪ {∞}. The locally constant prime spectrum identifies |X| with S.
The continuous function t(n) = 2^n, t(∞) = 0 defines a multiplication endomorphism
of the regular coefficient module. Its cokernel has a one-by-one finite presentation.
Every finitely presented scalar module is finite free, since the scalar ring is the
2-adic field. Geometric evaluation preserves finite sums and cokernels and identifies
the regular module with that field. The cokernel consequently has dimension zero
at every finite point and dimension one at infinity. A finite constant local model
would make this dimension constant on the image of each covering member.
The covering condition supplies finitely many affine opens of covering members whose
images cover X. Each image is compact in the Hausdorff space S and hence closed.
A function constant on every member of a finite closed cover is locally constant.
Its zero fibre would therefore be the dense proper subset ℕ of S and closed,
a contradiction. The universal implication is refuted by this single example;
no restriction on its quantified schemes or coefficients is imposed.
(blueprint: det-def-sfb-constructible-local-model). -/
theorem not_locallyFinitelyPresented_implies_finiteConstantLocalModel :
    ¬ ∀ (L : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj L] [IsCommMonObj L] (X : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj L X)),
      IsLocallyFinitelyPresented (condensedRingObj L X) M → HasFiniteConstantLocalModel L X M := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := counterexampleNormedField.{u}
  let E := ULift.{u} ℚ_[2]
  have : TotallyDisconnectedSpace E :=
    Topology.IsEmbedding.uliftDown.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let S := ULift.{u} (OnePoint ℕ)
  have : TotallyDisconnectedSpace S := Homeomorph.ulift.symm.totallyDisconnectedSpace
  let t₀ : C(OnePoint ℕ, ℚ_[2]) := OnePoint.continuousMapMkNat
    (fun n ↦ (2 : ℚ_[2]) ^ n) 0
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := 2)))
  let t : C(S, E) := ⟨fun s ↦ ULift.up (t₀ s.down),
    continuous_uliftUp.comp (t₀.continuous.comp continuous_uliftDown)⟩
  apply counterexample_of_zeroIndicator E S t
  intro h
  have hs : IsLocallyConstant (fun s : OnePoint ℕ ↦
      if t₀ s = 0 then (1 : ℕ) else 0) := by
    have hh := h.comp_continuous
      (continuous_uliftUp : Continuous (ULift.up : OnePoint ℕ → S))
    have hz (a : ℚ_[2]) : (ULift.up a : E) = 0 ↔ a = 0 :=
      ULift.up_injective.eq_iff
    simpa only [Function.comp_def, t, ContinuousMap.coe_mk,
      ULift.down_up, hz] using hh
  have hclosed : IsClosed (Set.range ((↑) : ℕ → OnePoint ℕ)) := by
    have he : {s : OnePoint ℕ | (if t₀ s = 0 then (1 : ℕ) else 0) = 0} =
        Set.range ((↑) : ℕ → OnePoint ℕ) := by
      ext s
      induction s using OnePoint.rec with
      | infty => simp [t₀, OnePoint.continuousMapMkNat,
          OnePoint.continuousMapMkDiscrete, OnePoint.continuousMapMk]
      | coe n => simp [t₀, OnePoint.continuousMapMkNat,
          OnePoint.continuousMapMkDiscrete, OnePoint.continuousMapMk]
    exact he ▸ hs.isClosed_fiber 0
  have heq := (OnePoint.denseRange_coe (X := ℕ)).closure_range
  rw [hclosed.closure_eq] at heq
  exact OnePoint.infty_notMem_range_coe (X := ℕ) (heq ▸ Set.mem_univ _)

end AlgebraicGeometry.ProEtale
