/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Sheaf.Paper.ScalarCounitFlatPullback
import all Sheaf.Paper.PadicConstantLocalModelTor
import all Sheaf.Paper.FiniteDiscreteScalarConstantModels
import Mathlib.Algebra.Category.ModuleCat.Projective
import all Sheaf.Paper.InternalModuleAbEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Cohomology of admissible constant scalar models

Source: blueprint `sec-six-functors-basics/sk-prop-scalar-six/`
`det-prop-scalar-six-ctf.proof.md`, paragraph (2), and the node's expanded proof,
Stacks Tags 00FM, 093J, 05VD, 08FC, 03ER, 00IK and 010N
(blueprint: lem-sfb-admissible-scalar-model-cohomology).

The scalar realization is the existing `finiteConstantScalarExtension`, with its canonical
constant-scalar map. Ordinary scalar modules are represented by the equivalent internal
modules in abelian groups. The algebraic-closure coefficient is the existing sheaf of
finite-subextension-valued functions. No completion of complexes is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.AdmissibleScalarModel

variable (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Γ] [IsCommMonObj Γ]

/-- The ordinary commutative ring Γ(*), with the multiplication of the existing scalar
ring object. This only applies the existing internal-to-ordinary ring functor.
Source: blueprint local-model paragraph (2), scalar evaluation
(blueprint: lem-sfb-admissible-scalar-model-cohomology). -/
abbrev scalarRing : CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.commMonToRing.obj (CommMon.mk (scalarRingObj Γ))

/-- An internal scalar module read as the same ordinary module, using its actual action.
Source: blueprint local-model paragraph (2), ordinary scalar modules
(blueprint: lem-sfb-admissible-scalar-model-cohomology). -/
def ordinaryScalarModule (M : Mod Ab.{u + 1} (scalarRingObj Γ)) :
    ModuleCat.{u + 1} (scalarRing Γ) :=
  @ModuleCat.of (scalarRing Γ) _ M.X _
    (InternalAbelianSheafModule.ordinaryModule (scalarRingObj Γ) M)

/-- The bounded finite-projective scalar complexes occurring in the statement. The
bounds and term conditions are the same ones used by `IsPerfectRingComplex`, before
localization; the module structure is the existing internal action, read ordinarily.
Source: blueprint local-model paragraph (2), bounded projective scalar model
(blueprint: lem-sfb-admissible-scalar-model-cohomology). -/
def boundedProjectiveScalars :
    ObjectProperty (CochainComplex (Mod Ab.{u + 1} (scalarRingObj Γ)) ℤ) :=
  fun Q ↦ ∃ a b : ℤ, Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
    ∀ i : ℤ, Module.Projective (scalarRing Γ) (ordinaryScalarModule Γ (Q.X i)) ∧
      Module.Finite (scalarRing Γ) (ordinaryScalarModule Γ (Q.X i))

/-- The common conclusions for one coefficient: Noetherian scalars, additive exact
realization on all modules, finitely presented scalar cohomology, its natural realization
isomorphism, and a finite constant local model for each realized cohomology sheaf.
The isomorphism is between functors on the full category of bounded finite-projective
scalar complexes, so naturality includes every morphism of those complexes.
Source: blueprint local-model paragraph (2); Stacks Tags 00IK and 010N
(blueprint: lem-sfb-admissible-scalar-model-cohomology). -/
def Assertions (W : Scheme.{u}) : Prop :=
  IsNoetherianRing (scalarRing Γ) ∧
  ∃ (_ : (finiteConstantScalarExtension Γ W).Additive),
    PreservesFiniteLimits (finiteConstantScalarExtension Γ W) ∧
    PreservesFiniteColimits (finiteConstantScalarExtension Γ W) ∧
    (∀ q : ℤ, Nonempty
      ((boundedProjectiveScalars Γ).ι ⋙
          (finiteConstantScalarExtension Γ W).mapHomologicalComplex (.up ℤ) ⋙
          HomologicalComplex.homologyFunctor _ (.up ℤ) q ≅
        (boundedProjectiveScalars Γ).ι ⋙
          HomologicalComplex.homologyFunctor _ (.up ℤ) q ⋙
          finiteConstantScalarExtension Γ W)) ∧
    ∀ (Q : (boundedProjectiveScalars Γ).FullSubcategory) (q : ℤ),
      Module.FinitePresentation (scalarRing Γ)
        (ordinaryScalarModule Γ (Q.obj.homology q)) ∧
      HasFiniteConstantLocalModel Γ W
        (((finiteConstantScalarExtension Γ W).mapHomologicalComplex (.up ℤ)).obj
          Q.obj |>.homology q)

@[instance_reducible]
private def pointSheafMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := inferInstance

@[instance_reducible]
private def schemeSheafMonoidal (W : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) := inferInstance

section ProofHelpers

attribute [local instance] pointSheafMonoidal schemeSheafMonoidal

attribute [local irreducible] Mod.extendScalars Mod.extendScalarsComp
  Mod.extendScalarsIsoOfEq Mod.extendScalarsIsoComapInv Mod.extendRestrictAdjunction
  Mod.regularExtensionIso scalarCoefficientHom finiteConstantScalarExtension

private def scalarIdentity : AddCommGrpCat.of (scalarRing Γ) ⟶ scalarRingObj Γ := 𝟙 _

private instance scalarIdentity_iso : IsIso (scalarIdentity Γ) := by
  unfold scalarIdentity
  infer_instance

private instance scalarIdentity_monoidal : IsMonHom (scalarIdentity Γ) := by
  constructor
  · ext z
    change (z.down : scalarRing Γ) = (MonObj.one (X := scalarRingObj Γ)).hom z
    rw [← zsmul_one]
    change z.down • ((MonObj.one (X := scalarRingObj Γ)).hom (ULift.up 1)) = _
    rw [← map_zsmul]
    apply congrArg (MonObj.one (X := scalarRingObj Γ)).hom
    apply ULift.ext
    change z.down • (1 : ℤ) = z.down
    simp
  · apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    rfl

private def ordinaryFunctor : Mod Ab.{u + 1} (scalarRingObj Γ) ⥤
    ModuleCat.{u + 1} (scalarRing Γ) :=
  Mod.comap (scalarIdentity Γ) ⋙ internalToModule (scalarRing Γ)

private instance ordinaryFunctor_equivalence : (ordinaryFunctor Γ).IsEquivalence := by
  have : (Mod.comap (scalarIdentity Γ)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (scalarIdentity Γ)).isEquivalence_functor
  unfold ordinaryFunctor
  infer_instance

private instance ordinaryFunctor_additive : (ordinaryFunctor Γ).Additive := by
  have : (internalToModule (scalarRing Γ)).Additive := ⟨by intros; rfl⟩
  unfold ordinaryFunctor
  infer_instance

private theorem finitePresentation_homology [IsNoetherianRing (scalarRing Γ)]
    (Q : (boundedProjectiveScalars Γ).FullSubcategory) (q : ℤ) :
    Module.FinitePresentation (scalarRing Γ)
      (ordinaryScalarModule Γ (Q.obj.homology q)) := by
  obtain ⟨a, b, ha, hb, hterms⟩ := Q.property
  let F := ordinaryFunctor Γ
  let C := (F.mapHomologicalComplex (.up ℤ)).obj Q.obj
  have : Module.Finite (scalarRing Γ) (ordinaryScalarModule Γ (Q.obj.X q)) :=
    (hterms q).2
  have : Module.Finite (scalarRing Γ) (C.X q) :=
    Module.Finite.equiv (show ordinaryScalarModule Γ (Q.obj.X q) ≃ₗ[scalarRing Γ]
      C.X q from { __ := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl })
  let S := C.sc q
  have : Module.Finite (scalarRing Γ) S.X₂ := by
    change Module.Finite (scalarRing Γ) (C.X q)
    infer_instance
  have : Module.Finite (scalarRing Γ) (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective _ (LinearMap.ker S.g.hom).injective_subtype
  have : Module.Finite (scalarRing Γ) S.moduleCatLeftHomologyData.H := by
    change Module.Finite (scalarRing Γ)
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  have : Module.Finite (scalarRing Γ) (C.homology q) :=
    Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm
  let e := (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app Q.obj
  have : Module.Finite (scalarRing Γ) (ordinaryScalarModule Γ (Q.obj.homology q)) :=
    Module.Finite.equiv (M := C.homology q) e.toLinearEquiv
  exact Module.finitePresentation_of_finite _ _

private def regularCoordinates :
    (ordinaryFunctor Γ).obj (Mod.regular (scalarRingObj Γ)) ≃ₗ[scalarRing Γ]
      scalarRing Γ where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def freeCoordinates (n : ℕ) :
    (ordinaryFunctor Γ).obj (Mod.finiteFree (scalarRingObj Γ) n) ≃ₗ[scalarRing Γ]
      (Fin n → scalarRing Γ) :=
  (((ordinaryFunctor Γ).mapBiproduct _).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi _).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ regularCoordinates Γ)

private theorem internal_finitelyPresented
    (P : Mod Ab.{u + 1} (scalarRingObj Γ))
    (hP : Module.FinitePresentation (scalarRing Γ) (ordinaryScalarModule Γ P)) :
    Mod.IsFinitelyPresented (scalarRingObj Γ) P := by
  let H := ordinaryFunctor Γ
  let R := scalarRingObj Γ
  have : Module.FinitePresentation (scalarRing Γ) (H.obj P) := hP
  obtain ⟨n, m, f, g, hf, hg⟩ :=
    Module.FinitePresentation.exists_fin' (scalarRing Γ) (H.obj P)
  let fn := (freeCoordinates Γ n).toModuleIso
  let fm := (freeCoordinates Γ m).toModuleIso
  let g' : H.obj (Mod.finiteFree R m) ⟶ H.obj (Mod.finiteFree R n) :=
    fm.hom ≫ ModuleCat.ofHom g ≫ fn.inv
  let f' : H.obj (Mod.finiteFree R n) ⟶ H.obj P := fn.hom ≫ ModuleCat.ofHom f
  have hsurj : Function.Surjective f' := hf.comp fn.toLinearEquiv.surjective
  have hexact : Function.Exact g'.hom f'.hom := by
    intro x
    change f ((freeCoordinates Γ n) x) = 0 ↔ _
    rw [hg]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(freeCoordinates Γ m).symm y, ?_⟩
      change (freeCoordinates Γ n).symm
        (g ((freeCoordinates Γ m) ((freeCoordinates Γ m).symm y))) = x
      rw [LinearEquiv.apply_symm_apply, hy, LinearEquiv.symm_apply_apply]
    · rintro ⟨y, hy⟩
      refine ⟨(freeCoordinates Γ m) y, ?_⟩
      change (freeCoordinates Γ n).symm (g ((freeCoordinates Γ m) y)) = x at hy
      exact ((freeCoordinates Γ n).symm_apply_eq).mp hy
  let gi := H.preimage g'
  have hgi : H.map gi = g' := H.map_preimage _
  let ci : H.obj P ≅ cokernel g' :=
    (ModuleCat.isColimitCokernelCofork g' f' hexact hsurj).coconePointUniqueUpToIso
      (colimit.isColimit _)
  refine ⟨n, m, gi, ⟨H.preimageIso ?_⟩⟩
  exact ci ≪≫ cokernel.mapIso g' (H.map gi) (Iso.refl _) (Iso.refl _) (by simp [hgi]) ≪≫
    (PreservesCokernel.iso H gi).symm

private theorem realization_has_model (W : Scheme.{u})
    (P : Mod Ab.{u + 1} (scalarRingObj Γ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Γ) P)
    (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Γ W))
    (e : M ≅ (finiteConstantScalarExtension Γ W).obj P) :
    HasFiniteConstantLocalModel Γ W M := by
  apply (finiteConstantLocalModel_iff_exists_cover Γ M).mpr
  let C : Scheme.Cover.{u} Scheme.proetalePrecoverage W :=
    CategoryTheory.Precoverage.ZeroHypercover.singleton (𝟙 W)
      (by simpa using Scheme.proetalePrecoverage.mem_coverings_of_isIso (𝟙 W))
  refine ⟨C, fun i ↦ ⟨P, hP, ⟨?_⟩⟩⟩
  exact (CondensedRing.upperStarId Γ W).app M ≪≫ e

private theorem assertions_of_exact (W : Scheme.{u})
    (hn : IsNoetherianRing (scalarRing Γ))
    (hl : PreservesFiniteLimits (finiteConstantScalarExtension Γ W)) : Assertions Γ W := by
  let := hn
  let := hl
  have hr : PreservesFiniteColimits (finiteConstantScalarExtension Γ W) := by
    unfold finiteConstantScalarExtension
    infer_instance
  have ha : (finiteConstantScalarExtension Γ W).Additive :=
    Functor.additive_of_preserves_binary_products _
  refine ⟨hn, ha, hl, hr, ?_, ?_⟩
  · intro q
    exact ⟨Functor.isoWhiskerLeft _
      ((finiteConstantScalarExtension Γ W).mapHomologicalComplexHomologyIso (.up ℤ) q)⟩
  · intro Q q
    have hp := finitePresentation_homology Γ Q q
    refine ⟨hp, ?_⟩
    exact realization_has_model Γ W _ (internal_finitelyPresented Γ _ hp) _
      (((finiteConstantScalarExtension Γ W).mapHomologicalComplexHomologyIso
        (.up ℤ) q).app Q.obj)

private def scalarCoordinates (K : Type (u + 1)) [CommRing K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Γ) [IsMonHom φ] [IsIso φ] :
    K ≃+* scalarRing Γ :=
  { toEquiv := Equiv.ofBijective (fun x : K ↦ φ.hom x)
      (ConcreteCategory.bijective_of_isIso φ)
    map_add' := φ.hom.map_add
    map_mul' := fun a b ↦
      ConcreteCategory.congr_hom (IsMonHom.mul_hom φ) (a ⊗ₜ[ℤ] b) }

private theorem scalar_noetherian (K : Type (u + 1)) [CommRing K]
    [IsNoetherianRing K] (φ : AddCommGrpCat.of K ⟶ scalarRingObj Γ)
    [IsMonHom φ] [IsIso φ] : IsNoetherianRing (scalarRing Γ) :=
  isNoetherianRing_of_ringEquiv K (scalarCoordinates Γ K φ)

private theorem field_exact (K : Type (u + 1)) [Field K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Γ) [IsMonHom φ] [IsIso φ]
    (W : Scheme.{u}) : PreservesFiniteLimits (finiteConstantScalarExtension Γ W) := by
  let H := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : H.IsEquivalence := by dsimp only [H]; infer_instance
  have : (internalToModule K).Additive := ⟨by intros; rfl⟩
  have : H.Additive := by dsimp only [H]; infer_instance
  let F := finiteConstantScalarExtension Γ W
  have : PreservesFiniteColimits F := by
    dsimp only [F, finiteConstantScalarExtension]
    infer_instance
  have : PreservesBinaryBiproducts F :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hex : ∀ S : ShortComplex _, S.ShortExact → (S.map F).ShortExact := by
    intro S hS
    have : CategoryTheory.Projective (H.obj S.X₃) := inferInstance
    have : CategoryTheory.Projective S.X₃ := H.projective_of_map_projective inferInstance
    exact (hS.splittingOfProjective.map F).shortExact
  exact (((Functor.exact_tfae F).out 0 3 rfl rfl).mp hex).1

private theorem finite_extension_equivalence (W : Scheme.{u})
    [IsIso (scalarCoefficientHom Γ W)] :
    (Mod.extendScalars (scalarCoefficientHom Γ W)).IsEquivalence := by
  have : (Mod.comap (asIso (scalarCoefficientHom Γ W)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (asIso (scalarCoefficientHom Γ W)).inv).isEquivalence_functor
  exact Functor.isEquivalence_of_iso
    (Mod.extendScalarsIsoComapInv (scalarCoefficientHom Γ W)).symm

private theorem finite_exact (W : Scheme.{u}) [IsIso (scalarCoefficientHom Γ W)] :
    PreservesFiniteLimits (finiteConstantScalarExtension Γ W) := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint W) := by
    dsimp only [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteLimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (scalarConstant W) := by
    unfold scalarConstant
    infer_instance
  have := finite_extension_equivalence Γ W
  unfold finiteConstantScalarExtension
  infer_instance

end ProofHelpers

/-- For every admissible coefficient and every scheme the scalar realization is exact,
and the cohomology of every bounded finite-projective scalar model is the realization
of its finitely presented scalar cohomology, naturally in the model. For finite rings
the actual canonical scalar ring map and its extension-restriction unit are invertible;
this is the canonical constant-ring identification and `m ↦ 1 ⊗ m` identification of
all realized modules with constants. For integral coefficients the regular coefficient
module restricted along that same canonical map is flat.

Source: blueprint `det-prop-scalar-six-ctf.proof.md`, paragraph (2), and the expanded
node proof, Steps 1–7 (blueprint: lem-sfb-admissible-scalar-model-cohomology).

Proof plan:
1. Evaluate Γ at the one-point profinite set. The scalar rings are respectively the
finite ring, O_E, E, and the algebraic closure. Finite rings and fields are Noetherian,
including the finite zero ring. The integral ring is a PID by
lem-weil-l-adic-extension-integers-dvr, hence Noetherian by
lem-weil-pbc-pid-noetherian-normal.
2. For finite discrete rings, lem-sfb-totally-disconnected-coefficient-realization
identifies the coefficient sheaf with the constant sheaf, respecting products and
constant scalars. The canonical scalar map is therefore its inverse ring isomorphism.
The tensor unit maps give the asserted extension-restriction unit isomorphism on
all modules, naturally; constants are additive and exact by
def-sfb-site-derived-constant-module-functor (Stacks 093J).
3. In the integral case lem-sfb-constant-to-continuous-scalar-flat gives flatness on
the point. Transfer by lem-c2-internal-section-module-flatness, pull back by
lem-weil-pbc-ringed-topos-flat-module-pullback, and identify pulled-back constants by
lem-sfb-geometric-inverse-image-constant-module. This is flatness for precisely the
canonical scalar action in the statement.
4. For both field cases lem-exc-constant-field-module-flat gives flatness over the
constant scalar field. This uses no constant-sheaf assertion for the coefficient;
it also applies to the finite-subextension-valued algebraic-closure sheaf.
5. The functor is the canonical scalar realization of def-sfb-flat-scalar-realization.
It is additive, and lem-sfb-flat-scalar-realization-exact gives exactness from
Steps 3–4; Step 2 supplies the finite case.
6. Apply lem-weil-pbc-scalar-perfect-cohomology-and-pid-models to the bounded
finite-projective scalar complex over the Noetherian scalar ring. Its cohomology is
finitely presented, without requiring it to be projective or torsion free.
7. Apply lem-weil-pbc-exact-functor-complex-cohomology to termwise realization.
Exactness identifies cycles and boundaries, hence their quotient, naturally in the
complex. The finite presentation from Step 6 and the identity cover witness
det-def-sfb-constructible-local-model, also for torsion and zero cohomology.
All complexes and cohomology here are ordinary and uncompleted. -/
theorem admissible_scalar_model_cohomology (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [Finite A] [DiscreteTopology A],
      Assertions (Profinite.continuousCoefficientRingObj A) W ∧
      IsIso (scalarCoefficientHom (Profinite.continuousCoefficientRingObj A) W) ∧
      ∀ M : Mod Ab.{u + 1} (scalarRingObj (Profinite.continuousCoefficientRingObj A)),
        IsIso ((Mod.extendRestrictAdjunction
          (scalarCoefficientHom (Profinite.continuousCoefficientRingObj A) W)).unit.app
            (((scalarConstant W).mapMod
              (scalarRingObj (Profinite.continuousCoefficientRingObj A))).obj M))) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Assertions (Profinite.padicIntegersRingObj ℓ E) W ∧
      ObjectProperty.flat
        ((Mod.comap (scalarCoefficientHom (Profinite.padicIntegersRingObj ℓ E) W)).obj
          (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W))) ∧
      Assertions (Profinite.continuousMapRingObj E) W) ∧
    Assertions (Profinite.padicAlgClRingObj ℓ) W := by
  let := pointSheafMonoidal.{u}
  let := schemeSheafMonoidal W
  refine ⟨?_, ?_, ?_⟩
  · intro A _ _ _ _ _
    let Γ := Profinite.continuousCoefficientRingObj A
    have hi : IsIso (scalarCoefficientHom Γ W) :=
      FiniteDiscreteOrdinary.scalarCoefficient_isIso A W
    refine ⟨assertions_of_exact Γ W
      (scalar_noetherian Γ (ULift.{u + 1} A) (FiniteDiscreteOrdinary.scalarHom A))
      (finite_exact Γ W), hi, ?_⟩
    have := finite_extension_equivalence Γ W
    intro M
    infer_instance
  · intro E
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : IsTopologicalRing (PadicAlgCl.integers ℓ E) :=
      PadicAlgCl.isTopologicalRing_integers ℓ E
    have : IsNoetherianRing (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) :=
      isNoetherianRing_of_ringEquiv _ ULift.ringEquiv.symm
    refine ⟨assertions_of_exact _ W
      (scalar_noetherian _ _ (continuousScalarHom (PadicAlgCl.integers ℓ E)))
      (scalarExtension_leftExact _
        (counitExtension_leftExact (PadicAlgCl.integers ℓ E)) W), ?_, ?_⟩
    · exact scalarCounit_flat_pullback _
        (counitExtension_leftExact (PadicAlgCl.integers ℓ E)) W
    · have : IsNoetherianRing (ULift.{u + 1} E) :=
        isNoetherianRing_of_ringEquiv E ULift.ringEquiv.symm
      exact assertions_of_exact _ W
        (scalar_noetherian _ _ (continuousScalarHom E))
        (field_exact _ _ (continuousScalarHom E) W)
  · have : IsNoetherianRing (ULift.{u + 1} (PadicAlgCl ℓ)) :=
      isNoetherianRing_of_ringEquiv (PadicAlgCl ℓ) ULift.ringEquiv.symm
    exact assertions_of_exact _ W
      (scalar_noetherian _ _ (qbarScalarHom ℓ)) (field_exact _ _ (qbarScalarHom ℓ) W)

end AlgebraicGeometry.ProEtale.AdmissibleScalarModel
