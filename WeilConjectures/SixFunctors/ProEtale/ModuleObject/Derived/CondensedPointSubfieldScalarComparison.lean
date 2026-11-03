/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Separation
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
public import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.AlgebraicGeometry.Sp.SpSliceNormalizedScalarExtensionBasis
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompNatIsoCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarScalarBasisSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint

/-! # Condensed point-section scalar comparison for finite subfields

Source: Hemo–Richarz–Scholbach, Lemma 4.1(1), specialized to a separably closed
geometric point (blueprint: lem-zl-condensed-point-subfield-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev terminalCoefficientRing (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :=
  Evaluation.A (Scheme.ProEt.topology X) Λ (Scheme.ProEt.mk (𝟙 X))

private def regularSectionIso
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) Λ).functor.obj (Mod.regular Λ) ≅
      SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) Λ)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    apply ConcreteCategory.hom_ext
    intro m
    rfl
  · intro Z W f
    ext
    rfl

private def regularSectionEquiv
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) Λ) :
    (Mod.regular Λ ⟶ M) ≃
      (Evaluation.sections (Scheme.ProEt.topology X) Λ (Scheme.ProEt.mk (𝟙 X))).obj M :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) Λ
  e.fullyFaithfulFunctor.homEquiv.trans
    ((Iso.homCongr (regularSectionIso X Λ) (Iso.refl _)).trans
      ((SheafOfModules.unitHomEquiv (e.functor.obj M)).trans
        (Evaluation.terminalSectionsEquiv (Scheme.ProEt.mk (𝟙 X)) (Scheme.ProEt.isTerminalMkId X)
          (e.functor.obj M))))

private theorem regularSectionEquiv_apply
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) Λ)
    (f : Mod.regular Λ ⟶ M) :
    regularSectionEquiv X Λ M f =
      (Evaluation.sections (Scheme.ProEt.topology X) Λ
        (Scheme.ProEt.mk (𝟙 X))).map f (1 : (terminalCoefficientRing X Λ)) := by
  rfl

private def scalarSectionHom
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ →+* (terminalCoefficientRing X Λ) where
  toFun s := regularSectionEquiv X Λ (Mod.regular Λ) (Mod.regularEndRingHom s)
  map_one' := by
    rw [map_one, regularSectionEquiv_apply]
    change (Evaluation.sections (Scheme.ProEt.topology X) Λ
      (Scheme.ProEt.mk (𝟙 X))).map (𝟙 (Mod.regular Λ)) (1 : (terminalCoefficientRing X Λ)) =
        (1 : (terminalCoefficientRing X Λ))
    rfl
  map_mul' s t := by
    let S := Evaluation.sections (Scheme.ProEt.topology X) Λ (Scheme.ProEt.mk (𝟙 X))
    let ms : terminalCoefficientRing X Λ →ₗ[terminalCoefficientRing X Λ]
        terminalCoefficientRing X Λ :=
      (S.map (Mod.regularEndRingHom s)).hom
    let mt : terminalCoefficientRing X Λ →ₗ[terminalCoefficientRing X Λ]
        terminalCoefficientRing X Λ :=
      (S.map (Mod.regularEndRingHom t)).hom
    rw [map_mul]
    change S.map (Mod.regularEndRingHom t ≫ Mod.regularEndRingHom s)
      (1 : (terminalCoefficientRing X Λ)) = _
    rw [S.map_comp]
    change ms (mt 1) = ms 1 * mt 1
    calc
      ms (mt 1) = mt 1 * ms 1 := by
        simpa only [smul_eq_mul, _root_.mul_one] using ms.map_smul (mt 1) 1
      _ = ms 1 * mt 1 := mul_comm _ _
  map_zero' := by
    rw [map_zero, regularSectionEquiv_apply, Functor.map_zero]
    rfl
  map_add' s t := by
    simp only [regularSectionEquiv_apply, map_add]
    rfl

private def scalarSectionEquiv
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ ≃+* (terminalCoefficientRing X Λ) :=
  RingEquiv.ofBijective (scalarSectionHom X Λ)
    ((regularSectionEquiv X Λ (Mod.regular Λ)).bijective.comp Mod.regularEndRingHom_bijective)

private def pointCoyoneda
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  coyonedaSections ((Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (MonObj.Γ Λ)).toRingHom)

private def pointCoyonedaIso
    (X : Scheme.{u})
    (Λ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    pointCoyoneda X Λ ≅ Evaluation.sections (Scheme.ProEt.topology X) Λ
      (Scheme.ProEt.mk (𝟙 X)) ⋙
        ModuleCat.restrictScalars.{u + 1} (scalarSectionEquiv X Λ).toRingHom := by
  let S := Evaluation.sections (Scheme.ProEt.topology X) Λ (Scheme.ProEt.mk (𝟙 X))
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply LinearEquiv.toModuleIso (X₁ := (pointCoyoneda X Λ).obj M)
      (X₂ := (S ⋙ ModuleCat.restrictScalars.{u + 1}
        (scalarSectionEquiv X Λ).toRingHom).obj M)
    refine
      { toEquiv := regularSectionEquiv X Λ M
        map_add' := fun f g ↦ by
          change S.map (f + g) (1 : (terminalCoefficientRing X Λ)) =
            S.map f (1 : terminalCoefficientRing X Λ) +
              S.map g (1 : terminalCoefficientRing X Λ)
          rw [S.map_add]
          rfl
        map_smul' := fun s f ↦ by
          change S.map (Mod.regularEndRingHom s ≫ f) (1 : (terminalCoefficientRing X Λ)) =
            scalarSectionHom X Λ s • S.map f (1 : (terminalCoefficientRing X Λ))
          rw [S.map_comp]
          let lf : terminalCoefficientRing X Λ →ₗ[terminalCoefficientRing X Λ] S.obj M :=
            (S.map f).hom
          change lf (scalarSectionHom X Λ s) = scalarSectionHom X Λ s • lf 1
          simpa only [smul_eq_mul, _root_.mul_one] using
            lf.map_smul (scalarSectionHom X Λ s) 1 }
  · intro M N f
    ext g
    change S.map (g ≫ f) (1 : (terminalCoefficientRing X Λ)) =
      S.map f (S.map g (1 : (terminalCoefficientRing X Λ)))
    rw [S.map_comp]
    rfl

private theorem scalarSectionHom_eq (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (s : MonObj.Γ R) :
    scalarSectionHom X R s =
      InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R
        (Scheme.ProEt.mk (𝟙 X)) s := by
  change regularSectionEquiv X R (Mod.regular R) (Mod.regularEndRingHom s) = _
  rw [regularSectionEquiv_apply]
  let U := op (Scheme.ProEt.mk (𝟙 X))
  let z := ((Functor.LaxMonoidal.ε
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})).app U).hom (ULift.up 1)
  have h := congrArg (fun f ↦ (f.hom.app U).hom z)
    (Mod.one_comp_regularLift_regular s.hom)
  exact h

-- Coverings of the geometric point split; sheafification therefore preserves its sections.

private theorem point_cover_id (k : Type u) [Field k] [IsSepClosed k]
    {S : Sieve (Scheme.ProEt.mk (𝟙 (Spec (.of k))))}
    (hS : S ∈ Scheme.ProEt.topology (Spec (.of k)) _) : S (𝟙 _) := by
  obtain ⟨R, hR, hRS⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  have hR' := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
    inf_le_right) _ hR
  obtain ⟨Y, g, hg, x, -⟩ := hR'.1 (IsLocalRing.closedPoint k)
  obtain ⟨hg⟩ := hg
  obtain @⟨V, f, hf⟩ := hg
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale_of_isSepClosed V.hom x
  have : S (MorphismProperty.Over.homMk
      (A := Scheme.ProEt.mk (𝟙 (Spec (.of k)))) σ hσ ≫ f) :=
    S.downward_closed (hRS _ _ hf) _
  convert this using 1
  exact (Scheme.ProEt.isTerminalMkId _).hom_ext _ _

private theorem point_sheafify_bijective (k : Type u) [Field k] [IsSepClosed k]
    (P : (Spec (.of k)).ProEtᵒᵖ ⥤ Ab.{u + 1}) :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology (Spec (.of k))) P).app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · simpa using point_cover_id k
      (Presheaf.equalizerSieve_mem _ (toSheafify _ P) x y hxy)
  · obtain ⟨t, ht⟩ := point_cover_id k
      (Presheaf.imageSieve_mem _ (toSheafify _ P) s)
    exact ⟨t, by simpa using ht⟩

private instance pointPullback_additive (X : Scheme.{u}) :
    (upperStarFromPoint X).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)

-- Transport the actual convolution scalars together with the module sections.

private def pointScalarEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsSepClosed k] :
    MonObj.Γ Λ ≃+* Evaluation.A (Scheme.ProEt.topology (Spec (.of k)))
      (condensedRingObj Λ (Spec (.of k))) (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) :=
  (RingEquiv.ofBijective (condensedRingScalarSections Λ (Spec (.of k)))
    (InternalAbelianSheafModule.globalMapFunctor_bijective
      (upperStarFromPoint (Spec (.of k))) (Functor.FullyFaithful.ofFullyFaithful _) Λ)).trans
    (scalarSectionEquiv (Spec (.of k)) (condensedRingObj Λ (Spec (.of k))))

private def pointSectionEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsSepClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    LinearEquiv (RingHomClass.toRingHom (pointScalarEquiv Λ k))
      (σ' := (RingHomClass.toRingHom (pointScalarEquiv Λ k).symm))
      ((condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
      ((Evaluation.sections (Scheme.ProEt.topology (Spec (.of k)))
        (condensedRingObj Λ (Spec (.of k))) (Scheme.ProEt.mk (𝟙 (Spec (.of k))))).obj M) where
  toEquiv := regularSectionEquiv (Spec (.of k)) (condensedRingObj Λ (Spec (.of k))) M
  map_add' f g := by
    exact (pointCoyonedaIso (Spec (.of k)) (condensedRingObj Λ (Spec (.of k)))).hom.app M
      |>.hom.map_add f g
  map_smul' s f := by
    exact (pointCoyonedaIso (Spec (.of k)) (condensedRingObj Λ (Spec (.of k)))).hom.app M
      |>.hom.map_smul (condensedRingScalarSections Λ (Spec (.of k)) s) f

private theorem scalarSectionHom_natural (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (p : R ⟶ S) [IsMonHom p] (s : MonObj.Γ R) :
    scalarSectionHom X S (MonObj.Γ.map p s) =
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) p).hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        (scalarSectionHom X R s) := by
  rw [scalarSectionHom_eq, scalarSectionHom_eq]
  rfl

private theorem pointScalarEquiv_natural
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (k : Type u) [Field k] [IsSepClosed k]
    (s : MonObj.Γ Λ) :
    pointScalarEquiv Λ' k (MonObj.Γ.map a s) =
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) (coefficientMap a (Spec (.of k)))).hom.app
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) (pointScalarEquiv Λ k s) := by
  change scalarSectionHom _ _
    (MonObj.Γ.mapFunctor (upperStarFromPoint (Spec (.of k))) (MonObj.Γ.map a s)) = _
  rw [MonObj.Γ.mapFunctor_map]
  exact scalarSectionHom_natural _ _ _

private theorem regularSectionEquiv_extend (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (p : R ⟶ S) [IsMonHom p]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (m : Mod.regular R ⟶ M) :
    regularSectionEquiv X S ((Mod.extendScalars p).obj M)
        ((Mod.extendScalarsObjRegularIso p).inv ≫ (Mod.extendScalars p).map m) =
      (Mod.extendUnitHom p M).hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        (regularSectionEquiv X R M m) := by
  rw [regularSectionEquiv_apply, regularSectionEquiv_apply]
  have h : η[S] ≫
      ((Mod.extendScalarsObjRegularIso p).inv ≫ (Mod.extendScalars p).map m).hom =
      η[R] ≫ m.hom ≫ Mod.extendUnitHom p M := by
    rw [Mod.comp_hom', Mod.one_comp_extendScalarsObjRegularIso_inv_hom_assoc,
      Mod.extendUnitHom_naturality]
  let U := op (Scheme.ProEt.mk (𝟙 X))
  let z := ((Functor.LaxMonoidal.ε
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})).app U).hom (ULift.up 1)
  exact congrArg (fun f ↦ (f.hom.app U).hom z) h


-- The convolution ring of constant E-sections is a field, so scalar extension is exact.

private theorem subfield_sections_exact (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E))) := by
  let Λ := Profinite.continuousMapRingObj.{u} E
  let V := Profinite.of PUnit.{u + 1}
  let e := InternalAbelianSheafModule.sectionGlobalEquiv.{u + 1, u + 1, u}
    (coherentTopology Profinite.{u}) Λ V Profinite.isTerminalPUnit
  have : Nontrivial ((InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (coherentTopology Profinite.{u}) Λ).obj.obj (op V)) :=
    inferInstanceAs (Nontrivial (ULift.{u + 1} C(V, E)))
  have : Nontrivial (MonObj.Γ Λ) := e.symm.injective.nontrivial
  let c := Profinite.continuousMapConstRingHom.{u} E
  let r := RingEquiv.ofBijective c ⟨c.injective,
    Profinite.continuousMapConstRingHom_surjective E⟩
  let : Field (MonObj.Γ Λ) := (r.symm.toMulEquiv.isField (Field.toIsField E)).toField
  let f := MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E)
  have hf : f.Flat := by
    let := f.toAlgebra
    change Module.Flat (MonObj.Γ Λ) (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ))
    infer_instance
  exact ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf

private theorem point_comparison_isIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (k : Type u) [Field k] [IsSepClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (α : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (MonObj.Γ.map a)).obj
        ((condensedRingCoefficientSections Λ (Spec (.of k))).obj M) ⟶
      (condensedRingCoefficientSections Λ' (Spec (.of k))).obj
        ((Mod.extendScalars (coefficientMap a (Spec (.of k)))).obj M))
    (hα : ∀ m : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M,
      α ((1 : MonObj.Γ Λ') ⊗ₜ[MonObj.Γ Λ, MonObj.Γ.map a] m) =
        (Mod.extendScalarsObjRegularIso (coefficientMap a (Spec (.of k)))).inv ≫
          (Mod.extendScalars (coefficientMap a (Spec (.of k)))).map m) : IsIso α := by
  let X := Spec (.of k)
  let J := Scheme.ProEt.topology X
  let R := condensedRingObj Λ X
  let S := condensedRingObj Λ' X
  let p := coefficientMap a X
  let U := op (Scheme.ProEt.mk (𝟙 X))
  let ER := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let ES := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J S
  let q := InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} J p
  let f := MonObj.Γ.map a
  let f' := (q.hom.app U).hom
  let := f.toAlgebra
  let := f'.toAlgebra
  let ea := pointScalarEquiv Λ k
  let eb := pointScalarEquiv Λ' k
  let em := pointSectionEquiv Λ k M
  let bE : LinearEquiv (RingHomClass.toRingHom ea) (σ' := (RingHomClass.toRingHom ea.symm))
      (MonObj.Γ Λ') (Evaluation.A J S U.unop) :=
    { toEquiv := eb.toEquiv
      map_add' := eb.map_add
      map_smul' := fun r b ↦ by
        change eb (f r * (b : MonObj.Γ Λ')) = f' (ea r) * eb b
        rw [map_mul, pointScalarEquiv_natural a k r] }
  let et := TensorProduct.congr bE em
  let t := AlgebraicGeometry.ProEtale.sectionExtensionIso X p M
  let tu := (SheafOfModules.evaluation _ U).mapIso t
  let en0 := pointSectionEquiv Λ' k ((Mod.extendScalars p).obj M)
  let en := en0.toAddEquiv.trans tu.toLinearEquiv.toAddEquiv
  have en_smul (b : MonObj.Γ Λ')
      (n : (condensedRingCoefficientSections Λ' X).obj ((Mod.extendScalars p).obj M)) :
      en (b • n) = eb b • en n := by
    change tu.hom (en0 (b • n)) = eb b • tu.hom (en0 n)
    rw [map_smulₛₗ, map_smul]
    rfl
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} q (ER.functor.obj M)
  let j := ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app P).app U
  have hj : Function.Bijective j := point_sheafify_bijective k P.presheaf
  have hn (m : (condensedRingCoefficientSections Λ X).obj M) :
      en (α ((1 : MonObj.Γ Λ') ⊗ₜ[MonObj.Γ Λ, f] m)) =
        j ((1 : Evaluation.A J S U.unop) ⊗ₜ[Evaluation.A J R U.unop, f'] em m) := by
    rw [hα]
    change t.hom.val.app U (regularSectionEquiv X S _ _) = _
    rw [regularSectionEquiv_extend]
    exact AlgebraicGeometry.ProEtale.sectionExtensionIso_unit X p M U (em m)
  have hcmp : (fun z ↦ en (α z)) = (fun z ↦ j (et z)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b m =>
      let b' : MonObj.Γ Λ' := b
      change en (α (b' ⊗ₜ[MonObj.Γ Λ, f] m)) = j (et (b' ⊗ₜ[MonObj.Γ Λ, f] m))
      have hb : b' ⊗ₜ[MonObj.Γ Λ, f] m =
          b' • ((1 : MonObj.Γ Λ') ⊗ₜ[MonObj.Γ Λ, f] m) := by
        change _ = (b' * 1) ⊗ₜ[MonObj.Γ Λ, f] m
        rw [_root_.mul_one]
      calc
        en (α (b' ⊗ₜ[MonObj.Γ Λ, f] m)) =
            en (α (b' • ((1 : MonObj.Γ Λ') ⊗ₜ[MonObj.Γ Λ, f] m))) :=
          congrArg (fun z ↦ en (α z)) hb
        _ = en (b' • α ((1 : MonObj.Γ Λ') ⊗ₜ[MonObj.Γ Λ, f] m)) :=
          congrArg en (α.hom.map_smul b' _)
        _ = eb b' • en (α ((1 : MonObj.Γ Λ') ⊗ₜ[MonObj.Γ Λ, f] m)) :=
          en_smul _ _
        _ = eb b' • j ((1 : Evaluation.A J S U.unop) ⊗ₜ[
            Evaluation.A J R U.unop, f'] em m) := congrArg (fun z ↦ eb b' • z) (hn m)
        _ = j (eb b' • ((1 : Evaluation.A J S U.unop) ⊗ₜ[
            Evaluation.A J R U.unop, f'] em m)) := (j.hom.map_smul _ _).symm
        _ = j (et (b' ⊗ₜ[MonObj.Γ Λ, f] m)) := by
          change j ((eb b' * 1) ⊗ₜ[Evaluation.A J R U.unop, f'] em m) =
            j (eb b' ⊗ₜ[Evaluation.A J R U.unop, f'] em m)
          rw [_root_.mul_one]
  have hbij : Function.Bijective (fun z ↦ en (α z)) := by
    rw [hcmp]
    exact hj.comp et.bijective
  apply (ConcreteCategory.isIso_iff_bijective α).mpr
  refine ⟨fun x y h ↦ hbij.1 (congrArg en h), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hbij.2 (en y)
  exact ⟨x, en.injective hx⟩

/-- Target sections in the point scalar comparison.
Source: HRS Lemma 4.1(1)
(blueprint: lem-zl-condensed-point-subfield-scalar-comparison). -/
abbrev pointAlgClSections (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] :=
  condensedRingCoefficientSections (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))

/-- Internal scalar extension at the point in the comparison.
Source: HRS Lemma 4.1(1)
(blueprint: lem-zl-condensed-point-subfield-scalar-comparison). -/
abbrev pointSubfieldExtension (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k] :=
  Mod.extendScalars
    (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (Spec (.of k)))

/-- Ordinary section-ring scalar extension in the comparison.
Source: HRS Lemma 4.1(1)
(blueprint: lem-zl-condensed-point-subfield-scalar-comparison). -/
abbrev pointSubfieldSectionExtension (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (MonObj.Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E))

private theorem subfield_internal_exact (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k] :
    PreservesFiniteLimits (pointSubfieldExtension ℓ E k) := by
  obtain ⟨idx, b, hcoh, hflat, hbasis⟩ :=
    exists_condensedQbar_scalar_basis_sections.{u} ℓ E
  exact hflat (Spec (.of k))

private theorem localization_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (RF : A' ⥤ B') (LG : B' ⥤ D') (LH : A' ⥤ C') (RI : C' ⥤ D')
    (LA : A ⥤ A') (W : MorphismProperty A) [LA.IsLocalization W]
    (LB : B ⥤ B') (LC : C ⥤ C') (LD : D ⥤ D')
    (e0 : F ⋙ G ≅ H ⋙ I)
    (uF : F ⋙ LB ≅ LA ⋙ RF) (cG : LB ⋙ LG ≅ G ⋙ LD)
    (cH : LA ⋙ LH ≅ H ⋙ LC) (uI : I ⋙ LD ≅ LC ⋙ RI) :
    ∃ eta : RF ⋙ LG ≅ LH ⋙ RI, ∀ K,
      LG.map (uF.hom.app K) ≫ eta.hom.app (LA.obj K) ≫ RI.map (cH.hom.app K) =
        cG.hom.app (F.obj K) ≫ LD.map (e0.hom.app K) ≫ uI.hom.app (H.obj K) := by
  let pre : LA ⋙ (RF ⋙ LG) ≅ LA ⋙ (LH ⋙ RI) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight uF.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ cG ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e0 _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ uI ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cH.symm _ ≪≫ Functor.associator _ _ _
  let ff := Localization.fullyFaithfulWhiskeringLeft LA W D'
  let eta := ff.preimageIso pre
  refine ⟨eta, ?_⟩
  intro K
  have he : eta.hom.app (LA.obj K) = pre.hom.app K :=
    NatTrans.congr_app (ff.map_preimage pre.hom) K
  rw [he]
  dsimp only [pre, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← LG.map_comp_assoc, Iso.hom_inv_id_app, LG.map_id, Category.id_comp]
  rw [← RI.map_comp, Iso.inv_hom_id_app, RI.map_id]
  erw [Category.comp_id]

private theorem homotopy_square_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (K : HomotopyCategory A (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompNatIso e (.up ℤ)).hom.app K =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K := by
  rw [Functor.mapHomotopyCategoryCompNatIso_hom]
  simp only [NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.comp_id]
  erw [Category.id_comp]

private theorem homotopy_localization_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Category A'] [Category B'] [Category C'] [Category D']
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (RF : A' ⥤ B') (LG : B' ⥤ D') (LH : A' ⥤ C') (RI : C' ⥤ D')
    (LA : HomotopyCategory A (.up ℤ) ⥤ A')
    (W : MorphismProperty (HomotopyCategory A (.up ℤ))) [LA.IsLocalization W]
    (LB : HomotopyCategory B (.up ℤ) ⥤ B')
    (LC : HomotopyCategory C (.up ℤ) ⥤ C')
    (LD : HomotopyCategory D (.up ℤ) ⥤ D')
    (e0 : F ⋙ G ≅ H ⋙ I)
    (uF : F.mapHomotopyCategory (.up ℤ) ⋙ LB ≅ LA ⋙ RF)
    (cG : LB ⋙ LG ≅ G.mapHomotopyCategory (.up ℤ) ⋙ LD)
    (cH : LA ⋙ LH ≅ H.mapHomotopyCategory (.up ℤ) ⋙ LC)
    (uI : I.mapHomotopyCategory (.up ℤ) ⋙ LD ≅ LC ⋙ RI) :
    ∃ eta : RF ⋙ LG ≅ LH ⋙ RI, ∀ K,
      LG.map (uF.hom.app K) ≫ eta.hom.app (LA.obj K) ≫ RI.map (cH.hom.app K) =
        cG.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
          LD.map ((NatTrans.mapHomotopyCategory e0.hom (.up ℤ)).app K) ≫
            uI.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨eta, hη⟩ := localization_square
    (F.mapHomotopyCategory (.up ℤ)) (G.mapHomotopyCategory (.up ℤ))
    (H.mapHomotopyCategory (.up ℤ)) (I.mapHomotopyCategory (.up ℤ))
    RF LG LH RI LA W LB LC LD
    (Functor.mapHomotopyCategoryCompNatIso e0 (.up ℤ)) uF cG cH uI
  refine ⟨eta, fun K ↦ ?_⟩
  simpa only [homotopy_square_hom F G H I e0 K] using hη K

private theorem mapHomotopy_quotient_obj
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      (HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := rfl

end AlgebraicGeometry.ProEtale.CondensedRing
