/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModelData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FlatCondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.ContinuousMap.LocallyConstant
import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
import WeilConjectures.WeilObject.Sheaf.Stalk
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Direct condensed coefficient fibres at a geometric point

Source: current blueprint, def-weil-finite-coefficient-point; Bhatt--Scholze,
Example 4.1.10; Hemo--Richarz--Scholbach, Lemma 4.1
(blueprint: def-weil-finite-coefficient-point).

The four coefficient rings are used themselves. No category of coefficient-stage
representatives occurs in these constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- Bounded finitely generated scalar cohomology. For the finite quotient this is
finite cohomology, and for either field it is finite-dimensional cohomology.
Source: def-weil-finite-coefficient-point, displayed four target categories
(blueprint: def-weil-finite-coefficient-point). -/
def scalarFiniteCohomology : ObjectProperty
    (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :=
  fun K ↦ (∃ I : Finset ℤ, ∀ i : ℤ, i ∉ I →
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).obj K)) ∧
    ∀ i : ℤ, Module.Finite (condensedScalarRing Λ)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (condensedScalarRing Λ)) i).obj K)

/-- Direct derived evaluation restricted to bounded constructible complexes.
Source: def-weil-finite-coefficient-point, fibre equivalences
(blueprint: def-weil-finite-coefficient-point). -/
def boundedFiber (h : ∀ K : (constantModelBoundedConstructible Λ (Spec (.of k))).FullSubcategory,
    scalarFiniteCohomology Λ ((fiber Λ k).obj K.obj)) :=
  (scalarFiniteCohomology Λ).lift
    ((constantModelBoundedConstructible Λ (Spec (.of k))).ι ⋙ fiber Λ k) h

/-- The inverse is the existing derived scalar realization, restricted to finite
cohomology. Its data is the actual constant sheaf followed by derived extension.
Source: def-weil-finite-coefficient-point, quasi-inverse formula
(blueprint: def-weil-finite-coefficient-point). -/
def boundedRealization (h : ∀ P : (scalarFiniteCohomology Λ).FullSubcategory,
    constantModelBoundedConstructible Λ (Spec (.of k))
      ((condensedScalarRealization Λ (Spec (.of k))).obj P.obj)) :=
  (constantModelBoundedConstructible Λ (Spec (.of k))).lift
    ((scalarFiniteCohomology Λ).ι ⋙ condensedScalarRealization Λ (Spec (.of k))) h

/-- Actual underived evaluation on the geometric point, transported along its
canonical equivalence with the condensed point topos.
Source: def-weil-finite-coefficient-point, exactness assertion
(blueprint: def-weil-finite-coefficient-point). -/
def heartFiber :=
  (((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).inverse ⋙
    CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})

/-- The exact scalar-extension/evaluation adjunction and its derived equivalence.
The selected left adjoint in the heart is specified by its adjunction, so is
unique up to the unique adjunction-compatible isomorphism. Its derived functor
is identified with the fixed scalar realization.
Source: def-weil-finite-coefficient-point, extension/sections adjunction and
four displayed equivalences (blueprint: def-weil-finite-coefficient-point). -/
def DirectPointStatement : Prop :=
  PreservesFiniteLimits (heartFiber Λ k) ∧ PreservesFiniteColimits (heartFiber Λ k) ∧
  ∃ (J : ModuleCat.{u + 1} (condensedScalarRing Λ) ⥤
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        ((upperStarFromPoint (Spec (.of k))).obj Λ))
    (adj : J ⊣ heartFiber Λ k),
    ∃ (hlim : PreservesFiniteLimits J) (hcolim : PreservesFiniteColimits J),
    IsIso adj.unit ∧
    (∃ a : J.Additive,
      letI := a
      letI := hlim
      letI := hcolim
      Nonempty (J.mapDerivedCategory ≅ condensedScalarRealization Λ (Spec (.of k)))) ∧
    ∃ (hF : ∀ K : (constantModelBoundedConstructible Λ (Spec (.of k))).FullSubcategory,
        scalarFiniteCohomology Λ ((fiber Λ k).obj K.obj))
      (hJ : ∀ P : (scalarFiniteCohomology Λ).FullSubcategory,
        constantModelBoundedConstructible Λ (Spec (.of k))
          ((condensedScalarRealization Λ (Spec (.of k))).obj P.obj))
      (a : boundedRealization Λ k hJ ⊣ boundedFiber Λ k hF),
      IsIso a.unit ∧ IsIso a.counit

private theorem ring_equiv_flat {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : e.toRingHom.Flat :=
  RingHom.Flat.of_bijective e.bijective

/-- Canonical section coordinates of a ring sheaf's underlying internal ring.
Source: latest blueprint def-weil-finite-coefficient-point, scalar identification
(blueprint: def-weil-finite-coefficient-point). -/
def ringSheafSectionCoordinates
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] (S : Profinite.{u}) :
    (condensedSectionRing ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)).obj.obj (op S) ≃+*
      R.obj.obj (op S) := by
  let T := coherentTopology Profinite.{u}
  let A := (sheafCompose T (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hm : (sheafToPresheaf T Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  refine { toEquiv := Equiv.refl _
           map_add' := fun _ _ ↦ rfl
           map_mul' := ?_ }
  intro a b
  change (((sheafToPresheaf T Ab.{u + 1}).monObjObj A).mul.app (op S)).hom
    (a ⊗ₜ[ℤ] b) = (show R.obj.obj (op S) from a) * (show R.obj.obj (op S) from b)
  have h := congrArg (fun m : MonObj A.obj ↦ m.mul) hm
  rw [h]
  rfl

private def section_coordinates
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] (S : Profinite.{u}) :
    (condensedSectionRing ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)).obj.obj (op S) ≃+*
      R.obj.obj (op S) := by
  let T := coherentTopology Profinite.{u}
  let A := (sheafCompose T (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hm : (sheafToPresheaf T Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  refine { toEquiv := Equiv.refl _
           map_add' := fun _ _ ↦ rfl
           map_mul' := ?_ }
  intro a b
  change (((sheafToPresheaf T Ab.{u + 1}).monObjObj A).mul.app (op S)).hom
    (a ⊗ₜ[ℤ] b) = (show R.obj.obj (op S) from a) * (show R.obj.obj (op S) from b)
  have h := congrArg (fun m : MonObj A.obj ↦ m.mul) hm
  rw [h]
  rfl

private def continuous_scalar_coordinates
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    condensedScalarRing (Profinite.continuousMapRingObj.{u} T) ≃+* T :=
  (ringSheafSectionCoordinates (Profinite.continuousMapRingSheaf T) (⊤_ Profinite.{u})).trans
    (ULift.ringEquiv.trans
      { toFun := fun f ↦ f default
        invFun := ContinuousMap.const _
        left_inv := fun f ↦ ContinuousMap.ext fun _x ↦
          congrArg f (Subsingleton.elim _ _)
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl })

private theorem continuous_scalar_flat
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (h : ∀ S : Profinite.{u}, (ContinuousMap.C (α := S) (R := T) (A := T)).Flat)
    (S : Profinite.{u}) :
    (CondensedRing.scalarSectionMap (Mon.mk (Profinite.continuousMapRingObj T)) S).Flat := by
  let e := continuous_scalar_coordinates.{u} T
  let d : (condensedSectionRing (Profinite.continuousMapRingObj.{u} T)).obj.obj
      (op S) ≃+* ULift.{u + 1} C(S, T) :=
    ringSheafSectionCoordinates (Profinite.continuousMapRingSheaf T) S
  let a := CondensedRing.scalarSectionMap (Mon.mk (Profinite.continuousMapRingObj T)) S
  have ha : a = d.symm.toRingHom.comp
      ((ULift.ringEquiv.symm.toRingHom.comp ContinuousMap.C).comp e.toRingHom) := by
    ext f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change f.down ((terminal.from S) x) = f.down default
    exact congrArg f.down (Subsingleton.elim _ _)
  change a.Flat
  rw [ha]
  have he : e.toRingHom.Flat :=
    ring_equiv_flat e
  have hd : d.symm.toRingHom.Flat := ring_equiv_flat d.symm
  let v : C(S, T) →+* ULift.{u + 1} C(S, T) := ULift.ringEquiv.symm.toRingHom
  have hv : v.Flat :=
    RingHom.Flat.of_bijective (f := v) ULift.ringEquiv.symm.bijective
  have hc : (v.comp (ContinuousMap.C (α := S) (R := T) (A := T))).Flat :=
    RingHom.Flat.comp (f := ContinuousMap.C) (g := v) (h S) hv
  have hce : ((v.comp (ContinuousMap.C (α := S) (R := T) (A := T))).comp
      e.toRingHom).Flat :=
    RingHom.Flat.comp (f := e.toRingHom) (g := v.comp ContinuousMap.C) he hc
  exact RingHom.Flat.comp (f := (v.comp ContinuousMap.C).comp e.toRingHom)
    (g := d.symm.toRingHom) hce hd

private def scalar_properties : Prop :=
  IsNoetherianRing (condensedScalarRing Λ) ∧
    ∀ S : Profinite.{u}, ExtremallyDisconnected S →
      (CondensedRing.scalarSectionMap (Mon.mk Λ) S).Flat

private theorem continuous_scalar_properties
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [IsNoetherianRing T]
    (h : ∀ S : Profinite.{u}, (ContinuousMap.C (α := S) (R := T) (A := T)).Flat) :
    scalar_properties (Profinite.continuousMapRingObj.{u} T) :=
  ⟨isNoetherianRing_of_ringEquiv _ (continuous_scalar_coordinates T).symm,
    fun S _ ↦ continuous_scalar_flat T h S⟩

private theorem integers_scalar_properties
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    scalar_properties (Profinite.padicIntegersRingObj.{u} ℓ E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  apply continuous_scalar_properties (PadicAlgCl.integers ℓ E)
  intro S
  rw [show ContinuousMap.C (α := S) (R := PadicAlgCl.integers ℓ E)
    (A := PadicAlgCl.integers ℓ E) = algebraMap _ C(S, PadicAlgCl.integers ℓ E)
    from rfl, RingHom.flat_algebraMap_iff]
  let : Module.IsTorsionFree (PadicAlgCl.integers ℓ E)
      C(S, PadicAlgCl.integers ℓ E) := by
    constructor
    intro a ha f g hfg
    apply ContinuousMap.ext
    intro x
    exact ha.left (ContinuousMap.congr_fun hfg x)
  infer_instance

private theorem field_scalar_properties
    (E : Type) [TopologicalSpace E] [Field E] [IsTopologicalRing E] :
    scalar_properties (Profinite.continuousMapRingObj.{u} E) := by
  apply continuous_scalar_properties E
  intro S
  exact RingHom.Flat.of_isField (Field.toIsField E) _

private def algClosure_scalar_coordinates (ℓ : ℕ) [Fact ℓ.Prime] :
    condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ) ≃+* PadicAlgCl ℓ :=
  (ringSheafSectionCoordinates (Profinite.padicAlgClCondensedRing ℓ) (⊤_ Profinite.{u})).trans
    { toFun := fun f ↦ f.down.val default
      invFun := Profinite.PadicAlgCl.constSectionRingHom ℓ (op (⊤_ Profinite.{u}))
      left_inv := fun f ↦ by
        apply ULift.ext
        apply Subtype.ext
        apply ContinuousMap.ext
        intro x
        exact congrArg f.down.val (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

private theorem singleton_cover_id
    {S : Sieve (⊤_ Profinite.{u})} (hS : S ∈ coherentTopology Profinite.{u} _) :
    S (𝟙 _) := by
  obtain ⟨I, hI, Y, π, hπ, hS⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S).mp hS
  let := hI
  have hs : ∀ b : (⊤_ Profinite.{u}), ∃ (i : I) (y : Y i), π i y = b :=
    ((Profinite.effectiveEpiFamily_tfae Y π).out 0 2).mp hπ
  obtain ⟨i, y, _⟩ := hs ((terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit)
  let σ : (⊤_ Profinite.{u}) ⟶ Y i := ConcreteCategory.ofHom
    ⟨fun _ ↦ y, continuous_const⟩
  have hσ : σ ≫ π i = 𝟙 _ := terminalIsTerminal.hom_ext _ _
  simpa only [hσ] using S.downward_closed (hS i) σ

private theorem singleton_abelian_colimits
    (I : Type (u + 1)) [SmallCategory I] :
    PreservesColimitsOfShape I
      ((sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (op (⊤_ Profinite.{u}))) := by
  let J := coherentTopology Profinite.{u}
  let T := op (⊤_ Profinite.{u})
  let E := (sheafSections J Ab.{u + 1}).obj T
  have hb (G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
      Function.Bijective ((toSheafify J G).app T) := by
    refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
    · have hh := singleton_cover_id (Presheaf.equalizerSieve_mem J
        (toSheafify _ G) x y hxy)
      change G.map (𝟙 T) x = G.map (𝟙 T) y at hh
      simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hh
    · obtain ⟨t, ht⟩ := singleton_cover_id
        (Presheaf.imageSieve_mem J (toSheafify _ G) s)
      change (toSheafify J G).app T t = (sheafify J G).map (𝟙 T) s at ht
      rw [CategoryTheory.Functor.map_id] at ht
      exact ⟨t, ht⟩
  have (G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) : IsIso ((Functor.whiskerRight
      (sheafificationAdjunction J Ab.{u + 1}).unit
      ((evaluation _ Ab.{u + 1}).obj T)).app G) :=
    (isIso_iff_of_reflects_iso _ (forget Ab.{u + 1})).1
      ((isIso_iff_bijective _).2 (hb G))
  have : IsIso (Functor.whiskerRight (sheafificationAdjunction J Ab.{u + 1}).unit
      ((evaluation _ Ab.{u + 1}).obj T)) := NatIso.isIso_of_isIso_app _
  have : PreservesColimitsOfShape I (presheafToSheaf J Ab.{u + 1} ⋙ E) :=
    preservesColimitsOfShape_of_natIso (asIso (Functor.whiskerRight
      (sheafificationAdjunction J Ab.{u + 1}).unit
      ((evaluation _ Ab.{u + 1}).obj T)))
  exact (sheafificationAdjunction J Ab.{u + 1}).preservesColimitsOfShape_of_comp E I

private theorem singleton_sections_colimits : PreservesColimitsOfSize.{u + 1, u + 1}
    (CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})) := by
  constructor
  intro I hI
  let J := coherentTopology Profinite.{u}
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (condensedSectionRing Λ)
  let M := SheafOfModules.evaluation.{u + 1} R (op (⊤_ Profinite.{u}))
  let E := (sheafSections J Ab.{u + 1}).obj (op (⊤_ Profinite.{u}))
  have : PreservesColimitsOfShape I E := singleton_abelian_colimits I
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf R) :=
    ((moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.2.2.2 I).2.1
  let U := forget₂ (ModuleCat.{u + 1} (R.obj.obj (op (⊤_ Profinite.{u})))) Ab.{u + 1}
  have : PreservesColimitsOfShape I (M ⋙ U) :=
    inferInstanceAs (PreservesColimitsOfShape I (SheafOfModules.toSheaf R ⋙ E))
  have : PreservesColimitsOfShape I M :=
    preservesColimitsOfShape_of_reflects_of_preserves M U
  exact inferInstanceAs (PreservesColimitsOfShape I
    ((InternalAbelianSheafModule.sectionModuleEquivalence J Λ).functor ⋙ M))

private theorem finite_support_iff_bounded
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    (∃ I : Finset ℤ, ∀ i, i ∉ I →
      IsZero ((DerivedCategory.homologyFunctor C i).obj K)) ↔
      DerivedCategory.TStructure.t.bounded K := by
  classical
  have h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} ↔
      DerivedCategory.TStructure.t.bounded K := by
    rw [Set.finite_iff_bddBelow_bddAbove]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ by
        by_contra hh
        exact (not_le_of_gt hi) (ha hh)⟩,
        ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ by
          by_contra hh
          exact (not_le_of_gt hi) (hb hh)⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨⟨a, fun i hi ↦ le_of_not_gt fun hh ↦
        hi ((DerivedCategory.isGE_iff K a).1 ha i hh)⟩,
        ⟨b, fun i hi ↦ le_of_not_gt fun hh ↦
          hi ((DerivedCategory.isLE_iff K b).1 hb i hh)⟩⟩
  rw [← h]
  constructor
  · rintro ⟨I, hI⟩
    exact I.finite_toSet.subset fun i hi ↦ by
      by_contra hh
      exact hi (hI i hh)
  · intro hI
    exact ⟨hI.toFinset, fun i hi ↦ by
      by_contra hh
      exact hi (hI.mem_toFinset.mpr hh)⟩

private theorem restrict_adjunction
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [IsIso adj.unit]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj))
    (hQ : ∀ Y : Q.FullSubcategory, F.essImage Y.obj) :
    ∃ a : Q.lift (P.ι ⋙ F) hF ⊣ P.lift (Q.ι ⋙ G) hG,
      IsIso a.unit ∧ IsIso a.counit := by
  have ff := adj.fullyFaithfulLOfIsIsoUnit
  let := ff.full
  let := ff.faithful
  let L := Q.lift (P.ι ⋙ F) hF
  let R := P.lift (Q.ι ⋙ G) hG
  let a : L ⊣ R := adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulι P)
    (ObjectProperty.fullyFaithfulι Q) (Iso.refl _) (Iso.refl _)
  have hi (Y : Q.FullSubcategory) : IsIso (a.counit.app Y) := by
    have := (adj.isIso_counit_app_iff_mem_essImage).mpr (hQ Y)
    let X : P.FullSubcategory := ⟨G.obj Y.obj, hG Y⟩
    let e : Q.ι.obj (L.obj X) ≅ Q.ι.obj Y := asIso (adj.counit.app Y.obj)
    exact a.isIso_counit_app_of_iso ((ObjectProperty.fullyFaithfulι Q).preimageIso e).symm
  exact ⟨a, inferInstance, NatIso.isIso_of_isIso_app _⟩

def heartFiberDerivedIso : (heartFiber Λ k).mapDerivedCategory ≅ fiber Λ k := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u})
  let := Functor.additive_of_preserves_binary_products e.inverse
  exact Functor.mapDerivedCategoryCompIso e.inverse S ≪≫
    Functor.isoWhiskerLeft e.inverse.mapDerivedCategory
      S.rightDerivedFunctorIsoMapDerivedCategory.symm

private theorem heart_adjunction_unit
    (J : ModuleCat.{u + 1} (condensedScalarRing Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        ((upperStarFromPoint (Spec (.of k))).obj Λ))
    (adj : J ⊣ heartFiber Λ k) : IsIso adj.unit := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u})
  let L := J ⋙ e.inverse
  let a : L ⊣ S := (adj.comp e.symm.toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm S ≪≫ Functor.leftUnitor S)
  have : IsIso a.unit := CondensedRing.Evaluation.contractible_realization_ordinary_unit
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
    (singleton_sections_colimits Λ) L a
  have ff := a.fullyFaithfulLOfIsIsoUnit
  have : L.Full := ff.full
  have : L.Faithful := ff.faithful
  have : J.Full := Functor.Full.of_comp_faithful J e.inverse
  have : J.Faithful := Functor.Faithful.of_comp J e.inverse
  infer_instance

private def ordinary_adjunction :
    CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k)) ⊣ heartFiber Λ k := by
  let T := coherentTopology Profinite.{u}
  let c := commutativeSiteConstantModuleFunctor T (condensedScalarRing Λ)
  let m := condensedScalarExtensionModel Λ
  let e := InternalAbelianSheafModule.sectionModuleEquivalence T Λ
  let E := SheafOfModules.flatScalarExtension T (condensedScalarMap Λ)
  let t : m.E ≅ E := NatIso.ofComponents (fun M ↦ eqToIso (m.obj_eq M)) (by
    intro M N f
    dsimp [E]
    rw [m.map_eq]
    simp
    rfl)
  let R := c ⋙ m.E ⋙ e.inverse
  let r : R ≅ CondensedRing.Evaluation.terminalScalarRealization T Λ
      (⊤_ Profinite.{u}) terminalIsTerminal :=
    Functor.isoWhiskerLeft c (Functor.isoWhiskerRight t e.inverse) ≪≫
      (Functor.associator c E e.inverse).symm
  let d := CondensedRing.Evaluation.contractible_realization_underived_data
    T Λ (⊤_ Profinite.{u}) terminalIsTerminal
  let a := d.choose_spec.choose_spec.some
  let b : R ⊣ CondensedRing.Evaluation.sections T Λ (⊤_ Profinite.{u}) :=
    a.ofNatIsoLeft r.symm
  let p := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  exact (b.comp p.toAdjunction).ofNatIsoLeft
    (Functor.associator c (m.E ⋙ e.inverse) p.functor ≪≫
      Functor.isoWhiskerLeft c (Functor.associator m.E e.inverse p.functor))

private theorem point_global_model
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    IsConstantModelConstructible Λ (Spec (.of k)) M ↔
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ P ∧
          Nonempty (((upperStarFromPoint (Spec (.of k))).mapMod Λ).obj P ≅ M) := by
  classical
  have hqc : CompactSpace (Spec (.of k)) ∧ QuasiSeparatedSpace (Spec (.of k)) :=
    ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hqc]
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨z⟩ : Nonempty (Spec (.of k)) := inferInstance
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ ▸ Set.mem_univ z)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, hy⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField
      (S.immersion a) (Field.toIsField k) (𝟙 _) z ha
    obtain ⟨𝒰, h𝒰⟩ := hS a
    obtain ⟨i, g, hg⟩ := 𝒰.exists_comp_eq_of_isSepClosed_of_proetale y
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    let G := CondensedRing.upperStar Λ g
    let N := (CondensedRing.upperStar Λ (𝒰.f i)).obj
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M)
    let e : G.obj N ≅ M :=
      G.mapIso ((CondensedRing.upperStarComp Λ (𝒰.f i) (S.immersion a)).app M).symm ≪≫
        ((CondensedRing.upperStarComp Λ g (𝒰.f i ≫ S.immersion a)).app M).symm ≪≫
        eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
          (by rw [reassoc_of% hg, hy])) ≪≫ (CondensedRing.upperStarId Λ _).app M
    exact ⟨P, hP, ⟨((CondensedRing.upperStarFromPointModComp Λ g).app P).symm ≪≫
      G.mapIso eP.symm ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    refine ⟨Scheme.Stratification.trivial _, fun a ↦ ?_⟩
    refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    refine ⟨P, hP, ⟨?_⟩⟩
    exact (CondensedRing.upperStarId Λ _).app _ ≪≫
      (CondensedRing.upperStarId Λ _).app _ ≪≫ eP.symm

private def condensed_regular_iso
    (L : ModuleCat.{u + 1} (condensedScalarRing Λ) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (adj : L ⊣ CondensedRing.Evaluation.sections
      (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})) :
    L.obj (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)) ≅
      Mod.regular Λ := by
  let T := coherentTopology Profinite.{u}
  let e := InternalAbelianSheafModule.sectionModuleEquivalence T Λ
  let R := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (condensedSectionRing Λ)
  let B := e.inverse.obj (SheafOfModules.unit R)
  let S := CondensedRing.Evaluation.sections T Λ (⊤_ Profinite.{u})
  let F := S ⋙ forget (ModuleCat.{u + 1} (condensedScalarRing Λ))
  let p : F.CorepresentableBy
      (L.obj (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ))) :=
    { homEquiv := fun {M} ↦ (adj.homEquiv _ M).trans
        (ModuleCat.homEquiv.trans
          (LinearMap.ringLmapEquivSelf (condensedScalarRing Λ) ℤ (S.obj M)).toEquiv)
      homEquiv_comp := by
        intro M N f g
        simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
        rfl }
  let q : F.CorepresentableBy B :=
    { homEquiv := fun {M} ↦ (e.symm.toAdjunction.homEquiv (SheafOfModules.unit R) M).trans
        ((SheafOfModules.unitHomEquiv (e.functor.obj M)).trans
          (CondensedRing.Evaluation.terminalSectionsEquiv
            (⊤_ Profinite.{u}) terminalIsTerminal (e.functor.obj M)))
      homEquiv_comp := by intro M N f g; rfl }
  let r : e.functor.obj (Mod.regular Λ) ≅ SheafOfModules.unit R := by
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
  exact p.uniqueUpToIso q ≪≫ e.inverse.mapIso r.symm ≪≫
    (e.unitIso.app (Mod.regular Λ)).symm

private theorem scalar_models_iff
    [IsNoetherianRing (condensedScalarRing Λ)]
    (L : ModuleCat.{u + 1} (condensedScalarRing Λ) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    [L.Additive] [L.Full] [PreservesFiniteColimits L]
    (r : L.obj (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)) ≅
      Mod.regular Λ)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Mod.IsFinitelyPresented Λ P ↔
      ∃ N : ModuleCat.{u + 1} (condensedScalarRing Λ),
        Module.Finite (condensedScalarRing Λ) N ∧ Nonempty (L.obj N ≅ P) := by
  classical
  let R := condensedScalarRing Λ
  let B (n : ℕ) := ModuleCat.of R (Fin n → R)
  let b (n : ℕ) : L.obj (B n) ≅ Mod.finiteFree Λ n :=
    L.mapIso (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)).symm ≪≫
      L.mapBiproduct (fun _ : Fin n ↦ ModuleCat.of R R) ≪≫
        biproduct.mapIso (fun _ ↦ r)
  constructor
  · rintro ⟨n, m, f, ⟨ef⟩⟩
    let g : B m ⟶ B n := L.preimage ((b m).hom ≫ f ≫ (b n).inv)
    have : Module.Finite R (B n) := inferInstanceAs (Module.Finite R (Fin n → R))
    have : Module.Finite R (cokernel g : ModuleCat R) :=
      Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient g).toLinearEquiv.symm
    refine ⟨cokernel g, inferInstance, ⟨?_⟩⟩
    refine PreservesCokernel.iso L g ≪≫
      cokernel.mapIso (L.map g) f (b m) (b n) ?_ ≪≫ ef.symm
    simp [g]
  · rintro ⟨N, hN, ⟨eN⟩⟩
    have := hN
    have := Module.finitePresentation_of_finite R N
    obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R N
    let f' : B n ⟶ N := ModuleCat.ofHom f
    let g' : B m ⟶ B n := ModuleCat.ofHom g
    let eN' : N ≅ cokernel g' :=
      (ModuleCat.isColimitCokernelCofork g' f' hg hf).coconePointUniqueUpToIso
        (colimit.isColimit _)
    let t := (b m).inv ≫ L.map g' ≫ (b n).hom
    exact ⟨n, m, t, ⟨eN.symm ≪≫ L.mapIso eN' ≪≫ PreservesCokernel.iso L g' ≪≫
      cokernel.mapIso (L.map g') t (b m) (b n) (by simp [t])⟩⟩

private theorem heart_classification [IsNoetherianRing (condensedScalarRing Λ)]
    (J : ModuleCat.{u + 1} (condensedScalarRing Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k))))
    [J.Additive] [PreservesFiniteColimits J] (adj : J ⊣ heartFiber Λ k)
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    IsConstantModelConstructible Λ (Spec (.of k)) M ↔
      ∃ N : ModuleCat.{u + 1} (condensedScalarRing Λ),
        Module.Finite (condensedScalarRing Λ) N ∧ Nonempty (J.obj N ≅ M) := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let L := J ⋙ e.inverse
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u})
  let a : L ⊣ S := (adj.comp e.symm.toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm S ≪≫ Functor.leftUnitor S)
  have : IsIso a.unit := CondensedRing.Evaluation.contractible_realization_ordinary_unit
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
    (singleton_sections_colimits Λ) L a
  let := a.fullyFaithfulLOfIsIsoUnit.full
  let := Functor.additive_of_preserves_binary_products e.inverse
  rw [point_global_model]
  constructor
  · rintro ⟨P, hP, ⟨eP⟩⟩
    obtain ⟨N, hN, ⟨i⟩⟩ :=
      (scalar_models_iff Λ L (condensed_regular_iso Λ L a) P).mp hP
    exact ⟨N, hN, ⟨(e.counitIso.app (J.obj N)).symm ≪≫ e.functor.mapIso i ≪≫ eP⟩⟩
  · rintro ⟨N, hN, ⟨eN⟩⟩
    exact ⟨L.obj N,
      (scalar_models_iff Λ L (condensed_regular_iso Λ L a) _).mpr
        ⟨N, hN, ⟨Iso.refl _⟩⟩,
      ⟨e.counitIso.app (J.obj N) ≪≫ eN⟩⟩

private theorem direct_of_heart
    [PreservesFiniteLimits (heartFiber Λ k)]
    [PreservesFiniteColimits (heartFiber Λ k)]
    (J : ModuleCat.{u + 1} (condensedScalarRing Λ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        ((upperStarFromPoint (Spec (.of k))).obj Λ))
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (adj : J ⊣ heartFiber Λ k) [IsIso adj.unit]
    (eJ : J.mapDerivedCategory ≅ condensedScalarRealization Λ (Spec (.of k)))
    (eH : (heartFiber Λ k).mapDerivedCategory ≅ fiber Λ k)
    (hheart : ∀ M,
      IsConstantModelConstructible Λ (Spec (.of k)) M ↔
      ∃ N : ModuleCat.{u + 1} (condensedScalarRing Λ),
        Module.Finite (condensedScalarRing Λ) N ∧ Nonempty (J.obj N ≅ M)) :
    DirectPointStatement Λ k := by
  let H := heartFiber Λ k
  let P := constantModelBoundedConstructible Λ (Spec (.of k))
  let Q := scalarFiniteCohomology Λ
  have hPiso {M N} (e : M ≅ N)
      (h : IsConstantModelConstructible Λ (Spec (.of k)) M) :
      IsConstantModelConstructible Λ (Spec (.of k)) N := by
    obtain ⟨V, hV, ⟨i⟩⟩ := (hheart M).mp h
    exact (hheart N).mpr ⟨V, hV, ⟨i ≪≫ e⟩⟩
  have hJfinite (N : ModuleCat.{u + 1} (condensedScalarRing Λ))
      (hN : Module.Finite (condensedScalarRing Λ) N) :
      IsConstantModelConstructible Λ (Spec (.of k)) (J.obj N) :=
    (hheart _).mpr ⟨N, hN, ⟨Iso.refl _⟩⟩
  have hHfinite (M) (hM : IsConstantModelConstructible Λ (Spec (.of k)) M) :
      Module.Finite (condensedScalarRing Λ) (H.obj M) := by
    obtain ⟨N, hN, ⟨e⟩⟩ := (hheart M).mp hM
    have := hN
    let e' : N ≅ H.obj M := (asIso (adj.unit.app N)) ≪≫ H.mapIso e
    exact Module.Finite.equiv e'.toLinearEquiv
  have hF (K : P.FullSubcategory) : Q ((fiber Λ k).obj K.obj) := by
    have hb := H.bounded_mapDerivedCategory_obj K.property.1
    have hb' := DerivedCategory.TStructure.t.bounded.prop_of_iso (eH.app K.obj) hb
    refine ⟨(finite_support_iff_bounded _).mpr hb', fun i ↦ ?_⟩
    have := hHfinite _ (K.property.2 i)
    let e : H.obj ((DerivedCategory.homologyFunctor _ i).obj K.obj) ≅
        (DerivedCategory.homologyFunctor _ i).obj ((fiber Λ k).obj K.obj) :=
      ((H.mapDerivedCategoryHomologyFunctorIso i).app K.obj) ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso (eH.app K.obj)
    exact Module.Finite.equiv e.toLinearEquiv
  have hR (N : Q.FullSubcategory) : P
      ((condensedScalarRealization Λ (Spec (.of k))).obj N.obj) := by
    have hb := J.bounded_mapDerivedCategory_obj
      ((finite_support_iff_bounded _).mp N.property.1)
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso (eJ.app N.obj) hb, fun i ↦ ?_⟩
    exact hPiso (((J.mapDerivedCategoryHomologyFunctorIso i).app N.obj) ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (eJ.app N.obj)) (hJfinite _
        (N.property.2 i))
  let d := adj.mapDerivedCategoryAdjunction
  have ff := d.fullyFaithfulLOfIsIsoUnit
  let := ff.full
  let := ff.faithful
  have hEss (K : P.FullSubcategory) : J.mapDerivedCategory.essImage K.obj := by
    refine DerivedCategory.prop_of_bounded J.mapDerivedCategory.essImage J.essImage
      ?_ K.obj K.property.1 (fun i ↦ ?_)
    · rintro M ⟨N, ⟨e⟩⟩
      exact ⟨(DerivedCategory.singleFunctor _ 0).obj N,
        ⟨(J.mapDerivedCategorySingleFunctor 0).app N ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩
    · obtain ⟨N, _, ⟨e⟩⟩ := (hheart _).mp (K.property.2 i)
      exact ⟨N, ⟨e⟩⟩
  let a := (d.ofNatIsoLeft eJ).ofNatIsoRight eH
  have hunit : IsIso a.unit := by
    have : (condensedScalarRealization Λ (Spec (.of k))).Full :=
      Functor.Full.of_iso eJ
    have : (condensedScalarRealization Λ (Spec (.of k))).Faithful :=
      Functor.Faithful.of_iso eJ
    infer_instance
  have := hunit
  have hEss' (K : P.FullSubcategory) :
      (condensedScalarRealization Λ (Spec (.of k))).essImage K.obj := by
    obtain ⟨N, ⟨e⟩⟩ := hEss K
    exact ⟨N, ⟨(eJ.app N).symm ≪≫ e⟩⟩
  obtain ⟨b, hb₁, hb₂⟩ := restrict_adjunction a Q P hR hF hEss'
  exact ⟨inferInstance, inferInstance, J, adj, inferInstance, inferInstance,
    inferInstance, ⟨inferInstance, ⟨eJ⟩⟩, hF, hR, b, hb₁, hb₂⟩

private theorem direct_of_scalar_properties (h : scalar_properties Λ) :
    DirectPointStatement Λ k := by
  let := h.1
  obtain ⟨ha, hl, hc, ⟨e⟩⟩ := CondensedRing.flat_ordinaryScalarRealization
    (Mon.mk Λ) h.2 (Spec (.of k))
  let := ha
  let := hl
  let := hc
  let a := ordinary_adjunction Λ k
  have := heart_adjunction_unit Λ k _ a
  exact direct_of_heart Λ k _ a e (heartFiberDerivedIso Λ k) (heart_classification Λ k _ a)

end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
