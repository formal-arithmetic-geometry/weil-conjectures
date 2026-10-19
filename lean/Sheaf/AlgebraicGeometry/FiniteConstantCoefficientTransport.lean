/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Sheaf.Paper.CompactSupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Sheaf.Paper.EtaleOriginWitness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Normalized finite coefficient and etale-origin transport

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-finite-constant-coefficient-transport).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- Forgetting commutativity commutes with sheafification at the original site universes.
Source: Stacks, Tags 00W1 and 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: the plus construction uses limits of matching families and filtered colimits
of coverings. Forgetting commutativity creates these limits and preserves these
filtered colimits. Apply the construction twice and its universal property to
identify ring sheafification with forgotten commutative-ring sheafification.
The resulting comparison preserves the sheafification unit. -/
@[instance]
theorem constantRingForget_preservesSheafification (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  exact GrothendieckTopology.instPreservesSheafification _ _

/-- The canonical coefficient map sends a scalar to its constant function after φ.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def finiteScalarMap (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X) ⟶
        finiteCoefficientRingSheaf X Λ :=
  (constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of B) ≫
  (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map (RingCat.ofHom φ) ≫
  ((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv
    _ _).symm (finiteCoefficientScalarMap X Λ)

/-- Actual restriction of module scalars along the specified constant-section map.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def finiteRestriction (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    FiniteCoefficientModules X Λ ⥤ Modules B X :=
  SheafOfModules.restrictScalars (finiteScalarMap B X Λ φ)

/-- Restriction of scalars is exact; no flatness of φ is required.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: restriction leaves the underlying additive sheaf, restrictions and maps
unchanged. Kernels and sheafified cokernels have the same restricted scalar action,
so both finite-limit and finite-colimit comparisons are isomorphisms. -/
theorem finiteRestriction_exact (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (finiteRestriction B X Λ φ).Additive ∧
      PreservesFiniteLimits (finiteRestriction B X Λ φ) ∧
        PreservesFiniteColimits (finiteRestriction B X Λ φ) := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
  let S := finiteCoefficientRingSheaf X Λ
  let F := finiteRestriction B X Λ φ
  have he : F ⋙ SheafOfModules.toSheaf.{u + 1} R ≅ SheafOfModules.toSheaf.{u + 1} S := Iso.refl _
  have : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
      preservesFiniteLimits_of_natIso he.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R) :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteColimits F := by
    have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
      preservesFiniteColimits_of_natIso he.symm
    exact preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)
  exact ⟨inferInstanceAs (SheafOfModules.restrictScalars (finiteScalarMap B X Λ φ)).Additive,
    inferInstance, inferInstance⟩

/-- Additivity of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_additive (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (finiteRestriction B X Λ φ).Additive := (finiteRestriction_exact B X Λ φ).1

/-- Left exactness of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteLimits (finiteRestriction B X Λ φ) := (finiteRestriction_exact B X Λ φ).2.1

/-- Right exactness of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteColimits (finiteRestriction B X Λ φ) := (finiteRestriction_exact B X Λ φ).2.2

/-- A level may have its own finite coefficient ring and its own lower bound. The
etale witness is exactly the recorded dependency's witness, followed by actual
restriction of scalars. Source: blueprint finite-origin hypothesis
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
structure ScalarEtaleOrigin (X : Scheme.{u}) (K : DerivedCategory (Modules B X)) where
  Λ : Type (u + 1)
  [ring : CommRing Λ]
  [finite : Finite Λ]
  [topology : TopologicalSpace Λ]
  [discrete : DiscreteTopology Λ]
  φ : B →+* Λ
  F : FiniteCoefficientDerivedCategoryPlus X Λ
  origin : EtaleOriginWitness X Λ F
  iso : (finiteRestriction B X Λ φ).mapDerivedCategory.obj F.obj ≅ K

attribute [instance] ScalarEtaleOrigin.ring ScalarEtaleOrigin.finite
  ScalarEtaleOrigin.topology ScalarEtaleOrigin.discrete


/-- Realize finite fixed-ring sheaves, then restrict the specified scalar action.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def C (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤ Modules B X :=
  finiteCoefficientRealization X Λ ⋙ finiteRestriction B X Λ φ

/-- The realization comparison is uniquely normalized on the sheafification unit.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: module sheafification has the sheafification of the underlying additive
presheaf as its underlying sheaf. The counit to the original additive sheaf is
an isomorphism and sends each unit section to itself. Local surjectivity of the
unit gives uniqueness. Scalar restriction leaves all these sections unchanged. -/
theorem cUnderlying_existsUnique (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ∃! e : C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅
        sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat),
      ∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
        (U : X.ProEtᵒᵖ) (m : F.obj.obj U),
        (e.hom.app F).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj).presheaf).app U m) = m := by
  let J := Scheme.ProEt.topology X
  let D := sheafCompose J (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)
  let adj := sheafificationAdjunction J AddCommGrpCat.{u + 1}
  let e : C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅ D :=
    NatIso.ofComponents (fun F ↦ asIso (adj.counit.app (D.obj F)))
      (fun f ↦ adj.counit.naturality (D.map f))
  have he (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      toSheafify J (D.obj F).obj ≫ (e.hom.app F).hom = 𝟙 _ :=
    adj.right_triangle_components (D.obj F)
  refine ⟨e, ?_, ?_⟩
  · intro F U m
    exact ConcreteCategory.congr_hom (congr_app (he F) U) m
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (D.obj F).property
    ext U m
    exact (he' F U m).trans (ConcreteCategory.congr_hom (congr_app (he F) U) m).symm

/-- The specified underlying-sheaf identification, fixed on all unit sections.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def cUnderlying (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅
      sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat) :=
  Classical.choose (cUnderlying_existsUnique B X Λ φ)

private theorem finiteScalarMap_unit (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Functor.whiskerRight
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
      (finiteScalarMap B X Λ φ).hom =
    (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫ finiteCoefficientScalarMap X Λ := by
  change _ ≫ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of B)).hom ≫
    sheafifyMap (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ)) ≫
    (((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv
      _ _).symm (finiteCoefficientScalarMap X Λ)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  simp only [← Category.assoc, sheafComposeIso_inv_fac]
  have hc : (constComp X.ProEtᵒᵖ (CommRingCat.of B)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom = 𝟙 _ := rfl
  rw [hc, sheafifyMap_id, Category.comp_id, ← toSheafify_naturality, Category.assoc]
  congr 1
  exact Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv _ _)
    (finiteCoefficientScalarMap X Λ)

private noncomputable abbrev scalarUnit (X : Scheme.{u}) :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private theorem scalarUnit_surjective (X : Scheme.{u}) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (scalarUnit B X) := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  change Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
  infer_instance

private theorem cUnderlying_inv_unit (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    ((cUnderlying B X Λ φ).inv.app F).hom =
      toSheafify (Scheme.ProEt.topology X)
        ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj).presheaf := by
  apply (cancel_mono ((cUnderlying B X Λ φ).hom.app F).hom).mp
  ext U m
  exact (ConcreteCategory.congr_hom
    (congr_app (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        ((cUnderlying B X Λ φ).inv_hom_id_app F)) U) m).trans
      ((Classical.choose_spec (cUnderlying_existsUnique B X Λ φ)).1 F U m).symm

private theorem cUnderlying_unit_smul (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (U : X.ProEtᵒᵖ)
    (b : B) (m : F.obj.obj U) :
    ((cUnderlying B X Λ φ).inv.app F).hom.app U (φ b • m) =
      HSMul.hSMul (β := ((C B X Λ φ).obj F).val.obj U)
        ((scalarUnit B X).app U b) (((cUnderlying B X Λ φ).inv.app F).hom.app U m) := by
  rw [cUnderlying_inv_unit]
  have h := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (finiteCoefficientScalarMap X Λ)).unit.app
      ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj)).app U).hom.map_smul (φ b) m
  have hs := ConcreteCategory.congr_hom (congr_app (finiteScalarMap_unit B X Λ φ) U) b
  change (finiteScalarMap B X Λ φ).hom.app U ((scalarUnit B X).app U b) =
    (finiteCoefficientScalarMap X Λ).app U (φ b) at hs
  change _ = HSMul.hSMul (β := ((finiteCoefficientRealization X Λ).obj F).val.obj U)
    ((finiteScalarMap B X Λ φ).hom.app U ((scalarUnit B X).app U b)) _
  rw [hs]
  exact h

private theorem cUnderlying_hom_smul (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (U : X.ProEtᵒᵖ)
    (b : B) (m : ((C B X Λ φ).obj F).val.obj U) :
    ((cUnderlying B X Λ φ).hom.app F).hom.app U ((scalarUnit B X).app U b • m) =
      HSMul.hSMul (β := F.obj.obj U) (φ b)
        (((cUnderlying B X Λ φ).hom.app F).hom.app U m) := by
  apply (ConcreteCategory.bijective_of_isIso
    (((cUnderlying B X Λ φ).inv.app F).hom.app U)).1
  have hi (n : ((C B X Λ φ).obj F).val.obj U) :
      ((cUnderlying B X Λ φ).inv.app F).hom.app U
        (((cUnderlying B X Λ φ).hom.app F).hom.app U n) = n :=
    ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        ((cUnderlying B X Λ φ).hom_inv_id_app F)) U) n
  rw [cUnderlying_unit_smul, hi, hi]

private theorem moduleDirectImage_scalarUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules B X) (U : Y.ProEtᵒᵖ) (b : B)
    (m : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
    HSMul.hSMul (β := ((moduleDirectImage B f).obj M).val.obj U)
      ((scalarUnit B Y).app U b) m =
    (scalarUnit B X).app ((Scheme.proEtaleBaseChange f).op.obj U) b • m := by
  have hρ : Scheme.proEtaleRingDirectImageMap f (coefficients B Y)
      (coefficients B X) (constantRingIso B f) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B) := by
    exact ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hn := Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (coefficients B X)))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))))
  change _ ≫ (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
    (CommRingCat.of B)).hom = _ at hn
  have hu := ConcreteCategory.congr_hom (congr_app hn U) b
  change HSMul.hSMul (β := M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U))
    ((Scheme.proEtaleRingDirectImageMap f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).hom.app U
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))).app U b)) m = _
  rw [hρ]
  exact congrArg (fun r ↦ r • m) hu

/-- Direct image commutes with this scalar realization by identity on sections.
Source: Stacks, Tag 0D6E
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: after the underlying-sheaf identifications both sides have sections of F
on U ×_Y X. Identity on these sections is B-linear because both coefficient maps
send b to the constant value φ(b). It is natural and invertible. Faithfulness of
underlying additive sheaves proves uniqueness. -/
theorem cDirect_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ∃! e : ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ ≅
        C B X Λ φ ⋙ moduleDirectImage B f,
      ∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
        (U : Y.ProEtᵒᵖ)
        (m : ((C B Y Λ φ).obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).val.obj U),
        ((cUnderlying B X Λ φ).hom.app F).hom.app
            ((Scheme.proEtaleBaseChange f).op.obj U) ((e.hom.app F).val.app U m) =
          ((cUnderlying B Y Λ φ).hom.app
            ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom.app U m := by
  let L := ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ
  let R := C B X Λ φ ⋙ moduleDirectImage B f
  let T := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B Y))
  let a : L ⋙ T ≅ R ⋙ T :=
    isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f) (cUnderlying B Y Λ φ) ≪≫
      isoWhiskerRight (cUnderlying B X Λ φ).symm (ProEtale.lowerStar AddCommGrpCat.{u + 1} f)
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology Y) (scalarUnit B Y) :=
    scalarUnit_surjective B Y
  let g (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      L.obj F ⟶ R.obj F :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (scalarUnit B Y) (R.obj F).isSheaf).symm
      (PresheafOfModules.homMk (a.hom.app F).hom (fun U b m ↦ by
        change ((cUnderlying B X Λ φ).inv.app F).hom.app
            ((Scheme.proEtaleBaseChange f).op.obj U)
            (((cUnderlying B Y Λ φ).hom.app
              ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom.app U
                ((scalarUnit B Y).app U b • (show (L.obj F).val.obj U from m))) = _
        rw [cUnderlying_hom_smul, cUnderlying_unit_smul]
        exact (moduleDirectImage_scalarUnit B f ((C B X Λ φ).obj F) U b _).symm))⟩
  have hg (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      T.map (g F) = a.hom.app F := rfl
  let t : L ⟶ R :=
    { app := g
      naturality := fun {F G} h ↦ by
        apply T.map_injective
        simp only [Functor.map_comp, hg]
        exact a.hom.naturality h }
  have ht (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      IsIso (t.app F) := by
    have : IsIso (T.map (t.app F)) := by
      change IsIso (T.map (g F))
      rw [hg]
      infer_instance
    exact isIso_of_reflects_iso _ T
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, ?_, ?_⟩
  · intro F U m
    change ((cUnderlying B X Λ φ).hom.app F).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U) ((t.app F).val.app U m) = _
    have he := ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        ((cUnderlying B X Λ φ).inv_hom_id_app F))
          ((Scheme.proEtaleBaseChange f).op.obj U))
    exact he _
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply T.map_injective
    apply Sheaf.hom_ext
    ext U m
    apply (ConcreteCategory.bijective_of_isIso
      (((cUnderlying B X Λ φ).hom.app F).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U))).1
    exact (he F U m).trans (by
      have h := ConcreteCategory.congr_hom (congr_app
        (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
          ((cUnderlying B X Λ φ).inv_hom_id_app F))
            ((Scheme.proEtaleBaseChange f).op.obj U))
      exact (h _).symm)

/-- The canonical sectionwise scalar/direct-image comparison.
Source: Stacks, Tag 0D6E
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def cDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ ≅
      C B X Λ φ ⋙ moduleDirectImage B f :=
  Classical.choose (cDirect_existsUnique B f Λ φ)

/-- The actual etale-to-pro-etale comparison followed by scalar realization.
Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def H (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ Modules B X :=
  comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙ C B X Λ φ

/-- The canonical inverse-image-square mate, followed by identity on scalar sections.
Source: Stacks, Tags 099R, 0D6E and 07A7
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ H B Y Λ φ ⟶
      H B X Λ φ ⋙ moduleDirectImage B f :=
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv) (C B Y Λ φ) ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    (cDirect B f Λ φ).hom ≫ (Functor.associator _ _ _).inv

/-- The inverse-image comparison is precisely the inverse mate of hDirect.
Source: Stacks, Tags 03EK and 07A7
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hPullbackInv {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    H B Y Λ φ ⋙ modulePullback B f ⟶
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ H B X Λ φ :=
  (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))).symm (hDirect B f Λ φ)

/-- The specified coefficient/site pullback comparison is invertible.
Source: Stacks, Tags 03EK and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: separate site inverse image from scalar restriction. The former has the
canonical inverse-image comparison; the latter keeps the inverse-image additive
sheaf and restricts its action. On constant scalars the two actions coincide.
The unit-section normalization identifies their composite with this inverse mate.
No flatness and no preservation of injectives by scalar restriction is used. -/
theorem hPullbackInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hPullbackInv B f Λ φ) := by
  sorry

/-- The inverse open comparison is the open-adjunction inverse mate of pullback.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hOpenInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    H B U Λ φ ⋙ moduleJ B j ⟶
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ H B X Λ φ :=
  ((mateEquiv (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) j) (moduleJAdj B j)).symm
    (@inv _ _ _ _ (hPullbackInv B j Λ φ) (hPullbackInv_isIso B j Λ φ))).natTrans

/-- The specified inverse open comparison is invertible.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: extension by zero has the original module on the open and zero off it.
Site comparison and scalar restriction retain these sections. The open-unit
transpose of their sectionwise identification is the displayed mate. The inverse
sectionwise identification has the inverse transpose, proving invertibility. -/
theorem hOpenInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hOpenInv B j Λ φ) := by
  sorry

/-- The forward open comparison is the inverse of the specified open-adjunction mate.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ H B X Λ φ ⟶
      H B U Λ φ ⋙ moduleJ B j :=
  (@asIso _ _ _ _ (hOpenInv B j Λ φ) (hOpenInv_isIso B j Λ φ)).inv

/-- The normalized forward open comparison is invertible.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: this is the inverse of the invertible unit-normalized inverse comparison,
so the two inverse identities give invertibility of the forward arrow. -/
theorem hOpen_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hOpen B j Λ φ) := by
  dsimp only [hOpen]
  infer_instance

/-- The comparison functor is additive and exact.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: comparison inverse image, finite realization and scalar restriction are
additive and exact. Their composite therefore preserves finite limits and colimits. -/
theorem h_exact (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (H B X Λ φ).Additive ∧ PreservesFiniteLimits (H B X Λ φ) ∧
      PreservesFiniteColimits (H B X Λ φ) := by
  dsimp only [H, C]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_additive (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (H B X Λ φ).Additive := (h_exact B X Λ φ).1

/-- Left exactness of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteLimits (H B X Λ φ) := (h_exact B X Λ φ).2.1

/-- Right exactness of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteColimits (H B X Λ φ) := (h_exact B X Λ φ).2.2

/-- The bounded-below comparison included into the unbounded target.
Source: Stacks, Tags 099R and 05RU
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def HD (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Modules B X) :=
  (H B X Λ φ).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι

/-- Canonical derived direct-image comparison; its unit normalization is built into
rightDerivedFunctorPlusBaseChange. Source: Stacks, Tags 099R and 0B65
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hR {U X : Scheme.{u}} (f : U ⟶ X) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙ HD B X Λ φ ⟶
      HD B U Λ φ ⋙ (moduleDirectImage B f).rightDerivedFunctor :=
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusBaseChange (hDirect B f Λ φ))
    DerivedCategory.Plus.ι ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (H B U Λ φ).mapDerivedCategoryPlus
    (moduleDirectImage B f).rightDerivedFunctorPlusCompatibility.hom ≫
  (Functor.associator _ _ _).inv

/-- This particular direct-image comparison is an isomorphism for qcqs maps.
Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: factor hDirect into the canonical etale/pro-etale mate and the sectionwise
scalar comparison. On bounded-below etale origins the former is invertible by
the cohomology-continuity comparison. The scalar-change derived-adjunction theorem
identifies the latter with restriction of the original derived direct image.
The unit factorizations show this is the specified hR. Both factors are invertible;
no flatness assumption or preservation of K-injectives by restriction is required. -/
theorem hR_isIso {U X : Scheme.{u}} (f : U ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hR B f Λ φ) := by
  sorry

/-- Derived open comparison with the same open-unit normalization.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        HD B X Λ φ ≅ HD B U Λ φ ⋙ (moduleJ B j).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
  isoWhiskerRight
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (@asIso _ _ _ _ (hOpen B j Λ φ) (hOpen_isIso B j Λ φ)) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _) DerivedCategory.Plus.ι ≪≫
  Functor.associator _ _ _ ≪≫
  isoWhiskerLeft (H B U Λ φ).mapDerivedCategoryPlus
    (moduleJ B j).mapDerivedCategoryPlusCompatibility ≪≫
  (Functor.associator _ _ _).symm

/-- The canonical comparison from H of the etale origin to its scalar-restricted
finite-coefficient realization. Source: blueprint finite-origin hypothesis
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def originIso {X : Scheme.{u}} {K : DerivedCategory (Modules B X)}
    (w : ScalarEtaleOrigin B X K) : (HD B X w.Λ w.φ).obj w.origin.L ≅ K :=
  (isoWhiskerRight
    (Functor.mapDerivedCategoryPlusCompIso
      (finiteCoefficientComparison X w.Λ) (finiteRestriction B X w.Λ w.φ))
    DerivedCategory.Plus.ι ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (finiteCoefficientComparison X w.Λ).mapDerivedCategoryPlus
      (finiteRestriction B X w.Λ w.φ).mapDerivedCategoryPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm).app w.origin.L ≪≫
  (finiteRestriction B X w.Λ w.φ).mapDerivedCategory.mapIso
    (DerivedCategory.Plus.ι.mapIso w.origin.alpha) ≪≫ w.iso

end AlgebraicGeometry.ProEtale.StrictTower
