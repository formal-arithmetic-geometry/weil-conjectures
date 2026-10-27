/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Scalar realization data for integral constructible local models

Source: blueprint main-20261015, integral-heart-local-model, clauses (1)--(3);
Stacks Project, Tags 099I, 09C7, 09C4, 0990, 099Q and 099Y
(blueprint: def-sfb-integral-heart-local-model-data).

The coefficient ring is exactly the sibling integral-heart theorem's ring. Scalar
modules are lifted copies of the integers in the canonical small presentation of E.
Their realization is sheafified extension of scalars along constant functions,
followed by the existing equivalence with internal module objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The coefficient DVR, lifted only to the sheaf-value universe.
Source: integral-heart coefficient setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartScalars (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :=
  ULift.{u + 1} (SmallAdicCompletion.Coefficients.integers ℓ E)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- The actual section ring sheaf of the condensed integral ring.
Source: pulled-back coefficient setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartPointRing :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E))

/-- A scalar as its constant continuous function, in the reconstructed section ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartScalarSection (S : Profinite.{u}ᵒᵖ)
    (a : integralHeartScalars.{u} ℓ E) :
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj.obj S :=
  ULift.up (ContinuousMap.const S.unop a.down)

/-- The constant scalar one is the unit of the reconstructed section ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model).
Proof: the internal unit of continuous functions is the constant function one.
Evaluating its section-ring reconstruction gives the same constant function. -/
theorem integralHeartScalarSection_one (S : Profinite.{u}ᵒᵖ) :
    integralHeartScalarSection.{u} ℓ E S 1 = 1 := by
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let F := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : MonObj R.obj :=
    (Profinite.continuousMapRingSheaf.{u}
      (SmallAdicCompletion.Coefficients.integers ℓ E)).obj.monObjCompForget₂
  change _ = ((Functor.LaxMonoidal.ε F ≫ F.map η[R]).app S).hom (ULift.up 1)
  rw [Sheaf.ε_comp_map_one]
  change ULift.up (ContinuousMap.const S.unop
    (1 : SmallAdicCompletion.Coefficients.integers ℓ E)) =
      ((1 : ℤ) : ULift.{u + 1} C(S.unop, SmallAdicCompletion.Coefficients.integers ℓ E))
  simp only [Int.cast_one]
  rfl

/-- Constant continuous functions preserve multiplication in the reconstructed ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model).
Proof: the reconstructed internal multiplication evaluated on a pure tensor is the
original pointwise multiplication of continuous functions. The two constant functions
multiply to the constant function on the scalar product. -/
theorem integralHeartScalarSection_mul (S : Profinite.{u}ᵒᵖ)
    (a b : integralHeartScalars.{u} ℓ E) :
    integralHeartScalarSection.{u} ℓ E S (a * b) =
      integralHeartScalarSection.{u} ℓ E S a * integralHeartScalarSection.{u} ℓ E S b := by
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let F := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let : MonObj R.obj :=
    (Profinite.continuousMapRingSheaf.{u}
      (SmallAdicCompletion.Coefficients.integers ℓ E)).obj.monObjCompForget₂
  change _ = ((Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]).app S).hom
    (integralHeartScalarSection.{u} ℓ E S a ⊗ₜ[ℤ]
      integralHeartScalarSection.{u} ℓ E S b)
  rw [Sheaf.μ_comp_map_mul]
  rfl

/-- Constant scalar functions in every profinite section ring.
Source: the scalar-extension model in clause (1)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantMap :
    (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)) ⟶
      (sectionRingSheaf (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj where
  app S := @CommRingCat.ofHom
    (integralHeartScalars.{u} ℓ E)
    ((sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).obj.obj S) inferInstance
    (CommRingCat.commRing _)
    { toFun := integralHeartScalarSection.{u} ℓ E S
      map_one' := integralHeartScalarSection_one.{u} ℓ E S
      map_mul' := integralHeartScalarSection_mul.{u} ℓ E S
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- Constant scalar module presheaves on the point, with identity restrictions.
Source: the scalar-extension model in clause (1)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantPresheaf : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    PresheafOfModules.{u + 1}
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (integralHeartScalars.{u} ℓ E))) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- Additivity of constant module presheaves.
Source: clause (1), constant realization (blueprint: det-lem-int-integral-heart-local-model).
Proof: evaluate a sum of morphisms at each profinite object; its value is the original
sum of linear maps, so additivity is pointwise. -/
theorem integralHeartConstantPresheaf_additive :
    (integralHeartConstantPresheaf.{u} ℓ E).Additive := by
  constructor
  intro X Y f g
  ext S x
  rfl

attribute [instance] integralHeartConstantPresheaf_additive

/-- The constant scalar ring sheaf.
Source: the scalar model in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartConstantRing :=
  (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
    (CommRingCat.of (integralHeartScalars.{u} ℓ E))

/-- The sheafification unit for the constant scalar ring, forgetting commutativity.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantUnit :=
  Functor.whiskerRight
    (toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (integralHeartScalars.{u} ℓ E))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The constant ring sheafification unit is locally injective after forgetting
commutativity. Source: constant sheafification, Stacks 03DA
(blueprint: det-lem-int-integral-heart-local-model).
Proof: the underlying functions and equalizer sieves are unchanged by forgetting
commutativity, and the original sheafification unit is locally injective. -/
theorem integralHeartConstantUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (integralHeartConstantUnit.{u} ℓ E) := by
  let τ := toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
  constructor
  intro S x y h
  exact Presheaf.equalizerSieve_mem (coherentTopology Profinite.{u}) τ x y h

/-- The constant ring sheafification unit is locally surjective after forgetting
commutativity. Source: constant sheafification, Stacks 03DA
(blueprint: det-lem-int-integral-heart-local-model).
Proof: the underlying functions and image sieves are unchanged by forgetting
commutativity, and the original sheafification unit is locally surjective. -/
theorem integralHeartConstantUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (integralHeartConstantUnit.{u} ℓ E) := by
  let τ := toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
  constructor
  intro U x
  exact Presheaf.imageSieve_mem (coherentTopology Profinite.{u}) τ x

attribute [instance] integralHeartConstantUnit_isLocallyInjective
  integralHeartConstantUnit_isLocallySurjective

/-- The canonical ring map from constant scalars to continuous coefficients.
Source: scalar realization in clauses (1)--(2)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartScalarMap : integralHeartConstantRing.{u} ℓ E ⟶
    sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).homEquiv
    _ _).symm (integralHeartConstantMap.{u} ℓ E)

/-- Modules over the constant scalar ring on the point.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartConstantModules :=
  SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))

/-- The map laws of the existing canonical sectionwise scalar-extension construction.
Source: sheaf tensor, Stacks 03EK (blueprint: det-lem-int-integral-heart-local-model).
Proof: before sheafification all maps are id tensor f. Tensor functoriality gives
identity and composition on pure tensors. Sheafification preserves both equations. -/
theorem integralHeartExtension_laws :
    (∀ M : integralHeartConstantModules.{u} ℓ E,
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M (𝟙 M) = 𝟙 _) ∧
    (∀ (M N P : integralHeartConstantModules.{u} ℓ E) (f : M ⟶ N) (g : N ⟶ P),
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M (f ≫ g) =
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M f ≫
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) N g) := by
  let α := integralHeartScalarMap.{u} ℓ E
  let L := PresheafOfModules.sheafification.{u + 1}
    (𝟙 (integralHeartPointRing.{u} ℓ E).obj)
  constructor
  · intro M
    let t : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
        SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M :=
      { app U := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (α.hom.app U).hom).map (𝟙 (M.val.obj U))
        naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
          α M (𝟙 M) }
    have ht : t = 𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map_id _
    change L.map t = 𝟙 _
    rw [ht, L.map_id]
  · intro M N P f g
    let t {A B : integralHeartConstantModules.{u} ℓ E} (h : A ⟶ B) :
        SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α A ⟶
          SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α B :=
      { app U := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map (h.val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
          α A h }
    have ht : t (f ≫ g) = t f ≫ t g := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map_comp _ _
    change L.map (t (f ≫ g)) = L.map (t f) ≫ L.map (t g)
    rw [ht, L.map_comp]

/-- Actual completed scalar extension, sheafifying the sectionwise tensor product.
Source: scalar realization in clauses (1)--(2)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartExtension :
    SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E)) ⥤
    SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E) where
  obj M := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap.{u} ℓ E) M
  map {M _N} f := SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap.{u} ℓ E) M f
  map_id M := (integralHeartExtension_laws.{u} ℓ E).1 M
  map_comp f g := (integralHeartExtension_laws.{u} ℓ E).2 _ _ _ f g

private theorem integralHeartExtension_additive :
    (integralHeartExtension.{u} ℓ E).Additive where
  map_add {M N} f g := by
    let α := integralHeartScalarMap.{u} ℓ E
    let L := PresheafOfModules.sheafification.{u + 1}
      (𝟙 (integralHeartPointRing.{u} ℓ E).obj)
    let t (h : M ⟶ N) :
        SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
          SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α N :=
      { app U := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map (h.val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
          α M h }
    have ht : t (f + g) = t f + t g := by
      apply PresheafOfModules.hom_ext
      intro U
      have : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).Additive :=
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          (α.hom.app U).hom).left_adjoint_additive
      exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (α.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)
    have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    change L.map (t (f + g)) = L.map (t f) + L.map (t g)
    rw [ht, L.map_add]

/-- The canonical completed scalar-module realization on the point. It first forms
constant module sheaves, then extends scalars along constant functions, and finally
uses the existing internal-module equivalence. No realization functor is an input.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartPointRealization : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    CategoryTheory.Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  integralHeartConstantPresheaf.{u} ℓ E ⋙
    PresheafOfModules.sheafification
      (R := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))
      (integralHeartConstantUnit.{u} ℓ E) ⋙
    integralHeartExtension.{u} ℓ E ⋙
    (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).inverse

/-- Additivity of completed scalar realization.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model).
Proof: constant presheaves preserve addition pointwise. Scalar extension and
sheafification are additive; the inverse of an additive equivalence is additive. -/
theorem integralHeartPointRealization_additive :
    (integralHeartPointRealization.{u} ℓ E).Additive := by
  have := integralHeartExtension_additive.{u} ℓ E
  let L := PresheafOfModules.sheafification.{u + 1}
    (R := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))
    (integralHeartConstantUnit.{u} ℓ E)
  have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  change (integralHeartConstantPresheaf.{u} ℓ E ⋙ L ⋙
    integralHeartExtension.{u} ℓ E ⋙ _).Additive
  infer_instance

attribute [instance] integralHeartPointRealization_additive

/-- Scalar-module realization on a scheme by the published inverse image from the point.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartRealization (X : Scheme.{u}) :=
  integralHeartPointRealization.{u} ℓ E ⋙
    (upperStarFromPoint X).mapMod (SmallAdicCompletion.Coefficients.integerRing ℓ E)

/-- Additivity of realization on the scheme.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model).
Proof: point realization is additive and inverse image is additive; compose these
properties. This is only the structure needed to map cochain complexes. -/
theorem integralHeartRealization_additive (X : Scheme.{u}) :
    (integralHeartRealization.{u} ℓ E X).Additive := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold integralHeartRealization
  infer_instance

attribute [instance] integralHeartRealization_additive

/-- The ordinary unbounded category with exactly the integral-heart coefficient ring.
Source: the standing setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) X))

/-- The q-th cohomology sheaf in degree zero.
Source: clause (2) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartCohomology (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X) (q : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj K)

/-- Finite free models and all their cohomology models on the same strata and charts.
The differential matrices are over the scalar DVR since P is a scalar cochain complex.
Source: clauses (1) and (2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartFiniteFreeLocalModel (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X) : Prop :=
  ∃ s : Scheme.FiniteLocallyClosedStratification X,
    (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
    ∀ a : Fin s.n, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
      ∀ i : 𝒰.I₀,
        ∃ (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
          (b c : ℤ),
          P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
          (∀ q : ℤ, Module.Free (integralHeartScalars.{u} ℓ E) (P.X q) ∧
            Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
          Nonempty (((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
              (𝒰.f i ≫ s.immersion a)).mapDerivedCategory).obj K ≅
            DerivedCategory.Q.obj
              (((integralHeartRealization.{u} ℓ E (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj P)) ∧
          (∀ q : ℤ,
            Module.Finite (integralHeartScalars.{u} ℓ E) (P.homology q) ∧
            Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj K) ≅
              (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj (P.homology q)))

end AlgebraicGeometry.ProEtale
