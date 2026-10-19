/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-!
# Adic coefficient datum and reduction tower

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-complete-coefficient-datum.md, order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum).

The construction uses one K-flat model with flat terms. Quotient reductions are actual
changed complexes. The ordinary balancing and transition maps are specified uniquely on
local tensor generators; their images under localization are the canonical derived maps.

## Main definitions

- `CompleteCoefficientDatum`: the ring, ideal, torsion, and perfectness conditions.
- `AdicKFlatModel`: one flat-term K-flat representative of an arbitrary derived object.
- `adicReduction`, `adicReductionUnderlying`: the quotient reduction and its scalar restriction.
- `adicTransition`: the localized map induced by the quotient homomorphism.
- `adicNormalization`: the localized scalar-extension balancing isomorphism.

## Main statements

- `adicKFlatModel_exists`: availability of models for every unbounded derived object.
- `adicTransition_id`, `adicTransition_comp`: the transition identities.
- `adicNormalization_cocycle`, `adicNormalization_unit`: normalization coherence.
- `adicReductionUnderlying_tensor`: comparison with the recorded derived tensor product.
-/

@[expose] public section

universe t

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings


namespace AlgebraicGeometry.Scheme

/-- The constant commutative ring sheaf, before forgetting commutativity.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicConstantRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))

/-- The underlying constant ring sheaf used by the recorded pro-etale derived category.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicModuleRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (adicConstantRing X A)

/-- The functorial constant sheaf map associated to a coefficient homomorphism.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicConstantMap (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    adicConstantRing X A ⟶ adicConstantRing X B :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
    (CommRingCat.ofHom (RingHom.ulift φ))

private theorem adicConstantMap_id (X : Scheme.{t}) (A : Type t) [CommRing A] :
    adicConstantMap X (RingHom.id A) = 𝟙 (adicConstantRing X A) := by
  unfold adicConstantMap
  change (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map (𝟙 _) = _
  exact CategoryTheory.Functor.map_id _ _

private theorem adicConstantMap_comp (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    adicConstantMap X φ ≫ adicConstantMap X ψ = adicConstantMap X (ψ.comp φ) := by
  unfold adicConstantMap
  rw [← Functor.map_comp]
  rfl

/-- The same coefficient map, regarded as a map of ring sheaves.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicModuleMap (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    adicModuleRing X A ⟶ adicModuleRing X B :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (adicConstantMap X φ)

/-- Localization into the exact derived category recorded for the small pro-etale site.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicLocalization (X : Scheme.{t}) (A : Type t) [CommRing A] :
    CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ ⥤
      proEtaleDerivedCategory X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Perfectness of the actual quotient module over the original coefficient ring,
placed in degree zero. Source: blueprint order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicQuotientPerfect (Λ : Type t) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{t} Λ)
  DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{t} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I ^ n)))

/-- Precisely the coefficient hypotheses, without an assumption of I-adic completeness,
finiteness of the quotient sets, or flatness of any quotient.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
structure CompleteCoefficientDatum (Λ : Type t) [CommRing Λ] where
  ideal : Ideal Λ
  noetherian : IsNoetherianRing Λ
  finitelyGenerated : ideal.FG
  quotientTorsion : ∀ x : Λ ⧸ ideal, ∃ m : ℕ, 0 < m ∧ m • x = 0
  quotientPerfect : ∀ n : ℕ, 1 ≤ n → adicQuotientPerfect Λ ideal n

/-- One K-flat flat-term representative of the arbitrary derived object K. The realization
is part of the choice of model, rather than a restriction on K.
Source: blueprint order 1255, construction step 1; Stacks Tag 06YS
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
structure AdicKFlatModel (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (K : proEtaleDerivedCategory X Λ) where
  complex : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ
  isKFlat : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X Λ) complex
  flatTerms : ∀ p : ℤ, CategoryTheory.exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (adicConstantRing X Λ)) (complex.X p))
  realization :
    (adicLocalization X Λ).obj complex ≅ K

/-- Every derived object has a model of the stipulated kind; no boundedness or flatness
of the quotient coefficients is assumed. Source: blueprint order 1255, construction step 1;
Stacks Tag 06YS.
Proof: represent K by a cochain complex, take its K-flat resolution with flat terms
(lem-pc-kflat-resolution), and compose the localization of the augmentation with the
representative isomorphism. The augmentation is a quasi-isomorphism, so its localization
is invertible. The small-site universe convention does not change this construction.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicKFlatModel_exists (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (K : proEtaleDerivedCategory X Λ) : Nonempty (AdicKFlatModel X Λ K) := by
  classical
  have : (adicLocalization X Λ).EssSurj := by
    dsimp only [adicLocalization]
    infer_instance
  let G := (adicLocalization X Λ).objPreimage K
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionGeneral (R := adicConstantRing X Λ) G
  have := hf
  have : IsIso ((adicLocalization X Λ).map f) := by
    dsimp only [adicLocalization]
    infer_instance
  exact ⟨⟨P, hP, hflat,
    asIso ((adicLocalization X Λ).map f) ≪≫ (adicLocalization X Λ).objObjPreimageIso K⟩⟩

/-- The quotient map for two powers of the ideal, sending the class of x to the class of x.
Source: blueprint order 1255, construction step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicQuotientMap {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (b a : ℕ) (hab : a ≤ b) : Λ ⧸ I ^ b →+* Λ ⧸ I ^ a :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)

/-- Termwise scalar extension, with the target coefficient action retained.
Source: blueprint order 1255, steps 1 and 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicChange (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :=
  SheafOfModules.changeOfRingsComplex.{t + 1, t} (adicConstantMap X φ) P

/-- Termwise restriction of scalars, retaining the same abelian sheaves and differentials.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :=
  ((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- The local pure tensor s tensor m, mapped into the sheafified scalar extension.
Source: blueprint order 1255, steps 2 and 3; Stacks Tag 03EK
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M)).app U
        (s ⊗ₜ[(adicConstantRing X A).obj.obj U,
          ((adicConstantMap X φ).hom.app U).hom] m)

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorSection_smul (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s r : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    adicTensorSection X φ M U (s * r) m = s • adicTensorSection X φ M U r m := by
  unfold adicTensorSection
  rw [← ModuleCat.ExtendScalars.smul_tmul ((adicConstantMap X φ).hom.app U).hom s r m]
  exact (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafChangeHom_comp (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {M N P : SheafOfModules.{t + 1} (adicModuleRing X A)} (f : M ⟶ N) (g : N ⟶ P) :
    SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X φ) M (f ≫ g) =
      SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X φ) M f ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X φ) N g := by
  unfold SheafOfModules.changeOfRingsHom
  rw [← Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  change (ModuleCat.extendScalars ((adicConstantMap X φ).hom.app U).hom).map
    (f.val.app U ≫ g.val.app U) = _
  exact Functor.map_comp _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorHom_ext (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    {N : SheafOfModules.{t + 1} (adicModuleRing X B)}
    (f g : SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U),
      f.val.app U (adicTensorSection X φ M U s m) =
        g.val.app U (adicTensorSection X φ M U s m)) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv.{t + 1} (𝟙 (adicModuleRing X B).obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h U 1 m

set_option backward.isDefEq.respectTransparency false in
private theorem adicChangeHom_tensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {M N : SheafOfModules.{t + 1} (adicModuleRing X A)} (f : M ⟶ N)
    (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (adicConstantMap X φ) M f).val.app U
        (adicTensorSection X φ M U s m) =
      adicTensorSection X φ N U s (f.val.app U m) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) N :=
    { app := fun V ↦ (ModuleCat.extendScalars ((adicConstantMap X φ).hom.app V).hom).map
        (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality _ M f }
  have hn := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.naturality p
  have hv := congrArg (fun q ↦ q.app U) hn
  have hx := ConcreteCategory.congr_hom hv
    (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m)
  change adicTensorSection X φ N U s (f.val.app U m) = _ at hx
  exact hx.symm

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorSection_map (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    {U V : X.ProEtᵒᵖ} (i : U ⟶ V)
    (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1}
      (adicConstantMap X φ) M).val.map i (adicTensorSection X φ M U s m) =
    adicTensorSection X φ M V ((adicConstantRing X B).obj.map i s) (M.val.map i m) := by
  have hn := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{t + 1}
      (𝟙 (adicModuleRing X B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M)) i
    (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m)
  change _ = (SheafOfModules.changeOfRings.{t, t + 1, t + 1}
    (adicConstantMap X φ) M).val.map i (adicTensorSection X φ M U s m) at hn
  have ht := Classical.choose_spec
    (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1} (adicConstantMap X φ) M i) s m
  change SheafOfModules.changeOfRingsMap (adicConstantMap X φ) M i _ = _ at ht
  change ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
        (adicConstantMap X φ) M)).app V
      (SheafOfModules.changeOfRingsMap (adicConstantMap X φ) M i _) = _ at hn
  rw [ht] at hn
  exact hn.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicTranspose (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (f : SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N) :
    M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N where
  val.app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{t + 1, t + 1, t + 1}
    ((adicConstantMap X φ).hom.app U).hom
      ((PresheafOfModules.sheafificationHomEquiv.{t + 1}
        (𝟙 (adicModuleRing X B).obj) f).app U)
  val.naturality {U V} i := by
    ext m
    change f.val.app V (adicTensorSection X φ M V 1 (M.val.map i m)) =
      N.val.map i (f.val.app U (adicTensorSection X φ M U 1 m))
    have hn := PresheafOfModules.naturality_apply f.val i
      (adicTensorSection X φ M U 1 m)
    rw [adicTensorSection_map, map_one] at hn
    exact hn

private theorem adicTranspose_apply (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (f : SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N)
    (U : X.ProEtᵒᵖ) (m : M.val.obj U) :
    (adicTranspose X φ M N f).val.app U m =
      f.val.app U (adicTensorSection X φ M U 1 m) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem adicTranspose_injective (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B)) :
    Function.Injective (adicTranspose X φ M N) := by
  intro f g h
  apply (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have hv := congrArg (fun q ↦ q.val.app U) h
  exact ConcreteCategory.congr_hom hv m

set_option backward.isDefEq.respectTransparency false in
private theorem adicTensorAddHom_ext (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : Sheaf (ProEt.topology X) AddCommGrpCat.{t + 1})
    (f g : (SheafOfModules.toSheaf (adicModuleRing X B)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U),
      f.hom.app U (adicTensorSection X φ M U s m) =
        g.hom.app U (adicTensorSection X φ M U s m)) : f = g := by
  apply ((CategoryTheory.sheafificationAdjunction (ProEt.topology X)
    AddCommGrpCat.{t + 1}).homEquiv
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
        (adicConstantMap X φ) M).presheaf N).injective
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let : Module ((adicConstantRing X A).obj.obj U) ((adicConstantRing X B).obj.obj U) :=
    Module.compHom _ ((adicConstantMap X φ).hom.app U).hom
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul s m => exact h U s m
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem adicModuleLift_tmul (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) (U : X.ProEtᵒᵖ)
    (M : ModuleCat.{t + 1} ((adicConstantRing X A).obj.obj U))
    (N : ModuleCat.{t + 1} ((adicConstantRing X B).obj.obj U))
    (g : M ⟶ (ModuleCat.restrictScalars ((adicConstantMap X φ).hom.app U).hom).obj N)
    (s : (adicConstantRing X B).obj.obj U) (m : M) :
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
      ((adicConstantMap X φ).hom.app U).hom g
        (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m) =
      s • (show N from g m) := by
  let : Module ((adicConstantRing X A).obj.obj U) ((adicConstantRing X B).obj.obj U) :=
    Module.compHom _ ((adicConstantMap X φ).hom.app U).hom
  let : Module ((adicConstantRing X A).obj.obj U) N :=
    Module.compHom N ((adicConstantMap X φ).hom.app U).hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicLiftSeed (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (g : M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N) :
    SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶
      N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
    ((adicConstantMap X φ).hom.app U).hom (g.val.app U)
  naturality {U V} i := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
      ((adicConstantMap X φ).hom.app V).hom (g.val.app V)
        (SheafOfModules.changeOfRingsMap (adicConstantMap X φ) M i _) =
      N.val.map i
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{t + 1, t + 1, t + 1}
          ((adicConstantMap X φ).hom.app U).hom (g.val.app U) _)
    erw [Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1}
        (adicConstantMap X φ) M i) 1 m, map_one]
    rw [adicModuleLift_tmul, adicModuleLift_tmul]
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g.val i m

private noncomputable def adicLift (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (g : M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).symm (adicLiftSeed X φ M N g)

set_option backward.isDefEq.respectTransparency false in
private theorem adicLift_tensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A))
    (N : SheafOfModules.{t + 1} (adicModuleRing X B))
    (g : M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N)
    (U : X.ProEtᵒᵖ) (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (adicLift X φ M N g).val.app U (adicTensorSection X φ M U s m) =
      s • (show N.val.obj U from g.val.app U m) := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).apply_symm_apply (adicLiftSeed X φ M N g)
  have hv := congrArg (fun q ↦ q.app U) h
  have hx := ConcreteCategory.congr_hom hv
    (s ⊗ₜ[(adicConstantRing X A).obj.obj U, ((adicConstantMap X φ).hom.app U).hom] m)
  dsimp [adicLiftSeed] at hx
  exact hx.trans (adicModuleLift_tmul X φ U _ _ (g.val.app U) s m)

private theorem adicConstantMap_comp_app (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (U : X.ProEtᵒᵖ) :
    ((adicConstantMap X χ).hom.app U).hom =
      ((adicConstantMap X ψ).hom.app U).hom.comp
        ((adicConstantMap X φ).hom.app U).hom := by
  have hm := adicConstantMap_comp X φ ψ
  rw [h] at hm
  exact congrArg CommRingCat.Hom.hom (congrArg (fun q ↦ q.hom.app U) hm).symm

private noncomputable def adicRestrictCompIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (N : SheafOfModules.{t + 1} (adicModuleRing X C)) :
    (SheafOfModules.restrictScalars (adicModuleMap X χ)).obj N ≅
      (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj
        ((SheafOfModules.restrictScalars (adicModuleMap X ψ)).obj N) where
  hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _
    (adicConstantMap_comp_app X φ ψ χ h U) (N.val.obj U)).hom
  hom.val.naturality i := by ext m; rfl
  inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _
    (adicConstantMap_comp_app X φ ψ χ h U) (N.val.obj U)).inv
  inv.val.naturality i := by ext m; rfl

private noncomputable def adicSheafExtendUnit (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    M ⟶ (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) :=
  adicTranspose X φ M _ (𝟙 _)

private noncomputable def adicSheafBalance (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X ψ)
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ⟶
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M :=
  adicLift X ψ _ _ (adicLift X φ _ _
    (adicSheafExtendUnit X χ M ≫ (adicRestrictCompIso X φ ψ χ h _).hom))

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafBalance_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X C).obj.obj U) (r : (adicConstantRing X B).obj.obj U)
    (m : M.val.obj U) :
    (adicSheafBalance X φ ψ χ h M).val.app U
      (adicTensorSection X ψ _ U s (adicTensorSection X φ M U r m)) =
    adicTensorSection X χ M U (s * (adicConstantMap X ψ).hom.app U r) m := by
  unfold adicSheafBalance
  rw [adicLift_tensorSection, adicLift_tensorSection]
  change s • ((adicConstantMap X ψ).hom.app U r •
    adicTensorSection X χ M U 1 m) = _
  rw [← mul_smul, ← adicTensorSection_smul, mul_one]

private noncomputable def adicSheafBalanceInv (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M ⟶
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X ψ)
        (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) :=
  adicLift X χ _ _ (adicSheafExtendUnit X φ M ≫
    (SheafOfModules.restrictScalars (adicModuleMap X φ)).map
      (adicSheafExtendUnit X ψ _) ≫ (adicRestrictCompIso X φ ψ χ h _).inv)

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafBalanceInv_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X C).obj.obj U) (m : M.val.obj U) :
    (adicSheafBalanceInv X φ ψ χ h M).val.app U (adicTensorSection X χ M U s m) =
    s • adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U 1 m) := by
  exact adicLift_tensorSection X χ _ _ _ U s m

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicSheafBalanceIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X ψ)
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ≅
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M where
  hom := adicSheafBalance X φ ψ χ h M
  inv := adicSheafBalanceInv X φ ψ χ h M
  hom_inv_id := by
    apply adicTranspose_injective X ψ
    apply adicTranspose_injective X φ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adicSheafBalanceInv X φ ψ χ h M).val.app U
      ((adicSheafBalance X φ ψ χ h M).val.app U
        (adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U 1 m))) =
      adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U 1 m)
    rw [adicSheafBalance_tensorSection, map_one, one_mul,
      adicSheafBalanceInv_tensorSection, one_smul]
  inv_hom_id := by
    apply adicTranspose_injective X χ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adicSheafBalance X φ ψ χ h M).val.app U
      ((adicSheafBalanceInv X φ ψ χ h M).val.app U
        (adicTensorSection X χ M U 1 m)) = adicTensorSection X χ M U 1 m
    rw [adicSheafBalanceInv_tensorSection, one_smul, adicSheafBalance_tensorSection,
      map_one, one_mul]

/-- The ordinary balancing map is uniquely specified on local tensor generators and is
invertible. Source: blueprint order 1255, step 3; Stacks Tags 03EK and 0D6D.
Proof: send s tensor (r tensor m) to (s * ψ(r)) tensor m. The balancing relations
make this well-defined; restriction maps commute with the formula. Sheafification gives
the sheaf morphism. Its inverse sends s tensor m to s tensor (1 tensor m).
The differential acts only on m, so these are chain maps. The two composites are
identities by the balancing relations. Local tensor generators prove uniqueness.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalance_exists (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    ∃! f : adicChange X ψ (adicChange X φ P) ⟶ adicChange X χ P,
      IsIso f ∧ ∀ (p : ℤ) (U : X.ProEtᵒᵖ)
        (s : (adicConstantRing X C).obj.obj U)
        (r : (adicConstantRing X B).obj.obj U) (m : (P.X p).val.obj U),
        (f.f p).val.app U
          (adicTensorSection X ψ _ U s (adicTensorSection X φ _ U r m)) =
          adicTensorSection X χ _ U (s * (adicConstantMap X ψ).hom.app U r) m := by
  let e : adicChange X ψ (adicChange X φ P) ≅ adicChange X χ P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ adicSheafBalanceIso X φ ψ χ h (P.X p)) (by
        intro i j hij
        apply adicTranspose_injective X ψ
        apply adicTensorHom_ext X φ
        intro U r m
        change (SheafOfModules.changeOfRingsHom (adicConstantMap X χ) _ (P.d i j)).val.app U
            ((adicSheafBalance X φ ψ χ h (P.X i)).val.app U
              (adicTensorSection X ψ _ U 1 (adicTensorSection X φ _ U r m))) =
          (adicSheafBalance X φ ψ χ h (P.X j)).val.app U
            ((SheafOfModules.changeOfRingsHom (adicConstantMap X ψ) _
              (SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (P.d i j))).val.app U
                (adicTensorSection X ψ _ U 1 (adicTensorSection X φ _ U r m)))
        rw [adicSheafBalance_tensorSection, adicChangeHom_tensorSection,
          adicChangeHom_tensorSection, adicChangeHom_tensorSection]
        exact (adicSheafBalance_tensorSection X φ ψ χ h (P.X j) U 1 r
          ((P.d i j).val.app U m)).symm)
  refine ⟨e.hom, ⟨inferInstance, ?_⟩, ?_⟩
  · intro p U s r m
    exact adicSheafBalance_tensorSection X φ ψ χ h (P.X p) U s r m
  · intro f hf
    apply HomologicalComplex.hom_ext
    intro p
    apply adicTranspose_injective X ψ
    apply adicTensorHom_ext X φ
    intro U r m
    exact (hf.2 p U 1 r m).trans
      (adicSheafBalance_tensorSection X φ ψ χ h (P.X p) U 1 r m).symm

/-- The uniquely characterized ordinary balancing chain map.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicBalanceHom (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X ψ (adicChange X φ P) ⟶ adicChange X χ P :=
  Classical.choose (adicBalance_exists X φ ψ χ h P)

private theorem adicBalanceHom_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ)
    (p : ℤ) (U : X.ProEtᵒᵖ) (s : (adicConstantRing X C).obj.obj U)
    (r : (adicConstantRing X B).obj.obj U) (m : (P.X p).val.obj U) :
    ((adicBalanceHom X φ ψ χ h P).f p).val.app U
      (adicTensorSection X ψ _ U s (adicTensorSection X φ _ U r m)) =
    adicTensorSection X χ _ U (s * (adicConstantMap X ψ).hom.app U r) m :=
  (Classical.choose_spec (adicBalance_exists X φ ψ χ h P)).1.2 p U s r m

/-- The chosen balancing map is invertible. Source: blueprint order 1255, step 3.
Proof: use the isomorphism clause of adicBalance_exists; its inverse is the formula
s tensor m maps to s tensor (1 tensor m).
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalanceHom_isIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    IsIso (adicBalanceHom X φ ψ χ h P) := by
  exact (Classical.choose_spec (adicBalance_exists X φ ψ χ h P)).1.1

/-- Scalar-extension associativity, on the explicit complexes before localization.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicBalanceIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X ψ (adicChange X φ P) ≅ adicChange X χ P :=
  letI := adicBalanceHom_isIso X φ ψ χ h P
  asIso (adicBalanceHom X φ ψ χ h P)

/-- Compatibility of the quotient maps with the coefficient map from Λ.
Source: blueprint order 1255, step 2.
Proof: both composites send the class of x to its class modulo I^a; quotient induction
reduces the equality to the formula for Ideal.Quotient.factor.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_comp_mk {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (b a : ℕ) (hab : a ≤ b) :
    (adicQuotientMap I b a hab).comp (Ideal.Quotient.mk (I ^ b)) =
      Ideal.Quotient.mk (I ^ a) := by
  exact Ideal.Quotient.factor_comp_mk _

/-- The quotient-coefficient reduction, computed by the fixed K-flat model.
Source: blueprint order 1255, step 1; Stacks Tag 06YY
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReduction (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n : ℕ)) :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (n : ℕ))).obj (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n
    : ℕ))) M.complex)

/-- The same reduction after termwise restriction of scalars to Λ.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReductionUnderlying (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) : proEtaleDerivedCategory X Λ :=
  (adicLocalization X Λ).obj
    (adicRestrict X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex))

/-- Each changed model remains K-flat, with flat terms over its quotient coefficients.
Source: blueprint order 1255, construction step 3; Stacks Tag 0G7E.
Proof: apply lem-pur-kflat-change-of-rings to the constant quotient sheaf homomorphism,
using the K-flat and flat-term fields of the chosen model. Thus a second scalar extension
of this very complex computes the derived scalar extension, by
lem-pur-derived-change-of-rings, without a flatness assumption on the quotient over Λ.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicReductionModel_isKFlat (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X (Λ ⧸ d.ideal ^ (n : ℕ)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex) ∧
      ∀ p : ℤ, CategoryTheory.exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (adicConstantRing X (Λ ⧸ d.ideal ^ (n : ℕ))))
          ((adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex).X p)) := by
  exact SheafOfModules.changeOfRings_isKFlat_of_flat_terms
    (adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ)))) M.complex
    M.isKFlat M.flatTerms

/-- The source of normalization, computed over the intermediate quotient coefficient ring.
Source: blueprint order 1255, step 3; Stacks Tag 0G7E
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReductionTwice (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (b a : ℕ+) (hab : a ≤ b) :
    proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (a : ℕ)) :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).obj
    (adicChange X (adicQuotientMap d.ideal b a hab)
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (b : ℕ))) M.complex))

/-- The normalization is precisely the localization of the ordinary balancing isomorphism.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicNormalization (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (b a : ℕ+) (hab : a ≤ b) :
    adicReductionTwice X d M b a hab ≅ adicReduction X d M a :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).mapIso
    (adicBalanceIso X (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
      (adicQuotientMap d.ideal b a hab) (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
      (adicQuotientMap_comp_mk d.ideal b a hab) M.complex)

private noncomputable def adicSheafTransition (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M) ⟶
    (SheafOfModules.restrictScalars (adicModuleMap X χ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X χ) M) :=
  (SheafOfModules.restrictScalars (adicModuleMap X φ)).map
      (adicSheafExtendUnit X ψ _) ≫ (adicRestrictCompIso X φ ψ χ h _).inv ≫
    (SheafOfModules.restrictScalars (adicModuleMap X χ)).map
      (adicSheafBalance X φ ψ χ h M)

set_option backward.isDefEq.respectTransparency false in
private theorem adicSheafTransition_tensorSection (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (r : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (adicSheafTransition X φ ψ χ h M).val.app U (adicTensorSection X φ M U r m) =
      adicTensorSection X χ M U ((adicConstantMap X ψ).hom.app U r) m := by
  change (adicSheafBalance X φ ψ χ h M).val.app U
    (adicTensorSection X ψ _ U 1 (adicTensorSection X φ M U r m)) = _
  rw [adicSheafBalance_tensorSection, one_mul]

/-- The transition chain map is uniquely specified by applying the quotient homomorphism
on the coefficient tensor factor. Source: blueprint order 1255, step 2; Stacks Tag 03EK.
Proof: the formula is balanced over Λ and commutes with restrictions. Extend it by the
universal property of module sheafification. It is Λ-linear after restriction of scalars
and commutes with the differential, which acts on the model factor. Tensor generators
locally generate the sheafifications in every degree, proving uniqueness.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransitionComplex_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) :
    ∃! f :
      adicRestrict X (Ideal.Quotient.mk (I ^ (b : ℕ)))
        (adicChange X (Ideal.Quotient.mk (I ^ (b : ℕ))) P) ⟶
      adicRestrict X (Ideal.Quotient.mk (I ^ (a : ℕ)))
        (adicChange X (Ideal.Quotient.mk (I ^ (a : ℕ))) P),
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ)
        (r : (adicConstantRing X (Λ ⧸ I ^ (b : ℕ))).obj.obj U)
        (m : (P.X p).val.obj U),
        (f.f p).val.app U (adicTensorSection X (Ideal.Quotient.mk (I ^ (b : ℕ)))
          _ U r m) =
        adicTensorSection X (Ideal.Quotient.mk (I ^ (a : ℕ))) _ U
          ((adicConstantMap X (adicQuotientMap I b a hab)).hom.app U r) m := by
  let φ := Ideal.Quotient.mk (I ^ (b : ℕ))
  let ψ := adicQuotientMap I b a hab
  let χ := Ideal.Quotient.mk (I ^ (a : ℕ))
  have h : ψ.comp φ = χ := adicQuotientMap_comp_mk I b a hab
  let f : adicRestrict X φ (adicChange X φ P) ⟶
      adicRestrict X χ (adicChange X χ P) :=
    { f p := adicSheafTransition X φ ψ χ h (P.X p)
      comm' i j hij := by
        apply (SheafOfModules.toSheaf (adicModuleRing X Λ)).map_injective
        apply adicTensorAddHom_ext X φ
        intro U r m
        change (SheafOfModules.changeOfRingsHom (adicConstantMap X χ) _ (P.d i j)).val.app U
            ((adicSheafTransition X φ ψ χ h (P.X i)).val.app U
              (adicTensorSection X φ _ U r m)) =
          (adicSheafTransition X φ ψ χ h (P.X j)).val.app U
            ((SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (P.d i j)).val.app U
              (adicTensorSection X φ _ U r m))
        rw [adicSheafTransition_tensorSection, adicChangeHom_tensorSection,
          adicChangeHom_tensorSection, adicSheafTransition_tensorSection] }
  refine ⟨f, ?_, ?_⟩
  · intro p U r m
    exact adicSheafTransition_tensorSection X φ ψ χ h (P.X p) U r m
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro p
    apply (SheafOfModules.toSheaf (adicModuleRing X Λ)).map_injective
    apply adicTensorAddHom_ext X φ
    intro U r m
    exact (hg p U r m).trans
      (adicSheafTransition_tensorSection X φ ψ χ h (P.X p) U r m).symm


/-- Apply the quotient map on the scalar factor, with the original Λ-action retained.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTransitionComplex (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) :
    adicRestrict X (Ideal.Quotient.mk (I ^ (b : ℕ)))
      (adicChange X (Ideal.Quotient.mk (I ^ (b : ℕ))) P) ⟶
    adicRestrict X (Ideal.Quotient.mk (I ^ (a : ℕ)))
      (adicChange X (Ideal.Quotient.mk (I ^ (a : ℕ))) P) :=
  Classical.choose (adicTransitionComplex_exists X I P b a hab)

private theorem adicTransitionComplex_tensorSection (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) (p : ℤ) (U : X.ProEtᵒᵖ)
    (r : (adicConstantRing X (Λ ⧸ I ^ (b : ℕ))).obj.obj U) (m : (P.X p).val.obj U) :
    ((adicTransitionComplex X I P b a hab).f p).val.app U
      (adicTensorSection X (Ideal.Quotient.mk (I ^ (b : ℕ))) _ U r m) =
    adicTensorSection X (Ideal.Quotient.mk (I ^ (a : ℕ))) _ U
      ((adicConstantMap X (adicQuotientMap I b a hab)).hom.app U r) m :=
  (Classical.choose_spec (adicTransitionComplex_exists X I P b a hab)).1 p U r m

/-- The derived transition q_{b,a}, in the original coefficient category.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTransition (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (b a : ℕ+) (hab : a ≤ b) :
    adicReductionUnderlying X d M b ⟶ adicReductionUnderlying X d M a :=
  (adicLocalization X Λ).map (adicTransitionComplex X d.ideal M.complex b a hab)

/-- Equal-index transitions are identity maps. Source: blueprint order 1255, step 2.
Proof: the quotient homomorphism is identity, so the transition and identity have the
same tensor-generator formula. Uniqueness gives equality of chain maps and localization
preserves the identity.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransition_id (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (a : ℕ+) :
    adicTransition X d M a a (le_refl a) = 𝟙 (adicReductionUnderlying X d M a) := by
  have hid : adicQuotientMap d.ideal a a (le_refl a) =
      RingHom.id (Λ ⧸ d.ideal ^ (a : ℕ)) := Ideal.Quotient.factor_eq
  have he : adicTransitionComplex X d.ideal M.complex a a (le_refl a) = 𝟙 _ := by
    apply Eq.symm
    apply (Classical.choose_spec
      (adicTransitionComplex_exists X d.ideal M.complex a a (le_refl a))).2
    intro p U r m
    rw [hid, adicConstantMap_id]
    rfl
  change (adicLocalization X Λ).map _ = _
  rw [he]
  exact (adicLocalization X Λ).map_id _

/-- Transition maps compose in the stated order. Source: blueprint order 1255, step 2.
Proof: quotient homomorphisms compose. On every local tensor generator both chain-map
paths send r tensor m to q_{c,a}(r) tensor m. Uniqueness gives equality of chain maps;
the localization functor preserves composition.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransition_comp (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (c b a : ℕ+) (hab : a ≤ b) (hbc : b ≤ c) :
    adicTransition X d M c a (le_trans hab hbc) =
      adicTransition X d M c b hbc ≫ adicTransition X d M b a hab := by
  have he : adicTransitionComplex X d.ideal M.complex c a (le_trans hab hbc) =
      adicTransitionComplex X d.ideal M.complex c b hbc ≫
        adicTransitionComplex X d.ideal M.complex b a hab := by
    apply Eq.symm
    apply (Classical.choose_spec
      (adicTransitionComplex_exists X d.ideal M.complex c a (le_trans hab hbc))).2
    intro p U r m
    change ((adicTransitionComplex X d.ideal M.complex b a hab).f p).val.app U
        (((adicTransitionComplex X d.ideal M.complex c b hbc).f p).val.app U _) = _
    rw [adicTransitionComplex_tensorSection, adicTransitionComplex_tensorSection]
    have hq : (adicQuotientMap d.ideal b a hab).comp
        (adicQuotientMap d.ideal c b hbc) =
        adicQuotientMap d.ideal c a (le_trans hab hbc) :=
      Ideal.Quotient.factor_comp _ _
    have hm := adicConstantMap_comp X (adicQuotientMap d.ideal c b hbc)
      (adicQuotientMap d.ideal b a hab)
    rw [hq] at hm
    have hv := congrArg (fun q ↦ q.hom.app U) hm
    have hr := ConcreteCategory.congr_hom hv r
    exact congrArg (fun z ↦
      adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) _ U z m) hr
  unfold adicTransition
  rw [← Functor.map_comp, ← he]

/-- Termwise extension of a chain map commutes with differentials.
Source: blueprint order 1255, steps 3 and 4; Stacks Tag 03EK.
Proof: extension of scalars preserves composition; apply it to the commutativity equation
for the original chain map, then sheafify. The resulting equality is exactly the displayed
chain-map condition.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicChangeHom_comm (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ}
    (f : P ⟶ Q) (i j : ℤ) :
    SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
        (adicConstantMap X φ) (P.X i) (f.f i) ≫ (adicChange X φ Q).d i j =
      (adicChange X φ P).d i j ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
          (adicConstantMap X φ) (P.X j) (f.f j) := by
  change SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (f.f i) ≫
      SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (Q.d i j) =
    SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (P.d i j) ≫
      SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (f.f j)
  rw [← adicSheafChangeHom_comp, ← adicSheafChangeHom_comp, f.comm]

/-- Extension of a chain map on each term, using the recorded sheaf change-of-rings map.
Source: blueprint order 1255, steps 3 and 4
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicChangeHom (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ}
    (f : P ⟶ Q) : adicChange X φ P ⟶ adicChange X φ Q where
  f i := SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
    (adicConstantMap X φ) (P.X i) (f.f i)
  comm' i j _ := adicChangeHom_comm X φ f i j

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary balancing is natural in the complex being extended.
Source: blueprint order 1255, step 3; Stacks Tag 0D6D.
Proof: both composites send s tensor (r tensor m) to
(s * ψ(r)) tensor f(m). Linearity, restriction compatibility, and local tensor generation
give equality of the sheaf maps in every degree, hence equality of chain maps. Inverting
quasi-isomorphisms between K-flat models preserves this equality, proving compatibility
with the canonical resolution comparisons of lem-pur-derived-change-of-rings.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalanceHom_naturality (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ} (f : P ⟶ Q) :
    adicChangeHom X ψ (adicChangeHom X φ f) ≫ adicBalanceHom X φ ψ χ h Q =
      adicBalanceHom X φ ψ χ h P ≫ adicChangeHom X χ f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply adicTranspose_injective X ψ
  apply adicTensorHom_ext X φ
  intro U r m
  change ((adicBalanceHom X φ ψ χ h Q).f p).val.app U
      ((SheafOfModules.changeOfRingsHom (adicConstantMap X ψ) _
        (SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (f.f p))).val.app U
          (adicTensorSection X ψ _ U 1 (adicTensorSection X φ _ U r m))) =
    (SheafOfModules.changeOfRingsHom (adicConstantMap X χ) _ (f.f p)).val.app U
      (((adicBalanceHom X φ ψ χ h P).f p).val.app U
        (adicTensorSection X ψ _ U 1 (adicTensorSection X φ _ U r m)))
  rw [adicChangeHom_tensorSection, adicChangeHom_tensorSection]
  rw [adicBalanceHom_tensorSection X φ ψ χ h P p U 1 r m]
  exact (adicBalanceHom_tensorSection X φ ψ χ h Q p U 1 r
    ((f.f p).val.app U m)).trans
      (adicChangeHom_tensorSection X χ (f.f p) U
        (1 * (adicConstantMap X ψ).hom.app U r) m).symm


/-- The transitions commute with comparison maps of the chosen complexes.
Source: blueprint order 1255, step 2.
Proof: both paths send r tensor m to q_{b,a}(r) tensor f(m), by the two defining
tensor formulas. Local tensor generation gives equality in every degree. After
localization, the equality persists under inversion of quasi-isomorphisms between K-flat
models; hence the canonical resolution comparisons preserve the transition tower.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransitionComplex_naturality (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ}
    (f : P ⟶ Q) (b a : ℕ+) (hab : a ≤ b) :
    ((SheafOfModules.restrictScalars.{t + 1}
        (adicModuleMap X (Ideal.Quotient.mk (I ^ (b : ℕ))))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (I ^ (b : ℕ))) f) ≫
      adicTransitionComplex X I Q b a hab =
    adicTransitionComplex X I P b a hab ≫
      ((SheafOfModules.restrictScalars.{t + 1}
        (adicModuleMap X (Ideal.Quotient.mk (I ^ (a : ℕ))))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (I ^ (a : ℕ))) f) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply (SheafOfModules.toSheaf (adicModuleRing X Λ)).map_injective
  apply adicTensorAddHom_ext X (Ideal.Quotient.mk (I ^ (b : ℕ)))
  intro U r m
  change ((adicTransitionComplex X I Q b a hab).f p).val.app U
      ((SheafOfModules.changeOfRingsHom
        (adicConstantMap X (Ideal.Quotient.mk (I ^ (b : ℕ)))) _ (f.f p)).val.app U
          (adicTensorSection X (Ideal.Quotient.mk (I ^ (b : ℕ))) _ U r m)) =
    (SheafOfModules.changeOfRingsHom
      (adicConstantMap X (Ideal.Quotient.mk (I ^ (a : ℕ)))) _ (f.f p)).val.app U
        (((adicTransitionComplex X I P b a hab).f p).val.app U
          (adicTensorSection X (Ideal.Quotient.mk (I ^ (b : ℕ))) _ U r m))
  rw [adicChangeHom_tensorSection, adicTransitionComplex_tensorSection,
    adicTransitionComplex_tensorSection, adicChangeHom_tensorSection]

/-- The direct and composite quotient homomorphisms coincide.
Source: blueprint order 1255, steps 2 and 4.
Proof: quotient induction reduces both maps to the identical map on representatives.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_comp {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (c b a : ℕ+) (hab : a ≤ b) (hbc : b ≤ c) :
    (adicQuotientMap I b a hab).comp (adicQuotientMap I c b hbc) =
      adicQuotientMap I c a (le_trans hab hbc) := by
  exact Ideal.Quotient.factor_comp _ _

set_option backward.isDefEq.respectTransparency false in
/-- The normalization cocycle, including the canonical associativity identification of
its source. The left path extends θ_{c,b} to P_a and then applies θ_{b,a}; the right
path first balances the last two extensions and then applies θ_{c,a}.
Source: blueprint order 1255, step 4; Stacks Tag 0D6D.
Proof: on local generators s tensor (r tensor (t tensor m)), both paths give
(s * q_{b,a}(r) * q_{c,a}(t)) tensor m. This uses composition and multiplicativity of the
quotient homomorphisms. Local tensor generation and sheafification give equality of chain
maps. Localization gives the displayed equality. K-flatness of successive extensions is
lem-pur-kflat-change-of-rings, so these models compute the successive derived extensions.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicNormalization_cocycle (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (c b a : ℕ+) (hab : a ≤ b) (hbc : b ≤ c) :
    (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map
      (adicChangeHom X (adicQuotientMap d.ideal b a hab)
        (adicBalanceHom X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
          (adicQuotientMap d.ideal c b hbc) (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
          (adicQuotientMap_comp_mk d.ideal c b hbc) M.complex)) ≫
      (adicNormalization X d M b a hab).hom =
    (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map
      (adicBalanceHom X (adicQuotientMap d.ideal c b hbc)
        (adicQuotientMap d.ideal b a hab) (adicQuotientMap d.ideal c a (le_trans hab hbc))
        (adicQuotientMap_comp d.ideal c b a hab hbc)
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) M.complex)) ≫
      (adicNormalization X d M c a (le_trans hab hbc)).hom := by
  change (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map _ ≫
      (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map _ =
    (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map _ ≫
      (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro p
  apply adicTranspose_injective X (adicQuotientMap d.ideal b a hab)
  apply adicTranspose_injective X (adicQuotientMap d.ideal c b hbc)
  apply adicTensorHom_ext X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
  intro U r m
  change ((adicBalanceHom X (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
      (adicQuotientMap d.ideal b a hab) (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
      (adicQuotientMap_comp_mk d.ideal b a hab) M.complex).f p).val.app U
    ((SheafOfModules.changeOfRingsHom
      (adicConstantMap X (adicQuotientMap d.ideal b a hab)) _
      ((adicBalanceHom X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
        (adicQuotientMap d.ideal c b hbc) (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
        (adicQuotientMap_comp_mk d.ideal c b hbc) M.complex).f p)).val.app U
      (adicTensorSection X (adicQuotientMap d.ideal b a hab) _ U 1
        (adicTensorSection X (adicQuotientMap d.ideal c b hbc) _ U 1
          (adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) _ U r m)))) = _
  rw [adicChangeHom_tensorSection]
  rw [adicBalanceHom_tensorSection X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
    (adicQuotientMap d.ideal c b hbc) (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
    (adicQuotientMap_comp_mk d.ideal c b hbc) M.complex p U 1 r m]
  rw [adicBalanceHom_tensorSection X (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
    (adicQuotientMap d.ideal b a hab) (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
    (adicQuotientMap_comp_mk d.ideal b a hab) M.complex p U 1
    (1 * (adicConstantMap X (adicQuotientMap d.ideal c b hbc)).hom.app U r) m]
  change _ = ((adicBalanceHom X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
      (adicQuotientMap d.ideal c a (le_trans hab hbc))
      (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
      (adicQuotientMap_comp_mk d.ideal c a (le_trans hab hbc)) M.complex).f p).val.app U
    (((adicBalanceHom X (adicQuotientMap d.ideal c b hbc)
      (adicQuotientMap d.ideal b a hab) (adicQuotientMap d.ideal c a (le_trans hab hbc))
      (adicQuotientMap_comp d.ideal c b a hab hbc)
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) M.complex)).f p).val.app U
      (adicTensorSection X (adicQuotientMap d.ideal b a hab) _ U 1
        (adicTensorSection X (adicQuotientMap d.ideal c b hbc) _ U 1
          (adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) _ U r m))))
  rw [adicBalanceHom_tensorSection X (adicQuotientMap d.ideal c b hbc)
    (adicQuotientMap d.ideal b a hab) (adicQuotientMap d.ideal c a (le_trans hab hbc))
    (adicQuotientMap_comp d.ideal c b a hab hbc)
    (adicChange X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) M.complex) p U 1 1
    (adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) _ U r m)]
  rw [adicBalanceHom_tensorSection X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
    (adicQuotientMap d.ideal c a (le_trans hab hbc))
    (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
    (adicQuotientMap_comp_mk d.ideal c a (le_trans hab hbc)) M.complex p U
    (1 * (adicConstantMap X (adicQuotientMap d.ideal b a hab)).hom.app U 1) r m]
  simp only [one_mul, map_one]
  have hmap := adicConstantMap_comp X (adicQuotientMap d.ideal c b hbc)
    (adicQuotientMap d.ideal b a hab)
  rw [adicQuotientMap_comp] at hmap
  exact congrArg (fun z ↦
    adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) _ U z m)
      (ConcreteCategory.congr_hom (congrArg (fun q ↦ q.hom.app U) hmap) r)

private theorem adicConstantMap_id_app (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) (U : X.ProEtᵒᵖ) :
    ((adicConstantMap X φ).hom.app U).hom = RingHom.id _ := by
  subst φ
  rw [adicConstantMap_id]
  rfl

private noncomputable def adicRestrictIdIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (N : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    (SheafOfModules.restrictScalars (adicModuleMap X φ)).obj N ≅ N where
  hom.val.app U := (ModuleCat.restrictScalarsId'App _
    (adicConstantMap_id_app X φ hφ U) (N.val.obj U)).hom
  hom.val.naturality i := by ext m; rfl
  inv.val.app U := (ModuleCat.restrictScalarsId'App _
    (adicConstantMap_id_app X φ hφ U) (N.val.obj U)).inv
  inv.val.naturality i := by ext m; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adicSheafUnitIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (N : SheafOfModules.{t + 1} (adicModuleRing X A)) :
    SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) N ≅ N where
  hom := adicLift X φ N N (adicRestrictIdIso X φ hφ N).inv
  inv := adicTranspose X φ N _ (𝟙 _) ≫ (adicRestrictIdIso X φ hφ _).hom
  hom_inv_id := by
    apply adicTranspose_injective X φ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change adicTensorSection X φ N U 1
        ((adicLift X φ N N (adicRestrictIdIso X φ hφ N).inv).val.app U
          (adicTensorSection X φ N U 1 m)) = adicTensorSection X φ N U 1 m
    rw [adicLift_tensorSection]
    change adicTensorSection X φ N U 1 ((1 : (adicConstantRing X A).obj.obj U) • m) = _
    rw [one_smul]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adicLift X φ N N (adicRestrictIdIso X φ hφ N).inv).val.app U
      (adicTensorSection X φ N U 1 m) = m
    rw [adicLift_tensorSection]
    change (1 : (adicConstantRing X A).obj.obj U) • m = m
    exact one_smul _ m

/-- Existence and the tensor-generator formula for the identity scalar extension map.
Source: blueprint order 1255, step 4; Stacks Tag 03EK.
Proof: construct the sheafified map sending `s tensor m` to `s • m` and its inverse
sending `m` to `1 tensor m`; verify restriction and differential compatibility on local
sections, then prove the two composites are identities by tensor induction.
(blueprint: adic-unit-exists-data) -/
theorem adicUnit_exists_data (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    ∃ f : adicChange X φ P ⟶ P, IsIso f ∧
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ) (s : (adicConstantRing X A).obj.obj U)
        (m : (P.X p).val.obj U),
        (f.f p).val.app U (adicTensorSection X φ _ U s m) = s • m  := by
  let e : adicChange X φ P ≅ P :=
    HomologicalComplex.Hom.isoOfComponents (fun p ↦ adicSheafUnitIso X φ hφ (P.X p)) (by
      intro i j hij
      apply adicTensorHom_ext X φ
      intro U s m
      change (P.d i j).val.app U
          ((adicLift X φ (P.X i) (P.X i)
            (adicRestrictIdIso X φ hφ (P.X i)).inv).val.app U
              (adicTensorSection X φ _ U s m)) =
        (adicLift X φ (P.X j) (P.X j)
          (adicRestrictIdIso X φ hφ (P.X j)).inv).val.app U
            ((SheafOfModules.changeOfRingsHom (adicConstantMap X φ) _ (P.d i j)).val.app U
              (adicTensorSection X φ _ U s m))
      rw [adicChangeHom_tensorSection, adicLift_tensorSection, adicLift_tensorSection]
      exact map_smul _ _ _)
  refine ⟨e.hom, inferInstance, ?_⟩
  intro p U s m
  exact adicLift_tensorSection X φ (P.X p) (P.X p)
    (adicRestrictIdIso X φ hφ (P.X p)).inv U s m

theorem adicUnit_exists (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    ∃! f : adicChange X φ P ⟶ P, IsIso f ∧
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ) (s : (adicConstantRing X A).obj.obj U)
        (m : (P.X p).val.obj U),
        (f.f p).val.app U (adicTensorSection X φ _ U s m) = s • m := by
  obtain ⟨f, hf, hform⟩ := adicUnit_exists_data X φ hφ P
  refine ⟨f, ⟨hf, hform⟩, ?_⟩
  intro g hg
  apply HomologicalComplex.hom_ext
  intro p
  apply adicTensorHom_ext
  intro U s m
  exact (hg.2 p U s m).trans (hform p U s m).symm


/-- The ordinary unit map, with its canonical tensor-generator formula.
Source: blueprint order 1255, step 4
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicUnitHom (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X φ P ⟶ P :=
  Classical.choose (adicUnit_exists X φ hφ P)

private theorem adicUnitHom_tensorSection (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ)
    (p : ℤ) (U : X.ProEtᵒᵖ) (s : (adicConstantRing X A).obj.obj U)
    (m : (P.X p).val.obj U) :
    ((adicUnitHom X φ hφ P).f p).val.app U (adicTensorSection X φ _ U s m) = s • m :=
  (Classical.choose_spec (adicUnit_exists X φ hφ P)).1.2 p U s m

/-- The equal-index quotient homomorphism is identity.
Source: blueprint order 1255, steps 2 and 4.
Proof: its defining quotient factor sends each class to itself, so quotient induction
proves equality to the identity homomorphism.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_id {Λ : Type t} [CommRing Λ] (I : Ideal Λ) (a : ℕ+) :
    adicQuotientMap I a a (le_refl a) = RingHom.id (Λ ⧸ I ^ (a : ℕ)) := by
  exact Ideal.Quotient.factor_eq

set_option backward.isDefEq.respectTransparency false in
/-- Equal-index normalization is the unit identification, rather than an arbitrary
isomorphism between its source and target. Source: blueprint order 1255, step 4.
Proof: on s tensor (r tensor m), balancing gives (s*r) tensor m. This is precisely
the action of the unit map on the changed complex. The unique tensor-generator
characterizations identify the chain maps, and then their localizations.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicNormalization_unit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (a : ℕ+) :
    (adicNormalization X d M a a (le_refl a)).hom =
      (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map
        (adicUnitHom X (adicQuotientMap d.ideal a a (le_refl a))
          (adicQuotientMap_id d.ideal a)
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) M.complex)) := by
  change (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map _ =
    (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map _
  congr 1
  apply HomologicalComplex.hom_ext
  intro p
  apply adicTranspose_injective X (adicQuotientMap d.ideal a a (le_refl a))
  apply adicTensorHom_ext X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
  intro U r m
  change ((adicBalanceHom X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
      (adicQuotientMap d.ideal a a (le_refl a))
      (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
      (adicQuotientMap_comp_mk d.ideal a a (le_refl a)) M.complex).f p).val.app U
    (adicTensorSection X (adicQuotientMap d.ideal a a (le_refl a)) _ U 1
      (adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) _ U r m)) =
    ((adicUnitHom X (adicQuotientMap d.ideal a a (le_refl a))
      (adicQuotientMap_id d.ideal a)
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) M.complex)).f p).val.app U
    (adicTensorSection X (adicQuotientMap d.ideal a a (le_refl a)) _ U 1
      (adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) _ U r m))
  rw [adicBalanceHom_tensorSection, adicUnitHom_tensorSection,
    adicQuotientMap_id, adicConstantMap_id]
  simp only [one_mul, one_smul]
  rfl

/-- Restricting the quotient reduction is the recorded derived tensor product with the
constant quotient ring. Source: blueprint order 1255, statement and step 1.
Proof: the fixed K-flat model computes both sides (lem-pur-derived-change-of-rings).
Termwise scalar extension restricted to Λ is tensor with the quotient ring sheaf.
Tensoring with its degree-zero complex has just one nonzero summand in each total degree;
the ordinary scalar-extension tensor formula identifies this summand and its differential.
These identifications commute with restrictions and pass to localization.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicReductionUnderlying_tensor (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    Nonempty (adicReductionUnderlying X d M n ≅
      derivedTensorRing X Λ (Λ ⧸ d.ideal ^ (n : ℕ))
        (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex M.complex
        (𝟙 M.complex) (inferInstance : QuasiIso (𝟙 M.complex)) M.isKFlat) := by
  let R := adicConstantRing X Λ
  let T := adicConstantRing X (Λ ⧸ d.ideal ^ (n : ℕ))
  let φ := adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ)))
  let U := SheafOfModules.restrictScalars (adicModuleMap X
    (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))))
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory T
  let := SheafOfModules.symmetricCategory R
  let V := 𝟙_ (SheafOfModules.{t + 1} (adicModuleRing X (Λ ⧸ d.ideal ^ (n : ℕ))))
  let S := U.obj V
  obtain ⟨e, he⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation φ
  let q (p : ℤ) : U.obj (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ (M.complex.X p)) ≅
      M.complex.X p ⊗ S :=
    U.mapIso (λ_ (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ (M.complex.X p))).symm ≪≫
      e V (M.complex.X p) ≪≫ β_ S (M.complex.X p)
  let c : adicRestrict X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex) ≅
      ((tensorRight S).mapHomologicalComplex (.up ℤ)).obj M.complex :=
    HomologicalComplex.Hom.isoOfComponents q (by
      intro i j hij
      let f := SheafOfModules.changeOfRingsHom φ (M.complex.X i) (M.complex.d i j)
      have hu := congrArg U.map (leftUnitor_inv_naturality f)
      rw [Functor.map_comp, Functor.map_comp] at hu
      have hh : U.map (V ◁ f) ≫ (e V (M.complex.X j)).hom =
          (e V (M.complex.X i)).hom ≫ S ◁ M.complex.d i j := by
        have hl : (𝟙 V) ⊗ₘ f = V ◁ f := id_tensorHom V f
        have hr : U.map (𝟙 V) ⊗ₘ M.complex.d i j = S ◁ M.complex.d i j := by
          rw [U.map_id V]
          exact id_tensorHom _ _
        exact (congrArg (fun z ↦ U.map z ≫ (e V (M.complex.X j)).hom) hl).symm.trans
          ((he (𝟙 V) (M.complex.d i j)).trans
            (congrArg (fun z ↦ (e V (M.complex.X i)).hom ≫ z) hr))
      change (q i).hom ≫ M.complex.d i j ▷ S = U.map f ≫ (q j).hom
      dsimp only [q, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
      simp only [Category.assoc]
      rw [← BraidedCategory.braiding_naturality_right, ← reassoc_of% hh]
      exact ((reassoc_of% hu)
        ((e V (M.complex.X j)).hom ≫ (β_ S (M.complex.X j)).hom)).symm)
  refine ⟨(adicLocalization X Λ).mapIso (c ≪≫
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) S M.complex).symm)⟩

end AlgebraicGeometry.Scheme
