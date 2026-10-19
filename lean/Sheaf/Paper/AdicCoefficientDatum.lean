/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.AdicLisseModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# The completed coefficient ring and its strict derived reduction tower

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-adic-coefficient-datum, order 1239; Stacks Tags 06XN, 06YS, 06YY.
(blueprint: def-weil-pbc-adic-coefficient-datum).

The index n : ℕ denotes the positive exponent n+1. Every quotient reduction retains
its own coefficient action; tower levels restrict that action along the limit projection.
No constant/completed coefficient comparison is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [local irreducible] AlgebraicGeometry.Scheme.completedAdicChangeData

namespace AlgebraicGeometry.Scheme.AdicCoefficients

open scoped ChangeOfRings MonoidalCategory TensorProduct

/-- The recorded pure tensor in scalar extension, using the existing normalized witness.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev tensorSection (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R))
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((completedAdicChange T φ).obj M).val.obj U :=
  completedAdicChangeTensor T φ M U s m

/-- The commutative-ring presentation of the recorded continuous-function coefficient
presheaf; its objects and restrictions are exactly `finiteCoefficientPresheaf`.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def functionPresheaf (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    T.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  { obj := fun U ↦ CommRingCat.of C(ConnectedComponents U.unop.left, Λ)
    map := fun f ↦ CommRingCat.ofHom ((ProEtale.finiteCoefficientPresheaf T Λ).map f).hom
    map_id := fun U ↦ by
      ext s c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      rfl
    map_comp := fun f g ↦ by
      ext s c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      rfl }

/-- The actual coefficient sheaf, sheafifying those continuous functions.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def coefficientRing (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj (functionPresheaf T Λ)

/-- Postcomposition with a map of finite discrete commutative rings.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def functionPresheafMap (T : Scheme.{u}) {Λ Λ' : Type (u + 1)}
    [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (φ : Λ →+* Λ') :
    functionPresheaf T Λ ⟶ functionPresheaf T Λ' :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  letI : TopologicalSpace Λ' := ⊥
  letI : DiscreteTopology Λ' := ⟨rfl⟩
  { app := fun U ↦ CommRingCat.ofHom
      { toFun := fun s ↦ (⟨φ, continuous_of_discreteTopology⟩ : C(Λ, Λ')).comp s
        map_one' := by ext c; exact φ.map_one
        map_mul' := fun s t ↦ by ext c; exact φ.map_mul _ _
        map_zero' := by ext c; exact φ.map_zero
        map_add' := fun s t ↦ by ext c; exact φ.map_add _ _ }
    naturality := fun _ _ f ↦ by ext s; rfl }

/-- The quotient homomorphism on coefficient sheaves is the sheafified postcomposition map.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def coefficientMap (T : Scheme.{u}) {Λ Λ' : Type (u + 1)}
    [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (φ : Λ →+* Λ') :
    coefficientRing T Λ ⟶ coefficientRing T Λ' :=
  (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (functionPresheafMap T φ)

/-- The strict inverse system of the actual finite quotient coefficient sheaves.
Source: blueprint coefficient convention, Tag 09BT
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
def ringSystem (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  letI := hf
  Functor.ofOpSequence (X := fun n ↦ coefficientRing T (A ⧸ I ^ (n + 1)))
    (fun n ↦ coefficientMap T (Ideal.Quotient.factorPowSucc I (n + 1)))

/-- Completed coefficients are the actual inverse limit of the function coefficient sheaves,
with compatible-family sections. Source: blueprint, Tag 09BT
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedRing (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :=
  limit (ringSystem T I hf)

/-- The nth quotient coefficient module with its completed scalar action.
Source: blueprint, Tags 06YY and 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def residue (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj (completedRing T I hf)) :=
  (SheafOfModules.restrictScalars ((adicLisseForget T).map
    (limit.π (ringSystem T I hf) (op n)))).obj
      (SheafOfModules.unit ((adicLisseForget T).obj ((ringSystem T I hf).obj (op n))))

/-- The constants-to-functions morphism on presheaves, with its constant value formula.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def constants (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ) ⟶ functionPresheaf T Λ :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  { app := fun U ↦ CommRingCat.ofHom
      { toFun := fun x ↦ ContinuousMap.const _ x
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    naturality := fun _ _ f ↦ by ext x; rfl }

/-- The canonical comparison from constant sheafification to function sheafification.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def constantComparison (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    adicLisseConstantRing T Λ ⟶ coefficientRing T Λ :=
  (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (constants T Λ)

/-- The RingCat presentation is precisely the dependency's recorded finite coefficient sheaf.
Source: blueprint coefficient convention (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def finiteRingPresentation (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : Sheaf (ProEt.topology T) RingCat.{u + 1} :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  ProEtale.finiteCoefficientRingSheaf T Λ

/-- The recorded presheaf's map into its RingCat sheafification.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def finiteRingUnit (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    functionPresheaf T Λ ⋙ forget₂ CommRingCat RingCat ⟶ (finiteRingPresentation T Λ).obj :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  toSheafify (ProEt.topology T) (ProEtale.finiteCoefficientPresheaf T Λ)

/-- Forgetting the commutative presentation gives the recorded coefficient sheaf, with the
comparison uniquely fixed by the sheafification units.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: a ring-valued sheaf receiving the continuous-function presheaf receives a unique
map from its sheafification. Commutativity holds locally on generating sections, hence
globally, so forgetting commutativity preserves this reflection. Both reflection units
therefore factor through each other uniquely, giving inverse maps with the stated equation. -/
theorem finiteRingComparison_exists (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    ∃! f : (adicLisseForget T).obj (coefficientRing T Λ) ⟶ finiteRingPresentation T Λ,
      IsIso f ∧
        Functor.whiskerRight (toSheafify (ProEt.topology T) (functionPresheaf T Λ))
          (forget₂ CommRingCat RingCat) ≫ f.hom = finiteRingUnit T Λ := by
  let J := ProEt.topology T
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let P := functionPresheaf T Λ
  let η := Functor.whiskerRight (toSheafify J P) F
  have hηi : Presheaf.IsLocallyInjective J η :=
    (Presheaf.isLocallyInjective_forget_iff J η).1
      (inferInstanceAs (Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J P) (CategoryTheory.forget CommRingCat.{u + 1}))))
  have hηs : Presheaf.IsLocallySurjective J η :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J η).2
      (inferInstanceAs (Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J P) (CategoryTheory.forget CommRingCat.{u + 1}))))
  let g : finiteRingPresentation T Λ ⟶ (adicLisseForget T).obj (coefficientRing T Λ) :=
    (sheafComposeNatTrans J F (sheafificationAdjunction J CommRingCat.{u + 1})
      (sheafificationAdjunction J RingCat.{u + 1})).app P
  have hg : toSheafify J (P ⋙ F) ≫ g.hom = η :=
    sheafComposeNatTrans_fac J F (sheafificationAdjunction J CommRingCat.{u + 1})
      (sheafificationAdjunction J RingCat.{u + 1}) P
  have : Presheaf.IsLocallyInjective J (toSheafify J (P ⋙ F) ≫ g.hom) :=
    hg.symm ▸ hηi
  have : Presheaf.IsLocallySurjective J (toSheafify J (P ⋙ F) ≫ g.hom) :=
    hg.symm ▸ hηs
  have : Sheaf.IsLocallyInjective g :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      J (toSheafify J (P ⋙ F)) g.hom
  have : Sheaf.IsLocallySurjective g :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J (toSheafify J (P ⋙ F)) g.hom
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).1 ⟨inferInstance, inferInstance⟩
  have he : η ≫ (inv g).hom = finiteRingUnit T Λ := by
    rw [← hg, Category.assoc]
    change toSheafify J (P ⋙ F) ≫ (g ≫ inv g).hom = _
    rw [IsIso.hom_inv_id]
    exact Category.comp_id _
  refine ⟨inv g, ⟨inferInstance, he⟩, ?_⟩
  intro f hf
  apply (cancel_epi g).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (finiteRingPresentation T Λ).property
  change toSheafify J (P ⋙ F) ≫ (g.hom ≫ f.hom) =
    toSheafify J (P ⋙ F) ≫ (g.hom ≫ (inv g).hom)
  calc
    _ = η ≫ f.hom := (Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ f.hom) hg)
    _ = finiteRingUnit T Λ := hf.2
    _ = η ≫ (inv g).hom := he.symm
    _ = _ := (congrArg (fun k ↦ k ≫ (inv g).hom) hg).symm.trans
      (Category.assoc _ _ _)

/-- Canonical identification with the existing RingCat coefficient sheaf, retaining its unit.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def finiteRingComparison (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (adicLisseForget T).obj (coefficientRing T Λ) ≅ finiteRingPresentation T Λ :=
  letI := (finiteRingComparison_exists T Λ).choose_spec.1.1
  asIso (finiteRingComparison_exists T Λ).choose

end AlgebraicGeometry.Scheme.AdicCoefficients

namespace AlgebraicGeometry.Scheme

/-- The quotient map between arbitrary positive powers, not just consecutive powers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionQuotientMap {A : Type (t + 1)} [CommRing A] (I : Ideal A)
    (b a : ℕ) (h : a ≤ b) : A ⧸ I ^ (b + 1) →+* A ⧸ I ^ (a + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The quotient coefficient sheaf, obtained from continuous component functions.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionCoefficient (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  (AdicCoefficients.ringSystem T d.ideal d.quotientFinite).obj (op n)

/-- Postcomposition by the actual quotient homomorphism, followed by sheafification.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionCoefficientMap (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    reductionCoefficient T d b ⟶ reductionCoefficient T d a :=
  (AdicCoefficients.ringSystem T d.ideal d.quotientFinite).map (homOfLE h).op

/-- Equal-index quotient coefficient maps are identities.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: quotient induction identifies the quotient map with the identity. Postcomposition
is then identity on component functions, and sheafification preserves identities. -/
theorem reductionCoefficientMap_id (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (a : ℕ) : reductionCoefficientMap T d a a (le_refl a) = 𝟙 _ := by
  exact (AdicCoefficients.ringSystem T d.ideal d.quotientFinite).map_id (op a)

/-- Quotient coefficient maps satisfy the quotient cocycle.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both quotient composites send the class of x to its class modulo I^(a+1).
Postcomposition and sheafification preserve that equality and composition. -/
theorem reductionCoefficientMap_comp (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    reductionCoefficientMap T d c b hbc ≫ reductionCoefficientMap T d b a hab =
      reductionCoefficientMap T d c a (hab.trans hbc) := by
  exact ((AdicCoefficients.ringSystem T d.ideal d.quotientFinite).map_comp
    (homOfLE hbc).op (homOfLE hab).op).symm

/-- The strict diagram of all positive quotient coefficient sheaves.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionCoefficientSystem (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  AdicCoefficients.ringSystem T d.ideal d.quotientFinite

/-- The actual inverse limit sheaf of commutative rings. Limits of sheaves are computed
on sections, so its sections are compatible families with pointwise operations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionCoefficient (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  limit (reductionCoefficientSystem T d)

/-- The n-th coordinate of the limit of quotient coefficient sheaves.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionProjection (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionCoefficient T d ⟶ reductionCoefficient T d n :=
  limit.π (reductionCoefficientSystem T d) (op n)

/-- The ring underlying a commutative coefficient sheaf on the small pro-etale site.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionModuleRing (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

/-- Left module sheaves over a given coefficient ring; this is the recorded category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionModules (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  ringedSiteModules.{t + 1} (reductionModuleRing T R)

/-- The standard localization for these module sheaves, keeping site sizes t+1 and t.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionModulesHasDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    HasDerivedCategory (reductionModules T R) := HasDerivedCategory.standard _

/-- D(Mod(R)) with its canonical cochain localization.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  DerivedCategory (reductionModules T R)

/-- Strict inverse sequences and compatible levelwise maps, indexed n↦n+1.
The coefficient ring B may be noncommutative.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev reductionTowerCategory (T : Scheme.{t}) (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :=
  ℕᵒᵖ ⥤ ringedSiteModules.{t + 1} B

/-- Strict module towers are Grothendieck abelian, including noncommutative coefficients.
Source: blueprint order 1239; Stacks Tags 079B and 079Q
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: replace the pro-etale site by its small skeleton in universe t+1. Apply
lem-weil-pbc-small-module-diagrams-grothendieck to the inverse-sequence index category.
Restriction along the site equivalence identifies the two module and diagram categories
and transports the Grothendieck structure. Kernels, cokernels, and exactness are
levelwise by lem-weil-tower-category-levelwise-abelian. -/
theorem reductionTower_isGrothendieckAbelian (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :
    IsGrothendieckAbelian.{t + 1} (reductionTowerCategory T B) := by
  let B' := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
    RingCat.{t + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj B
  let : (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).functor.IsContinuous
      (ProEt.topology T) (proEtaleModelTopology T) := proEtaleModelUp_isContinuous T
  let : (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology T) (ProEt.topology T) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology T) (ProEt.topology T)
    infer_instance
  let e : SheafOfModules.{t + 1} B' ≌ SheafOfModules.{t + 1} B :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)) (𝟙 B) (𝟙 B')
      (by ext U; dsimp [AsSmall.equiv]; erw [B'.obj.map_id]; rfl)
      (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
  have : IsGrothendieckAbelian.{t + 1}
      (AsSmall.{t + 1} ℕᵒᵖ ⥤ ringedSiteModules.{t + 1} B') :=
    smallModuleDiagrams_isGrothendieckAbelian (proEtaleModelTopology T) B'
      (AsSmall.{t + 1} ℕᵒᵖ)
  let eJ : ℕᵒᵖ ≌ AsSmall.{t + 1} ℕᵒᵖ := AsSmall.equiv
  have : IsGrothendieckAbelian.{t + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{t + 1} B') :=
    IsGrothendieckAbelian.of_equivalence (Equivalence.congrLeft eJ.symm)
  exact IsGrothendieckAbelian.of_equivalence (Equivalence.congrRight e)

/-- Exact evaluation of a strict inverse sequence at the positive exponent n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionTowerEvaluation (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ (ringedSiteModules.{t + 1} B)).obj (op n)

/-- The standard derived category of completed-coefficient towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionTowerHasDerivedCategory (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :
    HasDerivedCategory (reductionTowerCategory T B) := HasDerivedCategory.standard _

/-- Standard localization for modules over any coefficient ring sheaf B.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionRingModulesHasDerivedCategory (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :
    HasDerivedCategory (ringedSiteModules.{t + 1} B) := HasDerivedCategory.standard _

/-- Derived evaluation is induced by the exact termwise evaluation functor.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionTowerDerivedEvaluation (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ) :=
  (reductionTowerEvaluation T B n).mapDerivedCategory

/-- Specialize the recorded derived-change-of-rings theorem with standard localizations.
Its ordinary functor is fixed on objects and maps, and its derived pair is universal.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionChangeExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  completedAdicChangeData T φ

/-- Ordinary scalar extension, fixed by sheafified sectionwise tensor on objects and maps.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionModules T R ⥤ reductionModules T S := completedAdicChange T φ

/-- The additive structure supplied by the canonical scalar-extension witness.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionChangeAdditive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionChange T φ).Additive :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal derived scalar-extension pair, including its K-flat counit isomorphisms.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: specialize derivedChangeOfRingsIndependentCoefficients to the small pro-etale
site and the two specified coefficient sheaves. Select its ordinary tensor functor,
with the fixed object and map formulas, exactly as in reductionChange. Its additive
instance is reductionChangeAdditive. The final existence clause of that theorem
supplies the universal derived pair, shift compatibility and K-flat counit computation. -/
noncomputable def reductionDerivedExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ (LF : reductionDerivedCategory T R ⥤ reductionDerivedCategory T S)
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (reductionModules T R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (reductionModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  by
    simpa +instances only [reductionDerivedCategory, reductionChange, completedAdicChange,
      reductionChangeExistence, reductionModules, reductionModuleRing, ringedSiteModules,
      SheafOfModules.derivedChangeRingIndependentCoefficients,
      reductionModulesHasDerivedCategory, reductionRingModulesHasDerivedCategory] using
      (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived scalar extension is chosen with its universal comparison, hence is determined
up to unique compatible isomorphism, rather than by a mere existence of a functor.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionDerivedCategory T R ⥤ reductionDerivedCategory T S :=
  completedAdicDerivedChange T φ

/-- The universal counit comparing the derived functor with ordinary tensor on homotopy.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionDerivedCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    DerivedCategory.Qh ⋙ reductionDerivedChange T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (reductionDerivedExistence T φ).choose_spec.choose

/-- The left-derived universal property determining scalar extension and its counit.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionDerivedUniversal (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionDerivedChange T φ).IsLeftDerivedFunctor (reductionDerivedCounit T φ)
      (HomotopyCategory.quasiIso (reductionModules T R) (ComplexShape.up ℤ)) :=
  (reductionDerivedExistence T φ).choose_spec.choose_spec.1

/-- The sheafified pure tensor, including the object's canonical equality transport.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionTensorSection (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((reductionChange T φ).obj M).val.obj U :=
  completedAdicChangeTensor T φ M U s x

/-- Restrict the coefficient action without changing the underlying abelian sheaf.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionRestrict (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)

private theorem reductionChange_eq_witness (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionChange T φ = (reductionChangeExistence T φ).choose := rfl

private theorem reductionChange_map (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : reductionModules T R} (f : M ⟶ N) :
    (reductionChange T φ).map f =
      eqToHom ((reductionChangeExistence T φ).choose_spec.choose M) ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ M f ≫
          eqToHom ((reductionChangeExistence T φ).choose_spec.choose N).symm :=
  by
    simpa only [reductionChange_eq_witness] using
      (reductionChangeExistence T φ).choose_spec.choose_spec.choose f

private theorem reductionChange_quasiIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (reductionModules T R) ℤ} (f : P ⟶ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (hf : QuasiIso f) :
    QuasiIso (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).map f) :=
  by
    simpa only [reductionChange_eq_witness] using
      (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.1
        f hP hQ hf

private theorem reductionDerivedCounit_kflat (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso ((reductionDerivedCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionDerivedExistence T φ).choose_spec.choose_spec.2.2 P hP

attribute [local irreducible] completedAdicDerivedChange reductionDerivedCounit
  reductionDerivedExistence


private noncomputable def reductionTensorPresentation (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) :
    (reductionChange T φ).obj M ≅ SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M :=
  eqToIso ((reductionChangeExistence T φ).choose_spec.choose M)

private noncomputable def reductionRawTensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (reductionModuleRing T S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)

private theorem reductionTensorPresentation_tensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (reductionTensorPresentation T φ M).hom.val.app U
        (reductionTensorSection T φ M U s x) = reductionRawTensor T φ M U s x := by
  change ((reductionTensorPresentation T φ M).inv ≫
    (reductionTensorPresentation T φ M).hom).val.app U _ = _
  rw [Iso.inv_hom_id]
  rfl

private theorem reductionRawTensor_map (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) {U V : T.ProEtᵒᵖ} (i : U ⟶ V)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M).val.map i
      (reductionRawTensor T φ M U s x) =
      reductionRawTensor T φ M V (S.obj.map i s) (M.val.map i x) := by
  have hn := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{t + 1}
      (𝟙 (reductionModuleRing T S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)) i
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  change _ = (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M).val.map i
    (reductionRawTensor T φ M U s x) at hn
  have ht := Classical.choose_spec
    (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1} φ M i) s x
  change SheafOfModules.changeOfRingsMap.{t, t + 1, t + 1} φ M i _ = _ at ht
  change ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (reductionModuleRing T S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app V
        (SheafOfModules.changeOfRingsMap.{t, t + 1, t + 1} φ M i _) = _ at hn
  rw [ht] at hn
  exact hn.symm

private noncomputable def reductionRawTranspose (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : reductionModules T S)
    (f : SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M ⟶ N) :
    M ⟶ (reductionRestrict T φ).obj N where
  val.app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{t + 1, t + 1, t + 1}
    (φ.hom.app U).hom
      ((PresheafOfModules.sheafificationHomEquiv.{t + 1}
        (𝟙 (reductionModuleRing T S).obj) f).app U)
  val.naturality {U V} i := by
    ext x
    change f.val.app V (reductionRawTensor T φ M V 1 (M.val.map i x)) =
      N.val.map i (f.val.app U (reductionRawTensor T φ M U 1 x))
    have hn := PresheafOfModules.naturality_apply f.val i
      (reductionRawTensor T φ M U 1 x)
    rw [reductionRawTensor_map, map_one] at hn
    exact hn

private theorem reductionRawTranspose_injective (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : reductionModules T S) :
    Function.Injective (reductionRawTranspose T φ M N) := by
  intro f g h
  apply (PresheafOfModules.sheafificationHomEquiv.{t + 1}
    (𝟙 (reductionModuleRing T S).obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact ConcreteCategory.congr_hom (congrArg (fun q ↦ q.val.app U) h) x

private noncomputable def reductionTranspose (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : reductionModules T S)
    (f : (reductionChange T φ).obj M ⟶ N) :
    M ⟶ (reductionRestrict T φ).obj N :=
  reductionRawTranspose T φ M N ((reductionTensorPresentation T φ M).inv ≫ f)

private theorem reductionTranspose_injective (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : reductionModules T S) :
    Function.Injective (reductionTranspose T φ M N) := by
  intro f g h
  exact (cancel_epi (reductionTensorPresentation T φ M).inv).1
    (reductionRawTranspose_injective T φ M N h)

private theorem reductionTranspose_apply (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : reductionModules T S)
    (f : (reductionChange T φ).obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    (reductionTranspose T φ M N f).val.app U x =
      f.val.app U (reductionTensorSection T φ M U 1 x) := rfl

private theorem reductionTensorHom_ext (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : reductionModules T S)
    (f g : (reductionChange T φ).obj M ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (reductionTensorSection T φ M U 1 x) =
        g.val.app U (reductionTensorSection T φ M U 1 x)) : f = g := by
  apply reductionTranspose_injective T φ M N
  ext U x
  exact h U x

private theorem reductionDoubleTensorHom_ext (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (M : reductionModules T R) (N : reductionModules T U)
    (f g : (reductionChange T ψ).obj ((reductionChange T φ).obj M) ⟶ N)
    (h : ∀ (V : T.ProEtᵒᵖ) (x : M.val.obj V),
      f.val.app V (reductionTensorSection T ψ _ V 1
        (reductionTensorSection T φ M V 1 x)) =
      g.val.app V (reductionTensorSection T ψ _ V 1
        (reductionTensorSection T φ M V 1 x))) : f = g := by
  apply reductionTranspose_injective T ψ _ _
  apply reductionTensorHom_ext T φ
  intro V x
  exact (reductionTranspose_apply T ψ _ _ f V _).trans
    ((h V x).trans (reductionTranspose_apply T ψ _ _ g V _).symm)

private theorem reductionTripleTensorHom_ext (T : Scheme.{t})
    {R S U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (M : reductionModules T R) (N : reductionModules T V)
    (f g : (reductionChange T θ).obj
      ((reductionChange T ψ).obj ((reductionChange T φ).obj M)) ⟶ N)
    (h : ∀ (W : T.ProEtᵒᵖ) (x : M.val.obj W),
      f.val.app W (reductionTensorSection T θ _ W 1
        (reductionTensorSection T ψ _ W 1 (reductionTensorSection T φ M W 1 x))) =
      g.val.app W (reductionTensorSection T θ _ W 1
        (reductionTensorSection T ψ _ W 1 (reductionTensorSection T φ M W 1 x)))) : f = g := by
  apply reductionTranspose_injective T θ _ _
  apply reductionDoubleTensorHom_ext T φ ψ
  intro W x
  exact (reductionTranspose_apply T θ _ _ f W _).trans
    ((h W x).trans (reductionTranspose_apply T θ _ _ g W _).symm)

private theorem reductionRawChange_tensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : reductionModules T R} (f : M ⟶ N)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ M f).val.app U
        (reductionRawTensor T φ M U s x) =
      reductionRawTensor T φ N U s (f.val.app U x) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
  have hn := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (reductionModuleRing T S).obj)).unit.naturality p
  have hv := congrArg (fun q ↦ q.app U) hn
  have hx := ConcreteCategory.congr_hom hv
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  change reductionRawTensor T φ N U s (f.val.app U x) = _ at hx
  exact hx.symm

private theorem reductionTensorPresentation_naturality (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : reductionModules T R} (f : M ⟶ N) :
    (reductionChange T φ).map f ≫ (reductionTensorPresentation T φ N).hom =
      (reductionTensorPresentation T φ M).hom ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ M f := by
  rw [reductionChange_map]
  simp only [reductionTensorPresentation, eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem reductionChange_tensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : reductionModules T R} (f : M ⟶ N)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((reductionChange T φ).map f).val.app U (reductionTensorSection T φ M U s x) =
      reductionTensorSection T φ N U s (f.val.app U x) := by
  have hf := reductionChange_map T φ f
  change (reductionChange T φ).map f =
    (reductionTensorPresentation T φ M).hom ≫
      SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ M f ≫
        (reductionTensorPresentation T φ N).inv at hf
  rw [hf]
  change (reductionTensorPresentation T φ N).inv.val.app U
    ((SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ M f).val.app U
      ((reductionTensorPresentation T φ M).hom.val.app U
        (reductionTensorSection T φ M U s x))) = _
  rw [reductionTensorPresentation_tensor, reductionRawChange_tensor]
  rfl

private theorem reductionRawTensorAddHom_ext (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (N : Sheaf (ProEt.topology T) AddCommGrpCat.{t + 1})
    (f g : (SheafOfModules.toSheaf (reductionModuleRing T S)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M) ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      f.hom.app U (reductionRawTensor T φ M U s x) =
        g.hom.app U (reductionRawTensor T φ M U s x)) : f = g := by
  apply ((CategoryTheory.sheafificationAdjunction (ProEt.topology T)
    AddCommGrpCat.{t + 1}).homEquiv
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M).presheaf N).injective
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (φ.hom.app U).hom
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul s x => exact h U s x
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem reductionRestrictedTensorHom_ext (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M N : reductionModules T R)
    (f g : (reductionRestrict T φ).obj ((reductionChange T φ).obj M) ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (reductionTensorSection T φ M U s x) =
        g.val.app U (reductionTensorSection T φ M U s x)) : f = g := by
  let V := SheafOfModules.toSheaf (reductionModuleRing T R)
  let W := SheafOfModules.toSheaf (reductionModuleRing T S)
  apply V.map_injective
  apply (cancel_epi (W.map (reductionTensorPresentation T φ M).inv)).1
  apply reductionRawTensorAddHom_ext T φ M
  intro U s x
  exact h U s x

attribute [local irreducible] reductionTensorPresentation completedAdicChange
  reductionRawTensor reductionRawTranspose reductionTranspose

private noncomputable def reductionRestrictCompIso (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (N : reductionModules T U) :
    (reductionRestrict T χ).obj N ≅
      (reductionRestrict T φ).obj ((reductionRestrict T ψ).obj N) where
  hom.val.app V := (ModuleCat.restrictScalarsComp'App _ _ _
    (congrArg CommRingCat.Hom.hom (congrArg (fun q ↦ q.hom.app V) h).symm)
      (N.val.obj V)).hom
  hom.val.naturality i := by ext x; rfl
  inv.val.app V := (ModuleCat.restrictScalarsComp'App _ _ _
    (congrArg CommRingCat.Hom.hom (congrArg (fun q ↦ q.hom.app V) h).symm)
      (N.val.obj V)).inv
  inv.val.naturality i := by ext x; rfl

private noncomputable def reductionUnit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) :
    M ⟶ (reductionRestrict T φ).obj ((reductionChange T φ).obj M) :=
  reductionTranspose T φ M _ (𝟙 _)

/-- The ordinary coefficient-change complex, with its actual scalar-extension differential.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionChangeComplex (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    CochainComplex (reductionModules T R) ℤ ⥤ CochainComplex (reductionModules T S) ℤ :=
  (reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical balancing chain map is uniquely determined on local tensor generators.
Source: blueprint order 1239, normalization paragraph; Stacks Tag 03EK
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: send s tensor (r tensor x) to (s*ψ(r)) tensor x. The relation ψφ=χ makes
this balanced over both rings. Sheafification extends it uniquely; restrictions and
differentials commute with the formula. The inverse sends s tensor x to s tensor
(1 tensor x). Balancing verifies both inverse identities. Local tensor generation
proves uniqueness, including on the empty site object. -/
theorem reductionBalance_exists (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (_h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    ∃! f : (reductionChangeComplex T ψ).obj ((reductionChangeComplex T φ).obj P) ⟶
        (reductionChangeComplex T χ).obj P,
      IsIso f ∧ ∀ (p : ℤ) (V : T.ProEtᵒᵖ) (s : U.obj.obj V) (r : S.obj.obj V)
        (x : (P.X p).val.obj V),
        (f.f p).val.app V
          (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
            (reductionTensorSection T φ (P.X p) V r x)) =
          reductionTensorSection T χ (P.X p) V (s * ψ.hom.app V r) x := by
  obtain ⟨f, ⟨hi, hf⟩, hu⟩ := completedAdicBalance_exists T φ ψ χ _h P
  refine ⟨f, ⟨hi, ?_⟩, ?_⟩
  · intro p V s r x
    exact hf p V s r x
  · intro g hg
    apply hu g
    refine ⟨hg.1, ?_⟩
    intro p V s r x
    exact hg.2 p V s r x

/-- The canonical balancing map, selected from its unique local tensor formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionBalance (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T ψ).obj ((reductionChangeComplex T φ).obj P) ⟶
      (reductionChangeComplex T χ).obj P :=
  (reductionBalance_exists T φ ψ χ h P).exists.choose

/-- The balancing map is invertible, by its defining characterization.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionBalance_isIso (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ) : IsIso (reductionBalance T φ ψ χ h P) :=
  (reductionBalance_exists T φ ψ χ h P).exists.choose_spec.1

private theorem reductionBalance_tensor (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (reductionModules T R) ℤ)
    (p : ℤ) (V : T.ProEtᵒᵖ) (s : U.obj.obj V) (r : S.obj.obj V)
    (x : (P.X p).val.obj V) :
    ((reductionBalance T φ ψ χ h P).f p).val.app V
      (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X p)) V s
        (reductionTensorSection T φ (P.X p) V r x)) =
      reductionTensorSection T χ (P.X p) V (s * ψ.hom.app V r) x :=
  (reductionBalance_exists T φ ψ χ h P).exists.choose_spec.2 p V s r x

attribute [local irreducible] reductionBalance

private theorem reductionUnit_apply (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (reductionUnit T φ M).val.app V x = reductionTensorSection T φ M V 1 x :=
  reductionTranspose_apply T φ M _ (𝟙 _) V x

private noncomputable def reductionZeroComplex (T : Scheme.{t})
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (M : reductionModules T R) :
    CochainComplex (reductionModules T R) ℤ where
  X _ := M
  d _ _ := 0

private noncomputable def reductionModuleTransition (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (M : reductionModules T R) :
    (reductionRestrict T φ).obj ((reductionChange T φ).obj M) ⟶
      (reductionRestrict T χ).obj ((reductionChange T χ).obj M) :=
  (reductionRestrict T φ).map (reductionUnit T ψ ((reductionChange T φ).obj M)) ≫
    (reductionRestrictCompIso T φ ψ χ h _).inv ≫
      (reductionRestrict T χ).map ((reductionBalance T φ ψ χ h
        (reductionZeroComplex T M)).f 0)

attribute [local irreducible] reductionModuleTransition

private theorem reductionModuleTransition_tensor (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (M : reductionModules T R) (V : T.ProEtᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    (reductionModuleTransition T φ ψ χ h M).val.app V
      (reductionTensorSection T φ M V s x) =
        reductionTensorSection T χ M V (ψ.hom.app V s) x := by
  unfold reductionModuleTransition
  change ((reductionBalance T φ ψ χ h (reductionZeroComplex T M)).f 0).val.app V
    ((reductionUnit T ψ ((reductionChange T φ).obj M)).val.app V
      (reductionTensorSection T φ M V s x)) = _
  rw [reductionUnit_apply]
  exact (reductionBalance_tensor T φ ψ χ h (reductionZeroComplex T M)
    0 V 1 s x).trans (by rw [one_mul]; rfl)

private theorem reductionModuleTransition_naturality (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    {M N : reductionModules T R} (f : M ⟶ N) :
    (reductionChange T φ ⋙ reductionRestrict T φ).map f ≫
        reductionModuleTransition T φ ψ χ h N =
      reductionModuleTransition T φ ψ χ h M ≫
        (reductionChange T χ ⋙ reductionRestrict T χ).map f := by
  apply reductionRestrictedTensorHom_ext T φ M
  intro V s x
  change (reductionModuleTransition T φ ψ χ h N).val.app V
    (((reductionChange T φ).map f).val.app V
      (reductionTensorSection T φ M V s x)) =
    ((reductionChange T χ).map f).val.app V
      ((reductionModuleTransition T φ ψ χ h M).val.app V
        (reductionTensorSection T φ M V s x))
  rw [reductionChange_tensor, reductionModuleTransition_tensor,
    reductionModuleTransition_tensor, reductionChange_tensor]

/-- Ordinary reduction, with the completion's action restored by restriction of scalars.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionLevel (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  reductionChange T (completedReductionProjection T d n) ⋙
    reductionRestrict T (completedReductionProjection T d n)

/-- The unique natural transition sending s⊗x to q(s)⊗x after scalar restriction.
Source: blueprint order 1239, Stacks Tag 03EK
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the limit relation π_a=q_(b,a)π_b makes the displayed tensor formula balanced.
Extend on presheaf tensors and sheafify. It is linear over the completion, commutes with
restrictions, and is natural in M. Local pure tensors generate the sheafification, giving
uniqueness of the natural transformation. -/
theorem completedReductionTransition_exists (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    ∃! τ : completedReductionLevel T d b ⟶ completedReductionLevel T d a,
      ∀ (M : reductionModules T (completedReductionCoefficient T d)) (U : T.ProEtᵒᵖ)
        (s : (reductionCoefficient T d b).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection T
          (completedReductionProjection T d b) M U s x) =
          reductionTensorSection T (completedReductionProjection T d a) M U
            ((reductionCoefficientMap T d b a h).hom.app U s) x := by
  have hc : completedReductionProjection T d b ≫ reductionCoefficientMap T d b a h =
      completedReductionProjection T d a :=
    limit.w (reductionCoefficientSystem T d) (homOfLE h).op
  let τ : completedReductionLevel T d b ⟶ completedReductionLevel T d a :=
    { app := reductionModuleTransition T (completedReductionProjection T d b)
        (reductionCoefficientMap T d b a h) (completedReductionProjection T d a) hc
      naturality := fun _ _ f ↦ reductionModuleTransition_naturality T
        (completedReductionProjection T d b) (reductionCoefficientMap T d b a h)
        (completedReductionProjection T d a) hc f }
  have hτ : ∀ (M : reductionModules T (completedReductionCoefficient T d))
      (U : T.ProEtᵒᵖ) (s : (reductionCoefficient T d b).obj.obj U) (x : M.val.obj U),
      (τ.app M).val.app U (reductionTensorSection T
        (completedReductionProjection T d b) M U s x) =
        reductionTensorSection T (completedReductionProjection T d a) M U
          ((reductionCoefficientMap T d b a h).hom.app U s) x :=
    reductionModuleTransition_tensor T (completedReductionProjection T d b)
      (reductionCoefficientMap T d b a h) (completedReductionProjection T d a) hc
  refine ⟨τ, hτ, ?_⟩
  intro σ hσ
  apply NatTrans.ext
  funext M
  apply reductionRestrictedTensorHom_ext T (completedReductionProjection T d b) M
  intro U s x
  exact (hσ M U s x).trans (hτ M U s x).symm

/-- The canonical transition, specified uniquely on tensor generators.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionTransition (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    completedReductionLevel T d b ⟶ completedReductionLevel T d a :=
  (completedReductionTransition_exists T d b a h).exists.choose

attribute [local irreducible] completedReductionTransition

/-- The ordinary strict tower of a module sheaf, at all positive powers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionModuleTower (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : reductionModules T (completedReductionCoefficient T d)) :=
  Functor.ofOpSequence (X := fun n ↦ (completedReductionLevel T d n).obj M)
    (fun n ↦ (completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M)

/-- Naturality at consecutive indices supplies a compatible levelwise map of towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the transitions are natural transformations; their naturality square is exactly
this equality. Functor.ofOpSequence has the stipulated consecutive transition. -/
theorem completedReductionTowerMap_naturality (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {M N : reductionModules T (completedReductionCoefficient T d)} (f : M ⟶ N)
    (n : ℕ) :
    (completedReductionModuleTower T d M).map (homOfLE (Nat.le_succ n)).op ≫
        (completedReductionLevel T d n).map f =
      (completedReductionLevel T d (n + 1)).map f ≫
        (completedReductionModuleTower T d N).map (homOfLE (Nat.le_succ n)).op := by
  simpa only [completedReductionModuleTower, Functor.ofOpSequence_map_homOfLE_succ] using
    ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).naturality f).symm

/-- The ordinary tower construction on module morphisms.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionModuleTowerFunctor (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    reductionModules T (completedReductionCoefficient T d) ⥤
      reductionTowerCategory T (reductionModuleRing T (completedReductionCoefficient T d)) where
  obj M := completedReductionModuleTower T d M
  map f := NatTrans.ofOpSequence (fun n ↦ (completedReductionLevel T d n).map f)
    (completedReductionTowerMap_naturality T d f)
  map_id M := NatTrans.ext (funext (fun n ↦ (completedReductionLevel T d n.unop).map_id M))
  map_comp f g := NatTrans.ext (funext (fun n ↦ (completedReductionLevel T d n.unop).map_comp f g))

/-- The module-to-tower tensor construction is additive, levelwise.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: scalar extension and scalar restriction are additive. Equality of tower morphisms
is equality of their components, so their composite level functors prove additivity. -/
@[instance]
theorem completedReductionModuleTowerFunctor_additive (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionModuleTowerFunctor T d).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  have : (completedReductionLevel T d n.unop).Additive := by
    unfold completedReductionLevel reductionRestrict
    infer_instance
  exact (completedReductionLevel T d n.unop).map_add (f := f) (g := g)

/-- Apply the additive tower construction to terms and differentials. This gives actual
complexes in the tower category, not merely towers of derived objects.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionComplexTowerFunctor (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :=
  (completedReductionModuleTowerFunctor T d).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact functor from the homotopy category to the derived category of towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionHomotopyFunctor (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :=
  (completedReductionModuleTowerFunctor T d).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The universal property and representative computation of a reduction-tower pair.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def IsCompletedReductionTowerPair (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (LF : reductionDerivedCategory T (completedReductionCoefficient T d) ⥤
      DerivedCategory (reductionTowerCategory T
        (reductionModuleRing T (completedReductionCoefficient T d))))
    (ε : DerivedCategory.Qh ⋙ LF ⟶ completedReductionHomotopyFunctor T d) : Prop :=
  LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (reductionModules T (completedReductionCoefficient T d))
        (ComplexShape.up ℤ)) ∧
    (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
    ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
        (R := completedReductionCoefficient T d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))

/-- The reduction tower has its universal left derived pair, computed on every K-flat
complex; in particular the construction is functorial only after derived localization.
Source: blueprint order 1239; Stacks Tags 06XN, 06YS, 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the additive termwise tower construction preserves shifts and mapping cones.
Every representative has a K-flat resolution by lem-pc-kflat-resolution. By
lem-pur-derived-change-of-rings it sends quasi-isomorphisms between K-flat complexes to
levelwise quasi-isomorphisms. Tower cohomology is levelwise, hence these are tower
quasi-isomorphisms. Apply lem-pur-left-derived-from-kflat-class to obtain the universal
pair, its exactness and its counit isomorphisms at K-flat representatives. -/
theorem completedReductionTower_exists (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    ∃ (LF : reductionDerivedCategory T (completedReductionCoefficient T d) ⥤
        DerivedCategory (reductionTowerCategory T
          (reductionModuleRing T (completedReductionCoefficient T d))))
      (ε : DerivedCategory.Qh ⋙ LF ⟶ completedReductionHomotopyFunctor T d),
      IsCompletedReductionTowerPair T d LF ε := by
  let C := reductionModules T (completedReductionCoefficient T d)
  let D := reductionTowerCategory T (reductionModuleRing T (completedReductionCoefficient T d))
  let H := HomotopyCategory.quotient C (.up ℤ)
  let F := (completedReductionModuleTowerFunctor T d).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh
  let S : Set (HomotopyCategory C (.up ℤ)) :=
    {X | ∃ P : CochainComplex C ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := completedReductionCoefficient T d) P ∧
        H.obj P = X}
  have hres (X : HomotopyCategory C (.up ℤ)) :
      ∃ (X' : HomotopyCategory C (.up ℤ)) (s : X' ⟶ X),
        X' ∈ S ∧ HomotopyCategory.quasiIso C (.up ℤ) s := by
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedReductionCoefficient T d) G
    exact ⟨H.obj P, H.map s, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv (X Y : HomotopyCategory C (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ S) (hY : Y ∈ S) (hs : HomotopyCategory.quasiIso C (.up ℤ) s) :
      IsIso (F.map s) := by
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨Q, hQ, rfl⟩ := hY
    obtain ⟨a, rfl⟩ := H.map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hlevel (n : ℕ) : QuasiIso
        (((reductionTowerEvaluation T
          (reductionModuleRing T (completedReductionCoefficient T d)) n).mapHomologicalComplex
            (.up ℤ)).map ((completedReductionComplexTowerFunctor T d).map a)) := by
      let φ := completedReductionProjection T d n
      let V := SheafOfModules.toSheaf.{t + 1}
        (reductionModuleRing T (completedReductionCoefficient T d))
      have : PreservesFiniteLimits (reductionRestrict T φ ⋙ V) :=
        inferInstanceAs (PreservesFiniteLimits
          (SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T (reductionCoefficient T d n))))
      have : PreservesFiniteColimits (reductionRestrict T φ ⋙ V) :=
        inferInstanceAs (PreservesFiniteColimits
          (SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T (reductionCoefficient T d n))))
      have : PreservesFiniteLimits (reductionRestrict T φ) :=
        preservesFiniteLimits_of_reflects_of_preserves _ V
      have : PreservesFiniteColimits (reductionRestrict T φ) :=
        preservesFiniteColimits_of_reflects_of_preserves _ V
      have : QuasiIso (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).map a) :=
        reductionChange_quasiIso T φ a hP hQ ha
      exact inferInstanceAs (QuasiIso
        (((reductionRestrict T φ).mapHomologicalComplex (.up ℤ)).map
          (((reductionChange T φ).mapHomologicalComplex (.up ℤ)).map a)))
    have hEa : QuasiIso ((completedReductionComplexTowerFunctor T d).map a) :=
      (HomologicalComplex.quasiIso_iff_evaluation _).2 (fun n ↦ hlevel n.unop)
    dsimp only [F, completedReductionHomotopyFunctor, Functor.comp_map,
      Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso D (.up ℤ))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
  obtain ⟨_, LF, ε, hLF, htri, hcompute⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory D) F S hres hinv
  exact ⟨LF, ε, hLF, htri, fun P hP ↦ hcompute (H.obj P) ⟨P, hP, rfl⟩⟩

/-- K↦K_bullet is the canonical left derived functor, with its universal comparison.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionTower (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    reductionDerivedCategory T (completedReductionCoefficient T d) ⥤
      DerivedCategory (reductionTowerCategory T
        (reductionModuleRing T (completedReductionCoefficient T d))) :=
  (completedReductionTower_exists T d).choose

/-- The canonical quotient-coefficient object K_n, before restriction of scalars.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionObject (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (K : reductionDerivedCategory T (completedReductionCoefficient T d)) :=
  (reductionDerivedChange T (completedReductionProjection T d n)).obj K

/-- The completion projection followed by a quotient transition is the earlier projection.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: this is the limit cone's naturality equation for the arrow b to a in the
strict quotient coefficient system. -/
theorem completedReductionProjection_comp (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    completedReductionProjection T d b ≫ reductionCoefficientMap T d b a h =
      completedReductionProjection T d a := by
  exact limit.w (reductionCoefficientSystem T d) (homOfLE h).op

/-- The quotient normalization on a K-flat computation is the localization of balancing.
The same map is defined for any ordinary complex; K-flatness makes it compute derived
extension. The universal derived counits specify its comparison with K_b tensor^L P_a.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionNormalization (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ) :
    DerivedCategory.Q.obj ((reductionChangeComplex T (reductionCoefficientMap T d b a h)).obj
      ((reductionChangeComplex T (completedReductionProjection T d b)).obj P)) ≅
        DerivedCategory.Q.obj ((reductionChangeComplex T
          (completedReductionProjection T d a)).obj P) :=
  DerivedCategory.Q.mapIso (asIso (reductionBalance T (completedReductionProjection T d b)
    (reductionCoefficientMap T d b a h) (completedReductionProjection T d a)
    (completedReductionProjection_comp T d b a h) P))

/-- Balancing is natural on all representatives and therefore on K-flat computations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both composites send s tensor (r tensor x) to (s*ψ(r)) tensor f(x).
Local tensor generators give equality in each degree, and localization preserves it. -/
theorem reductionBalance_naturality (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    {P Q : CochainComplex (reductionModules T R) ℤ} (f : P ⟶ Q) :
    (reductionChangeComplex T ψ).map ((reductionChangeComplex T φ).map f) ≫
        reductionBalance T φ ψ χ h Q =
      reductionBalance T φ ψ χ h P ≫ (reductionChangeComplex T χ).map f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply reductionDoubleTensorHom_ext T φ ψ
  intro V x
  change ((reductionBalance T φ ψ χ h Q).f p).val.app V
      (((reductionChange T ψ).map ((reductionChange T φ).map (f.f p))).val.app V
        (reductionTensorSection T ψ _ V 1 (reductionTensorSection T φ _ V 1 x))) =
    ((reductionChange T χ).map (f.f p)).val.app V
      (((reductionBalance T φ ψ χ h P).f p).val.app V
        (reductionTensorSection T ψ _ V 1 (reductionTensorSection T φ _ V 1 x)))
  have h₁ := reductionChange_tensor T ψ ((reductionChange T φ).map (f.f p)) V 1
    (reductionTensorSection T φ _ V 1 x)
  have h₂ := reductionChange_tensor T φ (f.f p) V 1 x
  have h₃ := reductionBalance_tensor T φ ψ χ h Q p V 1 1 ((f.f p).val.app V x)
  have h₄ := reductionBalance_tensor T φ ψ χ h P p V 1 1 x
  have h₅ := reductionChange_tensor T χ (f.f p) V (1 * ψ.hom.app V 1) x
  exact (congrArg (fun z ↦ ((reductionBalance T φ ψ χ h Q).f p).val.app V z) h₁).trans
    ((congrArg (fun z ↦ ((reductionBalance T φ ψ χ h Q).f p).val.app V
      (reductionTensorSection T ψ _ V 1 z)) h₂).trans
        (h₃.trans (h₅.symm.trans
          (congrArg (fun z ↦ ((reductionChange T χ).map (f.f p)).val.app V z) h₄.symm))))

/-- The quotient normalization cocycle, with the actual associativity balancing map.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: on s tensor (r tensor (q tensor x)), both paths give
(s*ψ(r)*ψθ(q)) tensor x. Multiplicativity and associativity identify the coefficients.
Local tensor generation proves equality; localization preserves the same equality. -/
theorem reductionBalance_cocycle (T : Scheme.{t})
    {R S U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (reductionChangeComplex T θ).map (reductionBalance T φ ψ (φ ≫ ψ) rfl P) ≫
        reductionBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P =
      reductionBalance T ψ θ (ψ ≫ θ) rfl ((reductionChangeComplex T φ).obj P) ≫
        reductionBalance T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ) (Category.assoc φ ψ θ).symm P := by
  apply HomologicalComplex.hom_ext
  intro p
  apply reductionTripleTensorHom_ext T φ ψ θ
  intro W x
  change ((reductionBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P).f p).val.app W
      (((reductionChange T θ).map
        ((reductionBalance T φ ψ (φ ≫ ψ) rfl P).f p)).val.app W
          (reductionTensorSection T θ _ W 1
            (reductionTensorSection T ψ _ W 1 (reductionTensorSection T φ _ W 1 x)))) =
    ((reductionBalance T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ)
      (Category.assoc φ ψ θ).symm P).f p).val.app W
        (((reductionBalance T ψ θ (ψ ≫ θ) rfl
          ((reductionChangeComplex T φ).obj P)).f p).val.app W
            (reductionTensorSection T θ _ W 1
              (reductionTensorSection T ψ _ W 1 (reductionTensorSection T φ _ W 1 x))))
  have h₁ := reductionChange_tensor T θ
    ((reductionBalance T φ ψ (φ ≫ ψ) rfl P).f p) W 1
      (reductionTensorSection T ψ _ W 1 (reductionTensorSection T φ _ W 1 x))
  have h₂ := reductionBalance_tensor T φ ψ (φ ≫ ψ) rfl P p W 1 1 x
  have h₃ := reductionBalance_tensor T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P p W
    1 (1 * ψ.hom.app W 1) x
  have h₄ := reductionBalance_tensor T ψ θ (ψ ≫ θ) rfl
    ((reductionChangeComplex T φ).obj P) p W 1 1
      (reductionTensorSection T φ _ W 1 x)
  have h₅ := reductionBalance_tensor T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ)
    (Category.assoc φ ψ θ).symm P p W (1 * θ.hom.app W 1) 1 x
  have hcoeff : (1 : V.obj.obj W) * θ.hom.app W (1 * ψ.hom.app W 1) =
      (1 * θ.hom.app W 1) * (ψ ≫ θ).hom.app W 1 := by
    simp only [map_one, one_mul]
  exact (congrArg (fun z ↦
      ((reductionBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P).f p).val.app W z) h₁).trans
    ((congrArg (fun z ↦
      ((reductionBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P).f p).val.app W
        (reductionTensorSection T θ _ W 1 z)) h₂).trans
      (h₃.trans ((congrArg (fun z ↦ reductionTensorSection T ((φ ≫ ψ) ≫ θ)
        (P.X p) W z x) hcoeff).trans (h₅.symm.trans
          (congrArg (fun z ↦ ((reductionBalance T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ)
            (Category.assoc φ ψ θ).symm P).f p).val.app W z) h₄.symm)))))

/-- The consecutive transition is natural in strict towers.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the naturality square of a tower morphism at n+1 to n is the stated equation. -/
theorem completedTowerEvaluationStep_naturality (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ)
    {M N : reductionTowerCategory T B} (f : M ⟶ N) :
    f.app (op (n + 1)) ≫ N.map (homOfLE (Nat.le_succ n)).op =
      M.map (homOfLE (Nat.le_succ n)).op ≫ f.app (op n) := by
  exact (f.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The natural transformation between consecutive exact evaluation functors.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedTowerEvaluationStep (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) (n : ℕ) :
    reductionTowerEvaluation T B (n + 1) ⟶ reductionTowerEvaluation T B n where
  app M := M.map (homOfLE (Nat.le_succ n)).op
  naturality _ _ f := completedTowerEvaluationStep_naturality T B n f

/-- The evaluated derived objects, including arbitrary derived strict towers.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedTowerDerivedSequence (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d)))) (n : ℕ) :=
  (reductionTowerDerivedEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) n).obj M

/-- Derived transitions are the termwise transitions of exact evaluation, localized.
Source: blueprint order 1240 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedTowerDerivedStep (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d)))) (n : ℕ) :
    completedTowerDerivedSequence T d M (n + 1) ⟶ completedTowerDerivedSequence T d M n :=
  (Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _
    (reductionTowerDerivedEvaluation T
      (reductionModuleRing T (completedReductionCoefficient T d)) (n + 1))
    (reductionTowerDerivedEvaluation T
      (reductionModuleRing T (completedReductionCoefficient T d)) n)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
      (reductionModuleRing T (completedReductionCoefficient T d)) n) (ComplexShape.up ℤ))
        DerivedCategory.Q)).app M

universe u₁ v₁ w₁ u₂ v₂ w₂

/-- Read a universal homotopy counit on a complex using the canonical factorization maps.
Source: Stacks Tags 06XN and 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionComplexCounit
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ) :
    L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  L.map ((DerivedCategory.quotientCompQhIso B).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)


/-- The canonical scalar-extension comparison on any complex representative.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionScalarComplexCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ) :=
  reductionComplexCounit (reductionChange T φ) (reductionDerivedChange T φ)
    (reductionDerivedCounit T φ) P


/-- Restriction of coefficients preserves kernels, since it changes no underlying sections.
Source: blueprint order 1239, scalar restriction (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: kernels of module sheaves are computed sectionwise, with the restricted scalar
action. The same holds for finite products and the zero object, giving finite limits. -/
@[instance]
theorem reductionRestrict_preservesFiniteLimits (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteLimits (reductionRestrict T φ) := by
  let F := SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T R)
  have : PreservesFiniteLimits (reductionRestrict T φ ⋙ F) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T S)))
  exact preservesFiniteLimits_of_reflects_of_preserves (reductionRestrict T φ) F


/-- Restriction of coefficients preserves cokernels and finite direct sums.
Source: blueprint order 1239, scalar restriction (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: cokernels are the associated sheaves of sectionwise cokernels. Restriction changes
neither the underlying abelian presheaves nor their sheafification, and finite direct
sums are unchanged. This identifies the cokernel and finite-colimit universal properties. -/
@[instance]
theorem reductionRestrict_preservesFiniteColimits (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteColimits (reductionRestrict T φ) := by
  let F := SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T R)
  have : PreservesFiniteColimits (reductionRestrict T φ ⋙ F) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T S)))
  exact preservesFiniteColimits_of_reflects_of_preserves (reductionRestrict T φ) F


/-- Scalar restriction is additive on the unchanged underlying abelian sheaf.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance reductionRestrict_additive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionRestrict T φ).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).Additive

/-- The exact derived coefficient restriction, applied termwise before localization.
Source: blueprint order 1239; Stacks Tag 015F
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionDerivedRestrict (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (reductionRestrict T φ).mapDerivedCategory



universe e w z

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem restrictionLocalization
    {A : Type u} [Category.{e} A] {D : Type w} [Category.{z} D]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ D) [L.IsLocalization W] (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  have : V.HasRightCalculusOfFractions :=
    { exists_rightFraction := by
        intro X Y φ
        obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk φ.f.hom φ.s.hom φ.hs
          : W.LeftFraction X.obj Y.obj).exists_rightFraction
        obtain ⟨Z, r, hr⟩ := res ψ.X'
        refine ⟨MorphismProperty.RightFraction.mk
          (ObjectProperty.homMk (r ≫ ψ.s)) (W.comp_mem _ _ hr ψ.hs)
          (ObjectProperty.homMk (r ≫ ψ.f)), ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hψ).trans
          (Category.assoc _ _ _).symm)
      ext := by
        intro X Y Y' f g s hs h
        obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
          f.hom g.hom s.hom hs (congrArg (fun k ↦ k.hom) h)
        obtain ⟨T, r, hr⟩ := res Z
        refine ⟨T, ObjectProperty.homMk (r ≫ t), W.comp_mem _ _ hr ht, ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) heq).trans
          (Category.assoc _ _ _).symm) }
  let h : V.IsInvertedBy (P.ι ⋙ L) := fun _ _ s hs ↦ Localization.inverts L W s.hom hs
  let F := Localization.Construction.lift (P.ι ⋙ L) h
  have fac : V.Q ⋙ F = P.ι ⋙ L := Localization.Construction.fac _ _
  have fmap {X Y : P.FullSubcategory} (f : X ⟶ Y) :
      F.map (V.Q.map f) = L.map f.hom := by
    simpa using (eqToIso fac).hom.naturality f
  have hf : F.Full := by
    refine ⟨?_⟩
    intro X Y f
    let X₀ : P.FullSubcategory := X.as.obj
    let Y₀ : P.FullSubcategory := Y.as.obj
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W
      (show L.obj X₀.obj ⟶ L.obj Y₀.obj from f)
    obtain ⟨Z, r, hr⟩ := res φ.X'
    let ψ : V.RightFraction X₀ Y₀ := MorphismProperty.RightFraction.mk
      (ObjectProperty.homMk (r ≫ φ.s)) (W.comp_mem _ _ hr φ.hs)
      (ObjectProperty.homMk (r ≫ φ.f))
    refine ⟨ψ.map V.Q (Localization.inverts _ _), ?_⟩
    have : IsIso (L.map r) := Localization.inverts L W r hr
    have : IsIso (L.map φ.s) := Localization.inverts L W φ.s φ.hs
    have : IsIso (L.map (r ≫ φ.s)) :=
      Localization.inverts L W _ (W.comp_mem _ _ hr φ.hs)
    simp only [MorphismProperty.RightFraction.map, Functor.map_comp, Functor.map_inv, fmap]
    change inv (L.map (r ≫ φ.s)) ≫ L.map (r ≫ φ.f) = f
    rw [hφ]
    simp [MorphismProperty.RightFraction.map]
  have hfaith : F.Faithful := by
    refine ⟨?_⟩
    intro X Y f g heq
    let X₀ : P.FullSubcategory := X.as.obj
    let Y₀ : P.FullSubcategory := Y.as.obj
    obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction V.Q V
      (show V.Q.obj X₀ ⟶ V.Q.obj Y₀ from f)
    obtain ⟨ψ, rfl⟩ := Localization.exists_rightFraction V.Q V
      (show V.Q.obj X₀ ⟶ V.Q.obj Y₀ from g)
    let φ' : W.RightFraction X₀.obj Y₀.obj :=
      MorphismProperty.RightFraction.mk φ.s.hom φ.hs φ.f.hom
    let ψ' : W.RightFraction X₀.obj Y₀.obj :=
      MorphismProperty.RightFraction.mk ψ.s.hom ψ.hs ψ.f.hom
    have heq' : φ'.map L (Localization.inverts _ _) =
        ψ'.map L (Localization.inverts _ _) := by
      simpa only [MorphismProperty.RightFraction.map, Functor.map_comp, Functor.map_inv,
        fmap] using heq
    obtain ⟨Z, a, b, hs, hf, hw⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff L W φ' ψ').1 heq'
    obtain ⟨T, r, hr⟩ := res Z
    apply (MorphismProperty.RightFraction.map_eq_iff V.Q V φ ψ).2
    refine ⟨T, ObjectProperty.homMk (r ≫ a), ObjectProperty.homMk (r ≫ b), ?_, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans
        (Category.assoc _ _ _).symm)
    · apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hf).trans
        (Category.assoc _ _ _).symm)
    · change W ((r ≫ a) ≫ φ.s.hom)
      rw [Category.assoc]
      exact W.comp_mem _ _ hr hw
  have hess : F.EssSurj := by
    refine ⟨?_⟩
    intro X
    have := Localization.essSurj L W
    let Y := L.objPreimage X
    let e := L.objObjPreimageIso X
    obtain ⟨Z, r, hr⟩ := res Y
    exact ⟨V.Q.obj Z, ⟨Localization.isoOfHom L W r hr ≪≫ e⟩⟩
  have : F.IsEquivalence := { }
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V (eqToIso fac)


private theorem compareOnComplexes
    {C H : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category H]
    (P : CochainComplex C ℤ → Prop)
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (K' : CochainComplex C ℤ) (s : K' ⟶ K), P K' ∧ QuasiIso s)
    (F G : DerivedCategory C ⥤ H) (B : CochainComplex C ℤ ⥤ H)
    (α : DerivedCategory.Q ⋙ F ⟶ B) (β : DerivedCategory.Q ⋙ G ⟶ B)
    (hα : ∀ K, P K → IsIso (α.app K)) (hβ : ∀ K, P K → IsIso (β.app K)) :
    ∃! τ : F ⟶ G, IsIso τ ∧
      ∀ K, P K → τ.app (DerivedCategory.Q.obj K) ≫ β.app K = α.app K := by
  let S : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun X ↦ P X.as
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let L := S.ι ⋙ (DerivedCategory.Qh : HomotopyCategory C (.up ℤ) ⥤ _)
  have : L.IsLocalization (W.inverseImage S.ι) := by
    apply restrictionLocalization W DerivedCategory.Qh S
    intro X
    obtain ⟨K, s, hK, hs⟩ := hres X.as
    exact ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj K, hK⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let i := DerivedCategory.quotientCompQhIso C
  let e (K : CochainComplex C ℤ) (hK : P K) :
      F.obj (DerivedCategory.Q.obj K) ≅ G.obj (DerivedCategory.Q.obj K) :=
    let := hα K hK
    let := hβ K hK
    asIso (α.app K) ≪≫ (asIso (β.app K)).symm
  have he {K K' : CochainComplex C ℤ} (hK : P K) (hK' : P K') (f : K ⟶ K') :
      F.map (DerivedCategory.Q.map f) ≫ (e K' hK').hom =
        (e K hK).hom ≫ G.map (DerivedCategory.Q.map f) := by
    let := hβ K hK
    let := hβ K' hK'
    apply (cancel_mono (β.app K')).1
    dsimp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hb := β.naturality f
    dsimp only [Functor.comp_map] at hb
    rw [hb]
    simp only [IsIso.inv_hom_id_assoc]
    exact α.naturality f
  let c : L ⋙ F ≅ L ⋙ G := NatIso.ofComponents
    (fun X ↦ F.mapIso (i.app X.obj.as) ≪≫ e X.obj.as X.property ≪≫
      G.mapIso (i.app X.obj.as).symm) (by
        intro X Y f
        obtain ⟨K, hK⟩ := X
        obtain ⟨K', hK'⟩ := Y
        obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
        obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective K'
        change P K at hK
        change P K' at hK'
        obtain ⟨f₀, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f.hom
        dsimp only [L, Functor.comp_map, ObjectProperty.ι_map, Iso.trans_hom,
          Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv]
        change F.map (DerivedCategory.Qh.map f.hom) ≫
          (F.map (i.hom.app K') ≫ (e K' hK').hom ≫ G.map (i.inv.app K')) =
          (F.map (i.hom.app K) ≫ (e K hK).hom ≫ G.map (i.inv.app K)) ≫
            G.map (DerivedCategory.Qh.map f.hom)
        rw [← hf]
        have hn := i.hom.naturality f₀
        have hn' := i.inv.naturality f₀
        dsimp only [Functor.comp_map] at hn hn'
        rw [← F.map_comp_assoc, hn, F.map_comp, Category.assoc,
          ← Category.assoc (F.map (DerivedCategory.Q.map f₀)), he hK hK' f₀,
          Category.assoc, ← G.map_comp, hn', G.map_comp]
        simp only [Category.assoc])
  let E := Localization.fullyFaithfulWhiskeringLeft L (W.inverseImage S.ι) H
  let τ := E.preimageIso c
  have hτ (K : CochainComplex C ℤ) (hK : P K) :
      τ.hom.app (DerivedCategory.Q.obj K) ≫ β.app K = α.app K := by
    let X : S.FullSubcategory := ⟨(HomotopyCategory.quotient C (.up ℤ)).obj K, hK⟩
    have hc := congrArg (fun k ↦ k.app X) (E.map_preimage c.hom)
    have hn := τ.hom.naturality (i.hom.app K)
    change τ.hom.app (DerivedCategory.Qh.obj X.obj) =
      F.map (i.hom.app K) ≫ (e K hK).hom ≫ G.map (i.inv.app K) at hc
    change τ.hom.app ((HomotopyCategory.quotient C (.up ℤ) ⋙
      DerivedCategory.Qh).obj K) = _ at hc
    have hh : τ.hom.app (DerivedCategory.Q.obj K) = (e K hK).hom := by
      apply (cancel_epi (F.map (i.hom.app K))).1
      rw [hn, hc]
      simp only [Category.assoc, ← G.map_comp, i.inv_hom_id_app, G.map_id,
        Category.comp_id]
    rw [hh]
    let := hβ K hK
    simp [e]
  refine ⟨τ.hom, ⟨inferInstance, hτ⟩, ?_⟩
  intro σ hσ
  apply E.map_injective
  ext X
  let K := X.obj.as
  let := hβ K X.property
  have h := (cancel_mono (β.app K)).1 ((hσ.2 K X.property).trans (hτ K X.property).symm)
  have hn := σ.naturality (i.hom.app K)
  have hn' := τ.hom.naturality (i.hom.app K)
  apply (cancel_mono (G.map (i.hom.app K))).1
  exact hn.symm.trans ((congrArg (fun k ↦ F.map (i.hom.app K) ≫ k) h).trans hn')


private noncomputable def complexCounitNat
    {B : Type u} [Category.{e} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type z} [Category D] [Abelian D] [HasDerivedCategory D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := reductionComplexCounit E L ε P
  naturality P Q f := by
    unfold reductionComplexCounit
    have h := ε.naturality ((HomotopyCategory.quotient B (.up ℤ)).map f)
    have h₀ := (DerivedCategory.quotientCompQhIso B).inv.naturality f
    have h₁ := (E.mapHomotopyCategoryFactors (.up ℤ)).hom.naturality f
    have h₂ := (DerivedCategory.quotientCompQhIso D).hom.naturality
      ((E.mapHomologicalComplex (.up ℤ)).map f)
    dsimp only [Functor.comp_map] at h h₀ h₁ h₂ ⊢
    rw [← L.map_comp_assoc, h₀, L.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% h]
    rw [← DerivedCategory.Qh.map_comp_assoc, h₁, DerivedCategory.Qh.map_comp,
      Category.assoc, h₂]

private theorem complexCounitIso
    {B : Type u} [Category.{e} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type z} [Category D] [Abelian D] [HasDerivedCategory D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ)
    (h : IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P))) :
    IsIso ((complexCounitNat E L ε).app P) := by
  let := h
  change IsIso (reductionComplexCounit E L ε P)
  unfold reductionComplexCounit
  infer_instance


attribute [local irreducible] reductionComplexCounit

set_option synthInstance.maxSize 2048 in
open CategoryTheory.Limits MonoidalCategory in
private theorem reductionChange_kflat (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (reductionModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ p : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X p))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((reductionChangeComplex T φ).obj P) := by
  let e : (reductionChangeComplex T φ).obj P ≅ SheafOfModules.changeOfRingsComplex.{t + 1, t} φ P :=
    HomologicalComplex.Hom.isoOfComponents
      (V := reductionModules T S)
      (C₁ := (reductionChangeComplex T φ).obj P)
      (C₂ := SheafOfModules.changeOfRingsComplex.{t + 1, t} φ P)
      (fun i ↦ reductionTensorPresentation T φ (P.X i)) (by
        intro i j hij
        exact (reductionTensorPresentation_naturality T φ (P.d i j)).symm)
  have hP' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP
  have hraw :=
    (SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{t + 1, t} φ P hP' hflat).1
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  intro F hF i
  exact (hraw F hF i).of_iso
    (((curriedTensor _).map₂CochainComplex.obj F).mapIso e.symm)

/-- The quotient normalization is uniquely specified on every K-flat computation by
ordinary balancing and the universal scalar-extension counits.
Source: blueprint order 1239, normalization paragraph; Stacks Tag 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: scalar extension carries K-flat complexes to K-flat complexes, by testing against
acyclic target complexes and restricting scalars. On those representatives the two
successive derived changes are computed by successive ordinary changes. Balancing gives
an isomorphism to direct scalar extension. The local tensor formula proves naturality,
so these maps descend through quasi-isomorphisms between K-flat complexes. Every object
has such a representative. The universal counits give the displayed characterization
and show uniqueness, since their components are invertible on those representatives. -/
theorem completedReductionDerivedNormalization_exists (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    ∃! τ : reductionDerivedChange T (completedReductionProjection T d b) ⋙
        reductionDerivedChange T (reductionCoefficientMap T d b a h) ⟶
          reductionDerivedChange T (completedReductionProjection T d a),
      IsIso τ ∧
      ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
            (R := completedReductionCoefficient T d) P →
        τ.app (DerivedCategory.Q.obj P) ≫
            reductionScalarComplexCounit T (completedReductionProjection T d a) P =
          (reductionDerivedChange T (reductionCoefficientMap T d b a h)).map
              (reductionScalarComplexCounit T (completedReductionProjection T d b) P) ≫
            reductionScalarComplexCounit T (reductionCoefficientMap T d b a h)
              ((reductionChangeComplex T (completedReductionProjection T d b)).obj P) ≫
            DerivedCategory.Q.map
              (reductionBalance T (completedReductionProjection T d b)
                (reductionCoefficientMap T d b a h) (completedReductionProjection T d a)
                (completedReductionProjection_comp T d b a h) P) := by
  let φ := completedReductionProjection T d b
  let ψ := reductionCoefficientMap T d b a h
  let χ := completedReductionProjection T d a
  let hc := completedReductionProjection_comp T d b a h
  let E := reductionChangeComplex T φ
  let F := reductionChangeComplex T ψ
  let G := reductionChangeComplex T χ
  let LF := reductionDerivedChange T ψ
  let cφ := complexCounitNat (reductionChange T φ) (reductionDerivedChange T φ)
    (reductionDerivedCounit T φ)
  let cψ := complexCounitNat (reductionChange T ψ) LF (reductionDerivedCounit T ψ)
  let cχ := complexCounitNat (reductionChange T χ) (reductionDerivedChange T χ)
    (reductionDerivedCounit T χ)
  let α : DerivedCategory.Q ⋙ (reductionDerivedChange T φ ⋙ LF) ⟶
      G ⋙ DerivedCategory.Q :=
    { app := fun P ↦ LF.map (cφ.app P) ≫ cψ.app (E.obj P) ≫
        DerivedCategory.Q.map (reductionBalance T φ ψ χ hc P)
      naturality := by
        intro P Q f
        have hφ := cφ.naturality f
        have hψ := cψ.naturality (E.map f)
        have hb := congrArg DerivedCategory.Q.map (reductionBalance_naturality T φ ψ χ hc f)
        change (reductionDerivedChange T φ).map (DerivedCategory.Q.map f) ≫ cφ.app Q =
          cφ.app P ≫ DerivedCategory.Q.map (E.map f) at hφ
        change LF.map (DerivedCategory.Q.map (E.map f)) ≫ cψ.app (E.obj Q) =
          cψ.app (E.obj P) ≫ DerivedCategory.Q.map (F.map (E.map f)) at hψ
        simp only [Functor.map_comp] at hb
        change DerivedCategory.Q.map (F.map (E.map f)) ≫
            DerivedCategory.Q.map (reductionBalance T φ ψ χ hc Q) =
          DerivedCategory.Q.map (reductionBalance T φ ψ χ hc P) ≫
            DerivedCategory.Q.map (G.map f) at hb
        dsimp only [Functor.comp_map]
        rw [← LF.map_comp_assoc, hφ, LF.map_comp]
        simp only [Category.assoc]
        rw [reassoc_of% hψ, hb] }
  refine compareOnComplexes
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P) ?_ _ _ _ α cχ ?_ ?_
  · intro P
    obtain ⟨Q, s, hQ, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedReductionCoefficient T d) P
    exact ⟨Q, s, hQ, hs⟩
  · intro P hP
    obtain ⟨Q, s, hQ, hflat, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedReductionCoefficient T d) P
    have hQφ := reductionChange_kflat T φ Q hQ hflat
    have : IsIso (cφ.app Q) := complexCounitIso _ _ _ Q
      (reductionDerivedCounit_kflat T φ Q hQ)
    have : IsIso (cψ.app (E.obj Q)) := complexCounitIso _ _ _ (E.obj Q)
      (reductionDerivedCounit_kflat T ψ (E.obj Q) hQφ)
    have : IsIso (α.app Q) := by
      change IsIso (_ ≫ _ ≫ _)
      infer_instance
    have : QuasiIso s := hs
    have : QuasiIso (G.map s) :=
      reductionChange_quasiIso T χ s hQ hP hs
    have : IsIso (DerivedCategory.Q.map s) := by infer_instance
    have : IsIso ((G ⋙ DerivedCategory.Q).map s) := by
      change IsIso (DerivedCategory.Q.map (G.map s))
      infer_instance
    have hn := α.naturality s
    have : IsIso ((DerivedCategory.Q ⋙ (reductionDerivedChange T φ ⋙ LF)).map s) := by
      dsimp only [Functor.comp_map]
      infer_instance
    have : IsIso ((DerivedCategory.Q ⋙ (reductionDerivedChange T φ ⋙ LF)).map s ≫
        α.app P) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.Q ⋙ (reductionDerivedChange T φ ⋙ LF)).map s) (α.app P)
  · intro P hP
    exact complexCounitIso _ _ _ P
      (reductionDerivedCounit_kflat T χ P hP)

/-- The canonical normalization natural transformation, fixed by its K-flat formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionDerivedNormalization (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    reductionDerivedChange T (completedReductionProjection T d b) ⋙
      reductionDerivedChange T (reductionCoefficientMap T d b a h) ⟶
        reductionDerivedChange T (completedReductionProjection T d a) :=
  (completedReductionDerivedNormalization_exists T d b a h).choose

/-- The specified normalization is an isomorphism of functors, not just objectwise choices.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the defining unique-existence theorem asserts invertibility of the selected
natural transformation. Apply its existence specification to its chosen witness
and take the invertibility conjunct. -/
@[instance]
theorem completedReductionDerivedNormalization_isIso (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    IsIso (completedReductionDerivedNormalization T d b a h) := by
  exact (completedReductionDerivedNormalization_exists T d b a h).choose_spec.1.1

/-- The universal counit of the reduction tower, selected together with its left derived
functor and hence determining all resolution comparisons.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def coherenceReductionTowerCounit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    DerivedCategory.Qh ⋙ completedReductionTower T d ⟶
      completedReductionHomotopyFunctor T d :=
  (completedReductionTower_exists T d).choose_spec.choose

/-- The canonical reduction tower is universal, triangulated and computed on K-flat models.
Source: blueprint order 1239; Stacks Tags 06XN, 06YS and 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the total left derived functor has the universal right Kan extension counit.
The published existence theorem completedReductionTower_exists identifies this pair
with the exact homotopy functor on K-flat representatives. It therefore transports the
shift and triangle structure and makes the counit invertible on these representatives.
Uniqueness of derived pairs makes these the canonical resolution comparisons. -/
theorem completedReductionTower_properties (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionTower T d).IsLeftDerivedFunctor (coherenceReductionTowerCounit T d)
        (HomotopyCategory.quasiIso (reductionModules T (completedReductionCoefficient T d))
          (.up ℤ)) ∧
      (∃ (_ : (completedReductionTower T d).CommShift ℤ),
        (completedReductionTower T d).IsTriangulated) ∧
      ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := completedReductionCoefficient T d) P →
          IsIso ((coherenceReductionTowerCounit T d).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  exact (completedReductionTower_exists T d).choose_spec.choose_spec

/-- The tower counit on a complex, using canonical localization factorizations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionTowerComplexCounit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ) :
    (completedReductionTower T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedReductionComplexTowerFunctor T d).obj P) :=
  reductionComplexCounit (completedReductionModuleTowerFunctor T d)
    (completedReductionTower T d) (coherenceReductionTowerCounit T d) P

attribute [local irreducible] completedReductionTower

/-- Derived tower evaluation is canonically restriction of the quotient object K_n.
The equation fixes this comparison on every K-flat representative by the actual tower
and scalar-extension counits; no arbitrary identification is chosen.
Source: blueprint order 1239, evaluation paragraph; Stacks Tags 015F and 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: on a K-flat complex P both functors are computed by P tensor (P_n)_T with
its completion action. The two universal counits and exact evaluation identify that
same ordinary complex and all its maps. This gives the displayed comparison and its
naturality on K-flat representatives. Quasi-isomorphisms between these representatives
are inverted, so the comparison descends. Every object has a K-flat representative;
the displayed equality with invertible counits forces uniqueness and invertibility. -/
theorem completedReductionEvaluation_exists (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! τ : completedReductionTower T d ⋙
        reductionTowerDerivedEvaluation T
          (reductionModuleRing T (completedReductionCoefficient T d)) n ⟶
        reductionDerivedChange T (completedReductionProjection T d n) ⋙
          reductionDerivedRestrict T (completedReductionProjection T d n),
      IsIso τ ∧
      ∀ P : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
            (R := completedReductionCoefficient T d) P →
        τ.app (DerivedCategory.Q.obj P) ≫
            (reductionDerivedRestrict T (completedReductionProjection T d n)).map
              (reductionScalarComplexCounit T (completedReductionProjection T d n) P) ≫
            (reductionRestrict T
              (completedReductionProjection T d n)).mapDerivedCategoryFactors.hom.app
              ((reductionChangeComplex T (completedReductionProjection T d n)).obj P) =
          (reductionTowerDerivedEvaluation T
              (reductionModuleRing T (completedReductionCoefficient T d)) n).map
              (completedReductionTowerComplexCounit T d P) ≫
            (reductionTowerEvaluation T
              (reductionModuleRing T
                (completedReductionCoefficient T d)) n).mapDerivedCategoryFactors.hom.app
                  ((completedReductionComplexTowerFunctor T d).obj P) := by
  let φ := completedReductionProjection T d n
  let E := completedReductionModuleTowerFunctor T d
  let V := reductionTowerEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) n
  let R := reductionRestrict T φ
  let α : DerivedCategory.Q ⋙ (completedReductionTower T d ⋙ V.mapDerivedCategory) ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ V.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    { app := fun P ↦ V.mapDerivedCategory.map (completedReductionTowerComplexCounit T d P) ≫
        V.mapDerivedCategoryFactors.hom.app ((completedReductionComplexTowerFunctor T d).obj P)
      naturality := by
        intro P Q f
        have h := (complexCounitNat E (completedReductionTower T d)
          (coherenceReductionTowerCounit T d)).naturality f
        change (completedReductionTower T d).map (DerivedCategory.Q.map f) ≫
          completedReductionTowerComplexCounit T d Q =
          completedReductionTowerComplexCounit T d P ≫
            DerivedCategory.Q.map ((completedReductionComplexTowerFunctor T d).map f) at h
        dsimp only [Functor.comp_map]
        rw [← Category.assoc, ← V.mapDerivedCategory.map_comp, h,
          V.mapDerivedCategory.map_comp, Category.assoc,
          V.mapDerivedCategoryFactors_hom_naturality
            ((completedReductionComplexTowerFunctor T d).map f)]
        simp only [Category.assoc]
        rfl }
  let β : DerivedCategory.Q ⋙ (reductionDerivedChange T φ ⋙ R.mapDerivedCategory) ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ V.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    { app := fun P ↦ R.mapDerivedCategory.map (reductionScalarComplexCounit T φ P) ≫
        R.mapDerivedCategoryFactors.hom.app ((reductionChangeComplex T φ).obj P)
      naturality := by
        intro P Q f
        have h := (complexCounitNat (reductionChange T φ) (reductionDerivedChange T φ)
          (reductionDerivedCounit T φ)).naturality f
        change (reductionDerivedChange T φ).map (DerivedCategory.Q.map f) ≫
          reductionScalarComplexCounit T φ Q =
          reductionScalarComplexCounit T φ P ≫
            DerivedCategory.Q.map ((reductionChangeComplex T φ).map f) at h
        dsimp only [Functor.comp_map]
        rw [← Category.assoc, ← R.mapDerivedCategory.map_comp, h,
          R.mapDerivedCategory.map_comp, Category.assoc,
          R.mapDerivedCategoryFactors_hom_naturality ((reductionChangeComplex T φ).map f)]
        simp only [Category.assoc]
        rfl }
  refine compareOnComplexes
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P) ?_
    _ _ _ α β ?_ ?_
  · intro P
    obtain ⟨Q, s, hQ, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedReductionCoefficient T d) P
    exact ⟨Q, s, hQ, hs⟩
  · intro P hP
    have hc := (completedReductionTower_properties T d).2.2 P hP
    have : IsIso (completedReductionTowerComplexCounit T d P) :=
      complexCounitIso E (completedReductionTower T d) (coherenceReductionTowerCounit T d) P hc
    change IsIso (_ ≫ _)
    infer_instance
  · intro P hP
    have hc := reductionDerivedCounit_kflat T φ P hP
    have : IsIso (reductionScalarComplexCounit T φ P) :=
      complexCounitIso (reductionChange T φ) (reductionDerivedChange T φ)
        (reductionDerivedCounit T φ) P hc
    change IsIso (_ ≫ _)
    infer_instance


/-- The canonical evaluation comparison, fixed by its formula on K-flat representatives.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionEvaluation (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionTower T d ⋙ reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) n ⟶
      reductionDerivedChange T (completedReductionProjection T d n) ⋙
        reductionDerivedRestrict T (completedReductionProjection T d n) :=
  (completedReductionEvaluation_exists T d n).choose

/-- The canonical evaluation comparison is invertible as a natural transformation.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the defining unique-existence theorem asserts invertibility of the selected
natural transformation. Apply its existence specification to its chosen witness
and take the invertibility conjunct. -/
@[instance]
theorem completedReductionEvaluation_isIso (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    IsIso (completedReductionEvaluation T d n) := by
  exact (completedReductionEvaluation_exists T d n).choose_spec.1.1

/-- The quotient ring tower, indexed by the positive exponent n+1.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.ringTower {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (reductionQuotientMap d.ideal (n + 1) n (Nat.le_succ n)))

/-- The finite quotient ring sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.finiteRing {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) (n : ℕ) := reductionCoefficient T d n

/-- The actual completed coefficient ring sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.completedRing {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) := completedReductionCoefficient T d

/-- The specified coordinate of the completed coefficient sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.projection {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) (n : ℕ) :=
  completedReductionProjection T d n

/-- The ambient derived category of modules over the completed coefficient sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.derived {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) :=
  reductionDerivedCategory T (d.completedRing T)

/-- The strict tower category over the completed coefficient sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.towers {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) :=
  reductionTowerCategory T (reductionModuleRing T (d.completedRing T))

/-- Finite reduction retains the quotient coefficient action.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.reduction {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) (n : ℕ) :=
  reductionDerivedChange T (d.projection T n)

/-- Every finite quotient has exactly the finiteness certificate of the arithmetic datum.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance AdicCoefficientDatum.positiveQuotient_finite {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : Finite (A ⧸ d.ideal ^ (n + 1)) :=
  d.quotientFinite n

end AlgebraicGeometry.Scheme
