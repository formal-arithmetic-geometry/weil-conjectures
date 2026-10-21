/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.CompletedConstantFiniteComplexRealization
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Sheaf.Paper.CompletedConstantFiniteComplexRealization
import all Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients

/-!
# Completed adic coefficient datum and its strict reduction tower

Source: blueprint, proper base change, order 1239; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The site has object universe t+1 and morphism universe t. Coefficients and modules
are in t+1. The ambient ring is the actual inverse limit of the finite constant
quotient sheaves, not the constant sheaf associated to the original ring.

## Main definitions

* `ProEtaleAdicCoefficientDatum`: coefficient hypotheses.
* `adicDatumRing`: the actual completed coefficient sheaf.
* `adicDatumAdjunction`: normalized derived scalar adjunction.
* `adicDatumDerivedTower`: universal strict quotient tower.
* `adicDatumModelTower`: its explicit K-flat computation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The Noetherian, finitely generated, torsion, perfect and finite quotient hypotheses.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure ProEtaleAdicCoefficientDatum (A : Type (t + 1)) [CommRing A]
    extends CompleteCoefficientDatum A where
  quotientFinite : ∀ n : ℕ, Finite (A ⧸ ideal ^ (n + 1))

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

section FiniteCoefficientComparison
variable (P : Type (t + 1)) [CommRing P] [Finite P]
variable [TopologicalSpace P] [DiscreteTopology P]

/-- Canonical identification of the constant finite ring sheaf with the recorded
continuous-functions coefficient sheaf. The normalization fixes the constants map.
Source: order 1239; def-weil-pbc-proetale-modules
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: finiteCoefficientScalarMap_locallyBijective says constant scalars and continuous
functions on connected components have the same associated sheaf. The sheafification
universal property extends the constants map uniquely. Local bijectivity makes that
extension invertible, and the normalization uniquely determines the isomorphism. -/
theorem adicDatumFiniteCoefficientIso_exists :
    ∃! e : adicLisseRing T P ≅ AlgebraicGeometry.ProEtale.finiteCoefficientRingSheaf T P,
      adicLisseConstantUnit T P ≫ e.hom.hom =
        AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap T P := by
  let J := ProEt.topology T
  let R := ProEtale.finiteCoefficientRingSheaf T P
  let η := adicLisseConstantUnit T P
  let h := (J.W_of_isLocallyBijective η).homEquiv R.obj R.property
  let f : adicLisseRing T P ⟶ R := ⟨h.symm (ProEtale.finiteCoefficientScalarMap T P)⟩
  have hf : η ≫ f.hom = ProEtale.finiteCoefficientScalarMap T P := h.apply_symm_apply _
  have : Presheaf.IsLocallyInjective J (η ≫ f.hom) := by
    rw [hf]
    exact (ProEtale.finiteCoefficientScalarMap_locallyBijective T P).1
  have : Presheaf.IsLocallySurjective J (η ≫ f.hom) := by
    rw [hf]
    exact (ProEtale.finiteCoefficientScalarMap_locallyBijective T P).2
  have : Sheaf.IsLocallyInjective f :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J η f.hom
  have : Sheaf.IsLocallySurjective f :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J η f.hom
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp
    ⟨inferInstance, inferInstance⟩
  refine ⟨asIso f, hf, ?_⟩
  intro e he
  apply Iso.ext
  apply Sheaf.hom_ext
  exact h.injective (he.trans hf.symm)

/-- The normalized finite coefficient isomorphism; its quotient specializations
identify the inverse-limit ring used here with the node's completed coefficient sheaf.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumFiniteCoefficientIso :
    adicLisseRing T P ≅ AlgebraicGeometry.ProEtale.finiteCoefficientRingSheaf T P :=
  (adicDatumFiniteCoefficientIso_exists T P).exists.choose

/-- Transport of a finite coefficient homomorphism along the normalized isomorphisms
is exactly postcomposition on continuous functions, characterized before sheafification.
This supplies naturality for every quotient transition, hence for the limit projections.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both routes send a constant p to the constant φ(p). The sheafification
universal property identifies them. For any continuous section, its open level-set
cover makes it locally constant; this extends the equality to every section. -/
theorem adicDatumFiniteCoefficientIso_natural
    (B : Type (t + 1)) [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] (φ : P →+* B)
    (q : AlgebraicGeometry.ProEtale.finiteCoefficientPresheaf T P ⟶
      AlgebraicGeometry.ProEtale.finiteCoefficientPresheaf T B)
    (hq : ∀ (U : T.ProEtᵒᵖ)
      (s : C(ConnectedComponents U.unop.left, P))
      (c : ConnectedComponents U.unop.left),
      ContinuousMap.toFun (q.app U s) c = φ (s c)) :
    (adicDatumFiniteCoefficientIso T P).hom ≫
        (presheafToSheaf (ProEt.topology T) RingCat.{t + 1}).map q =
      (adicLisseForget T).map
        ((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom φ)) ≫ (adicDatumFiniteCoefficientIso T B).hom := by
  let J := ProEt.topology T
  let η := adicLisseConstantUnit T P
  let eP := adicDatumFiniteCoefficientIso T P
  let eB := adicDatumFiniteCoefficientIso T B
  have heP : η ≫ eP.hom.hom = ProEtale.finiteCoefficientScalarMap T P :=
    (adicDatumFiniteCoefficientIso_exists T P).exists.choose_spec
  have heB : adicLisseConstantUnit T B ≫ eB.hom.hom =
      ProEtale.finiteCoefficientScalarMap T B :=
    (adicDatumFiniteCoefficientIso_exists T B).exists.choose_spec
  have hη : η ≫ ((adicLisseForget T).map
        ((constantSheaf J CommRingCat.{t + 1}).map (CommRingCat.ofHom φ))).hom =
      (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫ adicLisseConstantUnit T B := by
    exact (congrArg (fun f ↦ Functor.whiskerRight f
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}))
        (toSheafify_naturality J
          ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ)))).symm
  have hc : ProEtale.finiteCoefficientConstants T P ≫ q =
      (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
        ProEtale.finiteCoefficientConstants T B := by
    ext U a
    apply ContinuousMap.ext
    intro c
    exact hq U (ContinuousMap.const _ a) c
  have hs : ProEtale.finiteCoefficientScalarMap T P ≫
        ((presheafToSheaf J RingCat.{t + 1}).map q).hom =
      (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫
        ProEtale.finiteCoefficientScalarMap T B := by
    dsimp only [ProEtale.finiteCoefficientScalarMap]
    rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc, hc, Category.assoc]
  apply Sheaf.hom_ext
  apply ((J.W_of_isLocallyBijective η).homEquiv _
    (ProEtale.finiteCoefficientRingSheaf T B).property).injective
  change η ≫ eP.hom.hom ≫ _ = η ≫ _ ≫ eB.hom.hom
  rw [← Category.assoc, heP, ← Category.assoc, hη, Category.assoc, heB]
  exact hs
end FiniteCoefficientComparison

/-- The completed coefficient sheaf, with its genuine compatible-family sections.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumRing := adicLisseCompletedRing T d.ideal

/-- Module sheaves over the completed coefficient sheaf.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumModules := completedConstantModules T (adicDatumRing T d)

/-- The ambient unbounded derived category, with the standard localization.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumDerived := completedConstantDerived (adicDatumModules T d)

/-- Finite biproducts are the usual products in the abelian module category.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance adicDatumFiniteBiproducts : HasFiniteBiproducts (adicDatumModules T d) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Strict inverse sequences of completed-coefficient module sheaves; index n is n+1.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumTowers := ℕᵒᵖ ⥤ adicDatumModules T d

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original ring acts by its compatible residues in every finite quotient.
The projection equations determine this map uniquely.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the constant quotient maps form a cone, since the quotient maps compose.
Use the limit lift; its projection identities prove existence and uniqueness. -/
theorem adicDatumScalar_exists :
    ∃! φ : adicLisseConstantRing T A ⟶ adicDatumRing T d,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
  let c : Cone (adicLisseRingSystem T d.ideal) :=
    { pt := adicLisseConstantRing T A
      π := NatTrans.ofOpSequence
        (fun n ↦ (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))) (by
            intro n
            simp only [Functor.const_obj_map, adicLisseRingSystem,
              Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp]
            congr 1) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · intro n
    exact limit.lift_π c (op n)
  · intro φ hφ
    apply limit.hom_ext
    intro n
    exact (hφ n.unop).trans (limit.lift_π c n).symm

/-- The unique compatible-residue coefficient map.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumScalar := (adicDatumScalar_exists T d).exists.choose

/-- The strict quotient tower as modules over the completed ring is uniquely specified
by its objects and the quotient formula on sections, as in CompletedConstantQuotientTower.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: restrict the regular module at each quotient along its limit projection.
The quotient sheaf map is linear because the limit projections commute with transitions.
Its underlying section map is the specified quotient. Identities and composition follow
from those of the ring diagram. The fields of the indicated structure fix all data. -/
theorem adicDatumQuotients_exists :
    Nonempty (CompletedConstantQuotientTower T d.ideal (adicDatumRing T d) (𝟙 _)) := by
  exact ⟨completedConstant_quotients T d.ideal (adicDatumRing T d) (𝟙 _)⟩

/-- The canonical quotient module tower, including its prescribed quotient transitions.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumQuotients : adicDatumTowers T d :=
  (Classical.choice (adicDatumQuotients_exists T d)).diagram

/-- One K-flat representative, without restricting the derived object.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicDatumModel (K : adicDatumDerived T d) where
  complex : CochainComplex (adicDatumModules T d) ℤ
  isKFlat : CochainComplex.IsAcyclicTensorKFlat (R := adicDatumRing T d) complex
  realization : (completedConstantQ _).obj complex ≅ K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The choice of model exists for every unbounded derived object.
Source: order 1239; Tag 06YS (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: choose a representative by essential surjectivity of localization, resolve it
by exists_isKFlatResolutionIndependentCoefficients and compose the localization of
that quasi-isomorphism with the representative isomorphism. -/
theorem adicDatumModel_exists (K : adicDatumDerived T d) :
    Nonempty (AdicDatumModel T d K) := by
  classical
  let Q := completedConstantQ (adicDatumModules T d)
  let G := Q.objPreimage K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := adicDatumRing T d) G
  have := hf
  have : IsIso (Q.map f) := by
    dsimp only [Q, completedConstantQ]
    infer_instance
  exact ⟨⟨P, (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP,
    asIso (Q.map f) ≪≫ Q.objObjPreimageIso K⟩⟩

section ScalarChange

variable {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)

/-- The homotopy localization with the same standard derived-category instance.
Source: Tag 05RU (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumQh (B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  @DerivedCategory.Qh (completedConstantModules T B) _ _ (HasDerivedCategory.standard _)

/-- Derived extension from the existing universal K-flat derived pair.
Its comparison counit is retained below, so no unrelated functor is chosen.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose

/-- The universal derived counit on homotopy complexes.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (completedConstantExtension T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S := by
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  unfold adicDatumQh adicDatumExtension completedConstantExtension
  exact ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose_spec.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction changes only the scalar action and is exact.
Source: order 1239; Tag 03D3 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the underlying abelian sheaves, kernels and sheafified cokernels are unchanged
by restriction. Their universal maps remain linear for the restricted action. -/
theorem adicDatumRestriction_exact :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)) ∧
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)) := by
  let U := SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)
  have : PreservesFiniteLimits
      (U ⋙ SheafOfModules.toSheaf ((adicLisseForget T).obj R)) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf ((adicLisseForget T).obj S)))
  have : PreservesFiniteColimits
      (U ⋙ SheafOfModules.toSheaf ((adicLisseForget T).obj R)) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf ((adicLisseForget T).obj S)))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf _),
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf _)⟩

/-- Exact derived restriction of scalars.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumRestriction :
    completedConstantDerived (completedConstantModules T S) ⥤
      completedConstantDerived (completedConstantModules T R) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI := (adicDatumRestriction_exact T φ).1
  letI := (adicDatumRestriction_exact T φ).2
  (SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)).mapDerivedCategory

/-- Local pure tensors in the actual sheafified extension, transported by the
specified object identification of the additive scalar-extension witness.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((completedConstantExtension T φ).obj M).val.obj U := by
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (φ.hom.app U).hom
  unfold completedConstantExtension
  exact (eqToHom
    ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
        φ).choose_spec.choose M).symm)
      |>.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{t + 1}
      (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
          (s ⊗ₜ[R.obj.obj U] m))

private theorem completedExtension_obj (M : completedConstantModules T R) :
    (completedConstantExtension T φ).obj M = SheafOfModules.changeOfRings φ M := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  exact (SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose M

private theorem completedExtension_map {M N : completedConstantModules T R} (a : M ⟶ N) :
    (completedConstantExtension T φ).map a =
      eqToHom (completedExtension_obj T φ M) ≫ SheafOfModules.changeOfRingsHom φ M a ≫
        eqToHom (completedExtension_obj T φ N).symm := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  exact (SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose_spec
    |>.choose a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumOrdinaryAdjunction_formula :
    ∃ a : completedConstantExtension T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ (M : completedConstantModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = adicDatumTensorSection T φ M U 1 x := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  let hobj := completedExtension_obj T φ
  obtain ⟨a, ha⟩ :=
    (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ).choose_spec.choose_spec
      (completedConstantExtension T φ) hobj
      (completedExtension_map T φ)
  refine ⟨a, ?_⟩
  intro M U x
  have h := ha M _ (eqToHom (hobj M).symm) U x
  have hid : eqToHom (hobj M) ≫ eqToHom (hobj M).symm = 𝟙 _ := by
    simp only [eqToHom_trans, eqToHom_refl]
  rw [hid, a.homEquiv_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary tensor/restriction unit, fixed by its local pure-tensor formula.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the presheaf tensor unit m maps to 1 tensor m and then sheafifies.
Naturality on restrictions gives a sheaf map; tensor generation gives uniqueness. -/
theorem adicDatumOrdinaryUnit_exists (M : completedConstantModules T R) :
    ∃! u : M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((completedConstantExtension T φ).obj M),
      ∀ (U : T.ProEtᵒᵖ) (m : M.val.obj U),
        u.val.app U m = adicDatumTensorSection T φ M U 1 m := by
  obtain ⟨a, ha⟩ := adicDatumOrdinaryAdjunction_formula T φ
  refine ⟨a.unit.app M, ha M, ?_⟩
  intro u hu
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (hu U x).trans (ha M U x).symm

/-- The ordinary unit, selected by the unique section formula.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryUnit (M : completedConstantModules T R) :
    M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((completedConstantExtension T φ).obj M) :=
  (adicDatumOrdinaryUnit_exists T φ M).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor/restriction adjunction normalized by the ordinary unit on every module.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the balanced map sends s tensor m to s times the proposed restricted map(m).
Sheafification extends it uniquely. Evaluation at 1 tensor m is its inverse;
the formulas commute with precomposition and postcomposition. -/
theorem adicDatumOrdinaryAdjunction_exists :
    ∃ adj : completedConstantExtension T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ M : completedConstantModules T R, adj.unit.app M = adicDatumOrdinaryUnit T φ M := by
  obtain ⟨a, ha⟩ := adicDatumOrdinaryAdjunction_formula T φ
  refine ⟨a, ?_⟩
  intro M
  exact (adicDatumOrdinaryUnit_exists T φ M).unique (ha M)
    (adicDatumOrdinaryUnit_exists T φ M).exists.choose_spec

/-- The canonical ordinary scalar adjunction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryAdjunction : completedConstantExtension T φ ⊣
    SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ) :=
  (adicDatumOrdinaryAdjunction_exists T φ).choose

/-- The exact restriction comparison, retaining its specified localization maps.
Source: Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumRestrictionComparison :
    adicDatumQh T S ⋙ adicDatumRestriction T φ ≅
      (SheafOfModules.restrictScalars.{t + 1}
        ((adicLisseForget T).map φ)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ adicDatumQh T R :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI := (adicDatumRestriction_exact T φ).1
  letI := (adicDatumRestriction_exact T φ).2
  (SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)).mapDerivedCategoryFactorsh

/-- The derived adjunction is fixed by compatibility with the ordinary normalized
adjunction and the universal derived counit, rather than by bare existence.
Source: order 1239; Tags 06YY and 09T5 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: derive the ordinary tensor/restriction adjunction, whose unit is 1 tensor m.
Restriction is exact. Identify its derived functor with exact restriction using its
localization comparison, and identify its left adjoint with the universal left-derived
pair already chosen above. The universal property fixes the displayed hom-equivalence
formula on homotopy representatives, which determines the adjunction after localization. -/
theorem adicDatumAdjunction_exists :
    ∃ adj : adicDatumExtension T φ ⊣ adicDatumRestriction T φ,
      ∀ (C : HomotopyCategory (completedConstantModules T R) (ComplexShape.up ℤ))
        (D : HomotopyCategory (completedConstantModules T S) (ComplexShape.up ℤ))
        (f : ((completedConstantExtension T φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj C ⟶ D),
        adj.homEquiv ((adicDatumQh T R).obj C) ((adicDatumQh T S).obj D)
          ((adicDatumExtensionCounit T φ).app C ≫ (adicDatumQh T S).map f) =
        (adicDatumQh T R).map
          ((adicDatumOrdinaryAdjunction T φ).mapHomotopyCategory (ComplexShape.up ℤ)
            |>.homEquiv C D f) ≫ (adicDatumRestrictionComparison T φ).inv.app D := by
  sorry

/-- The normalized derived scalar adjunction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumAdjunction : adicDatumExtension T φ ⊣ adicDatumRestriction T φ :=
  (adicDatumAdjunction_exists T φ).choose

/-- The universal scalar-extension comparison, now on complexes rather than homotopy
classes, using precisely the two localization comparison isomorphisms.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumComplexCounit (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumExtension T φ).obj ((completedConstantQ _).obj C) ⟶
      (completedConstantQ _).obj
        (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  (adicDatumExtension T φ).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
    (adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
    (adicDatumQh T S).map
      (((completedConstantExtension T φ).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app C) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)

/-- The specified comparison is invertible on every K-flat complex.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the universal derived counit is invertible on K-flat homotopy representatives
by derivedChangeOfRingsIndependentCoefficients. The two changes between homotopy
and complex localization above are isomorphisms, as is their image under a functor. -/
theorem adicDatumComplexCounit_isIso
    (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    IsIso (adicDatumComplexCounit T φ C) := by
  sorry

end ScalarChange

/-- The actual limit projection to the positive quotient level n+1.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumProjection (n : ℕ) :
    adicDatumRing T d ⟶ (adicLisseRingSystem T d.ideal).obj (op n) :=
  limit.π (adicLisseRingSystem T d.ideal) (op n)

attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The existing module-sheaf Abelian structure with a variable site.
Keeping the site variable retains the coefficient-universe proof arguments directly.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumSiteModulesAbelian {B : Type (t + 1)} [Category.{t} B]
    [EssentiallySmall.{t + 1} B] (J : GrothendieckTopology B)
    (R : Sheaf J RingCat.{t + 1}) : Abelian (SheafOfModules.{t + 1} R) := inferInstance

/-- The existing Abelian structure with the geometric coefficient-universe instance.
This fixed data interface prevents implicit instance choices from unfolding the
large sheafification construction in derived comparison types.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumModulesAbelian (U : Scheme.{t})
    (R : Sheaf (ProEt.topology U) CommRingCat.{t + 1}) :
    Abelian (proEtaleRingModules U R) :=
  adicDatumSiteModulesAbelian (ProEt.topology U)
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

/-- Finite reduction as a functor to the quotient-coefficient derived category.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumReduction (n : ℕ) :
    DerivedCategory (proEtaleRingModules T (adicDatumRing T d)) ⥤
      DerivedCategory (proEtaleRingModules T
        ((adicLisseRingSystem T d.ideal).obj (op n))) :=
  adicDatumExtension T (adicDatumProjection T d n)

/-- Derived tensor with the quotient, retaining the completed-ring action.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumReductionUnderlying (n : ℕ) :=
  adicDatumReduction T d n ⋙ adicDatumRestriction T (adicDatumProjection T d n)


/-- Ordinary reduction, retaining the A_T action.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryReduction (n : ℕ) : adicDatumModules T d ⥤ adicDatumModules T d :=
  completedConstantExtension T (adicDatumProjection T d n) ⋙
    SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map (adicDatumProjection T d n))

/-- Quotient transition on actual tensor sections, natural in the module.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the quotient map on the scalar factor respects the balancing relation because
its composite with the completion projection is the earlier projection. It respects
restrictions, addition and scalar action. Sheafification gives the map. Tensor
sections locally generate, proving uniqueness and naturality in the module. -/
theorem adicDatumOrdinaryTransition_exists (m n : ℕᵒᵖ) (g : m ⟶ n) :
    ∃! τ : adicDatumOrdinaryReduction T d m.unop ⟶ adicDatumOrdinaryReduction T d n.unop,
      ∀ (M : adicDatumModules T d) (U : T.ProEtᵒᵖ)
        (s : ((adicLisseRingSystem T d.ideal).obj m).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (adicDatumTensorSection T
          (adicDatumProjection T d m.unop) M U s x) =
        adicDatumTensorSection T (adicDatumProjection T d n.unop) M U
          (((adicLisseRingSystem T d.ideal).map g).hom.app U s) x := by
  sorry

/-- The specified quotient map on the scalar factor.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryTransition (m n : ℕᵒᵖ) (g : m ⟶ n) :
    adicDatumOrdinaryReduction T d m.unop ⟶ adicDatumOrdinaryReduction T d n.unop :=
  (adicDatumOrdinaryTransition_exists T d m n g).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Identity law for the quotient transitions.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the identity quotient fixes every scalar, hence every pure tensor. The unique
section formula identifies the sheaf map with the identity, naturally in M. -/
theorem adicDatumOrdinaryTransition_id (n : ℕᵒᵖ) :
    adicDatumOrdinaryTransition T d n n (𝟙 n) = 𝟙 _ := by
  apply (adicDatumOrdinaryTransition_exists T d n n (𝟙 n)).unique
    (adicDatumOrdinaryTransition_exists T d n n (𝟙 n)).exists.choose_spec
  intro M U s x
  rw [(adicLisseRingSystem T d.ideal).map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composition law for the quotient transitions.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: either composite sends s tensor x to q(s) tensor x. Composition of the ring
quotient diagram gives the same q, and uniqueness identifies the transformations. -/
theorem adicDatumOrdinaryTransition_comp (l m n : ℕᵒᵖ) (g : l ⟶ m) (h : m ⟶ n) :
    adicDatumOrdinaryTransition T d l n (g ≫ h) =
      adicDatumOrdinaryTransition T d l m g ≫ adicDatumOrdinaryTransition T d m n h := by
  apply (adicDatumOrdinaryTransition_exists T d l n (g ≫ h)).unique
    (adicDatumOrdinaryTransition_exists T d l n (g ≫ h)).exists.choose_spec
  intro M U s x
  change ((adicDatumOrdinaryTransition T d m n h).app M).val.app U
    (((adicDatumOrdinaryTransition T d l m g).app M).val.app U
      (adicDatumTensorSection T (adicDatumProjection T d l.unop) M U s x)) = _
  erw [(adicDatumOrdinaryTransition_exists T d l m g).exists.choose_spec M U s x,
    (adicDatumOrdinaryTransition_exists T d m n h).exists.choose_spec M U _ x,
    (adicLisseRingSystem T d.ideal).map_comp g h]
  rfl

/-- The strict diagram of ordinary reduction endofunctors, with genuine quotient maps.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryTower : ℕᵒᵖ ⥤ (adicDatumModules T d ⥤ adicDatumModules T d) where
  obj n := adicDatumOrdinaryReduction T d n.unop
  map {m n} g := adicDatumOrdinaryTransition T d m n g
  map_id n := adicDatumOrdinaryTransition_id T d n
  map_comp {l m n} g h := adicDatumOrdinaryTransition_comp T d l m n g h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The module-to-tower construction is additive.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: extension and restriction of scalars are additive. Addition of tower maps is
levelwise, so equality at every evaluation proves additivity of the whole functor. -/
theorem adicDatumOrdinaryTower_additive : (adicDatumOrdinaryTower T d).flip.Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (adicDatumOrdinaryReduction T d n.unop).map (f + g) =
    (adicDatumOrdinaryReduction T d n.unop).map f +
      (adicDatumOrdinaryReduction T d n.unop).map g
  have : (adicDatumOrdinaryReduction T d n.unop).Additive := by
    dsimp only [adicDatumOrdinaryReduction]
    infer_instance
  exact Functor.map_add _
attribute [instance] adicDatumOrdinaryTower_additive

/-- Actual strict tensor tower as a complex in Tow(Mod(A_T)).
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumTowerFunctor : CochainComplex (adicDatumModules T d) ℤ ⥤
    CochainComplex (adicDatumTowers T d) ℤ :=
  (adicDatumOrdinaryTower T d).flip.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ambient derived tower category uses the standard localization.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumTowerDerived := completedConstantDerived (adicDatumTowers T d)

/-- Universal derived strict tensor tower, computed on every K-flat representative.
Source: order 1239; Tag 06XN (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the strict construction commutes with shifts and the two finite summands of
cones. At every level, quasi-isomorphisms between K-flat complexes remain such after
extension, then restriction. Tower cohomology is levelwise, so it preserves these
quasi-isomorphisms in Tow. K-flat resolutions and the resolving-class theorem give
the universal left-derived pair, with invertible comparison on that class. -/
theorem adicDatumTowerDerived_exists :
    ∃ (F : adicDatumDerived T d ⥤ adicDatumTowerDerived T d)
      (ε : completedConstantQ _ ⋙ F ⟶
        adicDatumTowerFunctor T d ⋙ completedConstantQ _),
      F.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (adicDatumModules T d) (ComplexShape.up ℤ)) ∧
      ∀ C : CochainComplex (adicDatumModules T d) ℤ,
        CochainComplex.IsAcyclicTensorKFlat (R := adicDatumRing T d) C → IsIso (ε.app C) := by
  sorry

/-- Strict quotient tower in the derived category of towers; its universal counit
specifies the comparison between all K-flat computations.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumDerivedTower : adicDatumDerived T d ⥤ adicDatumTowerDerived T d :=
  (adicDatumTowerDerived_exists T d).choose

/-- Derived finite reduction at a model, with its quotient-coefficient action retained.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReduction {K : adicDatumDerived T d} (M : AdicDatumModel T d K) (n : ℕ) :=
  (completedConstantQ _).obj
    (((completedConstantExtension T (adicDatumProjection T d n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)

/-- The same strict model, with all transitions, in the one ambient derived category.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelTower {K : adicDatumDerived T d} (M : AdicDatumModel T d K) :
    ℕᵒᵖ ⥤ adicDatumDerived T d :=
  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
    ((adicDatumTowerFunctor T d).obj M.complex)) ⋙ completedConstantQ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Identity on every degree identifies evaluation of the strict tower complex
with successive termwise extension and restriction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both terms in every degree are the same restricted tensor module and both
differentials are obtained by applying extension then restriction to the original
differential. Identity components commute with these differentials and form the
required isomorphism; the component equation determines its hom, hence its inverse. -/
theorem adicDatumModelComplexRestrictionIso_exists {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    ∃! e : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
        ((adicDatumTowerFunctor T d).obj M.complex)).obj (op n) ≅
      ((SheafOfModules.restrictScalars.{t + 1}
        ((adicLisseForget T).map (adicDatumProjection T d n))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((completedConstantExtension T (adicDatumProjection T d n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex),
      ∀ i : ℤ, e.hom.f i = 𝟙 _ := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) ?_, ?_, ?_⟩
  · intro i j hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · intro i
    rfl
  · intro e he
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro i
    exact he i

/-- The degreewise identity comparison, fixed by its component equations.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelComplexRestrictionIso {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :=
  (adicDatumModelComplexRestrictionIso_exists T d M n).exists.choose

/-- Canonical exact scalar-restriction comparison for a finite quotient complex.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelRestriction {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumModelTower T d M).obj (op n) ≅
      (adicDatumRestriction T (adicDatumProjection T d n)).obj
        (adicDatumModelReduction T d M n) :=
  letI := HasDerivedCategory.standard (adicDatumModules T d)
  letI := HasDerivedCategory.standard
    (completedConstantModules T ((adicLisseRingSystem T d.ideal).obj (op n)))
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).1
  letI := (adicDatumRestriction_exact T (adicDatumProjection T d n)).2
  (completedConstantQ _).mapIso (adicDatumModelComplexRestrictionIso T d M n) ≪≫
    ((SheafOfModules.restrictScalars.{t + 1}
    ((adicLisseForget T).map (adicDatumProjection T d n))).mapDerivedCategoryFactors.app
      (((completedConstantExtension T (adicDatumProjection T d n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.complex)).symm

/-- Comparison from derived scalar extension of K to its specified K-flat computation.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReductionComparison {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumReduction T d n).obj K ⟶ adicDatumModelReduction T d M n :=
  (adicDatumReduction T d n).map M.realization.inv ≫
    adicDatumComplexCounit T (adicDatumProjection T d n) M.complex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison with a K-flat computation is invertible.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the model realization is an isomorphism and its functor image is invertible.
The remaining factor is the universal K-flat comparison just described. -/
theorem adicDatumModelReductionComparison_isIso {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    IsIso (adicDatumModelReductionComparison T d M n) := by
  have := adicDatumComplexCounit_isIso T (adicDatumProjection T d n) M.complex M.isKFlat
  unfold adicDatumModelReductionComparison
  infer_instance

/-- The canonical K-flat comparison as an isomorphism.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReductionIso {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumReduction T d n).obj K ≅ adicDatumModelReduction T d M n :=
  letI := adicDatumModelReductionComparison_isIso T d M n
  asIso (adicDatumModelReductionComparison T d M n)

section Balancing
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
variable (φ : R ⟶ S) (ψ : S ⟶ B)

/-- Ordinary scalar-extension associativity, with its balanced section formula.
This specifies the natural isomorphism uniquely, including all complex differentials.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: send s tensor (r tensor x) to (s times ψ(r)) tensor x; the inverse sends
s tensor x to s tensor (1 tensor x). The balancing relations prove both maps are
well defined and inverse. They commute with restrictions and differentials. A chain
map changes x only, giving naturality. Tensor sections locally generate, giving
uniqueness. For three scalar changes both composites multiply the same three scalars,
which proves the quotient cocycle, including identity quotient maps. -/
theorem adicDatumBalance_exists :
    ∃! e : (completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (completedConstantExtension T ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (completedConstantExtension T (φ ≫ ψ)).mapHomologicalComplex (ComplexShape.up ℤ),
      ∀ (C : CochainComplex (completedConstantModules T R) ℤ) (p : ℤ) (U : T.ProEtᵒᵖ)
        (s : B.obj.obj U) (r : S.obj.obj U) (x : (C.X p).val.obj U),
        ((e.hom.app C).f p).val.app U
          (adicDatumTensorSection T ψ ((completedConstantExtension T φ).obj (C.X p)) U s
            (adicDatumTensorSection T φ (C.X p) U r x)) =
        adicDatumTensorSection T (φ ≫ ψ) (C.X p) U
          (s * ψ.hom.app U r) x := by
  sorry

/-- The canonical balancing isomorphism of scalar-extension complexes.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumBalance :
    (completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (completedConstantExtension T ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (completedConstantExtension T (φ ≫ ψ)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (adicDatumBalance_exists T φ ψ).exists.choose

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open SheafOfModules MonoidalCategory in
/-- K-flatness survives ordinary extension, with no flatness hypothesis on the ring map.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor an acyclic S-complex N with the extended R-complex. Balancing identifies
it with the tensor of the original K-flat complex and the restricted N. Restriction
is exact, so the latter is acyclic. This is exactly the K-flatness criterion over S. -/
theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1
  let J := ProEt.topology T
  let K := C
  have hK := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC
  let E := completedConstantExtension T φ
  let h := completedExtension_obj T φ
  have hm {M N : completedConstantModules T R} (g : M ⟶ N) :
      E.map g = eqToHom (h M) ≫ changeOfRingsHom φ M g ≫ eqToHom (h N).symm :=
    completedExtension_map T φ g
  classical
  let := monoidalCategory R
  let := monoidalCategory S
  let α := (sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ
  let U := restrictScalars.{t + 1} α
  have hU := restrictScalars_exact_kflat α
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ toSheaf.{t + 1, t, t + 1, t + 1}
        ((sheafCompose J
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)).ReflectsIsomorphisms :=
      inferInstanceAs ((toSheaf.{t + 1, t, t + 1, t + 1}
        ((sheafCompose J
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp U (toSheaf.{t + 1, t, t + 1, t + 1} _)
  obtain ⟨e₀, he₀⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let e (M : SheafOfModules.{t + 1} ((sheafCompose J
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
      (N : SheafOfModules.{t + 1} ((sheafCompose J
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :=
    U.mapIso (((curriedTensor _).obj M).mapIso (eqToIso (h N))) ≪≫ e₀ M N
  have he {M M' : SheafOfModules.{t + 1} ((sheafCompose J
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)}
      {N N' : SheafOfModules.{t + 1} ((sheafCompose J
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)} (f : M ⟶ M') (g : N ⟶ N') :
      U.map (tensorHom f (E.map g)) ≫ (e M' N').hom =
        (e M N).hom ≫ tensorHom (U.map f) g := by
    have hs : tensorHom f (E.map g) ≫ whiskerLeft M' (eqToHom (h N')) =
        whiskerLeft M (eqToHom (h N)) ≫ tensorHom f (changeOfRingsHom φ N g) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp, hm, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (tensorHom f (E.map g)) ≫
        U.map (whiskerLeft M' (eqToHom (h N'))) ≫ (e₀ M' N').hom =
      U.map (whiskerLeft M (eqToHom (h N))) ≫ (e₀ M N).hom ≫ tensorHom (U.map f) g
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, he₀ f g]
  intro F hF
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
    ((E.mapHomologicalComplex (.up ℤ)).obj K)
  have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ toSheaf.{t + 1, t, t + 1, t + 1}
        ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape D (toSheaf.{t + 1, t, t + 1, t + 1}
        ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))
    have : ReflectsColimitsOfShape D (toSheaf.{t + 1, t, t + 1, t + 1}
        ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf.{t + 1, t, t + 1, t + 1} _)
  have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
  have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
  let f :
      (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj F)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ e (F.X i) (K.X j)) (by
          intro j j' hj
          change (e (F.X i) (K.X j)).hom ≫ whiskerLeft (U.obj (F.X i)) (K.d j j') =
            U.map (whiskerLeft (F.X i) (E.map (K.d j j'))) ≫
              (e (F.X i) (K.X j')).hom
          have hh := he (𝟙 (F.X i)) (K.d j j')
          change U.map (tensorHom (𝟙 (F.X i)) (E.map (K.d j j'))) ≫
              (e (F.X i) (K.X j')).hom =
            (e (F.X i) (K.X j)).hom ≫ tensorHom (U.map (𝟙 (F.X i))) (K.d j j') at hh
          rw [U.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e (F.X i) (K.X j)).hom ≫ whiskerRight (U.map (F.d i i')) (K.X j) =
          U.map (whiskerRight (F.d i i') (E.obj (K.X j))) ≫
            (e (F.X i') (K.X j)).hom
        simpa only [E.map_id, tensorHom_id]
          using (he (F.d i i') (𝟙 (K.X j))).symm)
  have h := hK ((U.mapHomologicalComplex (.up ℤ)).obj F)
    (acyclic_restrictScalars_kflat α F hF)
  apply acyclic_of_restrictScalars_kflat α
  intro i
  exact (h i).of_iso (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)).symm

/-- The actual balancing normalizations satisfy the cocycle, including all quotients.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: on a triple tensor s tensor (r tensor (q tensor x)), both routes give
s times χ(r) times χ(ψ(q)) tensor x. Associativity and preservation of multiplication
identify these coefficients. These sections locally generate, so the chain maps agree.
The final equality transport only reassociates composition of the same ring maps. -/
theorem adicDatumBalance_cocycle
    {V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (χ : B ⟶ V)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    ((completedConstantExtension T χ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((adicDatumBalance T φ ψ).hom.app C) ≫
      (adicDatumBalance T (φ ≫ ψ) χ).hom.app C =
    (adicDatumBalance T ψ χ).hom.app
        (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      (adicDatumBalance T φ (ψ ≫ χ)).hom.app C ≫
      eqToHom (congrArg (fun ξ ↦
        ((completedConstantExtension T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
          (Category.assoc φ ψ χ).symm) := by
  sorry
end Balancing

/-- Finite-level normalization on the K-flat computation, with its quotient action.
The limit projection equation identifies the composite scalar map with π_a.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (completedConstantQ _).obj
      (((completedConstantExtension T
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((completedConstantExtension T (adicDatumProjection T d b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex)) ≅ adicDatumModelReduction T d M a :=
  (completedConstantQ _).mapIso
    ((adicDatumBalance T (adicDatumProjection T d b)
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).app M.complex ≪≫
        eqToIso (congrArg (fun ξ ↦
          ((completedConstantExtension T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.complex) (limit.w (adicLisseRingSystem T d.ideal) (homOfLE h).op)))


/-- The quotient normalization in the actual derived quotient-coefficient categories.
It is the K-flat scalar-extension comparison followed by the specified balancing map.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelDerivedNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (adicDatumExtension T
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).obj
        (adicDatumModelReduction T d M b) ≅ adicDatumModelReduction T d M a :=
  letI := adicDatumComplexCounit_isIso T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((completedConstantExtension T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)
    (adicDatumExtension_kflat T (adicDatumProjection T d b) M.complex M.isKFlat)
  asIso (adicDatumComplexCounit T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((completedConstantExtension T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)) ≪≫ adicDatumModelNormalization T d M a b h

end AlgebraicGeometry.Scheme
