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
public import Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.Paper.AdicCoefficientDatum
import all Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Algebra.Homology.ScalarHomExtensionKFlat
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
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

universe t r u v uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory

attribute [local irreducible] Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors

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
def adicDatumRing := adicLisseCompletedRing T d.ideal

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

/-- The two presentations select the same ordinary tensor functor.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both are the ordinary functor in the same independent-coefficient witness,
with the same standard derived-category instances. -/
theorem adicDatumOrdinaryExtension_eq :
    completedConstantExtension T φ = reductionChange T φ := by
  rfl

/-- The homotopy localization with the same standard derived-category instance.
Source: Tag 05RU (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumQh (B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  @DerivedCategory.Qh (completedConstantModules T B) _ _ (HasDerivedCategory.standard _)

/-- The scalar derived pair with its specification stated in this coefficient presentation.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: take the universal pair in derivedChangeOfRingsIndependentCoefficients, using
its specified ordinary extension functor and the standard localizations. -/
theorem adicDatumScalarDerived_exists :
    ∃ (F : completedConstantDerived (completedConstantModules T R) ⥤
        completedConstantDerived (completedConstantModules T S))
      (ε : adicDatumQh T R ⋙ F ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ adicDatumQh T S),
      F.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (completedConstantModules T R) (.up ℤ)) ∧
        (∃ (_ : F.CommShift ℤ), F.IsTriangulated) ∧
        ∀ C : CochainComplex (completedConstantModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) C →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) := by
  change ∃ F, reductionDerivedSpec T φ F
  exact reductionDerivedExistence T φ

/-- The universal scalar pair as data, retaining its counit and K-flat computation.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicDatumScalarPair where
  functor : completedConstantDerived (completedConstantModules T R) ⥤
    completedConstantDerived (completedConstantModules T S)
  counit : adicDatumQh T R ⋙ functor ⟶
    (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ adicDatumQh T S
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (completedConstantModules T R) (.up ℤ))
  triangulated : ∃ (_ : functor.CommShift ℤ), functor.IsTriangulated
  computation (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C) :
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C))

/-- The specified universal pair, packaged once so its fields have a stable interface.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
@[irreducible]
def adicDatumScalarPair : AdicDatumScalarPair T φ where
  functor := (adicDatumScalarDerived_exists T φ).choose
  counit := (adicDatumScalarDerived_exists T φ).choose_spec.choose
  universal := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.1
  triangulated := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.2.1
  computation := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.2.2

/-- Derived extension from the existing universal K-flat derived pair.
Its comparison counit is retained below, so no unrelated functor is chosen.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  (adicDatumScalarPair T φ).functor

/-- The universal derived counit on homotopy complexes.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S :=
  (adicDatumScalarPair T φ).counit

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
  exact SheafOfModules.restrictScalars_exact_kflat ((adicLisseForget T).map φ)

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
abbrev adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((reductionChange T φ).obj M).val.obj U :=
  reductionTensorSection T φ M U s m

private theorem completedExtension_obj (M : completedConstantModules T R) :
    (reductionChange T φ).obj M = SheafOfModules.changeOfRings φ M :=
  reductionChange_obj_eq T φ M

private theorem completedExtension_map {M N : completedConstantModules T R} (a : M ⟶ N) :
    (reductionChange T φ).map a =
      eqToHom (completedExtension_obj T φ M) ≫ SheafOfModules.changeOfRingsHom φ M a ≫
        eqToHom (completedExtension_obj T φ N).symm :=
  reductionChange_map_eq T φ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumOrdinaryAdjunction_formula :
    ∃ a : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ (M : completedConstantModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = adicDatumTensorSection T φ M U 1 x := by
  refine ⟨(ordinaryAdjunction_exists T φ).choose, ?_⟩
  intro M U x
  exact reductionUnit_apply T φ M U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary tensor/restriction unit, fixed by its local pure-tensor formula.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the presheaf tensor unit m maps to 1 tensor m and then sheafifies.
Naturality on restrictions gives a sheaf map; tensor generation gives uniqueness. -/
theorem adicDatumOrdinaryUnit_exists (M : completedConstantModules T R) :
    ∃! u : M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((reductionChange T φ).obj M),
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
      ((adicLisseForget T).map φ)).obj ((reductionChange T φ).obj M) :=
  (adicDatumOrdinaryUnit_exists T φ M).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor/restriction adjunction normalized by the ordinary unit on every module.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the balanced map sends s tensor m to s times the proposed restricted map(m).
Sheafification extends it uniquely. Evaluation at 1 tensor m is its inverse;
the formulas commute with precomposition and postcomposition. -/
theorem adicDatumOrdinaryAdjunction_exists :
    ∃ adj : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ M : completedConstantModules T R, adj.unit.app M = adicDatumOrdinaryUnit T φ M := by
  obtain ⟨a, ha⟩ := adicDatumOrdinaryAdjunction_formula T φ
  refine ⟨a, ?_⟩
  intro M
  exact (adicDatumOrdinaryUnit_exists T φ M).unique (ha M)
    (adicDatumOrdinaryUnit_exists T φ M).exists.choose_spec

/-- The canonical ordinary scalar adjunction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryAdjunction : reductionChange T φ ⊣
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
        (f : ((reductionChange T φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj C ⟶ D),
        adj.homEquiv ((adicDatumQh T R).obj C) ((adicDatumQh T S).obj D)
          ((adicDatumExtensionCounit T φ).app C ≫ (adicDatumQh T S).map f) =
        (adicDatumQh T R).map
          ((adicDatumOrdinaryAdjunction T φ).mapHomotopyCategory (ComplexShape.up ℤ)
            |>.homEquiv C D f) ≫ (adicDatumRestrictionComparison T φ).inv.app D := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  let := (adicDatumRestriction_exact T φ).1
  let := (adicDatumRestriction_exact T φ).2
  apply SheafOfModules.sheafRingDerivedHomComparison φ
    (reductionChange T φ) (completedExtension_obj T φ)
    (completedExtension_map T φ) (adicDatumOrdinaryAdjunction T φ)
    (adicDatumExtension T φ) (adicDatumExtensionCounit T φ)
  exact (adicDatumScalarPair T φ).universal

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
        (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  (adicDatumExtension T φ).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
    (adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
    (adicDatumQh T S).map
      (((reductionChange T φ).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app C) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified comparison is invertible on every K-flat complex.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the universal derived counit is invertible on K-flat homotopy representatives
by derivedChangeOfRingsIndependentCoefficients. The two changes between homotopy
and complex localization above are isomorphisms, as is their image under a functor. -/
theorem adicDatumComplexCounit_isIso
    (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    IsIso (adicDatumComplexCounit T φ C) := by
  let := HasDerivedCategory.standard (completedConstantModules T R)
  let := HasDerivedCategory.standard (completedConstantModules T S)
  have : IsIso ((adicDatumExtensionCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) :=
    (adicDatumScalarPair T φ).computation C
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC)
  unfold adicDatumComplexCounit
  infer_instance

end ScalarChange

/-- The actual limit projection to the positive quotient level n+1.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumProjection (n : ℕ) :
    adicDatumRing T d ⟶ (adicLisseRingSystem T d.ideal).obj (op n) :=
  limit.π (adicLisseRingSystem T d.ideal) (op n)

/-- Compatibility of the completed-ring projections with every quotient transition.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: this is the naturality equation of the actual limit cone. -/
theorem adicDatumProjection_comp (m n : ℕᵒᵖ) (g : m ⟶ n) :
    adicDatumProjection T d m.unop ≫ (adicLisseRingSystem T d.ideal).map g =
      adicDatumProjection T d n.unop := by
  exact limit.w (adicLisseRingSystem T d.ideal) g

attribute [local irreducible] adicDatumRing adicLisseRingSystem

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
  reductionChange T (adicDatumProjection T d n) ⋙
    SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map (adicDatumProjection T d n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  exact scalarTransition_exists T (adicDatumProjection T d m.unop)
    (adicDatumProjection T d n.unop) ((adicLisseRingSystem T d.ideal).map g)
    (adicDatumProjection_comp T d m n g)


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

/-- Pass the resolving-class pair from homotopy representatives to complexes.
Source: Stacks Tags 05RU and 06XN (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: whisker the homotopy counit by the quotient functor and its two factorization
isomorphisms. Right Kan extension composes with localization; the factorization
isomorphisms preserve invertibility at each resolving representative. -/
private theorem derivedComplexPair_from_resolutions
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (E : C ⥤ D) [E.Additive] (P : CochainComplex C ℤ → Prop)
    (hres : ∀ X : CochainComplex C ℤ,
      ∃ (K : CochainComplex C ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hinv : ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L), P K → P L → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ (F : DerivedCategory C ⥤ DerivedCategory D)
      (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso C (.up ℤ)) ∧
        ∀ K : CochainComplex C ℤ, P K → IsIso (ε.app K) := by
  obtain ⟨F, ε, hF, _, hε⟩ := derivedPair_from_complex_resolutions E P hres hinv
  have := hF
  refine ⟨F, complexCounitNat E F ε, complexCounitNat_kan E F ε, ?_⟩
  intro K hK
  have := hε K hK
  rw [complexCounitNat_app]
  unfold reductionComplexCounit
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  let := HasDerivedCategory.standard (adicDatumModules T d)
  let := HasDerivedCategory.standard (adicDatumTowers T d)
  let E := (adicDatumOrdinaryTower T d).flip
  let P := fun C : CochainComplex (adicDatumModules T d) ℤ ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := adicDatumRing T d) C
  have hres (C : CochainComplex (adicDatumModules T d) ℤ) :
      ∃ (K : CochainComplex (adicDatumModules T d) ℤ) (f : K ⟶ C),
        P K ∧ QuasiIso f := by
    obtain ⟨K, f, hK, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := adicDatumRing T d) C
    exact ⟨K, f, hK, hf⟩
  have hinv {C D : CochainComplex (adicDatumModules T d) ℤ} (f : C ⟶ D)
      (hC : P C) (hD : P D) (hf : QuasiIso f) :
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    let φ := adicDatumProjection T d n.unop
    let U := SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)
    have := (adicDatumRestriction_exact T φ).1
    have := (adicDatumRestriction_exact T φ).2
    change QuasiIso (((reductionChange T φ).mapHomologicalComplex (.up ℤ) ⋙
      U.mapHomologicalComplex (.up ℤ)).map f)
    exact quasiIso_composite_map (reductionChange T φ) U f
      (reductionChange_quasiIso T φ f hC hD hf)
  obtain ⟨F, ε, hF, hε⟩ := derivedComplexPair_from_resolutions E P hres hinv
  exact ⟨F, ε, hF, fun C hC ↦
    hε C ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC)⟩


/-- Strict quotient tower in the derived category of towers; its universal counit
specifies the comparison between all K-flat computations.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumDerivedTower : adicDatumDerived T d ⥤ adicDatumTowerDerived T d :=
  (adicDatumTowerDerived_exists T d).choose

/-- Derived finite reduction at a model, with its quotient-coefficient action retained.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelReduction {K : adicDatumDerived T d} (M : AdicDatumModel T d K) (n : ℕ) :=
  (completedConstantQ _).obj
    (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
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
        (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
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
      (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
    ∃! e : (reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (reductionChange T ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (reductionChange T (φ ≫ ψ)).mapHomologicalComplex (ComplexShape.up ℤ),
      ∀ (C : CochainComplex (completedConstantModules T R) ℤ) (p : ℤ) (U : T.ProEtᵒᵖ)
        (s : B.obj.obj U) (r : S.obj.obj U) (x : (C.X p).val.obj U),
        ((e.hom.app C).f p).val.app U
          (adicDatumTensorSection T ψ ((reductionChange T φ).obj (C.X p)) U s
            (adicDatumTensorSection T φ (C.X p) U r x)) =
        adicDatumTensorSection T (φ ≫ ψ) (C.X p) U
          (s * ψ.hom.app U r) x := by
  let e : (reductionChange T φ).mapHomologicalComplex (.up ℤ) ⋙
      (reductionChange T ψ).mapHomologicalComplex (.up ℤ) ≅
      (reductionChange T (φ ≫ ψ)).mapHomologicalComplex (.up ℤ) :=
    NatIso.ofComponents
      (fun C ↦ asIso (reductionBalance T φ ψ (φ ≫ ψ) rfl C))
      (fun f ↦ reductionBalance_naturality T φ ψ (φ ≫ ψ) rfl f)
  refine ⟨e, ?_, ?_⟩
  · intro C p U s r x
    exact (reductionBalance_exists T φ ψ (φ ≫ ψ) rfl C).exists.choose_spec.2 p U s r x
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext C
    exact (reductionBalance_exists T φ ψ (φ ≫ ψ) rfl C).unique
      ⟨by infer_instance, he' C⟩
      (reductionBalance_exists T φ ψ (φ ≫ ψ) rfl C).exists.choose_spec


/-- The canonical balancing isomorphism of scalar-extension complexes.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumBalance :
    (reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (reductionChange T ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (reductionChange T (φ ≫ ψ)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (adicDatumBalance_exists T φ ψ).exists.choose

section GenericKFlatTransport

open SheafOfModules

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Transport K-flat preservation from an existing normalized scalar pair.
Source: Stacks Tag 0G7E (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the scalar pair exists by the universal derived scalar adjunction. Its
ordinary object and map formulas identify its extension functor with E by functor
extensionality. Apply scalarExtension_preservesKFlat to that functor. -/
private theorem adicDatumExtension_kflat_site
    {D : Type u} [Category.{v} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (ρ : R ⟶ S)
    (E : SheafOfModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    [E.Additive] (h : ∀ M, E.obj M = changeOfRings ρ M)
    (hm : ∀ {M N} (g : M ⟶ N), E.map g =
      eqToHom (h M) ≫ changeOfRingsHom ρ M g ≫ eqToHom (h N).symm)
    (K : CochainComplex (SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
  let := HasDerivedCategory.standard (scalarModules J R)
  let := HasDerivedCategory.standard (scalarModules J S)
  obtain ⟨s⟩ := scalarDerivedPair_exists ρ
  have hE : s.extension = E := by
    refine CategoryTheory.Functor.ext
      (fun M ↦ (s.extension_obj M).trans (h M).symm) ?_
    intro M N f
    rw [s.extension_map, hm]
    simp
  cases hE
  exact scalarExtension_preservesKFlat ρ s K hK

end GenericKFlatTransport

open SheafOfModules MonoidalCategory in
/-- K-flatness survives ordinary extension, with no flatness hypothesis on the ring map.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor an acyclic S-complex N with the extended R-complex. Balancing identifies
it with the tensor of the original K-flat complex and the restricted N. Restriction
is exact, so the latter is acyclic. This is exactly the K-flatness criterion over S. -/
theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1
  exact adicDatumExtension_kflat_site φ (reductionChange T φ)
    (completedExtension_obj T φ) (completedExtension_map T φ) C
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumBalance_eq
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumBalance T φ ψ).hom.app C = reductionBalance T φ ψ (φ ≫ ψ) rfl C := by
  exact (reductionBalance_exists T φ ψ (φ ≫ ψ) rfl C).unique
    ⟨by infer_instance, (adicDatumBalance_exists T φ ψ).exists.choose_spec C⟩
    (reductionBalance_exists T φ ψ (φ ≫ ψ) rfl C).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumBalance_transport
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (θ : R ⟶ B) (h : φ ≫ ψ = θ)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    (adicDatumBalance T φ ψ).hom.app C ≫
      eqToHom (congrArg (fun ξ ↦
        ((reductionChange T ξ).mapHomologicalComplex (.up ℤ)).obj C) h) =
      reductionBalance T φ ψ θ h C := by
  subst θ
  simpa only [eqToHom_refl, Category.comp_id] using adicDatumBalance_eq T φ ψ C

/-- The actual balancing normalizations satisfy the cocycle, including all quotients.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: on a triple tensor s tensor (r tensor (q tensor x)), both routes give
s times χ(r) times χ(ψ(q)) tensor x. Associativity and preservation of multiplication
identify these coefficients. These sections locally generate, so the chain maps agree.
The final equality transport only reassociates composition of the same ring maps. -/
theorem adicDatumBalance_cocycle
    {V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (χ : B ⟶ V)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    ((reductionChange T χ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((adicDatumBalance T φ ψ).hom.app C) ≫
      (adicDatumBalance T (φ ≫ ψ) χ).hom.app C =
    (adicDatumBalance T ψ χ).hom.app
        (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      (adicDatumBalance T φ (ψ ≫ χ)).hom.app C ≫
      eqToHom (congrArg (fun ξ ↦
        ((reductionChange T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
          (Category.assoc φ ψ χ).symm) := by
  rw [adicDatumBalance_transport T φ (ψ ≫ χ) ((φ ≫ ψ) ≫ χ)
    (Category.assoc φ ψ χ).symm C]
  rw [adicDatumBalance_eq, adicDatumBalance_eq, adicDatumBalance_eq]
  exact reductionBalance_cocycle T φ ψ χ C

end Balancing

/-- Finite-level normalization on the K-flat computation, with its quotient action.
The limit projection equation identifies the composite scalar map with π_a.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumModelNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (completedConstantQ _).obj
      (((reductionChange T
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((reductionChange T (adicDatumProjection T d b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex)) ≅ adicDatumModelReduction T d M a :=
  (completedConstantQ _).mapIso
    ((adicDatumBalance T (adicDatumProjection T d b)
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).app M.complex ≪≫
        eqToIso (congrArg (fun ξ ↦
          ((reductionChange T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.complex) (adicDatumProjection_comp T d (op b) (op a) (homOfLE h).op)))


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
    (((reductionChange T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)
    (adicDatumExtension_kflat T (adicDatumProjection T d b) M.complex M.isKFlat)
  asIso (adicDatumComplexCounit T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((reductionChange T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)) ≪≫ adicDatumModelNormalization T d M a b h

end AlgebraicGeometry.Scheme
