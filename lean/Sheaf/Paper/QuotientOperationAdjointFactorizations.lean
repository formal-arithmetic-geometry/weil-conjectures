/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.Paper.RingedTopoiTensorComparisonData
import all Sheaf.Paper.IntegralTensorReductionTowerComparison
import all Sheaf.Algebra.Homology.ScalarHomTensorCoherence
import all Sheaf.Paper.KFlatScalarComparisonNormalization
import all Sheaf.Algebra.Homology.ScalarHomExtensionKFlat
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact

/-! # Adjunct factorizations for actual tensor and pullback transitions

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 07A6;
sites-modules.tex, Tag 03EL
(blueprint: lem-pur-quotient-operation-adjoint-factorizations).

The inverse-image presentations include the specified ring isomorphisms. Scalar models
are the universal derived-change-of-rings pairs, not arbitrary extension functors.
All tensor and scalar comparisons below use their canonical localization counits.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.ScalarPullback
open scoped ChangeOfRings

namespace SheafOfModules.QuotientOperation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}}

/-- Flat-term K-flatness, using exactly the two recorded predicates.
Source: Stacks 0G7E (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def Good (P : CochainComplex (Modules A) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := A) P ∧
    ∀ i : ℤ, IsFlatOnSite (J := J) (R := A) (P.X i)

/-- The prescribed coproduct total tensor, with its signed cochain differential.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
abbrev total (P Q : CochainComplex (Modules A) ℤ) :=
  (WeilConjectures.coefficientTotalTensor.{u, u, u} J A).obj (P, Q)

/-- A homogeneous local generator of the actual direct-sum total tensor.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def totalPure (P Q : CochainComplex (Modules A) ℤ)
    (p q n : ℤ) (h : p + q = n) (W : Cᵒᵖ)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :
    ((total P Q).X n).val.obj W :=
  WeilConjectures.coefficientTensorGenerator.{u, u, u} J A P Q p q n h W x y

/-- Ordinary transition adjunct under the specified scalar adjunction.
Source: Stacks 07A6 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def ordinaryAdjunct {E : Modules A ⥤ Modules B} [E.Additive] {φ : A ⟶ B}
    (a : E ⊣ restriction φ) {P : CochainComplex (Modules A) ℤ}
    {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H) :
    (E.mapHomologicalComplex (.up ℤ)).obj P ⟶ H :=
  ((a.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm t

/-- The actual derived adjunct of the localized semilinear transition.
Source: Stacks 07A6 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def derivedAdjunct {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (d : m.T ⊣ (restriction φ).mapDerivedCategory)
    {P : CochainComplex (Modules A) ℤ} {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H) :
    m.T.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj H :=
  (d.homEquiv _ _).symm (DerivedCategory.Q.map t ≫
    (restriction φ).mapDerivedCategoryFactors.inv.app H)

/-- The canonical derived tensor in the recorded module category.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
abbrev derivedTensor (A : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules A)] :=
  @MonoidalCategory.tensor (DerivedCategory (Modules A)) _
    (CategoryTheory.RingedDerivedNative.monoidal.{u, u, u, w} J A)

/-- The canonical K-flat tensor comparison, rather than an unspecified isomorphism.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
abbrev tensorModel [HasDerivedCategory.{w} (Modules A)]
    (P Q : CochainComplex (Modules A) ℤ) (hP : Good P) :=
  CategoryTheory.RingedDerivedNative.tensorIso.{u, u, u, w} J A P Q (Or.inl hP.1)

/-- Scalar extension's canonical monoidal comparison on the prescribed representatives.
It is the localization of the balanced chain comparison, conjugated by the universal
scalar counits and the canonical tensor comparisons. This is the representative formula
that characterizes the strong monoidal comparison in Stacks 07A4.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def scalarTensorComparison {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (P Q : CochainComplex (Modules A) ℤ) (hP : Good P) (hQ : Good Q)
    (hEP : Good ((m.E.mapHomologicalComplex (.up ℤ)).obj P))
    (e : (m.E.mapHomologicalComplex (.up ℤ)).obj (total P Q) ≅
      total ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q)) :
    m.T.obj ((derivedTensor A).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ⟶
      (derivedTensor B).obj (m.T.obj (DerivedCategory.Q.obj P),
        m.T.obj (DerivedCategory.Q.obj Q)) :=
  m.T.map (tensorModel P Q hP).inv ≫ m.ε.app (total P Q) ≫
    DerivedCategory.Q.map e.hom ≫
    (tensorModel ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
      ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) hEP).hom ≫
    (derivedTensor B).map (Prod.mkHom
      (@inv _ _ _ _ (m.ε.app P) (m.computes P hP.1))
      (@inv _ _ _ _ (m.ε.app Q) (m.computes Q hQ.1)))

attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] ringedComparisonPure ScalarHomOrdinary.pure

private theorem fixed_proof_witness {P : Prop} {Q : P → Prop}
    (h : ∃ p, Q p) (p : P) : Q p := by
  obtain ⟨p', h⟩ := h
  exact h

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
private theorem ordinaryAdjunct_f {E : Modules A ⥤ Modules B} [E.Additive]
    {φ : A ⟶ B} (a : E ⊣ restriction φ)
    {P : CochainComplex (Modules A) ℤ} {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H) (n : ℤ) :
    (ordinaryAdjunct a t).f n = (a.homEquiv (P.X n) (H.X n)).symm (t.f n) := rfl

private theorem tensorModel_naturality [HasDerivedCategory.{w} (Modules A)]
    {P Q P' Q' : CochainComplex (Modules A) ℤ}
    (hP : Good P) (hP' : Good P') (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map
        ((WeilConjectures.coefficientTotalTensor.{u, u, u} J A).map (Prod.mkHom f g)) ≫
        (tensorModel P' Q' hP').hom =
      (tensorModel P Q hP).hom ≫
        (derivedTensor A).map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  unfold tensorModel derivedTensor
  exact CategoryTheory.RingedDerivedNative.tensorIso_naturality.{u, u, u, w} J A P Q P' Q'
    (Or.inl hP.1) (Or.inl hP'.1) f g

private theorem transpose_of_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {E : C ⥤ D} {U : D ⥤ C} (am : E ⊣ U)
    (A : C ⥤ C') (B : D ⥤ D')
    {F : C' ⥤ D'} {R : D' ⥤ C'} (ad : F ⊣ R)
    (ε : A ⋙ F ⟶ E ⋙ B) (ρ : B ⋙ R ≅ U ⋙ A)
    (P : C)
    (hu : ad.unit.app (A.obj P) ≫ R.map (ε.app P) ≫ ρ.hom.app (E.obj P) =
      A.map (am.unit.app P))
    (H : D) (g : P ⟶ U.obj H) :
    (ad.homEquiv (A.obj P) (B.obj H)).symm (A.map g ≫ ρ.inv.app H) =
      ε.app P ≫ B.map ((am.homEquiv P H).symm g) := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ad.homEquiv_unit]
  rw [R.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (A.obj P) ≫ R.map (ε.app P) =
      A.map (am.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact hu.trans (Category.comp_id _).symm
  rw [hu', Category.assoc]
  have hn := ρ.inv.naturality ((am.homEquiv P H).symm g)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← A.map_comp]
  have hg : am.unit.app P ≫ U.map ((am.homEquiv P H).symm g) = g := by
    exact (am.homEquiv_unit P H ((am.homEquiv P H).symm g)).symm.trans
      ((am.homEquiv P H).apply_symm_apply g)
  rw [hg]

private theorem cochain_transpose_of_unit
    {V W V' W' : Type*} [Category V] [Category W] [Category V'] [Category W']
    [Preadditive V] [Preadditive W] [Preadditive V'] [Preadditive W']
    {E : V ⥤ W} {U : W ⥤ V} (a : E ⊣ U) [E.Additive] [U.Additive]
    (I : V ⥤ V') (S : W ⥤ W') [I.Additive] [S.Additive]
    {F : V' ⥤ W'} {R : W' ⥤ V'} (b : F ⊣ R) [F.Additive] [R.Additive]
    (χ : I ⋙ F ≅ E ⋙ S) (ρ : U ⋙ I ≅ S ⋙ R)
    (hu : ∀ M, I.map (a.unit.app M) ≫ ρ.hom.app (E.obj M) =
      b.unit.app (I.obj M) ≫ R.map (χ.hom.app M))
    {P : CochainComplex V ℤ} {H : CochainComplex W ℤ}
    (t : P ⟶ (U.mapHomologicalComplex (.up ℤ)).obj H) :
    ((b.mapHomologicalComplex (.up ℤ)).homEquiv
      ((I.mapHomologicalComplex (.up ℤ)).obj P)
      ((S.mapHomologicalComplex (.up ℤ)).obj H)).symm
        ((I.mapHomologicalComplex (.up ℤ)).map t ≫
          (NatIso.mapHomologicalComplex ρ (.up ℤ)).hom.app H) =
      (NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app P ≫
        (S.mapHomologicalComplex (.up ℤ)).map
          (((a.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm t) := by
  apply transpose_of_unit (a.mapHomologicalComplex (.up ℤ))
    (I.mapHomologicalComplex (.up ℤ)) (S.mapHomologicalComplex (.up ℤ))
    (b.mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex χ (.up ℤ)).hom
    (NatIso.mapHomologicalComplex ρ.symm (.up ℤ)) P ?_ H t
  apply HomologicalComplex.Hom.ext
  funext n
  change b.unit.app (I.obj (P.X n)) ≫ R.map (χ.hom.app (P.X n)) ≫
    ρ.inv.app (E.obj (P.X n)) = I.map (a.unit.app (P.X n))
  rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem derivedAdjunct_eq {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory)
    (hn : AdjunctionNormalized m a d)
    {P : CochainComplex (Modules A) ℤ} (hP : Good P)
    {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H) :
    derivedAdjunct m d t = m.ε.app P ≫ DerivedCategory.Q.map (ordinaryAdjunct a t) := by
  exact transpose_of_unit (a.mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q d m.ε (restriction φ).mapDerivedCategoryFactors
    P (hn.2 P hP.1 hP.2) H t

private theorem isIso_pair {V W : Type*} [Category V] [Category W]
    {X Y : V} {Z T : W} (f : X ⟶ Y) (g : Z ⟶ T) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) := ((asIso f).prod (asIso g)).isIso_hom

private theorem derivedAdjunct_isIso {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory)
    (hn : AdjunctionNormalized m a d)
    {P : CochainComplex (Modules A) ℤ} (hP : Good P)
    {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H)
    [IsIso (ordinaryAdjunct a t)] : IsIso (derivedAdjunct m d t) := by
  rw [derivedAdjunct_eq m a d hn hP t]
  have := m.computes P hP.1
  infer_instance

private theorem scalarTensorComparison_isIso {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (P Q : CochainComplex (Modules A) ℤ) (hP : Good P) (hQ : Good Q)
    (hEP : Good ((m.E.mapHomologicalComplex (.up ℤ)).obj P))
    (hT : Good (total P Q))
    (e : (m.E.mapHomologicalComplex (.up ℤ)).obj (total P Q) ≅
      total ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q)) :
    IsIso (scalarTensorComparison m P Q hP hQ hEP e) := by
  have := m.computes P hP.1
  have := m.computes Q hQ.1
  have := m.computes (total P Q) hT.1
  have := isIso_pair (inv (m.ε.app P)) (inv (m.ε.app Q))
  dsimp only [scalarTensorComparison]
  infer_instance

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors

private theorem good_total [HasDerivedCategory.{w} (Modules A)]
    {P Q : CochainComplex (Modules A) ℤ} (hP : Good P) (hQ : Good Q) :
    Good (total P Q) := by
  have h := KFlatTotalTensorModel.kFlat_total_tensor_model A P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

private theorem good_scalar {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    {P : CochainComplex (Modules A) ℤ} (hP : Good P) :
    Good ((m.E.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine ⟨kflatOfScalarExtensionIdentification φ m.E m.obj_eq m.map_eq P hP.1, ?_⟩
  intro i
  exact flatOnSite_of_iso B
    (eqToIso (m.obj_eq (P.X i)) ≪≫
      ScalarHomOrdinary.extensionIso φ (P.X i)).symm
    (isFlat_changeOfRingsOfUniverses φ (P.X i) (hP.2 i))

private theorem adjunct_on_unit {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory)
    (hn : AdjunctionNormalized m a d)
    {P : CochainComplex (Modules A) ℤ} {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H)
    (n : ℤ) (W : Cᵒᵖ) (x : (P.X n).val.obj W) :
    ((ordinaryAdjunct a t).f n).val.app W (pure m (P.X n) W 1 x) =
      (t.f n).val.app W x := by
  rw [ordinaryAdjunct_f]
  have hh := a.homEquiv_unit (P.X n) (H.X n)
    ((a.homEquiv (P.X n) (H.X n)).symm (t.f n))
  have ht : a.unit.app (P.X n) ≫ (restriction φ).map
      ((a.homEquiv (P.X n) (H.X n)).symm (t.f n)) = t.f n :=
    hh.symm.trans ((a.homEquiv (P.X n) (H.X n)).apply_symm_apply (t.f n))
  have he := congrArg (fun f ↦ f.val.app W x) ht
  change ((a.homEquiv (P.X n) (H.X n)).symm (t.f n)).val.app W
    ((a.unit.app (P.X n)).val.app W x) = _ at he
  exact (congrArg (((a.homEquiv (P.X n) (H.X n)).symm (t.f n)).val.app W)
    (hn.1 _ W x).symm).trans he

private theorem total_map_pure {P Q P' Q' : CochainComplex (Modules A) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) (W : Cᵒᵖ)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :
    (((WeilConjectures.coefficientTotalTensor.{u, u, u} J A).map (Prod.mkHom f g)).f n).val.app W
        (totalPure P Q p q n h W x y) =
      totalPure P' Q' p q n h W ((f.f p).val.app W x) ((g.f q).val.app W y) := by
  unfold totalPure
  exact CategoryTheory.ScalarHomTensor.tensor_generator_map f g p q n h W x y

-- Control elaboration of the degreewise comparison.
private theorem total_comparison {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (P Q : CochainComplex (Modules A) ℤ) :
    ∃ ε : (m.E.mapHomologicalComplex (.up ℤ)).obj (total P Q) ≅
        total ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Q),
      ∀ p q n hpq W x y,
        (ε.hom.f n).val.app W (pure m ((total P Q).X n) W 1
          (totalPure P Q p q n hpq W x y)) =
        totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W
            (pure m (P.X p) W 1 x) (pure m (Q.X q) W 1 y) := by
  obtain ⟨b, hb⟩ := WeilConjectures.scalarTensorTotal.{u, u, u} φ m.E m.obj_eq m.map_eq
  refine ⟨b.app (P, Q), ?_⟩
  intro p q n hpq W x y
  unfold totalPure ScalarPullback.pure
  exact hb P Q p q n hpq W x y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem totalPure_smul_left (P Q : CochainComplex (Modules A) ℤ)
    (p q n : ℤ) (h : p + q = n) (W : Cᵒᵖ) (b : A.obj.obj W)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :
    totalPure P Q p q n h W (b • x) y = b • totalPure P Q p q n h W x y := by
  simp only [totalPure, WeilConjectures.coefficientTensorGenerator,
    ← TensorProduct.smul_tmul', map_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem totalPure_smul_right (P Q : CochainComplex (Modules A) ℤ)
    (p q n : ℤ) (h : p + q = n) (W : Cᵒᵖ) (b : A.obj.obj W)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :
    totalPure P Q p q n h W x (b • y) = b • totalPure P Q p q n h W x y := by
  simp only [totalPure, WeilConjectures.coefficientTensorGenerator,
    TensorProduct.tmul_smul, map_smul]

private theorem pull_conjugation
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (Q : C ⥤ D) (I : C ⥤ E) (S : D ⥤ F) (Q' : E ⥤ F)
    (r : Q ⋙ S ≅ I ⋙ Q') {P H : C} {X : F}
    (e : X ⟶ S.obj (Q.obj P)) (f : P ⟶ H) :
    e ≫ r.hom.app P ≫ Q'.map (I.map f) =
      e ≫ S.map (Q.map f) ≫ r.hom.app H := by
  have h := r.hom.naturality f
  exact congrArg (e ≫ ·) h.symm

private theorem tensor_conjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (T : D × D ⥤ D)
    {K X U V : C} {Z Y EU EV UN VN KN : D}
    (τ : K ≅ X) (εK : F.obj K ⟶ Z)
    (εU : F.obj U ⟶ EU) (εV : F.obj V ⟶ EV) [IsIso εU] [IsIso εV]
    (e : Z ≅ Y) (s : Y ≅ T.obj (EU, EV)) (t : KN ≅ T.obj (UN, VN))
    (qU : EU ⟶ UN) (qV : EV ⟶ VN) (qK : Y ⟶ KN)
    (h : qK ≫ t.hom = s.hom ≫ T.map (Prod.mkHom qU qV)) :
    εK ≫ e.hom ≫ qK =
      F.map τ.hom ≫
        (F.map τ.inv ≫ εK ≫ e.hom ≫ s.hom ≫
          T.map (Prod.mkHom (inv εU) (inv εV))) ≫
        T.map (Prod.mkHom (εU ≫ qU) (εV ≫ qV)) ≫ t.inv := by
  have hp : Prod.mkHom (inv εU) (inv εV) ≫
      Prod.mkHom (εU ≫ qU) (εV ≫ qV) = Prod.mkHom qU qV := by
    apply Prod.hom_ext
    · exact IsIso.inv_hom_id_assoc εU qU
    · exact IsIso.inv_hom_id_assoc εV qV
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, τ.hom_inv_id, F.map_id, Category.id_comp]
  rw [← T.map_comp_assoc, hp]
  rw [← Category.assoc _ _ t.inv, ← h]
  simp only [Category.assoc, t.hom_inv_id, Category.comp_id]

private theorem balanced_comparison
    {S : Type*} [CommRing S] {X U V Z : Type*}
    [AddCommGroup X] [Module S X] [AddCommGroup U] [Module S U]
    [AddCommGroup V] [Module S V] [AddCommGroup Z] [Module S Z]
    {M N : Type*} (f : X →ₗ[S] Z) (g : Z →ₗ[S] X)
    (hfg : ∀ x, g (f x) = x)
    (s : S → M → N → X) (u : S → M → U) (v : S → N → V)
    (t : U → V → Z)
    (hs : ∀ (b : S) (x : M) (y : N), s b x y = b • s 1 x y)
    (hu : ∀ (b : S) (x : M), u b x = b • u 1 x) (hv : ∀ (b : S) (y : N), v b y = b • v 1 y)
    (htl : ∀ (b : S) (x : U) (y : V), t (b • x) y = b • t x y)
    (htr : ∀ (b : S) (x : U) (y : V), t x (b • y) = b • t x y)
    (he : ∀ x y, f (s 1 x y) = t (u 1 x) (v 1 y)) :
    (∀ b x y, f (s b x y) = t (u b x) (v 1 y)) ∧
      (∀ b c x y, g (t (u b x) (v c y)) = s (b * c) x y) := by
  have hh (b : S) (x : M) (y : N) :
      f (s b x y) = t (u b x) (v 1 y) := by
    rw [hs b x y, map_smul, he x y, hu b x, htl]
  refine ⟨hh, ?_⟩
  intro b c x y
  have ht : t (u b x) (v c y) = (b * c) • t (u 1 x) (v 1 y) := by
    rw [hu b x, hv c y, htl, htr, mul_smul]
  have he' : f (s (b * c) x y) = (b * c) • t (u 1 x) (v 1 y) := by
    rw [hs (b * c) x y, map_smul, he]
  rw [ht, ← he', hfg]

attribute [local irreducible] totalPure

set_option maxHeartbeats 20000 in
-- Use the bilinear API without unfolding the scalar sheafification.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_full {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (P Q : CochainComplex (Modules A) ℤ)
    (ε : (m.E.mapHomologicalComplex (.up ℤ)).obj (total P Q) ≅
      total ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q))
    (he : ∀ p q n hpq W x y,
      (ε.hom.f n).val.app W (pure m ((total P Q).X n) W 1
        (totalPure P Q p q n hpq W x y)) =
      totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W
          (pure m (P.X p) W 1 x) (pure m (Q.X q) W 1 y)) :
    (∀ p q n hpq W x y b,
      (ε.hom.f n).val.app W (pure m ((total P Q).X n) W b
        (totalPure P Q p q n hpq W x y)) =
      totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W
          (pure m (P.X p) W b x) (pure m (Q.X q) W 1 y)) ∧
    (∀ p q n hpq W x y b c,
      (ε.inv.f n).val.app W
        (totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W
          (pure m (P.X p) W b x) (pure m (Q.X q) W c y)) =
      pure m ((total P Q).X n) W (b * c) (totalPure P Q p q n hpq W x y)) := by
  have hh (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ) := by
    exact balanced_comparison (S := B.obj.obj W) ((ε.hom.f n).val.app W).hom
      ((ε.inv.f n).val.app W).hom
      (fun z ↦ congrArg (fun f ↦ (f.f n).val.app W z) ε.hom_inv_id)
      (fun b x y ↦ pure m ((total P Q).X n) W b (totalPure P Q p q n hpq W x y))
      (pure m (P.X p) W) (pure m (Q.X q) W)
      (totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W)
      (fun b x y ↦ pure_smul_one m _ W b _)
      (pure_smul_one m _ W) (pure_smul_one m _ W)
      (fun b x y ↦ totalPure_smul_left ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W b x y)
      (fun b x y ↦ totalPure_smul_right ((m.E.mapHomologicalComplex (.up ℤ)).obj P)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq W b x y)
      (he p q n hpq W)
  exact ⟨fun p q n hpq W x y b ↦ (hh p q n hpq W).1 b x y,
    fun p q n hpq W x y b c ↦ (hh p q n hpq W).2 b c x y⟩

private theorem derived_tensor_factorization {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory)
    (hn : AdjunctionNormalized m a d)
    {Um Vm : CochainComplex (Modules A) ℤ} {Un Vn : CochainComplex (Modules B) ℤ}
    (hUm : Good Um) (hVm : Good Vm) (hUn : Good Un)
    (hEU : Good ((m.E.mapHomologicalComplex (.up ℤ)).obj Um))
    (hTot : Good (total Um Vm))
    (tU : Um ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj Un)
    (tV : Vm ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj Vn)
    (ε : (m.E.mapHomologicalComplex (.up ℤ)).obj (total Um Vm) ≅
      total ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)
        ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm))
    (tK : total Um Vm ⟶
      ((restriction φ).mapHomologicalComplex (.up ℤ)).obj (total Un Vn))
    (hk : ordinaryAdjunct a tK = ε.hom ≫ (WeilConjectures.coefficientTotalTensor.{u, u, u} J B).map
      (Prod.mkHom (ordinaryAdjunct a tU) (ordinaryAdjunct a tV))) :
    derivedAdjunct m d tK =
      m.T.map (tensorModel Um Vm hUm).hom ≫
        scalarTensorComparison m Um Vm hUm hVm hEU ε ≫
        (derivedTensor B).map (Prod.mkHom (derivedAdjunct m d tU) (derivedAdjunct m d tV)) ≫
        (tensorModel Un Vn hUn).inv := by
  have : IsIso (m.ε.app Um) := m.computes Um hUm.1
  have : IsIso (m.ε.app Vm) := m.computes Vm hVm.1
  have ht' := tensorModel_naturality hEU hUn
    (ordinaryAdjunct a tU) (ordinaryAdjunct a tV)
  have htensor := tensor_conjugation m.T (derivedTensor B) (tensorModel Um Vm hUm)
    (m.ε.app (total Um Vm)) (m.ε.app Um) (m.ε.app Vm)
    (DerivedCategory.Q.mapIso ε)
    (tensorModel ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)
      ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm) hEU)
    (tensorModel Un Vn hUn)
    (DerivedCategory.Q.map (ordinaryAdjunct a tU))
    (DerivedCategory.Q.map (ordinaryAdjunct a tV))
    (DerivedCategory.Q.map ((WeilConjectures.coefficientTotalTensor.{u, u, u} J B).map
      (Prod.mkHom (ordinaryAdjunct a tU) (ordinaryAdjunct a tV)))) ht'
  have hleft : derivedAdjunct m d tK =
      m.ε.app (total Um Vm) ≫ DerivedCategory.Q.map ε.hom ≫
        DerivedCategory.Q.map ((WeilConjectures.coefficientTotalTensor.{u, u, u} J B).map
          (Prod.mkHom (ordinaryAdjunct a tU) (ordinaryAdjunct a tV))) :=
    (derivedAdjunct_eq m a d hn hTot tK).trans
      ((congrArg (fun f ↦ m.ε.app (total Um Vm) ≫ DerivedCategory.Q.map f) hk).trans
        ((congrArg (m.ε.app (total Um Vm) ≫ ·)
          (DerivedCategory.Q.map_comp ε.hom _))))
  have hright := congrArg (fun f ↦
    m.T.map (tensorModel Um Vm hUm).hom ≫
      scalarTensorComparison m Um Vm hUm hVm hEU ε ≫
        (derivedTensor B).map f ≫ (tensorModel Un Vn hUn).inv)
    (congrArg₂ Prod.mkHom (derivedAdjunct_eq m a d hn hUm tU)
      (derivedAdjunct_eq m a d hn hVm tV))
  exact hleft.trans (htensor.trans hright.symm)

section Geometric

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A' B' : Sheaf K CommRingCat.{u}} {φ : A ⟶ B} {φ' : A' ⟶ B'}
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  (IA : InverseImage L A A') (IB : InverseImage L B B')
  (hc : L.map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose K
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ')
  [PreservesFiniteLimits L]

private theorem good_inverse
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ R)
    [(inverseModules IA).Additive]
    {P : CochainComplex (Modules A) ℤ} (hP : Good P) :
    Good (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P) := by
  have : (unliftInverseImage IA).modules.Additive := by
    change (inverseModules IA).Additive
    infer_instance
  refine ⟨kFlat_inverseImage_independent L R adj (unliftInverseImage IA) P hP.1 hP.2, ?_⟩
  intro i
  exact isFlat_algebraicInverseImageOfUniverses L R adj IA (P.X i) (hP.2 i)

/-- The actual pullback transition, using inverse image followed by the canonical action
identification. This gives q'(s) tensor g-inverse-image(t)(u) in tensor coordinates.
Source: Stacks 03EL (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def pullTransition [(inverseModules IA).Additive] [(inverseModules IB).Additive]
    {P : CochainComplex (Modules A) ℤ}
    {H : CochainComplex (Modules B) ℤ}
    (t : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj H) :
    ((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((restriction φ').mapHomologicalComplex (.up ℤ)).obj
        (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj H) :=
  ((inverseModules IA).mapHomologicalComplex (.up ℤ)).map t ≫
    (NatIso.mapHomologicalComplex (a_h IA IB hc inferInstance) (.up ℤ)).hom.app H

private theorem derived_pull_factorization
    [(inverseModules IA).Additive] [(inverseModules IB).Additive]
    [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
    [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    [PreservesFiniteLimits (restriction φ')] [PreservesFiniteColimits (restriction φ')]
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [HasDerivedCategory.{w} (Modules A')] [HasDerivedCategory.{w} (Modules B')]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (m' : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ')
    (a : m.E ⊣ restriction φ) (a' : m'.E ⊣ restriction φ')
    (d : m.T ⊣ (restriction φ).mapDerivedCategory)
    (d' : m'.T ⊣ (restriction φ').mapDerivedCategory)
    (hn : AdjunctionNormalized m a d) (hn' : AdjunctionNormalized m' a' d')
    (χ : (inverseModules IA) ⋙ m'.E ≅ m.E ⋙ (inverseModules IB))
    {Um : CochainComplex (Modules A) ℤ} {Un : CochainComplex (Modules B) ℤ}
    (hUm : Good Um)
    (hIA : Good (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um))
    (tU : Um ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj Un)
    (hpull : ordinaryAdjunct a' (pullTransition IA IB hc tU) =
      (NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um ≫
        ((inverseModules IB).mapHomologicalComplex (.up ℤ)).map (ordinaryAdjunct a tU))
    (hrep : m'.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um) =
      m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
        (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
        (inverseModules IB).mapDerivedCategory.map (m.ε.app Um) ≫
        (inverseModules IB).mapDerivedCategoryFactors.hom.app
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)) :
    derivedAdjunct m' d' (pullTransition IA IB hc tU) =
      m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
        (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
        (inverseModules IB).mapDerivedCategory.map (derivedAdjunct m d tU) ≫
        (inverseModules IB).mapDerivedCategoryFactors.hom.app Un := by
  have h₁ := derivedAdjunct_eq m' a' d' hn' hIA (pullTransition IA IB hc tU)
  have h₂ := congrArg (fun f ↦ m'.ε.app
    (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um) ≫
      DerivedCategory.Q.map f) hpull
  have h₃ := congrArg (m'.ε.app
    (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um) ≫ ·)
    (DerivedCategory.Q.map_comp
      ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um)
      (((inverseModules IB).mapHomologicalComplex (.up ℤ)).map (ordinaryAdjunct a tU)))
  have h₄ := congrArg (· ≫ DerivedCategory.Q.map
    (((inverseModules IB).mapHomologicalComplex (.up ℤ)).map (ordinaryAdjunct a tU))) hrep
  have h₅ := pull_conjugation DerivedCategory.Q
    ((inverseModules IB).mapHomologicalComplex (.up ℤ))
    (inverseModules IB).mapDerivedCategory DerivedCategory.Q
    (inverseModules IB).mapDerivedCategoryFactors
    (m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
      (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
      (inverseModules IB).mapDerivedCategory.map (m.ε.app Um)) (ordinaryAdjunct a tU)
  have h₆ := congrArg (fun f ↦
    m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
      (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
      (inverseModules IB).mapDerivedCategory.map f ≫
      (inverseModules IB).mapDerivedCategoryFactors.hom.app Un)
    (derivedAdjunct_eq m a d hn hUm tU)
  simp only [Category.assoc] at h₄ h₅
  have h₆' : _ := h₆.symm
  simp only [Functor.map_comp, Category.assoc] at h₆'
  have ha := Category.assoc
    (m'.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um))
    (DerivedCategory.Q.map
      (((inverseModules IB).mapHomologicalComplex (.up ℤ)).map (ordinaryAdjunct a tU)))
  exact h₁.trans (h₂.trans (h₃.trans (ha.symm.trans (h₄.trans (h₅.trans h₆')))))

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify K AddCommGrpCat] [K.WEqualsLocallyBijective AddCommGrpCat] in
set_option linter.unusedSectionVars false in
private theorem exact_inverse
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ R) :
    PreservesFiniteLimits (inverseModules IA) ∧
      PreservesFiniteColimits (inverseModules IA) := by
  let g : GeometricMorphism (Sheaf K (Type u)) (Sheaf J (Type u)) :=
    ⟨L, R, adj, inferInstance⟩
  exact (exactFunctor_iff _).mp
    (((GeometricMorphism.geometric_inverse_image_exact J K g).2.2 A).2 A' IA).1

attribute [local semireducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh

-- Keep representative constructions closed during the final assembly.

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 100000 in
-- Elaborate the nested witness tuple without unfolding its tensor models.
/-- Actual-transition tensor and pullback adjunct factorizations on the given complexes.
The isomorphism χ is fixed by the inverse-image unit equation for every module, not by
assuming that target-site sections are inverse images of individual source sections.
The four scalar adjunctions are normalized against the prescribed universal counits.

Source: Stacks 07A4, 0G7E, 07A6 and 03EL
(blueprint: lem-pur-quotient-operation-adjoint-factorizations).

Proof:
1. lem-pur-kflat-total-tensor-model gives flat-term K-flatness of both tensor outputs.
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback gives it for both inverse images
   and every scalar extension, including the extended tensor and pulled extension.
2. Construct ε on each total summand by (u tensor v) tensor a mapping to
   (u tensor a) tensor (v tensor 1). Its inverse multiplies the two final scalars.
   Balancing proves the inverse equations, and both differentials have the same
   sign (-1)^p. Sheafify the balanced maps and pass through the direct sums.
3. Construct the tensor transition on each summand by tU tensor tV. Semilinearity
   makes it balanced. Both its adjunct and the asserted composite send the same
   generator to a times (tU(u) tensor tV(v)), so sheafification and coproducts give equality.
4. Invert the coequalizer comparison of lem-sfb-kflat-scalar-comparison-normalization.
   Transport the ring actions along the specified inverseRing isomorphisms
   (lem-pur-ring-iso-derived-transport). Compatibility hc gives the displayed χ.
5. Naturality of the inverse-image unit gives the actual pullback transition.
   On unit generators both adjunct composites insert one and apply tU. The
   inverse-image adjunction detects equality, including every source-site object.
6. lem-pur-sheaf-ring-derived-coefficient-adjunction identifies actual derived
   adjuncts with localized ordinary ones. Naturality of tensor localization
   (lem-weil-pbc-site-derived-tensor-descent) gives the tensor formula.
   def-weil-pbc-canonical-ringed-tensor-comparison fixes ε on generators, and
   lem-weil-pbc-tensor-comparison-descent-representatives identifies its localization
   with the canonical strong monoidal comparison (lem-sfb-ringed-derived-monoidal-comparisons).
7. Localize χ and its unit equation. The normalization theorem identifies it with
   the specified mate θ_h. Localizing the ordinary pullback factorization gives
   the derived factorization with the exact-localization comparison maps displayed.
8. Tensor and inverse image preserve chain isomorphisms; compose their inverses
   with ε.inv or χ.inv. Localization preserves inverse pairs. No boundedness,
   flat coefficient maps, normalized whole system or replacement transition is used.
-/
theorem quotient_operation_adjoint_factorizations
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (_adj : L ⊣ R)
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [HasDerivedCategory.{w} (Modules A')] [HasDerivedCategory.{w} (Modules B')]
    : ∃ (_ : (inverseModules IA).Additive) (_ : (inverseModules IB).Additive)
      (_ : PreservesFiniteLimits (inverseModules IA))
      (_ : PreservesFiniteColimits (inverseModules IA))
      (_ : PreservesFiniteLimits (inverseModules IB))
      (_ : PreservesFiniteColimits (inverseModules IB))
      (_ : PreservesFiniteLimits (restriction φ))
      (_ : PreservesFiniteColimits (restriction φ))
      (_ : PreservesFiniteLimits (restriction φ'))
      (_ : PreservesFiniteColimits (restriction φ')),
    ∀(m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (m' : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ')
    (Um Vm : CochainComplex (Modules A) ℤ) (Un Vn : CochainComplex (Modules B) ℤ)
    (hUm : Good Um) (hVm : Good Vm) (_hUn : Good Un) (_hVn : Good Vn)
    (tU : Um ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj Un)
    (tV : Vm ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj Vn),
    ∃ (a : m.E ⊣ restriction φ) (a' : m'.E ⊣ restriction φ')
      (d : m.T ⊣ (restriction φ).mapDerivedCategory)
      (d' : m'.T ⊣ (restriction φ').mapDerivedCategory)
      (χ : (inverseModules IA) ⋙ m'.E ≅ m.E ⋙ (inverseModules IB))
      (ε : (m.E.mapHomologicalComplex (.up ℤ)).obj (total Um Vm) ≅
        total ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm))
      (tK : total Um Vm ⟶
        ((restriction φ).mapHomologicalComplex (.up ℤ)).obj (total Un Vn)),
    AdjunctionNormalized m a d ∧ AdjunctionNormalized m' a' d' ∧
    (∀ M : Modules A,
      (inverseModules IA).map (a.unit.app M) ≫
          (a_h IA IB hc inferInstance).hom.app (m.E.obj M) =
        a'.unit.app ((inverseModules IA).obj M) ≫ (restriction φ').map (χ.hom.app M)) ∧
    (∀ (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ)
        (x : (Um.X p).val.obj W) (y : (Vm.X q).val.obj W) (b : B.obj.obj W),
      (ε.hom.f n).val.app W (pure m ((total Um Vm).X n) W b
          (totalPure Um Vm p q n hpq W x y)) =
        totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm) p q n hpq W
            (pure m (Um.X p) W b x) (pure m (Vm.X q) W 1 y)) ∧
    (∀ (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ)
        (x : (Um.X p).val.obj W) (y : (Vm.X q).val.obj W) (b c : B.obj.obj W),
      (ε.inv.f n).val.app W
          (totalPure ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)
            ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm) p q n hpq W
              (pure m (Um.X p) W b x) (pure m (Vm.X q) W c y)) =
        pure m ((total Um Vm).X n) W (b * c) (totalPure Um Vm p q n hpq W x y)) ∧
    (∀ (p q n : ℤ) (hpq : p + q = n) (W : Cᵒᵖ)
        (x : (Um.X p).val.obj W) (y : (Vm.X q).val.obj W),
      (tK.f n).val.app W (totalPure Um Vm p q n hpq W x y) =
        totalPure Un Vn p q n hpq W ((tU.f p).val.app W x) ((tV.f q).val.app W y)) ∧
    ordinaryAdjunct a tK = ε.hom ≫ (KFlatTotalTensorModel.total B).map
      (Prod.mkHom (ordinaryAdjunct a tU) (ordinaryAdjunct a tV)) ∧
    ordinaryAdjunct a' (pullTransition IA IB hc tU) =
      (NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um ≫
        ((inverseModules IB).mapHomologicalComplex (.up ℤ)).map (ordinaryAdjunct a tU) ∧
    Good (total Um Vm) ∧ Good (total Un Vn) ∧
    Good (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um) ∧
    Good (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj Un) ∧
    Good ((m.E.mapHomologicalComplex (.up ℤ)).obj Um) ∧
    Good ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm) ∧
    Good ((m.E.mapHomologicalComplex (.up ℤ)).obj (total Um Vm)) ∧
    Good ((m'.E.mapHomologicalComplex (.up ℤ)).obj
      (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um)) ∧
    Good (total ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)
      ((m.E.mapHomologicalComplex (.up ℤ)).obj Vm)) ∧
    Good (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj
      ((m.E.mapHomologicalComplex (.up ℤ)).obj Um)) ∧
    ∃ (hEU : Good ((m.E.mapHomologicalComplex (.up ℤ)).obj Um))
      (hUn : Good Un),
    IsIso (scalarTensorComparison m Um Vm hUm hVm hEU ε) ∧
    IsIso (θ_h IA IB hc inferInstance d d') ∧
    derivedAdjunct m d tK =
      m.T.map (tensorModel Um Vm hUm).hom ≫
        scalarTensorComparison m Um Vm hUm hVm hEU ε ≫
        (derivedTensor B).map (Prod.mkHom (derivedAdjunct m d tU) (derivedAdjunct m d tV)) ≫
        (tensorModel Un Vn hUn).inv ∧
    m'.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um) =
      m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
        (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
        (inverseModules IB).mapDerivedCategory.map (m.ε.app Um) ≫
        (inverseModules IB).mapDerivedCategoryFactors.hom.app
          ((m.E.mapHomologicalComplex (.up ℤ)).obj Um) ∧
    derivedAdjunct m' d' (pullTransition IA IB hc tU) =
      m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
        (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
        (inverseModules IB).mapDerivedCategory.map (derivedAdjunct m d tU) ≫
        (inverseModules IB).mapDerivedCategoryFactors.hom.app Un ∧
    ((IsIso (ordinaryAdjunct a tU) ∧ IsIso (ordinaryAdjunct a tV)) →
      IsIso (ordinaryAdjunct a tK) ∧ IsIso (derivedAdjunct m d tK)) ∧
    (IsIso (ordinaryAdjunct a tU) →
      IsIso (ordinaryAdjunct a' (pullTransition IA IB hc tU)) ∧
        IsIso (derivedAdjunct m' d' (pullTransition IA IB hc tU))) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      classical
      have hAl := (exact_inverse IA R _adj).1
      have hAc := (exact_inverse IA R _adj).2
      have hBl := (exact_inverse IB R _adj).1
      have hBc := (exact_inverse IB R _adj).2
      have := Functor.additive_of_preserves_binary_products (inverseModules IA)
      have := Functor.additive_of_preserves_binary_products (inverseModules IB)
      have hYl : PreservesFiniteLimits (restriction φ) :=
        (sheafRingCoefficientOrdinaryAdjunction φ).1
      have hYc : PreservesFiniteColimits (restriction φ) :=
        (sheafRingCoefficientOrdinaryAdjunction φ).2.1
      have hXl : PreservesFiniteLimits (restriction φ') :=
        (sheafRingCoefficientOrdinaryAdjunction φ').1
      have hXc : PreservesFiniteColimits (restriction φ') :=
        (sheafRingCoefficientOrdinaryAdjunction φ').2.1
      refine ⟨inferInstance, inferInstance, hAl, hAc, hBl, hBc,
        hYl, hYc, hXl, hXc, ?_⟩
      intro m m' Um Vm Un Vn hUm hVm hUn hVn tU tV
      have normalized := kflat_scalar_comparison_normalization.{u, w}
        φ φ' L R _adj IA IB hc m m'
      have nr1 := fixed_proof_witness normalized
        (inferInstance : (inverseModules IA).Additive)
      have nr2 := fixed_proof_witness nr1
        (inferInstance : (inverseModules IB).Additive)
      have nr3 := fixed_proof_witness nr2
        (inferInstance : PreservesFiniteLimits (inverseModules IA))
      have nr4 := fixed_proof_witness nr3
        (inferInstance : PreservesFiniteColimits (inverseModules IA))
      have nr5 := fixed_proof_witness nr4
        (inferInstance : PreservesFiniteLimits (inverseModules IB))
      have nr6 := fixed_proof_witness nr5
        (inferInstance : PreservesFiniteColimits (inverseModules IB))
      have nr7 := fixed_proof_witness nr6
        (inferInstance : PreservesFiniteLimits (restriction φ))
      have nr8 := fixed_proof_witness nr7
        (inferInstance : PreservesFiniteColimits (restriction φ))
      have nr9 := fixed_proof_witness nr8
        (inferInstance : PreservesFiniteLimits (restriction φ'))
      have nr10 := fixed_proof_witness nr9
        (inferInstance : PreservesFiniteColimits (restriction φ'))
      clear normalized nr1 nr2 nr3 nr4 nr5 nr6 nr7 nr8 nr9
      obtain ⟨a, a', d, d', χ₀, hnorm⟩ := nr10
      have hn := hnorm.1
      have hn' := hnorm.2.1
      have hu := hnorm.2.2.2.2.2.1
      have hr := hnorm.2.2.2.2.2.2.1
      have hθ := hnorm.2.2.2.2.2.2.2
      let χ := χ₀.symm
      have hχ : χ = χ₀.symm := rfl
      have hu' (M : Modules A) :
          (inverseModules IA).map (a.unit.app M) ≫
            (a_h IA IB hc inferInstance).hom.app (m.E.obj M) =
          a'.unit.app ((inverseModules IA).obj M) ≫ (restriction φ').map (χ.hom.app M) := by
        apply (cancel_mono ((restriction φ').map (χ₀.hom.app M))).mp
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
          hχ, Iso.symm_hom]
        exact hu M
      have hh := total_comparison m Um Vm
      let ε := hh.choose
      have he₁ := hh.choose_spec
      have hf := comparison_full (φ := φ) (A := A) (B := B) m Um Vm ε he₁
      have he := hf.1
      have hei := hf.2
      let k := ε.hom ≫ (WeilConjectures.coefficientTotalTensor.{u, u, u} J B).map
        (Prod.mkHom (ordinaryAdjunct a tU) (ordinaryAdjunct a tV))
      let tK := (a.mapHomologicalComplex (.up ℤ)).homEquiv (total Um Vm) (total Un Vn) k
      have hk : ordinaryAdjunct a tK = k :=
        ((a.mapHomologicalComplex (.up ℤ)).homEquiv
          (total Um Vm) (total Un Vn)).symm_apply_apply k
      have hpull : ordinaryAdjunct a' (pullTransition IA IB hc tU) =
          (NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um ≫
            ((inverseModules IB).mapHomologicalComplex (.up ℤ)).map (ordinaryAdjunct a tU) := by
        exact cochain_transpose_of_unit a (inverseModules IA) (inverseModules IB) a' χ
          (a_h IA IB hc inferInstance) hu' tU
      have htK : ∀ p q n hpq W x y,
          (tK.f n).val.app W (totalPure Um Vm p q n hpq W x y) =
          totalPure Un Vn p q n hpq W ((tU.f p).val.app W x) ((tV.f q).val.app W y) := by
        intro p q n hpq W x y
        have hh := (adjunct_on_unit m a d hn tK n W
          (totalPure Um Vm p q n hpq W x y)).symm
        rw [hk] at hh
        change (tK.f n).val.app W _ = _
        exact hh.trans ((congrArg
          ((((WeilConjectures.coefficientTotalTensor.{u, u, u} J B).map
            (Prod.mkHom (ordinaryAdjunct a tU) (ordinaryAdjunct a tV))).f n).val.app W)
          (he₁ p q n hpq W x y)).trans
            ((total_map_pure (ordinaryAdjunct a tU) (ordinaryAdjunct a tV)
              p q n hpq W _ _).trans
              (congrArg₂ (totalPure Un Vn p q n hpq W)
                (adjunct_on_unit m a d hn tU p W x)
                (adjunct_on_unit m a d hn tV q W y))))
      have hTot := good_total hUm hVm
      have hTot' := good_total hUn hVn
      have hIA := good_inverse IA R _adj hUm
      have hIB := good_inverse IB R _adj hUn
      have hEU := good_scalar m hUm
      have hEV := good_scalar m hVm
      have hET := good_scalar m hTot
      have hEIA := good_scalar m' hIA
      have hTE := good_total hEU hEV
      have hIBE := good_inverse IB R _adj hEU
      refine ⟨a, a', d, d', χ, ε, tK, hn, hn', hu', he, hei, htK, hk, hpull,
        hTot, hTot', hIA, hIB, hEU, hEV, hET, hEIA, hTE, hIBE, hEU, hUn, ?_⟩
      have : IsIso (m.ε.app Um) := m.computes Um hUm.1
      have : IsIso (m.ε.app Vm) := m.computes Vm hVm.1
      have : IsIso (m.ε.app (total Um Vm)) := m.computes (total Um Vm) hTot.1
      have hiso := scalarTensorComparison_isIso m Um Vm hUm hVm hEU hTot ε
      have hrep : m'.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj Um) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Um) =
        m'.T.map ((inverseModules IA).mapDerivedCategoryFactors.inv.app Um) ≫
          (θ_h IA IB hc inferInstance d d').app (DerivedCategory.Q.obj Um) ≫
          (inverseModules IB).mapDerivedCategory.map (m.ε.app Um) ≫
          (inverseModules IB).mapDerivedCategoryFactors.hom.app
            ((m.E.mapHomologicalComplex (.up ℤ)).obj Um) := by
        rw [hχ]
        have h := (hr Um hUm.1 hUm.2).2
        exact ((m'.T.mapIso
          ((inverseModules IA).mapDerivedCategoryFactors.app Um)).eq_inv_comp).2 h.symm
      refine ⟨hiso, hθ, ?_, hrep, ?_, ?_, ?_⟩
      · exact derived_tensor_factorization m a d hn hUm hVm hUn hEU hTot tU tV ε tK hk
      · exact derived_pull_factorization IA IB hc m m' a a' d d' hn hn' χ hUm hIA tU hpull hrep
      · rintro ⟨hU, hV⟩
        have := hU
        have := hV
        have hi : IsIso (ordinaryAdjunct a tK) := by
          rw [hk]
          exact (ε ≪≫ (WeilConjectures.coefficientTotalTensor.{u, u, u} J B).mapIso
            ((asIso (ordinaryAdjunct a tU)).prod (asIso (ordinaryAdjunct a tV)))).isIso_hom
        refine ⟨hi, ?_⟩
        exact derivedAdjunct_isIso m a d hn hTot tK
      · intro hU
        have := hU
        have hi : IsIso (ordinaryAdjunct a' (pullTransition IA IB hc tU)) := by
          rw [hpull]
          exact (((NatIso.mapHomologicalComplex χ (.up ℤ)).app Um) ≪≫
            ((inverseModules IB).mapHomologicalComplex (.up ℤ)).mapIso
              (asIso (ordinaryAdjunct a tU))).isIso_hom
        refine ⟨hi, ?_⟩
        exact derivedAdjunct_isIso m' a' d' hn' hIA (pullTransition IA IB hc tU)
    

end Geometric
end SheafOfModules.QuotientOperation
