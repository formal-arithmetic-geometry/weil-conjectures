/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Whiskering

/-!
# Completion and scalar localization of compatible adjunction squares

Source: Bhatt–Scholze, Remark 6.8.15, and the rationalization/coherence paragraph of
`main-20261015/sec-proper-base-change/sk-thm-properbasechange/thm-weil-pbc-finite-extension`.
(blueprint: lem-weil-pbc-completed-localized-adjunction-square)

The raw localization uses the existing scalar-first tensor Hom modules, canonically
identified with the source's Hom-first order by tensor symmetry. Object equalities and
HEq express the specified formulas without choosing transports of existential functors.
No idempotent completion is taken. The categories may themselves be stable full
subcategories with their restricted adjunctions and comparison maps.
-/

@[expose] public section

set_option autoImplicit false

universe r uC vC uD vD uC' vC' uD' vD'

open TensorProduct

namespace CategoryTheory

section TensorConstruction

variable {A : Type r} [CommRing A] (t : A)
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear A C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear A D]
  {E : Type uC'} [Category.{vC'} E] [Preadditive E]
  [Linear (Localization.Away t) E]

open ScalarLocalization

private noncomputable def tensorMap (F : C ⥤ D) [F.Additive] [F.Linear A] :
    ScalarLocalization A C t ⥤ ScalarLocalization A D t where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} f := (F.mapLinearMap A).baseChange (Localization.Away t) f
  map_id X := by
    change ((F.mapLinearMap A).baseChange (Localization.Away t))
      ((1 : Localization.Away t) ⊗ₜ[A] 𝟙 X.obj) =
      (1 : Localization.Away t) ⊗ₜ[A] 𝟙 (F.obj X.obj)
    simp
  map_comp {X Y Z} f g := by
    change ((F.mapLinearMap A).baseChange (Localization.Away t))
        (composition A C t X.obj Y.obj Z.obj g f) =
      composition A D t (F.obj X.obj) (F.obj Y.obj) (F.obj Z.obj)
        (((F.mapLinearMap A).baseChange (Localization.Away t)) g)
        (((F.mapLinearMap A).baseChange (Localization.Away t)) f)
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul c g =>
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul b f => simp [composition_tmul]
      | add f h hf hh => simp [map_add, hf, hh]
    | add g h hg hh => simp [map_add, hg, hh]

@[simp] private theorem tensorMap_tmul (F : C ⥤ D) [F.Additive] [F.Linear A]
    {X Y : ScalarLocalization A C t} (b : Localization.Away t)
    (f : X.obj ⟶ Y.obj) :
    (tensorMap t F).map (b ⊗ₜ[A] f : X ⟶ Y) =
      b ⊗ₜ[A] F.map f := LinearMap.baseChange_tmul _ _ _

private instance tensorMap_additive (F : C ⥤ D) [F.Additive] [F.Linear A] :
    (tensorMap t F).Additive where
  map_add {_ _} {f g} := ((F.mapLinearMap A).baseChange (Localization.Away t)).map_add f g

private instance tensorMap_linear (F : C ⥤ D) [F.Additive] [F.Linear A] :
    (tensorMap t F).Linear (Localization.Away t) where
  map_smul {_ _} f b := ((F.mapLinearMap A).baseChange (Localization.Away t)).map_smul b f

private noncomputable def tensorLiftHom (F : C ⥤ E) [F.Additive]
    (hF : ∀ (X Y : C) (a : A) (f : X ⟶ Y),
      F.map (a • f) = algebraMap A (Localization.Away t) a • F.map f) (X Y : C) :
    (Localization.Away t ⊗[A] (X ⟶ Y)) →+ (F.obj X ⟶ F.obj Y) := by
  let β : Localization.Away t →+ (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
    { toFun := fun b ↦
        { toFun := fun f ↦ b • F.map f
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      map_zero' := by ext f; simp
      map_add' := by intros; ext f; simp [add_smul] }
  exact TensorProduct.liftAddHom β (by
    intro a b f
    dsimp [β]
    rw [hF, Algebra.smul_def, mul_smul, smul_smul, mul_comm, mul_smul])

@[simp] private theorem tensorLiftHom_tmul (F : C ⥤ E) [F.Additive]
    (hF : ∀ (X Y : C) (a : A) (f : X ⟶ Y),
      F.map (a • f) = algebraMap A (Localization.Away t) a • F.map f)
    (X Y : C) (b : Localization.Away t) (f : X ⟶ Y) :
    tensorLiftHom t F hF X Y (b ⊗ₜ[A] f) = b • F.map f := by
  rfl

private noncomputable def tensorLift (F : C ⥤ E) [F.Additive]
    (hF : ∀ (X Y : C) (a : A) (f : X ⟶ Y),
      F.map (a • f) = algebraMap A (Localization.Away t) a • F.map f) :
    ScalarLocalization A C t ⥤ E where
  obj X := F.obj X.obj
  map {X Y} f := tensorLiftHom t F hF X.obj Y.obj f
  map_id X := by
    change tensorLiftHom t F hF X.obj X.obj
      ((1 : Localization.Away t) ⊗ₜ[A] 𝟙 X.obj) = 𝟙 (F.obj X.obj)
    simp
  map_comp {X Y Z} f g := by
    change tensorLiftHom t F hF X.obj Z.obj
        (composition A C t X.obj Y.obj Z.obj g f) =
      tensorLiftHom t F hF X.obj Y.obj f ≫ tensorLiftHom t F hF Y.obj Z.obj g
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul c g =>
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul b f =>
        simp only [composition_tmul, tensorLiftHom_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul]
      | add f h hf hh => simp [map_add, hf, hh, Preadditive.add_comp]
    | add g h hg hh => simp [map_add, hg, hh, Preadditive.comp_add]

@[simp] private theorem tensorLift_tmul (F : C ⥤ E) [F.Additive]
    (hF : ∀ (X Y : C) (a : A) (f : X ⟶ Y),
      F.map (a • f) = algebraMap A (Localization.Away t) a • F.map f)
    {X Y : ScalarLocalization A C t} (b : Localization.Away t)
    (f : X.obj ⟶ Y.obj) :
    (tensorLift t F hF).map (b ⊗ₜ[A] f : X ⟶ Y) =
      b • F.map f := tensorLiftHom_tmul t F hF X.obj Y.obj b f

private instance tensorLift_additive (F : C ⥤ E) [F.Additive]
    (hF : ∀ (X Y : C) (a : A) (f : X ⟶ Y),
      F.map (a • f) = algebraMap A (Localization.Away t) a • F.map f) :
    (tensorLift t F hF).Additive where
  map_add {X Y} {f g} := (tensorLiftHom t F hF X.obj Y.obj).map_add f g

private instance tensorLift_linear (F : C ⥤ E) [F.Additive]
    (hF : ∀ (X Y : C) (a : A) (f : X ⟶ Y),
      F.map (a • f) = algebraMap A (Localization.Away t) a • F.map f) :
    (tensorLift t F hF).Linear (Localization.Away t) where
  map_smul {X Y} f b := by
    change tensorLiftHom t F hF X.obj Y.obj (b • f) =
      b • tensorLiftHom t F hF X.obj Y.obj f
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul c f => rw [TensorProduct.smul_tmul', smul_eq_mul, tensorLiftHom_tmul,
        tensorLiftHom_tmul, smul_smul]
    | add f g hf hg => simp only [smul_add, map_add, hf, hg]

private theorem tensorNaturality
    (F G : ScalarLocalization A C t ⥤ E)
    [F.Additive] [G.Additive]
    [F.Linear (Localization.Away t)] [G.Linear (Localization.Away t)]
    (τ : ∀ X, F.obj X ⟶ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y),
      F.map ((1 : Localization.Away t) ⊗ₜ[A] f) ≫ τ ⟨Y⟩ =
        τ ⟨X⟩ ≫ G.map ((1 : Localization.Away t) ⊗ₜ[A] f))
    {X Y : ScalarLocalization A C t} (f : X ⟶ Y) :
    F.map f ≫ τ Y = τ X ≫ G.map f := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul b f =>
    have hb := congrArg (fun z ↦ b • z) (h f)
    rw [← Linear.smul_comp, ← F.map_smul] at hb
    rw [← Linear.comp_smul, ← G.map_smul] at hb
    have he : b • ((1 : Localization.Away t) ⊗ₜ[A] f) = b ⊗ₜ[A] f := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he] at hb
    exact hb
  | add f g hf hg =>
    rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end TensorConstruction

/-- A compatible adjunction square persists under a specified left-adjoint isomorphism
and raw scalar localization. Source: Bhatt–Scholze, Remark 6.8.15 (ambient setting),
and the finite-extension rationalization paragraph of the main-20261015 blueprint.
(blueprint: lem-weil-pbc-completed-localized-adjunction-square)

Proof plan:
1. Apply `lem-sfb-adjunction-transport-left-iso`, namely `Adjunction.ofNatIsoLeft`.
Its Hom equivalence precomposes with γ; evaluating at identities gives the displayed
transported unit and counit.
2. Define the new comparison by whiskering γ inverse with FD and composing with α.
Naturality of β at γ cancels the γ and γ inverse terms in the unit equation.
Precomposing the old counit equation with FD(γ inverse) gives the new counit equation.
3. Apply the non-triangulated part of `lem-pur-semilinear-scalar-localization` to the
identity coefficient map A → A and inverted element t. Extend Ptilde, Q, the unit and
counit. Preservation of whiskering and composition gives both triangle identities;
the localized Hom bijection sends f to unit ≫ QB(f), with inverse PB(g) ≫ counit.
4. A B-linear category localized at 1 identifies with itself by b ⊗ f ↦ b • f,
with inverse f ↦ 1 ⊗ f, using tensor balancing and bilinear composition. Apply the
same semilinear extension lemma to A → B, inverted elements t and 1, and compose
with this identification. This gives FCbar and FDbar and their pure-tensor formulas,
hence their stated fraction formulas and B-linearity.
5. Extend the comparisons and their inverses. Their components remain αtilde and β.
Naturality on fractions follows by pulling t inverse powers through the B-linear
primed functors and applying the integral comparison naturality equations.
6. On every unchanged object FCbar(1 ⊗ unit) = FC(unit), and similarly for the
counit. Thus both localized compatibility equations are precisely those of Step 2.
7. Stable full subcategories have exactly the ambient Hom modules. Restrict the
ambient Hom bijections, units, counits and comparisons and apply Steps 1–6 there.
Empty subcategories and non-faithful localizations require no separate assumptions.
-/
theorem completed_localized_adjunction_square
    (A : Type r) [CommRing A] (t : A)
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear A C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear A D]
    {C' : Type uC'} [Category.{vC'} C'] [Preadditive C']
    [Linear (Localization.Away t) C']
    {D' : Type uD'} [Category.{vD'} D'] [Preadditive D']
    [Linear (Localization.Away t) D']
    (P : C ⥤ D) (Q : D ⥤ C) [P.Additive] [Q.Additive] [P.Linear A] [Q.Linear A]
    (a : P ⊣ Q) (P' : C' ⥤ D') (Q' : D' ⥤ C')
    [P'.Additive] [Q'.Additive] [P'.Linear (Localization.Away t)]
    [Q'.Linear (Localization.Away t)] (a' : P' ⊣ Q')
    (FC : C ⥤ C') (FD : D ⥤ D') [FC.Additive] [FD.Additive]
    (hFC : ∀ (N N' : C) (s : A) (f : N ⟶ N'),
      FC.map (s • f) = algebraMap A (Localization.Away t) s • FC.map f)
    (hFD : ∀ (M M' : D) (s : A) (f : M ⟶ M'),
      FD.map (s • f) = algebraMap A (Localization.Away t) s • FD.map f)
    (α : P ⋙ FD ≅ FC ⋙ P') (β : Q ⋙ FC ≅ FD ⋙ Q')
    (hη : ∀ N : C, FC.map (a.unit.app N) ≫ β.hom.app (P.obj N) ≫
      Q'.map (α.hom.app N) = a'.unit.app (FC.obj N))
    (hε : ∀ M : D, FD.map (a.counit.app M) =
      α.hom.app (Q.obj M) ≫ P'.map (β.hom.app M) ≫ a'.counit.app (FD.obj M))
    (Ptilde : C ⥤ D) [Ptilde.Additive] [Ptilde.Linear A] (γ : P ≅ Ptilde) :
    (∀ (N : C) (M : D) (f : Ptilde.obj N ⟶ M),
      (a.ofNatIsoLeft γ).homEquiv N M f = a.homEquiv N M (γ.hom.app N ≫ f)) ∧
    (∀ N : C, (a.ofNatIsoLeft γ).unit.app N =
      a.unit.app N ≫ Q.map (γ.hom.app N)) ∧
    (∀ M : D, (a.ofNatIsoLeft γ).counit.app M =
      γ.inv.app (Q.obj M) ≫ a.counit.app M) ∧
    ∃ αtilde : Ptilde ⋙ FD ≅ FC ⋙ P',
      (∀ N : C, αtilde.hom.app N = FD.map (γ.inv.app N) ≫ α.hom.app N) ∧
      (∀ N : C, FC.map ((a.ofNatIsoLeft γ).unit.app N) ≫
        β.hom.app (Ptilde.obj N) ≫ Q'.map (αtilde.hom.app N) =
          a'.unit.app (FC.obj N)) ∧
      (∀ M : D, FD.map ((a.ofNatIsoLeft γ).counit.app M) =
        αtilde.hom.app (Q.obj M) ≫ P'.map (β.hom.app M) ≫
          a'.counit.app (FD.obj M)) ∧
      ∃ (PB : ScalarLocalization A C t ⥤ ScalarLocalization A D t)
        (QB : ScalarLocalization A D t ⥤ ScalarLocalization A C t)
        (FCbar : ScalarLocalization A C t ⥤ C')
        (FDbar : ScalarLocalization A D t ⥤ D'),
        PB.Additive ∧ PB.Linear (Localization.Away t) ∧
        QB.Additive ∧ QB.Linear (Localization.Away t) ∧
        FCbar.Additive ∧ FCbar.Linear (Localization.Away t) ∧
        FDbar.Additive ∧ FDbar.Linear (Localization.Away t) ∧
        (∀ N : C, PB.obj ⟨N⟩ = ⟨Ptilde.obj N⟩) ∧
        (∀ M : D, QB.obj ⟨M⟩ = ⟨Q.obj M⟩) ∧
        (∀ N : C, FCbar.obj ⟨N⟩ = FC.obj N) ∧
        (∀ M : D, FDbar.obj ⟨M⟩ = FD.obj M) ∧
        (∀ (N N' : C) (f : N ⟶ N') (b : Localization.Away t),
          HEq (PB.map (b ⊗ₜ[A] f : (⟨N⟩ : ScalarLocalization A C t) ⟶ ⟨N'⟩))
            (b ⊗ₜ[A] Ptilde.map f)) ∧
        (∀ (M M' : D) (f : M ⟶ M') (b : Localization.Away t),
          HEq (QB.map (b ⊗ₜ[A] f : (⟨M⟩ : ScalarLocalization A D t) ⟶ ⟨M'⟩))
            (b ⊗ₜ[A] Q.map f)) ∧
        (∀ (N N' : C) (f : N ⟶ N') (b : Localization.Away t),
          HEq (FCbar.map (b ⊗ₜ[A] f : (⟨N⟩ : ScalarLocalization A C t) ⟶ ⟨N'⟩))
            (b • FC.map f)) ∧
        (∀ (M M' : D) (f : M ⟶ M') (b : Localization.Away t),
          HEq (FDbar.map (b ⊗ₜ[A] f : (⟨M⟩ : ScalarLocalization A D t) ⟶ ⟨M'⟩))
            (b • FD.map f)) ∧
        ∃ (aB : PB ⊣ QB) (αbar : PB ⋙ FDbar ≅ FCbar ⋙ P')
          (βbar : QB ⋙ FCbar ≅ FDbar ⋙ Q'),
          (∀ N : C, HEq (aB.unit.app ⟨N⟩)
            ((1 : Localization.Away t) ⊗ₜ[A] (a.ofNatIsoLeft γ).unit.app N)) ∧
          (∀ M : D, HEq (aB.counit.app ⟨M⟩)
            ((1 : Localization.Away t) ⊗ₜ[A] (a.ofNatIsoLeft γ).counit.app M)) ∧
          (∀ N : C, HEq (αbar.hom.app ⟨N⟩) (αtilde.hom.app N)) ∧
          (∀ M : D, HEq (βbar.hom.app ⟨M⟩) (β.hom.app M)) ∧
          (∀ N : ScalarLocalization A C t,
            FCbar.map (aB.unit.app N) ≫ βbar.hom.app (PB.obj N) ≫
              Q'.map (αbar.hom.app N) = a'.unit.app (FCbar.obj N)) ∧
          (∀ M : ScalarLocalization A D t, FDbar.map (aB.counit.app M) =
            αbar.hom.app (QB.obj M) ≫ P'.map (βbar.hom.app M) ≫
              a'.counit.app (FDbar.obj M)) := by
  let adjT := a.ofNatIsoLeft γ
  let αtilde : Ptilde ⋙ FD ≅ FC ⋙ P' := Functor.isoWhiskerRight γ.symm FD ≪≫ α
  have hα (N : C) : αtilde.hom.app N = FD.map (γ.inv.app N) ≫ α.hom.app N := rfl
  have hηT (N : C) : FC.map (adjT.unit.app N) ≫
      β.hom.app (Ptilde.obj N) ≫ Q'.map (αtilde.hom.app N) =
        a'.unit.app (FC.obj N) := by
    change FC.map (a.unit.app N ≫ Q.map (γ.hom.app N)) ≫ _ ≫ _ = _
    rw [FC.map_comp, Category.assoc]
    have hn := β.hom.naturality (γ.hom.app N)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, hα, Q'.map_comp]
    simp only [← Q'.map_comp_assoc, ← FD.map_comp, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp]
    exact hη N
  have hεT (M : D) : FD.map (adjT.counit.app M) =
      αtilde.hom.app (Q.obj M) ≫ P'.map (β.hom.app M) ≫
        a'.counit.app (FD.obj M) := by
    change FD.map (γ.inv.app (Q.obj M) ≫ a.counit.app M) = _
    rw [FD.map_comp, hε, hα, Category.assoc]
  refine ⟨?_, (fun _ ↦ rfl), (fun _ ↦ rfl), αtilde, hα, hηT, hεT, ?_⟩
  · intro N M f
    exact a.homEquiv_ofNatIsoLeft_apply γ f
  let PB := tensorMap t Ptilde
  let QB := tensorMap t Q
  let FCbar := tensorLift t FC hFC
  let FDbar := tensorLift t FD hFD
  let ηB : 𝟭 (ScalarLocalization A C t) ⟶ PB ⋙ QB :=
    { app := fun N ↦ (1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app N.obj
      naturality := by
        intro X Y f
        refine tensorNaturality t (𝟭 (ScalarLocalization A C t)) (PB ⋙ QB)
          (fun N ↦ (1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app N.obj) ?_ f
        intro X Y f
        change ((1 : Localization.Away t) ⊗ₜ[A] f) ≫
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app Y) =
          ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app X) ≫
            (tensorMap t Q).map ((tensorMap t Ptilde).map
              ((1 : Localization.Away t) ⊗ₜ[A] f))
        change ScalarLocalization.composition A C t X Y (Q.obj (Ptilde.obj Y))
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app Y)
            ((1 : Localization.Away t) ⊗ₜ[A] f) =
          ScalarLocalization.composition A C t X (Q.obj (Ptilde.obj X))
            (Q.obj (Ptilde.obj Y))
            ((tensorMap t Q).map ((tensorMap t Ptilde).map
              ((1 : Localization.Away t) ⊗ₜ[A] f)))
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app X)
        simp only [tensorMap, LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
          ScalarLocalization.composition_tmul, one_mul]
        exact congrArg (fun z ↦ (1 : Localization.Away t) ⊗ₜ[A] z)
          (adjT.unit.naturality f) }
  let εB : QB ⋙ PB ⟶ 𝟭 (ScalarLocalization A D t) :=
    { app := fun M ↦ (1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app M.obj
      naturality := by
        intro X Y f
        refine tensorNaturality t (QB ⋙ PB) (𝟭 (ScalarLocalization A D t))
          (fun M ↦ (1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app M.obj) ?_ f
        intro X Y f
        change (tensorMap t Ptilde).map ((tensorMap t Q).map
            ((1 : Localization.Away t) ⊗ₜ[A] f)) ≫
              ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app Y) =
          ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app X) ≫
            ((1 : Localization.Away t) ⊗ₜ[A] f)
        change ScalarLocalization.composition A D t (Ptilde.obj (Q.obj X))
            (Ptilde.obj (Q.obj Y)) Y
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app Y)
            ((tensorMap t Ptilde).map ((tensorMap t Q).map
              ((1 : Localization.Away t) ⊗ₜ[A] f))) =
          ScalarLocalization.composition A D t (Ptilde.obj (Q.obj X)) X Y
            ((1 : Localization.Away t) ⊗ₜ[A] f)
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app X)
        simp only [tensorMap, LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
          ScalarLocalization.composition_tmul, one_mul]
        exact congrArg (fun z ↦ (1 : Localization.Away t) ⊗ₜ[A] z)
          (adjT.counit.naturality f) }
  let aB : PB ⊣ QB :=
    { unit := ηB
      counit := εB
      left_triangle_components := by
        intro N
        change ScalarLocalization.composition A D t (Ptilde.obj N.obj)
            (Ptilde.obj (Q.obj (Ptilde.obj N.obj))) (Ptilde.obj N.obj)
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app (Ptilde.obj N.obj))
            ((tensorMap t Ptilde).map
              ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app N.obj)) =
          (1 : Localization.Away t) ⊗ₜ[A] 𝟙 (Ptilde.obj N.obj)
        simp only [tensorMap, LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
          ScalarLocalization.composition_tmul, one_mul, adjT.left_triangle_components]
      right_triangle_components := by
        intro M
        change ScalarLocalization.composition A C t (Q.obj M.obj)
            (Q.obj (Ptilde.obj (Q.obj M.obj))) (Q.obj M.obj)
            ((tensorMap t Q).map
              ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app M.obj))
            ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app (Q.obj M.obj)) =
          (1 : Localization.Away t) ⊗ₜ[A] 𝟙 (Q.obj M.obj)
        simp only [tensorMap, LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
          ScalarLocalization.composition_tmul, one_mul, adjT.right_triangle_components] }
  let αbar : PB ⋙ FDbar ≅ FCbar ⋙ P' :=
    NatIso.ofComponents (fun N ↦ αtilde.app N.obj) (by
      intro X Y f
      refine tensorNaturality t (PB ⋙ FDbar) (FCbar ⋙ P')
        (fun N ↦ αtilde.hom.app N.obj) ?_ f
      intro X Y f
      change (tensorLift t FD hFD).map ((tensorMap t Ptilde).map
          ((1 : Localization.Away t) ⊗ₜ[A] f)) ≫ αtilde.hom.app Y =
        αtilde.hom.app X ≫ P'.map ((tensorLift t FC hFC).map
          ((1 : Localization.Away t) ⊗ₜ[A] f))
      simpa only [Functor.comp_obj, Functor.comp_map,
        tensorMap, tensorLift, LinearMap.baseChange_tmul,
        Functor.coe_mapLinearMap, tensorLiftHom_tmul, one_smul] using
        αtilde.hom.naturality f)
  let βbar : QB ⋙ FCbar ≅ FDbar ⋙ Q' :=
    NatIso.ofComponents (fun M ↦ β.app M.obj) (by
      intro X Y f
      refine tensorNaturality t (QB ⋙ FCbar) (FDbar ⋙ Q')
        (fun M ↦ β.hom.app M.obj) ?_ f
      intro X Y f
      change (tensorLift t FC hFC).map ((tensorMap t Q).map
          ((1 : Localization.Away t) ⊗ₜ[A] f)) ≫ β.hom.app Y =
        β.hom.app X ≫ Q'.map ((tensorLift t FD hFD).map
          ((1 : Localization.Away t) ⊗ₜ[A] f))
      simpa only [Functor.comp_obj, Functor.comp_map,
        tensorMap, tensorLift, LinearMap.baseChange_tmul,
        Functor.coe_mapLinearMap, tensorLiftHom_tmul, one_smul] using β.hom.naturality f)
  refine ⟨PB, QB, FCbar, FDbar, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (fun _ ↦ rfl), (fun _ ↦ rfl), (fun _ ↦ rfl), (fun _ ↦ rfl),
    ?_, ?_, ?_, ?_, aB, αbar, βbar,
    (fun _ ↦ HEq.rfl), (fun _ ↦ HEq.rfl),
    (fun _ ↦ HEq.rfl), (fun _ ↦ HEq.rfl), ?_, ?_⟩
  · intro N N' f b
    exact heq_of_eq (tensorMap_tmul t Ptilde b f)
  · intro M M' f b
    exact heq_of_eq (tensorMap_tmul t Q b f)
  · intro N N' f b
    exact heq_of_eq (tensorLift_tmul t FC hFC b f)
  · intro M M' f b
    exact heq_of_eq (tensorLift_tmul t FD hFD b f)
  · intro N
    change (tensorLift t FC hFC).map
        ((1 : Localization.Away t) ⊗ₜ[A] adjT.unit.app N.obj) ≫
          β.hom.app (Ptilde.obj N.obj) ≫ Q'.map (αtilde.hom.app N.obj) = _
    simpa only [FCbar, FDbar, tensorLift, tensorLiftHom_tmul, one_smul] using hηT N.obj
  · intro M
    change (tensorLift t FD hFD).map
        ((1 : Localization.Away t) ⊗ₜ[A] adjT.counit.app M.obj) =
          αtilde.hom.app (Q.obj M.obj) ≫ P'.map (β.hom.app M.obj) ≫ _
    simpa only [FCbar, FDbar, tensorLift, tensorLiftHom_tmul, one_smul] using hεT M.obj

end CategoryTheory
