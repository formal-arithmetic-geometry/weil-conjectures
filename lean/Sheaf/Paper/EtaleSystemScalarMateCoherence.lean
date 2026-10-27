/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.EtaleSystemCoefficientProjection
public import Sheaf.Paper.EtaleSystemQuotientNormalization
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.EtaleSystemEvaluationBound
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.EtaleSystemProjectionPresentationCoherence
import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.SixFunctors.SystemProperOpenScalarSquare
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Coherent scalar mates on ordinary derived étale systems

Source: Zheng, Constructions 2.26 and 5.15, Proposition 2.29(2), Lemma 5.22;
Mathlib, Adjunction.Mates (blueprint: lem-pur-etale-system-scalar-mate-coherence).

All system categories and scalar operations are the recorded `SystemProjection` ones.
The auxiliary records specify choices of the actual projections, transitions and
left-extension comparisons, rather than unrelated level maps. Index n denotes level n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemScalarMate
open SystemProjection

/-- Choices of the actual invertible projections, with their arrows fixed by the
recorded system projection and finite-level compact scalar map. These isomorphisms
are unique once those arrows are fixed.
Source: Zheng 2.26, 5.15; Stacks 0GL6
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
structure Projections {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : Theory c l) where
  system : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings),
    (t.support B).F ⋙ (t.scalarY a).model.T ≅
      (t.scalarX a).model.T ⋙ (t.support C).F
  system_hom : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings),
    (system a).hom = t.q a
  single : ∀ (B C : Coefficients.{u} l) (m n : ℕ)
    (a : B.rings.obj (op m) ⟶ C.rings.obj (op n)),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (B.rings.obj (op m))) c ⋙
        scalarExtension a.hom Y ≅ scalarExtension a.hom X ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (C.rings.obj (op n))) c
  single_hom : ∀ (B C : Coefficients.{u} l) (m n : ℕ)
    (a : B.rings.obj (op m) ⟶ C.rings.obj (op n)),
    (single B C m n a).hom = compactScalarMap a.hom c

/-- A realization of the actual horizontal strict transition on constant-coefficient
module sheaves. The section equation fixes it uniquely, including for identity indices.
Source: Zheng 4.1 and 5.15
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
structure Transitions (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) where
  ordinary : ∀ {m n : ℕ} (h : n ≤ m), level W B m ⟶ level W B n ⋙
    Sheaf.restrictScalars W.smallEtaleTopology (B.map (homOfLE h).op).hom
  sections : ∀ {m n : ℕ} (h : n ≤ m) (M : Modules W B) (U : W.Etaleᵒᵖ),
    HEq (fun x ↦ (((ordinary h).app M).hom.app U) x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)

/-- Localize the specified ordinary strict transition termwise, using the same exact
evaluations as the projection theory. No family of derived level maps is lifted.
Source: Zheng 4.1; Stacks 05RU
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
def Transitions.derived {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : Transitions W B) {m n : ℕ} (h : n ≤ m)
    (em : Evaluation W B m) (en : Evaluation W B n) :
    em.E ⟶ en.E ⋙ Sheaf.derivedRestrictScalars W.smallEtaleTopology
      (B.map (homOfLE h).op).hom :=
  letI := em.additive
  letI := em.limits
  letI := em.colimits
  letI := en.additive
  letI := en.limits
  letI := en.colimits
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules W B) (.up ℤ)) _ _
    (level W B m).mapDerivedCategory
    ((level W B n ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (B.map (homOfLE h).op).hom)
      |>.mapDerivedCategory)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (d.ordinary h) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (level W B n)
      (Sheaf.restrictScalars W.smallEtaleTopology (B.map (homOfLE h).op).hom)).hom

/-- The derived tensor-adjoint of the actual strict transition.
Source: Zheng 4.1, 5.15; Stacks 07A6
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
def Transitions.reduction {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : Transitions W B) {m n : ℕ} (h : n ≤ m)
    (em : Evaluation W B m) (en : Evaluation W B n) (M : Derived W B) :
    (scalarExtension (B.map (homOfLE h).op).hom W).obj (em.E.obj M) ⟶ en.E.obj M :=
  ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
    (B.map (homOfLE h).op).hom)).homEquiv _ _).symm ((d.derived h em en).app M)

/-- Evaluation of both scalar-adjunction identities on the simultaneous ordinary
models. The adjunction is the normalized derived scalar adjunction, not a new choice.
Source: Zheng 4.1, 5.15; Stacks 07A6
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
def CoefficientAdjunctionEvaluation (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) (s : Scalar W a) (n : ℕ)
    (eb : Evaluation W B n) (ec : Evaluation W C n)
    (v : ScalarEvaluation W a s n eb ec) : Prop :=
  (∀ M : Derived W B,
    eb.E.map (s.adjunction.unit.app M) ≫
        v.restriction.hom.app (s.model.T.obj M) ≫
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology (a.app (op n)).hom).map
          (v.iso.hom.app M) =
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (a.app (op n)).hom)).unit.app (eb.E.obj M)) ∧
  (∀ N : Derived W C,
    (scalarExtension (a.app (op n)).hom W).map (v.restriction.hom.app N) ≫
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
          (a.app (op n)).hom)).counit.app (ec.E.obj N) =
      v.iso.inv.app ((restriction W a).obj N) ≫ ec.E.map (s.adjunction.counit.app N))

/-- Fixed system and finite adjunctions, with the stipulated counit-preserving
left-extension evaluation comparisons and transition-mate normalization. Left
extensions are adjoint to the actual exact evaluations; their comparison is fixed
by its mate, so their Hom chain is the node's six natural Hom bijections.
Source: Zheng 5.15, (5.16.2), 5.22
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
structure Adjoints {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : Theory c l) (q : Projections t) where
  G : ∀ B : Coefficients.{u} l, Derived Y B.rings ⥤ Derived X B.rings
  adj : ∀ B : Coefficients.{u} l, (t.support B).F ⊣ G B
  g : ∀ (B : Coefficients.{u} l) (n : ℕ),
    DerivedCategoryModule (B.rings.obj (op n)) Y ⥤
      DerivedCategoryModule (B.rings.obj (op n)) X
  adjN : ∀ (B : Coefficients.{u} l) (n : ℕ),
    rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (B.rings.obj (op n))) c ⊣ g B n
  theta : ∀ (B : Coefficients.{u} l) (n : ℕ),
    G B ⋙ (t.evaluationX B n).E ≅ (t.evaluationY B n).E ⋙ g B n
  counit : ∀ (B : Coefficients.{u} l) (n : ℕ) (M : Derived Y B.rings),
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (B.rings.obj (op n))) c).map ((theta B n).hom.app M) ≫
        (adjN B n).counit.app ((t.evaluationY B n).E.obj M) =
      (t.supportEvaluation B n).iso.inv.app ((G B).obj M) ≫
        (t.evaluationY B n).E.map ((adj B).counit.app M)
  unit : ∀ (B : Coefficients.{u} l) (n : ℕ) (K : Derived X B.rings),
    (t.evaluationX B n).E.map ((adj B).unit.app K) ≫
        (theta B n).hom.app ((t.support B).F.obj K) ≫
        (g B n).map ((t.supportEvaluation B n).iso.hom.app K) =
      (adjN B n).unit.app ((t.evaluationX B n).E.obj K)
  LX : ∀ (B : Coefficients.{u} l) (n : ℕ),
    DerivedCategoryModule (B.rings.obj (op n)) X ⥤ Derived X B.rings
  LY : ∀ (B : Coefficients.{u} l) (n : ℕ),
    DerivedCategoryModule (B.rings.obj (op n)) Y ⥤ Derived Y B.rings
  leftX : ∀ (B : Coefficients.{u} l) (n : ℕ), LX B n ⊣ (t.evaluationX B n).E
  leftY : ∀ (B : Coefficients.{u} l) (n : ℕ), LY B n ⊣ (t.evaluationY B n).E
  leftComparison : ∀ (B : Coefficients.{u} l) (n : ℕ),
    LX B n ⋙ (t.support B).F ≅
      rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (B.rings.obj (op n))) c ⋙ LY B n
  left_normalized : ∀ (B : Coefficients.{u} l) (n : ℕ),
    (mateEquiv (leftX B n) (leftY B n)
      (.mk _ _ _ _ (leftComparison B n).inv)).natTrans =
        (t.supportEvaluation B n).iso.inv
  hom_chain : ∀ (B : Coefficients.{u} l) (n : ℕ)
    (P : DerivedCategoryModule (B.rings.obj (op n)) X) (M : Derived Y B.rings)
    (z : P ⟶ (t.evaluationX B n).E.obj ((G B).obj M)),
    z ≫ (theta B n).hom.app M =
      (((((leftX B n).homEquiv P ((G B).obj M)).symm.trans
        ((adj B).homEquiv ((LX B n).obj P) M).symm).trans
        (Iso.homCongr ((leftComparison B n).app P) (Iso.refl M))).trans
        ((leftY B n).homEquiv _ M) |>.trans
        ((adjN B n).homEquiv P ((t.evaluationY B n).E.obj M))) z
  transitionX : ∀ B : Coefficients.{u} l, Transitions X B.rings
  transitionY : ∀ B : Coefficients.{u} l, Transitions Y B.rings
  transition_normalized : ∀ (B : Coefficients.{u} l) {m n : ℕ} (h : n ≤ m)
    (M : Derived Y B.rings),
    (transitionX B).reduction h (t.evaluationX B m) (t.evaluationX B n)
        ((G B).obj M) ≫ (theta B n).hom.app M =
      (scalarExtension (B.rings.map (homOfLE h).op).hom X).map
          ((theta B m).hom.app M) ≫
        (etaleCoefficientQuotientMate (B.rings.map (homOfLE h).op).hom c
          (adjN B m) (adjN B n) (q.single B B m n (B.rings.map (homOfLE h).op))).app
            ((t.evaluationY B m).E.obj M) ≫
        (g B n).map ((transitionY B).reduction h
          (t.evaluationY B m) (t.evaluationY B n) M)

/-- The actual mate of inverse system projection, constructed by units, counits and
whiskering on the derived category of entire strict systems.
Source: Zheng Construction 2.26, equation (2.26.1)
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
def mate {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    {t : Theory c l} (q : Projections t) (d : Adjoints t q)
    {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) :
    d.G B ⋙ (t.scalarX a).model.T ⟶ (t.scalarY a).model.T ⋙ d.G C :=
  (mateEquiv (d.adj B) (d.adj C) (.mk _ _ _ _ (q.system a).inv)).natTrans

/-- The two-step mate word, transported back by the canonical balanced associators.
Source: Zheng 2.26, 5.15; Stacks 0D6D
(blueprint: lem-pur-etale-system-scalar-mate-coherence). -/
def path {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    {t : Theory c l} (q : Projections t) (d : Adjoints t q)
    {B C D : Coefficients.{u} l} (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings) :
    d.G B ⋙ (t.scalarX (a ≫ b)).model.T ⟶ (t.scalarY (a ≫ b)).model.T ⋙ d.G D :=
  Functor.whiskerLeft (d.G B)
      (associator X (t.scalarX a) (t.scalarX b) (t.scalarX (a ≫ b))).inv ≫
    Functor.whiskerRight (mate q d a) (t.scalarX b).model.T ≫
    Functor.whiskerLeft (t.scalarY a).model.T (mate q d b) ≫
    Functor.whiskerRight
      (associator Y (t.scalarY a) (t.scalarY b) (t.scalarY (a ≫ b))).hom (d.G D)

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem scalar_adjunction_evaluation (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) (s : Scalar W a) (n : ℕ)
    (eb : Evaluation W B n) (ec : Evaluation W C n)
    (v : ScalarEvaluation W a s n eb ec) :
    CoefficientAdjunctionEvaluation W a s n eb ec v := by
  let R := Sheaf.derivedRestrictScalars W.smallEtaleTopology (a.app (op n)).hom
  let adj := Adjunction.ofIsRightAdjoint R
  let α : TwoSquare eb.E s.model.T R.leftAdjoint ec.E := v.iso.inv
  have hm : (mateEquiv s.adjunction adj α).natTrans = v.restriction.hom := by
    have hv : α = (mateEquiv s.adjunction adj).symm
        (TwoSquare.mk _ _ _ _ v.restriction.hom) := by
      apply TwoSquare.ext
      intro M
      exact congr_app v.mate M
    exact congrArg TwoSquare.natTrans
      ((Equiv.eq_symm_apply _).1 hv)
  constructor
  · intro M
    have h := unit_mateEquiv s.adjunction adj α M
    rw [show (mateEquiv s.adjunction adj α).app _ =
      v.restriction.hom.app _ from congr_app hm _] at h
    change eb.E.map (s.adjunction.unit.app M) ≫
      v.restriction.hom.app (s.model.T.obj M) =
        adj.unit.app (eb.E.obj M) ≫ R.map (v.iso.inv.app M) at h
    have hx := congrArg (fun z ↦ z ≫ R.map (v.iso.hom.app M)) h
    simp only [Category.assoc] at hx
    erw [← R.map_comp, v.iso.inv_hom_id_app, R.map_id, Category.comp_id] at hx
    exact hx
  · intro N
    have h := mateEquiv_counit s.adjunction adj α N
    rw [show (mateEquiv s.adjunction adj α).app _ =
      v.restriction.hom.app _ from congr_app hm _] at h
    exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem reduction_naturality {W : Scheme.{u}}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Transitions W B)
    {m n : ℕ} (h : n ≤ m) (em : Evaluation W B m) (en : Evaluation W B n)
    {M N : Derived W B} (z : M ⟶ N) :
    (scalarExtension (B.map (homOfLE h).op).hom W).map (em.E.map z) ≫
        d.reduction h em en N = d.reduction h em en M ≫ en.E.map z := by
  let adj := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
    W.smallEtaleTopology (B.map (homOfLE h).op).hom)
  have hn := (d.derived h em en).naturality z
  have hx := congrArg ((adj.homEquiv _ _).symm) hn
  dsimp only [Functor.comp_map] at hx
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm] at hx
  exact hx


private theorem support_transpose {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} {t : Theory c l}
    (q : Projections t) (d : Adjoints t q) (B : Coefficients.{u} l) (n : ℕ)
    (P : Derived X B.rings) (M : Derived Y B.rings) (z : (t.support B).F.obj P ⟶ M) :
    (t.evaluationX B n).E.map ((d.adj B).homEquiv P M z) ≫
        (d.theta B n).hom.app M =
      (d.adjN B n).homEquiv _ _
        ((t.supportEvaluation B n).iso.inv.app P ≫ (t.evaluationY B n).E.map z) := by
  apply ((d.adjN B n).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [d.counit]
  erw [reassoc_of% ((t.supportEvaluation B n).iso.inv.naturality
    ((d.adj B).homEquiv P M z))]
  erw [← Functor.map_comp, ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

private theorem finite_free_exact (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) (s : Scalar W a)
    (hf : ∀ n : ℕ, ∃ r : ℕ, Nonempty
      (Module.Basis (Fin r) (B.obj (op n))
        ((ModuleCat.restrictScalars (a.app (op n)).hom).obj
          (ModuleCat.of (C.obj (op n)) (C.obj (op n)))))) :
    PreservesFiniteLimits s.model.E ∧ PreservesFiniteColimits s.model.E ∧
      ∀ P : CochainComplex (Modules W B) ℤ, IsIso (s.model.ε.app P) := by
  have hflat (U : (ℕ × W.Etale)ᵒᵖ) : ((ringMap W a).hom.app U).hom.Flat := by
    let n := U.unop.1
    letI : Algebra (B.obj (op n)) (C.obj (op n)) := (a.app (op n)).hom.toAlgebra
    obtain ⟨r, ⟨b⟩⟩ := hf n
    letI : Module.Free (B.obj (op n)) (C.obj (op n)) := Module.Free.of_basis b
    letI : Module.Finite (B.obj (op n)) (C.obj (op n)) := Module.Finite.of_basis b
    obtain ⟨q, β, _⟩ := @CategoryTheory.constantFiniteFree_sectionBasis.{u + 1, u, u + 1}
      W.Etale inferInstance W.smallEtaleTopology
      (inferInstance : HasSheafify W.smallEtaleTopology CommRingCat.{u + 1})
      (inferInstance : W.smallEtaleTopology.HasSheafCompose
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (inferInstance : HasSheafify W.smallEtaleTopology AddCommGrpCat.{u + 1})
      (inferInstance : W.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1})
      (B.obj (op n)) (C.obj (op n)) inferInstance inferInstance inferInstance
    have hα : (ringMap W a).hom.app U =
        ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
          (a.app (op n))).hom.app (op U.unop.2) := by
      delta ringMap
      exact (WeilConjectures.SemilinearSections.systemMap_existsUnique W.smallEtaleTopology
        (coefficients W B) (transitions W B) (coefficients W C) (transitions W C)
        (fun n ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
          (a.app (op n))) (fun n ↦ by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg
              (fun z ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map z)
              (a.naturality (homOfLE (Nat.le_succ n)).op).symm)).exists.choose_spec
                U.unop.1 (op U.unop.2)
    rw [hα]
    letI : Algebra ((coefficients W B n).obj.obj (op U.unop.2))
        ((coefficients W C n).obj.obj (op U.unop.2)) :=
      (((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
        (a.app (op n))).hom.app (op U.unop.2)).hom.toAlgebra
    letI : Module.Free ((coefficients W B n).obj.obj (op U.unop.2))
        ((coefficients W C n).obj.obj (op U.unop.2)) := Module.Free.of_basis (β _)
    exact inferInstanceAs (Module.Flat ((coefficients W B n).obj.obj (op U.unop.2))
      ((coefficients W C n).obj.obj (op U.unop.2)))
  have : PreservesFiniteLimits s.model.E := model_limits_of_flat (ringMap W a) s.model hflat
  letI : s.model.E.IsLeftAdjoint := s.ordinaryAdj.isLeftAdjoint
  have : PreservesFiniteColimits s.model.E := inferInstance
  have : s.model.T.IsLeftDerivedFunctor s.model.ε (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    s.model.universal
  have : IsIso s.model.ε := by
    apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts s.model.T s.model.ε
      (W := HomologicalComplex.quasiIso _ (.up ℤ))
    intro P Q z hz
    have : QuasiIso z := hz
    have : QuasiIso ((s.model.E.mapHomologicalComplex (.up ℤ)).map z) := inferInstance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _
      ((s.model.E.mapHomologicalComplex (.up ℤ)).map z)).2 inferInstance
  exact ⟨inferInstance, inferInstance, fun _ ↦ inferInstance⟩

private structure GeneralAdjunctionEvaluation
    {X : Type*} {Y : Type*} {x : Type*} {y : Type*}
    [Category X] [Category Y] [Category x] [Category y] (E : X ⥤ x) (F : Y ⥤ y)
    {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R)
    {l : x ⥤ y} {r : y ⥤ x} (level : l ⊣ r) where
  /-- Evaluation of the left adjoint. -/
  left : L ⋙ F ≅ E ⋙ l
  /-- Evaluation of the right adjoint. -/
  right : R ⋙ E ≅ F ⋙ r
  /-- Unit evaluation. -/
  unit : ∀ A : X,
    E.map (adj.unit.app A) ≫ right.hom.app (L.obj A) ≫
      r.map (left.hom.app A) = level.unit.app (E.obj A)
  /-- Counit evaluation. -/
  counit : ∀ B : Y,
    l.map (right.hom.app B) ≫ level.counit.app (F.obj B) =
      left.inv.app (R.obj B) ≫ F.map (adj.counit.app B)


private theorem evaluation_mate_general
    {X : Type*} {Y : Type*} {Z : Type*} {W : Type*}
    {x : Type*} {y : Type*} {z : Type*} {w : Type*}
    [Category X] [Category Y] [Category Z] [Category W]
    [Category x] [Category y] [Category z] [Category w]
    {E₁ : X ⥤ x} {F₁ : Y ⥤ y} {E₂ : Z ⥤ z} {F₂ : W ⥤ w}
    {L₁ : X ⥤ Y} {R₁ : Y ⥤ X} {L₂ : Z ⥤ W} {R₂ : W ⥤ Z}
    {l₁ : x ⥤ y} {r₁ : y ⥤ x} {l₂ : z ⥤ w} {r₂ : w ⥤ z}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (level₁ : l₁ ⊣ r₁) (level₂ : l₂ ⊣ r₂)
    (A₁ : GeneralAdjunctionEvaluation E₁ F₁ adj₁ level₁)
    (A₂ : GeneralAdjunctionEvaluation E₂ F₂ adj₂ level₂)
    {G : X ⥤ Z} {H : Y ⥤ W} {g : x ⥤ z} {h : y ⥤ w}
    (γ : G ⋙ E₂ ≅ E₁ ⋙ g) (η : H ⋙ F₂ ≅ F₁ ⋙ h)
    (α : TwoSquare G L₁ L₂ H) (a : TwoSquare g l₁ l₂ h)
    (compatible : ∀ A : X,
      F₂.map (α.app A) ≫ η.hom.app (L₁.obj A) ≫ h.map (A₁.left.hom.app A) =
        A₂.left.hom.app (G.obj A) ≫ l₂.map (γ.hom.app A) ≫ a.app (E₁.obj A)) :
    ∀ B : Y,
      E₂.map ((mateEquiv adj₁ adj₂ α).app B) ≫ A₂.right.hom.app (H.obj B) ≫
          r₂.map (η.hom.app B) =
        γ.hom.app (R₁.obj B) ≫ g.map (A₁.right.hom.app B) ≫
          (mateEquiv level₁ level₂ a).app (F₁.obj B) := by
  intro B
  apply (level₂.homEquiv _ _).symm.injective
  change l₂.map _ ≫ level₂.counit.app _ = l₂.map _ ≫ level₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (A₂.left.hom.app (G.obj (R₁.obj B)))).1
  have hleft := A₂.left.hom.naturality ((mateEquiv adj₁ adj₂ α).app B)
  dsimp only [Functor.comp_map] at hleft
  rw [← reassoc_of% hleft]
  have hcounit := level₂.counit.naturality (η.hom.app B)
  dsimp only [Functor.comp_map, Functor.id_map] at hcounit
  rw [hcounit]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (A₂.counit (H.obj B))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← F₂.map_comp_assoc, mateEquiv_counit]
  rw [F₂.map_comp, Category.assoc]
  have hη := η.hom.naturality (adj₁.counit.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  rw [hη]
  rw [mateEquiv_counit]
  have ha := a.naturality (A₁.right.hom.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ha
  rw [reassoc_of% ha]
  rw [← reassoc_of% (compatible (R₁.obj B))]
  rw [← h.map_comp, A₁.counit]
  rw [← h.map_comp, Iso.hom_inv_id_app_assoc]


private theorem projection_inverse_evaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} {t : Theory c l}
    (q : Projections t) {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) (n : ℕ)
    (hq : ∀ P : Derived X B.rings,
      (scalarExtension (a.app (op n)).hom Y).map
          ((t.supportEvaluation B n).iso.inv.app P) ≫
        (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj P) ≫
        (t.evaluationY C n).E.map ((t.q a).app P) ≫
        (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj P) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).iso.hom.app P) =
        (compactScalarMap (a.app (op n)).hom c).app ((t.evaluationX B n).E.obj P))
    (P : Derived X B.rings) :
    (t.evaluationY C n).E.map ((q.system a).inv.app P) ≫
        (t.scalarEvaluationY a n).iso.hom.app ((t.support B).F.obj P) ≫
        (scalarExtension (a.app (op n)).hom Y).map
          ((t.supportEvaluation B n).iso.hom.app P) =
      (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj P) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).iso.hom.app P) ≫
        (q.single B C n n (a.app (op n))).inv.app ((t.evaluationX B n).E.obj P) := by
  let F := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (C.rings.obj (op n))) c
  let i := (scalarExtension (a.app (op n)).hom Y).mapIso
      ((t.supportEvaluation B n).iso.symm.app P) ≪≫
    (t.scalarEvaluationY a n).iso.symm.app ((t.support B).F.obj P) ≪≫
    (t.evaluationY C n).E.mapIso ((q.system a).app P) ≪≫
    (t.supportEvaluation C n).iso.app ((t.scalarX a).model.T.obj P) ≪≫
    F.mapIso ((t.scalarEvaluationX a n).iso.app P)
  have hi : i = (q.single B C n n (a.app (op n))).app ((t.evaluationX B n).E.obj P) := by
    apply Iso.ext
    simpa only [i, F, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
      q.system_hom, q.single_hom] using hq P
  have hh := congrArg (fun z ↦
    (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj P) ≫
      F.map ((t.scalarEvaluationX a n).iso.hom.app P) ≫ z) (congrArg Iso.inv hi)
  dsimp only [i] at hh
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hh
  dsimp only [F] at hh
  erw [F.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc] at hh
  exact hh

private theorem mate_evaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} {t : Theory c l}
    (q : Projections t) (d : Adjoints t q) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ)
    (hq : ∀ P : Derived X B.rings,
      (t.evaluationY C n).E.map ((q.system a).inv.app P) ≫
        (t.scalarEvaluationY a n).iso.hom.app ((t.support B).F.obj P) ≫
        (scalarExtension (a.app (op n)).hom Y).map
          ((t.supportEvaluation B n).iso.hom.app P) =
      (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj P) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).iso.hom.app P) ≫
        (q.single B C n n (a.app (op n))).inv.app ((t.evaluationX B n).E.obj P))
    (M : Derived Y B.rings) :
    (t.evaluationX C n).E.map ((mate q d a).app M) ≫
        (d.theta C n).hom.app ((t.scalarY a).model.T.obj M) ≫
        (d.g C n).map ((t.scalarEvaluationY a n).iso.hom.app M) =
      (t.scalarEvaluationX a n).iso.hom.app ((d.G B).obj M) ≫
        (scalarExtension (a.app (op n)).hom X).map ((d.theta B n).hom.app M) ≫
        (etaleCoefficientQuotientMate (a.app (op n)).hom c (d.adjN B n) (d.adjN C n)
          (q.single B C n n (a.app (op n)))).app ((t.evaluationY B n).E.obj M) := by
  exact evaluation_mate_general (d.adj B) (d.adj C) (d.adjN B n) (d.adjN C n)
    { left := (t.supportEvaluation B n).iso
      right := d.theta B n
      unit := d.unit B n
      counit := d.counit B n }
    { left := (t.supportEvaluation C n).iso
      right := d.theta C n
      unit := d.unit C n
      counit := d.counit C n }
    (t.scalarEvaluationX a n).iso (t.scalarEvaluationY a n).iso
    (.mk _ _ _ _ (q.system a).inv)
    (.mk _ _ _ _ (q.single B C n n (a.app (op n))).inv) hq M

private theorem levels_reflect_iso (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) {M N : Modules W B} (z : M ⟶ N)
    (hz : ∀ n, IsIso ((level W B n).map z)) : IsIso z := by
  let F : Modules W B ⥤ (ℕ × W.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _
  have hcomp : ∀ U, IsIso ((F.map z).app U) := by
    intro U
    obtain ⟨U⟩ := U
    obtain ⟨n, V⟩ := U
    have := hz n
    have hi : IsIso ((((level W B n).map z).hom).app (op V)) := inferInstance
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun x ↦ (z.val.app (op (n, V))) x)
    exact (ConcreteCategory.isIso_iff_bijective
      ((((level W B n).map z).hom).app (op V))).1 hi
  have : IsIso (F.map z) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso z F

private theorem evaluations_reflect_iso (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (e : ∀ n, Evaluation W B n)
    {M N : Derived W B} (z : M ⟶ N)
    (hz : ∀ n, IsIso ((e n).E.map z)) : IsIso z := by
  rw [DerivedCategory.isIso_iff]
  intro i
  apply levels_reflect_iso W B
  intro n
  letI := (e n).additive
  letI := (e n).limits
  letI := (e n).colimits
  have := hz n
  exact (NatIso.isIso_map_iff ((level W B n).mapDerivedCategoryHomologyFunctorIso i) z).2
    (inferInstance : IsIso ((DerivedCategory.homologyFunctor _ i).map ((e n).E.map z)))

private theorem mate_composition {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} {t : Theory c l}
    (q : Projections t) (d : Adjoints t q) {B C D : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings)
    (hcomp : t.q (a ≫ b) = t.path a b) :
    Functor.whiskerLeft (d.G B)
        (associator X (t.scalarX a) (t.scalarX b) (t.scalarX (a ≫ b))).hom ≫
        mate q d (a ≫ b) =
      Functor.whiskerRight (mate q d a) (t.scalarX b).model.T ≫
        Functor.whiskerLeft (t.scalarY a).model.T (mate q d b) ≫
        Functor.whiskerRight
          (associator Y (t.scalarY a) (t.scalarY b) (t.scalarY (a ≫ b))).hom (d.G D) := by
  let ix := associator X (t.scalarX a) (t.scalarX b) (t.scalarX (a ≫ b))
  let iy := associator Y (t.scalarY a) (t.scalarY b) (t.scalarY (a ≫ b))
  have hi : q.system (a ≫ b) =
      Functor.isoWhiskerLeft (t.support B).F iy.symm ≪≫
        Functor.isoWhiskerRight (q.system a) (t.scalarY b).model.T ≪≫
        Functor.isoWhiskerLeft (t.scalarX a).model.T (q.system b) ≪≫
        Functor.isoWhiskerRight ix (t.support D).F := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, q.system_hom,
      Theory.path, ix, iy] using hcomp
  have ht {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings)
      (M : Derived Y B.rings) :
      (t.support C).F.map ((mate q d a).app M) ≫
          (d.adj C).counit.app ((t.scalarY a).model.T.obj M) =
        (q.system a).inv.app ((d.G B).obj M) ≫
          (t.scalarY a).model.T.map ((d.adj B).counit.app M) :=
    mateEquiv_counit (d.adj B) (d.adj C) (.mk _ _ _ _ (q.system a).inv) M
  ext M
  apply ((d.adj D).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hnat := (d.adj D).counit.naturality (iy.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  rw [hnat, ht (a ≫ b) M]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (ht b _)]
  have hnatb := (q.system b).inv.naturality ((mate q d a).app M)
  dsimp only [Functor.comp_map] at hnatb
  rw [reassoc_of% hnatb]
  rw [← Functor.map_comp_assoc, ht a M, Functor.map_comp]
  rw [hi]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  rw [← (t.support D).F.map_comp_assoc, ix.hom_inv_id_app]
  erw [(t.support D).F.map_id, Category.id_comp]
  have hiy := iy.hom.naturality ((d.adj B).counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hiy
  rw [hiy]

private theorem mate_unit {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} {t : Theory c l}
    (q : Projections t) (d : Adjoints t q) (B : Coefficients.{u} l)
    (hunit : ∀ P : Derived X B.rings,
      (t.q (𝟙 B.rings)).app P ≫
        (t.support B).F.map ((unit X B.rings (t.scalarX (𝟙 B.rings))).hom.app P) =
      (unit Y B.rings (t.scalarY (𝟙 B.rings))).hom.app ((t.support B).F.obj P))
    (M : Derived Y B.rings) :
    (mate q d (𝟙 B.rings)).app M ≫
        (d.G B).map ((unit Y B.rings (t.scalarY (𝟙 B.rings))).hom.app M) =
      (unit X B.rings (t.scalarX (𝟙 B.rings))).hom.app ((d.G B).obj M) := by
  apply ((d.adj B).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hnat := (d.adj B).counit.naturality
    ((unit Y B.rings (t.scalarY (𝟙 B.rings))).hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  rw [hnat]
  have ht := mateEquiv_counit (d.adj B) (d.adj B)
    (.mk _ _ _ _ (q.system (𝟙 B.rings)).inv) M
  change (t.support B).F.map ((mate q d (𝟙 B.rings)).app M) ≫ _ = _ at ht
  rw [reassoc_of% ht]
  have hu := (unit Y B.rings (t.scalarY (𝟙 B.rings))).hom.naturality
    ((d.adj B).counit.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  dsimp only [Functor.id_obj, Functor.comp_obj] at hu
  change (q.system (𝟙 B.rings)).inv.app ((d.G B).obj M) ≫ _ = _
  erw [hu]
  rw [← Category.assoc]
  congr 1
  apply (cancel_epi ((q.system (𝟙 B.rings)).hom.app _)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [q.system_hom]
  exact (hunit _).symm

/-- Scalar mates are invertible, evaluate to the fixed finite mates, preserve actual
transitions and adjunction transposes, and obey composition, unit and mixed-square
identities before evaluation. Finite free scalar extension is already exact termwise.
Source: Zheng Constructions 2.26 and 5.15, Proposition 2.29(2), Lemma 5.22
(blueprint: lem-pur-etale-system-scalar-mate-coherence).

Proof, following the node's six steps:
The projection-level evaluation, composition and unit laws are supplied for the fixed
presentation by etaleSystemProjectionPresentationCoherence; the existential projection
construction alone does not specialize to an arbitrary fixed Theory.
1. The normalized scalar adjunctions are those on the ringed sequence topos, with
unit insertion of 1. Apply mateEquiv to the inverse actual projection. Its counit
identity gives the displayed transposition equation and uniquely determines the map.
2. Evaluate that equation using the projection's finite compactScalarMap normalization
and d.counit. The finite adjunction's Hom bijection identifies the result with exactly
etaleCoefficientQuotientMate. The finite-ring clause of quotient normalization makes
it invertible, even for nonflat quotients. Joint conservativity of exact evaluations
then makes the mate invertible on entire systems.
3. The stipulated left-extension Hom chain fixes theta, and d.transition_normalized
is the stated transition-mate normalization. The mate is an actual derived system map;
transpose its strict-transition naturality through the scalar adjunction to obtain
the transition equation below. Evaluation of adjunction transposes follows from the
unit/counit equations in d and the representative-normalized scalar models. In
particular coefficient units/counits and the displayed counit equation evaluate to
the finite ones; this uses the simultaneous models, never faithfulness of evaluation.
4. Invert the actual projection cocycle. Naturality of the outer counits and the
inverse projections transports the canonical tensor associators across the transpose.
This gives the displayed equality of natural transformations, before evaluation.
5. The projection unit and triangle identities give the mate unit equation. In a
commutative mixed quotient/extension square both projection words are the word of the
common composite. Transpose their equality, using the same balanced associators.
The same fixed balanced tensor associators occur in both projection words.
6. A finite basis of each D_n identifies ordinary level extension with a finite direct
sum. It is exact; componentwise exactness makes the system extension exact even when
ranks vary and bases do not respect transitions. It preserves acyclic complexes and
quasi-isomorphisms, so its left-derived comparison is invertible on every complex.
-/
theorem etaleSystemScalarMateCoherence
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime) (_hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) (t : Theory c l) (q : Projections t) (d : Adjoints t q) :
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings), IsIso (mate q d a)) ∧
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (M : Derived Y.left B.rings),
      (t.support C).F.map ((mate q d a).app M) ≫
          (d.adj C).counit.app ((t.scalarY a).model.T.obj M) =
        (q.system a).inv.app ((d.G B).obj M) ≫
          (t.scalarY a).model.T.map ((d.adj B).counit.app M)) ∧
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
      (M : Derived Y.left B.rings),
      (t.evaluationX C n).E.map ((mate q d a).app M) ≫
          (d.theta C n).hom.app ((t.scalarY a).model.T.obj M) ≫
          (d.g C n).map ((t.scalarEvaluationY a n).iso.hom.app M) =
        (t.scalarEvaluationX a n).iso.hom.app ((d.G B).obj M) ≫
          (scalarExtension (a.app (op n)).hom X.left).map ((d.theta B n).hom.app M) ≫
          (etaleCoefficientQuotientMate (a.app (op n)).hom c (d.adjN B n) (d.adjN C n)
            (q.single B C n n (a.app (op n)))).app ((t.evaluationY B n).E.obj M)) ∧
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) {m n : ℕ} (h : n ≤ m)
      (M : Derived Y.left B.rings),
      (scalarExtension (C.rings.map (homOfLE h).op).hom X.left).map
          ((t.evaluationX C m).E.map ((mate q d a).app M)) ≫
        (d.transitionX C).reduction h (t.evaluationX C m) (t.evaluationX C n)
          ((d.G C).obj ((t.scalarY a).model.T.obj M)) =
      (d.transitionX C).reduction h (t.evaluationX C m) (t.evaluationX C n)
          ((t.scalarX a).model.T.obj ((d.G B).obj M)) ≫
        (t.evaluationX C n).E.map ((mate q d a).app M)) ∧
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ),
      CoefficientAdjunctionEvaluation X.left a (t.scalarX a) n
        (t.evaluationX B n) (t.evaluationX C n) (t.scalarEvaluationX a n) ∧
      CoefficientAdjunctionEvaluation Y.left a (t.scalarY a) n
        (t.evaluationY B n) (t.evaluationY C n) (t.scalarEvaluationY a n)) ∧
    (∀ (B : Coefficients.{u} l) (n : ℕ) (P : Derived X.left B.rings)
      (M : Derived Y.left B.rings) (z : (t.support B).F.obj P ⟶ M),
      (t.evaluationX B n).E.map ((d.adj B).homEquiv P M z) ≫
          (d.theta B n).hom.app M =
        (d.adjN B n).homEquiv _ _
          ((t.supportEvaluation B n).iso.inv.app P ≫ (t.evaluationY B n).E.map z)) ∧
    (∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
      Functor.whiskerLeft (d.G B)
          (associator X.left (t.scalarX a) (t.scalarX b) (t.scalarX (a ≫ b))).hom ≫
          mate q d (a ≫ b) =
        Functor.whiskerRight (mate q d a) (t.scalarX b).model.T ≫
          Functor.whiskerLeft (t.scalarY a).model.T (mate q d b) ≫
          Functor.whiskerRight
            (associator Y.left (t.scalarY a) (t.scalarY b) (t.scalarY (a ≫ b))).hom
              (d.G D)) ∧
    (∀ (B : Coefficients.{u} l) (M : Derived Y.left B.rings),
      (mate q d (𝟙 B.rings)).app M ≫
          (d.G B).map ((unit Y.left B.rings (t.scalarY (𝟙 B.rings))).hom.app M) =
        (unit X.left B.rings (t.scalarX (𝟙 B.rings))).hom.app ((d.G B).obj M)) ∧
    (∀ (B C D H : Coefficients.{u} l) (a : B.rings ⟶ C.rings)
      (b : C.rings ⟶ H.rings) (e : B.rings ⟶ D.rings) (v : D.rings ⟶ H.rings),
      a ≫ b = e ≫ v → HEq (path q d a b) (path q d e v)) ∧
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings)
      (_free : ∀ n : ℕ, ∃ r : ℕ, Nonempty
        (Module.Basis (Fin r) (B.rings.obj (op n))
          ((ModuleCat.restrictScalars (a.app (op n)).hom).obj
            (ModuleCat.of (C.rings.obj (op n)) (C.rings.obj (op n)))))),
      (PreservesFiniteLimits (t.scalarX a).model.E ∧
        PreservesFiniteColimits (t.scalarX a).model.E ∧
        ∀ P : CochainComplex (Modules X.left B.rings) ℤ,
          IsIso ((t.scalarX a).model.ε.app P)) ∧
      (PreservesFiniteLimits (t.scalarY a).model.E ∧
        PreservesFiniteColimits (t.scalarY a).model.E ∧
        ∀ P : CochainComplex (Modules Y.left B.rings) ℤ,
          IsIso ((t.scalarY a).model.ε.app P))) := by
  obtain ⟨heval, hcomp, hunit⟩ :=
    etaleSystemProjectionPresentationCoherence k l _hl _hlp X Y f c t
  letI : X.left.Over (Spec (CommRingCat.of k.k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (CommRingCat.of k.k)) := ⟨Y.hom⟩
  letI : f.left.IsOver (Spec (CommRingCat.of k.k)) := ⟨Over.w f⟩
  letI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k.k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  letI : QuasiCompact (X.left ↘ Spec (CommRingCat.of k.k)) :=
    inferInstanceAs (QuasiCompact X.hom)
  letI : LocallyOfFiniteType (Y.left ↘ Spec (CommRingCat.of k.k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  letI : QuasiCompact (Y.left ↘ Spec (CommRingCat.of k.k)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  have hm (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
      (M : Derived Y.left B.rings) :=
    mate_evaluation q d a n
      (projection_inverse_evaluation q a n (heval B C a n)) M
  have hc (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings)
      (b : C.rings ⟶ D.rings) := mate_composition q d a b (hcomp B C D a b)
  refine ⟨?_, ?_, hm, ?_, ?_, ?_, hc, ?_, ?_, ?_⟩
  · intro B C a
    have hcomponents : ∀ M, IsIso ((mate q d a).app M) := by
      intro M
      apply evaluations_reflect_iso X.left C.rings (t.evaluationX C)
      intro n
      letI : Fact l.Prime := ⟨_hl⟩
      letI := B.finite n
      letI := C.finite n
      obtain ⟨qn, hqn, _, _, ρ, _, _, bn, hbn, _⟩ :=
        etaleCoefficientQuotientNormalization k l _hlp f.left c
          (B.rings.obj (op n)) (C.rings.obj (op n)) (B.torsion n) (C.torsion n)
          (a.app (op n)).hom (d.g B n) (d.g C n) (d.adjN B n) (d.adjN C n)
      have hq : qn = q.single B C n n (a.app (op n)) := by
        apply Iso.ext
        exact hqn.trans (q.single_hom B C n n (a.app (op n))).symm
      have hfinite : IsIso (etaleCoefficientQuotientMate (a.app (op n)).hom c
          (d.adjN B n) (d.adjN C n) (q.single B C n n (a.app (op n)))) := by
        rw [← hq, ← hbn]
        infer_instance
      have hz := hm B C a n M
      have hiso : IsIso
          ((t.evaluationX C n).E.map ((mate q d a).app M) ≫
            (d.theta C n).hom.app ((t.scalarY a).model.T.obj M) ≫
            (d.g C n).map ((t.scalarEvaluationY a n).iso.hom.app M)) := by
        rw [hz]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((t.evaluationX C n).E.map ((mate q d a).app M))
        ((d.theta C n).hom.app ((t.scalarY a).model.T.obj M) ≫
          (d.g C n).map ((t.scalarEvaluationY a n).iso.hom.app M))
    exact NatIso.isIso_of_isIso_app _
  · intro B C a M
    exact mateEquiv_counit (d.adj B) (d.adj C) (.mk _ _ _ _ (q.system a).inv) M
  · intro B C a m n h M
    exact reduction_naturality (d.transitionX C) h (t.evaluationX C m)
      (t.evaluationX C n) ((mate q d a).app M)
  · intro B C a n
    exact ⟨scalar_adjunction_evaluation X.left a (t.scalarX a) n
        (t.evaluationX B n) (t.evaluationX C n) (t.scalarEvaluationX a n),
      scalar_adjunction_evaluation Y.left a (t.scalarY a) n
        (t.evaluationY B n) (t.evaluationY C n) (t.scalarEvaluationY a n)⟩
  · exact support_transpose q d
  · intro B M
    exact mate_unit q d B (hunit B) M
  · intro B C D H a b e v h
    have hp {B C D : Coefficients.{u} l} (a : B.rings ⟶ C.rings)
        (b : C.rings ⟶ D.rings) : path q d a b = mate q d (a ≫ b) := by
      dsimp only [path]
      rw [← hc B C D a b]
      ext M
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
        Iso.inv_hom_id_app_assoc]
    rw [hp a b, hp e v]
    exact congr_arg_heq (fun z : B.rings ⟶ H.rings ↦ mate q d z) h
  · intro B C a hf
    exact ⟨finite_free_exact X.left a (t.scalarX a) hf,
      finite_free_exact Y.left a (t.scalarY a) hf⟩

end AlgebraicGeometry.Etale.SystemScalarMate
