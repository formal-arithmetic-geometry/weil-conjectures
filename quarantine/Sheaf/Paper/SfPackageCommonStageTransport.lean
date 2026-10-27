/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcIdempotentCompleteTriangulation
import Sheaf.Paper.SfCoefficientCoherentInverse
import Mathlib.CategoryTheory.Idempotents.Basic

/-! # Common-stage descent transported between coefficient presentations

Source: blueprint, sec-six-functors/sk-thm-sf-package, clause (1), and the six-step
transport argument in the DAG (blueprint: lem-sf-package-common-stage-transport).

The functor and transformation constructions are the existing literal pair-category
constructions. The transported PBC family's scalar comparison is fixed by the mixed
scalar square and the inverse-equivalence unit, including repeated coefficient fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem map_heq {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {X Y X' Y' : A} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private abbrev comparisonExact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ m : ℕ, topologicalKrullDim T ≤ (m : WithBot ℕ∞))]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (J : FdCoefficientComparison l Ω T)
    (hJ : ∀ E : Padic.FiniteCoefficientFields l Ω, (J.family.Φ E).IsTriangulated) :
    StageSystem.CoherentExactMorphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out) where
  base := J.family
  additive E := by
    have := hJ E
    infer_instance
  commShift := J.finite_shift
  betaCommShift := J.scalar_shift
  triangulated := hJ


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev transportedFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T S : Scheme.{u}) [IsNoetherian T] [IsNoetherian S]
    [dT : Fact (∃ m : ℕ, topologicalKrullDim T ≤ (m : WithBot ℕ∞))]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    [dS : Fact (∃ m : ℕ, topologicalKrullDim S ≤ (m : WithBot ℕ∞))]
    [iS : Fact (∀ t : S, IsUnit (l : S.presheaf.stalk t))]
    (H : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω T dT.out iT.out)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T))
    (F : StageSystem.CoherentExactMorphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω S))
    (J : FdCoefficientComparison l Ω S)
    (hJ : ∀ E : Padic.FiniteCoefficientFields l Ω, (J.family.Φ E).IsTriangulated) :
    StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω T dT.out iT.out)
      (pbcScalarSystem l Ω S dS.out iS.out) := by
  letI := H.commShift
  letI := F.commShift
  let J' := comparisonExact l Ω S J hJ
  refine
    { base := H.base.comp (F.base.comp J.family)
      additive := ?_
      commShift := fun E ↦ by
        change (H.base.Φ E ⋙ F.base.Φ E ⋙ J.family.Φ E).CommShift ℤ
        infer_instance
      betaCommShift := ?_
      triangulated := ?_ }
  · intro E
    have := H.additive E
    have := F.additive E
    have := J'.additive E
    change (H.base.Φ E ⋙ F.base.Φ E ⋙ J.family.Φ E).Additive
    infer_instance
  · intro E L h
    have := H.betaCommShift h
    have := F.betaCommShift h
    have := J.scalar_shift h
    dsimp only [StageSystem.Morphism.comp, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  · intro E
    have := H.triangulated E
    have := F.triangulated E
    have := J'.triangulated E
    change (H.base.Φ E ⋙ F.base.Φ E ⋙ J.family.Φ E).IsTriangulated
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def postcomposeInverseUnit
    {I : Type*} [Preorder I]
    {A B V : I → Type*} [∀ i, Category* (A i)] [∀ i, Category* (B i)]
    [∀ i, Category* (V i)]
    {S : StageSystem A} {R : StageSystem B} {U : StageSystem V}
    (J : StageSystem.Morphism S R) (H : StageSystem.Morphism R S)
    (ν : StageSystem.Morphism.Hom (J.comp H) (StageSystem.Morphism.id S))
    (Q : StageSystem.Morphism S U) :
    StageSystem.Morphism.Hom (J.comp (H.comp Q)) Q where
  τ E := Functor.whiskerRight (ν.τ E) (Q.Φ E)
  comm {i j} h K := by
    have hν := ν.comm h K
    simp only [StageSystem.Morphism.id_β_hom_app,
      StageSystem.Morphism.comp_β_hom_app] at hν
    dsimp only [StageSystem.Morphism.id_Φ, Functor.id_obj,
      StageSystem.Morphism.comp_Φ, Functor.comp_obj] at hν
    erw [Category.comp_id] at hν
    change (U.T h).map ((Q.Φ i).map ((ν.τ i).app K)) ≫ (Q.β h).hom.app K = _
    erw [(Q.β h).hom.naturality]
    simp only [Functor.comp_map]
    erw [hν, Functor.map_comp, Functor.map_comp]
    simp only [Functor.whiskerRight_app, StageSystem.Morphism.comp_β_hom_app,
      Functor.comp_obj, Category.assoc]
    rfl

/-- Exact descent, compatible transformations and their equations, comparison with
conjugated PBC descent, and retract closure on the literal common-stage categories.
Source: functor-package clause (1), returned steps 9--10
(blueprint: lem-sf-package-common-stage-transport).

Proof:
1. Apply pbcIdempotentCompleteTriangulation to the PBC categories. Transport along
J inverse using triangulatedEquivalenceTransfer. The coefficient comparison identifies
both shifts and both distinguished classes with the prescribed common-stage data.
Finite-stage inclusions are exact because their composites with J are the PBC inclusions
composed with the exact finite comparisons. Lift a splitting of J(e) through full
faithfulness to split each idempotent e inside the literal category.
2. For each finite comparison J, take its specified inverse H, unit eta and counit
 epsilon. Full faithfulness specifies the inverse scalar comparison h by
J(h) = epsilon followed by P(epsilon inverse) followed by j inverse. Applying J to
the tower equation reduces it, by naturality and cancellation of epsilon, to the j
cocycle. Repeated fields and shifts give the unit and shift equations.
3. Set G_E = H_T,E followed by Phi_E followed by J_S,E. Its scalar comparison is
j_S inverse, then beta, then h_T inverse. Naturality and the three cocycle equations
prove the unit, tower and shift equations. Equivalently it is the unique comparison
making the mixed scalar square commute with the inverse-unit components stated below.
4. Apply pbcDescentFunctors to G. Transport every scalar-compatible transformation
by the same finite equivalences; its mixed square follows from naturality of the outer
factors and the original scalar square. Transformations and equations descend on PBC.
5. At X=(E,K), use J_S Phi_E(eta_T,K) to compare J_S(E,Phi_E K) with G J_T X.
Conjugate the PBC arrow action by these object isomorphisms and lift through faithful J_S.
Units, counits and triangle identities cancel to leave beta followed by Phi_M(u)
followed by beta inverse. Thus this is the existing literal functor F.base.functor,
with exactly its object and representative formulas. The comparison is natural and
exactness follows from that of the three factors and the comparison equivalences.
6. Lift the descended transformation by the same conjugation. Its finite component
is tau_E,K by naturality of eta. Faithfulness reflects all compatible equations,
including identity and composition, as recorded by DescentSpec. No scalar transition
is assumed fully faithful and no Karoubi objects are introduced. -/
theorem sfPackageCommonStageTransport
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E₀ : Type u) [Field E₀] [Algebra (Padic C.l) E₀]
    [FiniteDimensional (Padic C.l) E₀] (n : ℕ) (hn : 1 ≤ n)
    (_operations : SixFunctorOperationDatum D C E₀ n hn)
    (Ω : Type w) [Field Ω] [Algebra (Padic C.l) Ω] [IsAlgClosure (Padic C.l) Ω]
    (T S : SixFunctorSpace D) [IsSeparated T.obj.hom] [IsSeparated S.obj.hom]
    [IsNoetherian T.obj.left] [IsNoetherian S.obj.left]
    [dT : Fact (∃ m : ℕ, topologicalKrullDim T.obj.left ≤ (m : WithBot ℕ∞))]
    [iT : Fact (∀ t : T.obj.left, IsUnit (C.l : T.obj.left.presheaf.stalk t))]
    [dS : Fact (∃ m : ℕ, topologicalKrullDim S.obj.left ≤ (m : WithBot ℕ∞))]
    [iS : Fact (∀ s : S.obj.left, IsUnit (C.l : S.obj.left.presheaf.stalk s))]
    (JT : FdCoefficientComparison C.l Ω T.obj.left)
    (JS : FdCoefficientComparison C.l Ω S.obj.left)
    (F : StageSystem.CoherentExactMorphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω T.obj.left)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω S.obj.left)) :
    StageSystem.Morphism.DescentSpec F.base ∧
      (∃ HT : ∀ E : Padic.FiniteCoefficientFields C.l Ω,
        GeneralAlgebraicallyClosedCoefficients.Stage C.l Ω T.obj.left E ≌
          pbcStageCategory C.l Ω T.obj.left E,
        (∀ E : Padic.FiniteCoefficientFields C.l Ω, (HT E).functor = JT.family.Φ E) ∧
        ∃ G : StageSystem.CoherentExactMorphism
          (pbcScalarSystem C.l Ω T.obj.left dT.out iT.out)
          (pbcScalarSystem C.l Ω S.obj.left dS.out iS.out),
          (∀ E : Padic.FiniteCoefficientFields C.l Ω,
            G.base.Φ E = (HT E).inverse ⋙ F.base.Φ E ⋙ JS.family.Φ E) ∧
          (∃ τ : StageSystem.Morphism.Hom (JT.family.comp G.base) (F.base.comp JS.family),
            (∀ E : Padic.FiniteCoefficientFields C.l Ω, IsIso (τ.τ E)) ∧
            ∀ (E : Padic.FiniteCoefficientFields C.l Ω)
              (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l Ω T.obj.left E),
              HEq ((τ.τ E).app K)
                ((JS.family.Φ E).map
                  ((F.base.Φ E).map ((HT E).unitIso.inv.app K)))) ∧
          StageSystem.Morphism.DescentSpec G.base ∧
          Nonempty (F.base.functor ⋙ JS.equivalence.functor ≅
            JT.equivalence.functor ⋙ G.base.functor)) ∧
      (IsTriangulated (generalAlgebraicallyClosedConstructibleCategory C.l Ω T.obj.left) ∧
        IsIdempotentComplete (generalAlgebraicallyClosedConstructibleCategory C.l Ω T.obj.left) ∧
        ∀ E : Padic.FiniteCoefficientFields C.l Ω,
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := Ω) (Y := T.obj.left) E).IsTriangulated) ∧
      (IsTriangulated (generalAlgebraicallyClosedConstructibleCategory C.l Ω S.obj.left) ∧
        IsIdempotentComplete (generalAlgebraicallyClosedConstructibleCategory C.l Ω S.obj.left) ∧
        ∀ E : Padic.FiniteCoefficientFields C.l Ω,
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := Ω) (Y := S.obj.left) E).IsTriangulated) := by
  classical
  obtain ⟨HT, hHT, H, hH, ν, hνiso, hν⟩ :=
    (sfCoefficientCoherentInverse C.l Ω T.obj.left JT).2
  have hJS := (sfCoefficientCoherentInverse C.l Ω S.obj.left JS).1
  let G := transportedFamily C.l Ω T.obj.left S.obj.left H F JS hJS
  let τ : StageSystem.Morphism.Hom (JT.family.comp G.base) (F.base.comp JS.family) :=
    postcomposeInverseUnit JT.family H.base ν (F.base.comp JS.family)
  have hτiso (E : Padic.FiniteCoefficientFields C.l Ω) : IsIso (τ.τ E) := by
    have := hνiso E
    change IsIso (Functor.whiskerRight (ν.τ E)
      (F.base.Φ E ⋙ JS.family.Φ E))
    exact (Functor.isoWhiskerRight (asIso (ν.τ E))
      (F.base.Φ E ⋙ JS.family.Φ E)).isIso_hom
  have hτ (E : Padic.FiniteCoefficientFields C.l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l Ω T.obj.left E) :
      HEq ((τ.τ E).app K)
        ((JS.family.Φ E).map ((F.base.Φ E).map ((HT E).unitIso.inv.app K))) := by
    dsimp [τ, postcomposeInverseUnit]
    have hsource : (H.base.Φ E).obj ((JT.family.Φ E).obj K) =
        (HT E).inverse.obj ((HT E).functor.obj K) := by rw [hH E, hHT E]
    exact map_heq (JS.family.Φ E) (congrArg (F.base.Φ E).obj hsource) rfl
      (map_heq (F.base.Φ E) hsource rfl (hν E K))
  have hG := pbcDescentFunctors C.l Ω T.obj.left S.obj.left G
  have hpair : Nonempty (F.base.functor ⋙ JS.equivalence.functor ≅
      JT.equivalence.functor ⋙ G.base.functor) := by
    have := StageSystem.Morphism.isIso_descNatTrans τ hτiso
    rw [JS.pair_functor, JT.pair_functor]
    exact ⟨(StageSystem.Morphism.functorCompIso F.base JS.family).symm ≪≫
      (asIso (StageSystem.Morphism.descNatTrans τ)).symm ≪≫
      StageSystem.Morphism.functorCompIso JT.family G.base⟩
  have hF : StageSystem.Morphism.DescentSpec F.base := by
    obtain ⟨e⟩ := hpair
    obtain ⟨sG, htG⟩ := hG.1.2
    let := sG
    have := htG
    have := JT.pair_exact
    have := JS.pair_exact
    let := Functor.CommShift.ofComp e ℤ
    have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
    have : F.base.functor.IsTriangulated :=
      (Functor.isTriangulated_iff_comp_right e).2 inferInstance
    refine ⟨⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro K L M hK hL u
      exact F.base.functor_map_mkHom hK hL u
    · intro A B α K
      exact StageSystem.Morphism.descNatTrans_app α K
    · intro A B α α' h
      ext K
      exact congrArg ((GeneralAlgebraicallyClosedCoefficients.stageSystem
        C.l Ω S.obj.left).ι K.stage).map (h K.stage K.obj)
    · exact StageSystem.Morphism.descNatTrans_id
    · intro A B V α β
      exact StageSystem.Morphism.descNatTrans_comp α β
  have hclosed (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ m : ℕ, topologicalKrullDim W ≤ (m : WithBot ℕ∞))]
      [Fact (∀ t : W, IsUnit (C.l : W.presheaf.stalk t))]
      (J : FdCoefficientComparison C.l Ω W) :
      IsTriangulated (generalAlgebraicallyClosedConstructibleCategory C.l Ω W) ∧
        IsIdempotentComplete (generalAlgebraicallyClosedConstructibleCategory C.l Ω W) ∧
        ∀ E : Padic.FiniteCoefficientFields C.l Ω,
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := Ω) (Y := W) E).IsTriangulated := by
    exact ⟨inferInstance,
      CategoryTheory.Idempotents.Equivalence.isIdempotentComplete J.equivalence.symm
        (pbcIdempotentCompleteTriangulation C.l Ω W).2.2.2.2.1,
      fun E ↦ inferInstance⟩
  refine ⟨hF, ⟨HT, hHT, G, ?_, ⟨τ, hτiso, hτ⟩, hG, hpair⟩,
    hclosed T.obj.left JT, hclosed S.obj.left JS⟩
  intro E
  change H.base.Φ E ⋙ F.base.Φ E ⋙ JS.family.Φ E = _
  rw [hH E]

end WeilConjectures
