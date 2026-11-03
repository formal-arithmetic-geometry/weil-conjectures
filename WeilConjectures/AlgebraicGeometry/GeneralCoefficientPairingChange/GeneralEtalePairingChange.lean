/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientPairingChange.GeneralEtalePairingChangeMaps
public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientPairingChange.GeneralEtaleDirectProjectionChange
public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientPairingChange.GeneralEtaleOpenProjectionChange

/-! # General finite coefficient change of an étale internal-adjunction pairing

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: lem-coef-general-etale-pairing-change).

The statement uses the canonical ordinary étale constructions of
`Sheaf.Paper.GeneralEtalePairingChangeMaps` (blueprint: def-coef-general-etale-pairing-maps):
the compact-support factorization, the ordinary direct-image comparison
`FiniteCoefficientOrdinary.directImageMaps.etale`, the evaluation comparison, and the
exceptional counit, over the fixed derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.GeneralCoefficientPairingChange

/-- The actual direct-image counit field fixes the scalar-unit normalization
of its geometric transpose, entirely in the fixed ordinary model. -/
private theorem scalarPullComparison_unit (φ : A →+* B) (f : Z ⟶ X)
    (K : DerivedCategoryModule A Z) :
    L(upperStar (ModuleCat A) f).map
        ((FiniteCoefficientOrdinary.scalarAdjunction X.smallEtaleTopology φ).unit.app
          (R(lowerStar (ModuleCat A) f).obj K)) ≫
      (leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
        ((scalarExtension φ X).obj (R(lowerStar (ModuleCat A) f).obj K)) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((scalarPullComparison φ f).app (R(lowerStar (ModuleCat A) f).obj K) ≫
          (scalarExtension φ Z).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).counit.app K)) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat A) f).counit.app K ≫
        (FiniteCoefficientOrdinary.scalarAdjunction Z.smallEtaleTopology φ).unit.app K := by
  have h := directImageMaps.etale_counit φ f K
  have hm := mateEquiv_counit_symm
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat B) f)
    (TwoSquare.mk _ _ _ _ (directImageMaps.etale φ f)) K
  change L(upperStar (ModuleCat B) f).map ((directImageMaps.etale φ f).app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat B) f).counit.app
        ((scalarExtension φ Z).obj K) =
    (scalarPullComparison φ f).app (R(lowerStar (ModuleCat A) f).obj K) ≫
      (scalarExtension φ Z).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).counit.app K) at hm
  rw [hm] at h
  exact h

private def pullComparison (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z) :
    scalarExtension φ X ⋙ L(upperStar (ModuleCat B) g) ⋙
        L(upperStar (ModuleCat B) j) ⟶
      L(upperStar (ModuleCat A) g) ⋙ L(upperStar (ModuleCat A) j) ⋙ scalarExtension φ S :=
  Functor.whiskerRight (scalarPullComparison φ g) L(upperStar (ModuleCat B) j) ≫
    Functor.whiskerLeft L(upperStar (ModuleCat A) g) (scalarPullComparison φ j)

private theorem projection_change (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    [IsOpenImmersion j] (K : DerivedCategoryModule A S) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat B) X).map (compactComparison φ g j K)).app
        ((scalarExtension φ X).obj T) ≫
      projection B g j ((scalarExtension φ S).obj K) ((scalarExtension φ X).obj T) ≫
      (shriek B g j).map
        (((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
            ((pullComparison φ g j).app T) ≫
          (tensorComparison S φ K
            (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))).hom) =
    (tensorComparison X φ ((shriek A g j).obj K) T).hom ≫
      (scalarExtension φ X).map (projection A g j K T) ≫
      compactComparison φ g j
        (((derivedTensor (ModuleCat A) S).obj K).obj
          (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))) := by
  let RB := R(lowerStar (ModuleCat B) g)
  let TB := derivedTensor (ModuleCat B) X
  let UB := derivedTensor (ModuleCat B) Z
  let JB := derivedExtension (A := B) j
  let FL := (scalarExtension φ S).obj K
  let q := (fixedOpenScalarExtension φ j).hom.app K
  let σ := (scalarPullComparison φ g).app T
  have hp := NatTrans.congr_app
    ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).naturality q)
    ((scalarExtension φ X).obj T)
  change (TB.map (RB.map q)).app ((scalarExtension φ X).obj T) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).app (JB.obj FL)).app
        ((scalarExtension φ X).obj T) =
    ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).app
        ((scalarExtension φ Z).obj ((derivedExtension (A := A) j).obj K))).app
        ((scalarExtension φ X).obj T) ≫
      RB.map ((UB.map q).app
        (L(upperStar (ModuleCat B) g).obj ((scalarExtension φ X).obj T))) at hp
  let eb := (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app FL
  have hopen := eb.naturality σ
  change (UB.obj (JB.obj FL)).map σ ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app FL).app
        ((scalarExtension φ Z).obj (L(upperStar (ModuleCat A) g).obj T)) =
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app FL).app
        (L(upperStar (ModuleCat B) g).obj ((scalarExtension φ X).obj T)) ≫
      JB.map (((derivedTensor (ModuleCat B) S).obj FL).map
        (L(upperStar (ModuleCat B) j).map σ)) at hopen
  have hq := (UB.map q).naturality σ
  have ho := openProjection_change φ j K (L(upperStar (ModuleCat A) g).obj T)
  have hd := directProjection_change φ g ((derivedExtension (A := A) j).obj K) T
  have hn := (directImageMaps.etale φ g).naturality
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app K).app
      (L(upperStar (ModuleCat A) g).obj T))
  have hh := projectionPasting RB hp hq hopen ho hd hn
  simpa only [RB, TB, UB, JB, FL, q, σ, scalarExtension,
    derivedTensorWhiskeringRightLeftDerivedUpperStar,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    compactComparison, projection, pullComparison, shriek, Functor.comp_obj, Functor.id_obj,
    Functor.comp_map, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using hh

private theorem ordinaryComparison_counit (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : DerivedCategoryModule A S) :
    L(upperStar (ModuleCat B) j).map
        (L(upperStar (ModuleCat B) g).map (ordinaryComparison φ g j Q)) ≫
        ordinaryCounit B g j ((scalarExtension φ S).obj Q) =
      (pullComparison φ g j).app ((star A g j).obj Q) ≫
        (scalarExtension φ S).map (ordinaryCounit A g j Q) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat A) g
  let a' := derivedUpperStarLowerStarAdjunction (ModuleCat B) g
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat A) j
  let b' := derivedUpperStarLowerStarAdjunction (ModuleCat B) j
  let α := TwoSquare.mk _ _ _ _ (scalarPullComparison φ g)
  let β := TwoSquare.mk _ _ _ _ (scalarPullComparison φ j)
  have h := mateEquiv_counit (a.comp b) (a'.comp b') (α ≫ᵥ β) Q
  rw [mateEquiv_hcomp] at h
  simpa only [a, a', b, b', α, β, ordinaryComparison, ordinaryCounit,
    scalarPullComparison, Equiv.apply_symm_apply, pullComparison,
    TwoSquare.hComp, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, TwoSquare.mk,
    Functor.associator_hom_app, Functor.associator_inv_app,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc] using h

private theorem compactComparison_naturality (φ : A →+* B)
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    {K K' : DerivedCategoryModule A S} (f : K ⟶ K') :
    (scalarExtension φ X).map ((shriek A g j).map f) ≫ compactComparison φ g j K' =
      compactComparison φ g j K ≫
        (shriek B g j).map ((scalarExtension φ S).map f) := by
  unfold compactComparison
  dsimp only [shriek, Functor.comp_map]
  have hn := (directImageMaps.etale φ g).naturality
    ((derivedExtension (A := A) j).map f)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  erw [(fixedOpenScalarExtension φ j).hom.naturality]
  rfl

private theorem evaluationComparison_transpose (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    ((derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ T).obj K)).homEquiv
      _ _).symm (evaluationComparison φ T K M) =
      (tensorComparison T φ K _).hom ≫
        (scalarExtension φ T).map
          ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app M) := by
  unfold evaluationComparison
  exact Equiv.symm_apply_apply _ _

private theorem innerEvaluation_change (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    (K N : DerivedCategoryModule A S) (N' : DerivedCategoryModule B S)
    (b : (scalarExtension φ S).obj N ⟶ N') :
    let Q := ((derivedHom (ModuleCat A) S).obj (op K)).obj N
    let Q' := ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).obj N'
    let h := ordinaryComparison φ g j Q ≫ (star B g j).map
      (evaluationComparison φ S K N ≫
        ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).map b)
    ((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
        (L(upperStar (ModuleCat B) j).map (L(upperStar (ModuleCat B) g).map h)) ≫
      (((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
          (ordinaryCounit B g j Q') ≫
        (derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ S).obj K)).counit.app
          N') =
      ((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
          ((pullComparison φ g j).app ((star A g j).obj Q)) ≫
        (tensorComparison S φ K
          (L(upperStar (ModuleCat A) j).obj
            (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)))).hom ≫
        (scalarExtension φ S).map
          (((derivedTensor (ModuleCat A) S).obj K).map (ordinaryCounit A g j Q) ≫
            (derivedTensorHomAdjunction (ModuleCat A) K).counit.app N) ≫ b := by
  dsimp only
  let Q := ((derivedHom (ModuleCat A) S).obj (op K)).obj N
  let Q' := ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).obj N'
  let w := evaluationComparison φ S K N ≫
    ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).map b
  let PB := L(upperStar (ModuleCat B) g) ⋙ L(upperStar (ModuleCat B) j)
  let TB := (derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)
  let a := (derivedUpperStarLowerStarAdjunction (ModuleCat B) g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat B) j)
  have hc : PB.map (ordinaryComparison φ g j Q ≫ (star B g j).map w) ≫
      ordinaryCounit B g j Q' =
    (pullComparison φ g j).app ((star A g j).obj Q) ≫
      (scalarExtension φ S).map (ordinaryCounit A g j Q) ≫ w := by
    rw [PB.map_comp, Category.assoc]
    erw [a.counit_naturality w]
    change PB.map (ordinaryComparison φ g j Q) ≫
        ordinaryCounit B g j ((scalarExtension φ S).obj Q) ≫ w = _
    dsimp only [PB, Functor.comp_map]
    rw [reassoc_of% ordinaryComparison_counit]
    rfl
  have hew : TB.map w ≫
      (derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ S).obj K)).counit.app N' =
      (tensorComparison S φ K Q).hom ≫
        (scalarExtension φ S).map
          ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app N) ≫ b := by
    change ((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map w ≫
      (derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ S).obj K)).counit.app
        N' = _
    erw [← Adjunction.homEquiv_counit]
    unfold w
    rw [Adjunction.homEquiv_naturality_right_symm, evaluationComparison_transpose]
    simp only [Category.assoc]
    rfl
  change TB.map (PB.map (ordinaryComparison φ g j Q ≫ (star B g j).map w)) ≫
    (TB.map (ordinaryCounit B g j Q') ≫ _) = _
  rw [← Category.assoc, ← TB.map_comp, hc]
  simp only [TB.map_comp, Category.assoc]
  rw [hew]
  have hn := (GeneralCoefficientTensor.existsUnique φ S).choose_spec.1.2.1 K
    (ordinaryCounit A g j Q)
  erw [reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- The parameterized transpose formula for the specified evaluation comparison. -/
private theorem evaluationComparison_formula (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    evaluationComparison φ T K M =
      (derivedTensorHomAdjunction₂ (ModuleCat B) T).homEquiv
        ((tensorComparison T φ K _).hom ≫
          (scalarExtension φ T).map
            (((derivedTensorHomAdjunction₂ (ModuleCat A) T).adj K).counit.app M)) := by
  rfl

private theorem pairing_change [Finite A] [Finite B] (φ : A →+* B)
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M))
    (_hb : CounitCompatible φ g j M b) : PairingChangeEquation φ g j L M b := by
  let a := derivedTensorHomAdjunction₂ (ModuleCat A) X
  let a' := derivedTensorHomAdjunction₂ (ModuleCat B) X
  let F := scalarExtension φ X
  let G := scalarExtension φ S
  let E' := shriek B g j
  let N := (exceptional A g j).obj M
  let Q := ((derivedHom (ModuleCat A) S).obj (op L)).obj N
  let N' := (exceptional B g j).obj (F.obj M)
  let e := ((derivedTensor (ModuleCat A) S).obj L).map
      (ordinaryCounit A g j
        (((derivedHom (ModuleCat A) S).obj (op L)).obj
          ((derivedRestriction j).obj (R(lowerStar (ModuleCat A) g).rightAdjoint.obj M)))) ≫
    (derivedTensorHomAdjunction (ModuleCat A) L).counit.app
      ((derivedRestriction j).obj (R(lowerStar (ModuleCat A) g).rightAdjoint.obj M))
  unfold PairingChangeEquation
  as_aux_lemma =>
    rw [internalAdjunction_formula B g j ((scalarExtension φ S).obj L)
        ((scalarExtension φ X).obj M),
      internalAdjunction_formula A g j L M,
      evaluationComparison_formula φ X ((shriek A g j).obj L) M]
    as_aux_lemma =>
      apply pairingTranspose (derivedTensor (ModuleCat B) X)
        (derivedHom (ModuleCat B) X) (derivedTensorHomAdjunction₂ (ModuleCat B) X)
        (K := (scalarExtension φ X).obj ((shriek A g j).obj L))
        (K' := (shriek B g j).obj ((scalarExtension φ S).obj L))
        (U := (star B g j).obj
          (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).obj
            ((exceptional B g j).obj ((scalarExtension φ X).obj M))))
        (U' := (scalarExtension φ X).obj
          (((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M))
        (M := (scalarExtension φ X).obj M)
      as_aux_lemma =>
        dsimp only [shriek, Functor.comp_obj, Functor.id_obj]
        rw [reassoc_of% (projection_naturality B g j ((scalarExtension φ S).obj L) _)]
        as_aux_lemma =>
          let PB := L(upperStar (ModuleCat B) g) ⋙ L(upperStar (ModuleCat B) j)
          let UB := (derivedTensor (ModuleCat B) S).obj (G.obj L)
          let Q' := ((derivedHom (ModuleCat B) S).obj (op (G.obj L))).obj N'
          let h := ordinaryComparison φ g j Q ≫ (star B g j).map
            (evaluationComparison φ S L N ≫
              ((derivedHom (ModuleCat B) S).obj (op (G.obj L))).map b.hom)
          let eB := UB.map (ordinaryCounit B g j Q') ≫
            (derivedTensorHomAdjunction (ModuleCat B) (G.obj L)).counit.app N'
          have hi : UB.map (PB.map h) ≫ eB =
              UB.map ((pullComparison φ g j).app ((star A g j).obj Q)) ≫
                (tensorComparison S φ L
                  (L(upperStar (ModuleCat A) j).obj
                    (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)))).hom ≫
                G.map e ≫ b.hom := innerEvaluation_change φ g j L N N' b.hom
          have hi' := congrArg E'.map hi
          simp only [E'.map_comp] at hi'
          dsimp only [E', shriek, Functor.comp_map, UB, PB, G, h, eB, Q', N', F, Q, N] at hi'
          dsimp only [shriek, star, exceptional, Functor.comp_map, Functor.comp_obj] at hi' ⊢
          rw [reassoc_of% hi']
          as_aux_lemma =>
            have hp := projection_change φ g j L ((star A g j).obj Q)
            dsimp only [E', shriek, Functor.comp_map, G, F, Q, N] at hp
            dsimp only [shriek, star, exceptional, Functor.comp_map, Functor.comp_obj] at hp
            simp only [Functor.map_comp] at hp
            rw [reassoc_of% hp]
            as_aux_lemma =>
              have hμ : GeneralCoefficientTensor.Canonical φ X (tensorComparison X φ) := by
                unfold tensorComparison GeneralCoefficientTensor.comparison
                exact (GeneralCoefficientTensor.existsUnique φ X).choose_spec.1
              rw [reassoc_of% (hμ.2.1 _ _)]
              simp only [← (scalarExtension φ X).map_comp]
              rw [counitTranspose]
              have hn := compactComparison_naturality φ g j e
              dsimp only [Q, N, star, exceptional, shriek, Functor.comp_map,
                Functor.comp_obj, Functor.id_obj] at hn
              dsimp only [CounitCompatible, shriek, Functor.comp_map, Functor.comp_obj] at _hb
              have hc := counitPasting (scalarExtension φ X)
                (projection A g j L ((star A g j).obj Q))
                ((shriek A g j).map e) (counit A g j M)
                _ _ _ _ _ hn _hb
              dsimp only [Q, N, star, exceptional, shriek, Functor.comp_map,
                Functor.comp_obj] at hc
              exact congrArg (fun z ↦
                (tensorComparison X φ ((shriek A g j).obj L)
                  ((star A g j).obj Q)).hom ≫ z) hc

/-- Arbitrary finite coefficient change preserves the specified étale internal-adjunction
pairing.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: lem-coef-general-etale-pairing-change).

Proof. Put `T = R s_* Q`, `N' = s_B^! F_X M`, `Q' = H_B(F_S L, N')`, `w = H_B(1, b) u` and
`d = R s_{*,B}(w) c_{s,Q}`; write `μ` for the K-flat-normalized tensor comparison, `λ` for the
pullback/scalar comparison, `P_R` for the first pairing arrow and `h_A = ev_A (α_A ⊗ 1)`.
1. Use `c_g` on all derived objects as the counit-defined scalar mate and
   `q_s = R g_*(q_j) c_g` as a natural transformation; on the constructible inputs these are
   the comparisons of the statement.
2. Paste the direct scalar/projection square for `g` at `(V, j_! L)` with `R g_*` of the
   ordered open square for `j` at `(g^* V, L)`; scalar-mate naturality and the
   compactification pullback equation give
   `s_!(τ_V) q_s F_X(P_A(V, L)) μ_X = P_B(F_X V, F_S L)(1 ⊗ q_{s,L})`.
3. The defining transpose of `c_{s,Q}` and counit naturality give
   `α_{B,Q'} s_B^* d = w F_S α_A λ_T`.
4. The defining transpose of `u` and naturality of evaluation in `b` give
   `ev_B (w ⊗ 1) = b F_S ev_A μ_S(Q, L)`.
5. Substituting 3 and 4 and naturality of `μ_S` give `h_B (s_B^* d ⊗ 1) τ_T = b F_S h_A`.
6. The tensor--Hom transpose of the left side is `ε_B s_!(h_B) P_B(T', F_S L)(d ⊗ q_{s,L})`;
   naturality of `P_B`, Step 2 at `V = T` and Step 5 rewrite it as
   `ε_B s_!(b F_S h_A) q_s F_X P_A(T, L) μ_X`.
7. Naturality of `q_s` along `h_A` and the assumed counit equation `_hb` turn this into
   `F_X(ε_A s_!(h_A) P_A(T, L)) μ_X`, the scalar extension of the transpose of `I_A`.
8. By the defining transpose of `v` and naturality of `μ_X`, the right side has the same
   transpose; injectivity of the tensor--Hom hom equivalence gives the equality. No
   invertibility of `v` is used.
-/
theorem generalEtalePairingChange
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (_hell : IsUnit (ell : k))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (_hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    (_hB : ∃ r : ℕ, (ell ^ r : B) = 0)
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) (L : DerivedCategoryModule A S)
    (_hM : DerivedCategory.isBoundedConstructible A X M)
    (_hMtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b M)
    (_hL : DerivedCategory.isBoundedConstructible A S L)
    (_hLtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A S a b L)
    (_hN : DerivedCategory.isBoundedConstructible A S
      ((exceptional A g j).obj M))
    (_hNtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A S a b
      ((exceptional A g j).obj M))
    (_hQ : DerivedCategory.isBoundedConstructible A S
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))
    (_hQtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A S a b
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M))
    (_hb : CounitCompatible φ g j M b) :
    PairingChangeEquation φ g j L M b := by
  have _hk := hk
  exact pairing_change φ g j L M b _hb

end AlgebraicGeometry.Etale.GeneralCoefficientPairingChange
