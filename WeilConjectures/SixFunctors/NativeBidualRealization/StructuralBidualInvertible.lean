/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeBidualRealization.NativeBidualEvaluationRealization
import WeilConjectures.SixFunctors.NativeBidualRealization.StructuralDualizingIdentification
import Mathlib.CategoryTheory.Yoneda

/-! # Invertibility of the common-stage structural evaluation transpose

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, paragraph 1,
and sk-prop-sf-biduality-general.proof.md, coefficient transports paragraph.
(blueprint: lem-sf-structural-evaluation-bidual-invertible).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.AdicQbarRealization WeilConjectures.NativeExceptionalForgetful
open WeilConjectures.NativeDualRealization WeilConjectures.NativeBidualRealization

namespace WeilConjectures.NativeBidualRealization

private theorem tensor_comp {B : Type*} [Category B] (T : B × B ⥤ B)
    {X Y Z X' Y' Z' : B} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
    T.map (Prod.mkHom (f ≫ g) (f' ≫ g')) =
      T.map (Prod.mkHom f f') ≫ T.map (Prod.mkHom g g') :=
  T.map_comp (Prod.mkHom f f') (Prod.mkHom g g')

/-- A fully faithful contravariant Hom functor makes the actual transpose reflexive.
The proof uses only the two representing bijections and the naturality of evaluation. -/
private theorem bidual_iso_of_fullyFaithful
    {B E : Type*} [Category B] [Category E]
    (F : Bᵒᵖ ⥤ B) (ff : F.FullyFaithful) (V : B ⥤ E)
    (T : E × E ⥤ E) (s : ∀ P Q : E, T.obj (P, Q) ≅ T.obj (Q, P))
    (hs : ∀ {P P' Q Q' : E} (f : P ⟶ P') (g : Q ⟶ Q'),
      T.map (Prod.mkHom f g) ≫ (s P' Q').hom =
        (s P Q).hom ≫ T.map (Prod.mkHom g f))
    (W : E) (ev : ∀ K : B, T.obj (V.obj (F.obj (op K)), V.obj K) ⟶ W)
    (hb : ∀ K P : B, Function.Bijective (fun f : P ⟶ F.obj (op K) ↦
      T.map (Prod.mkHom (V.map f) (𝟙 (V.obj K))) ≫ ev K))
    (hn : ∀ {K L : B} (f : K ⟶ L),
      T.map (Prod.mkHom (V.map (F.map f.op)) (𝟙 (V.obj K))) ≫ ev K =
        T.map (Prod.mkHom (𝟙 (V.obj (F.obj (op L)))) (V.map f)) ≫ ev L)
    (M : B) (d : M ⟶ F.obj (op (F.obj (op M))))
    (hd : T.map (Prod.mkHom (V.map d) (𝟙 _)) ≫ ev (F.obj (op M)) =
      (s (V.obj M) (V.obj (F.obj (op M)))).hom ≫ ev M) : IsIso d := by
  apply isIso_of_yoneda_map_bijective
  intro P
  let q (g : P ⟶ F.obj (op (F.obj (op M)))) :=
    (s (V.obj P) (V.obj (F.obj (op M)))).inv ≫
      T.map (Prod.mkHom (V.map g) (𝟙 _)) ≫ ev (F.obj (op M))
  have hq : Function.Bijective q := by
    simpa [q, Iso.homCongr, Function.comp_def, Category.assoc] using
      (Iso.homCongr (s (V.obj P) (V.obj (F.obj (op M)))) (Iso.refl W)).bijective.comp
        (hb (F.obj (op M)) P)
  have hf : Function.Bijective (fun f : P ⟶ M ↦ F.map f.op) :=
    (ff.map_bijective (op M) (op P)).comp (opEquiv (op M) (op P)).symm.bijective
  have he : Function.Bijective (fun f : P ⟶ M ↦
      T.map (Prod.mkHom (V.map (F.map f.op)) (𝟙 (V.obj P))) ≫ ev P) :=
    (hb P (F.obj (op M))).comp hf
  have heq : (fun f : P ⟶ M ↦ q (f ≫ d)) =
      (fun f : P ⟶ M ↦
        T.map (Prod.mkHom (V.map (F.map f.op)) (𝟙 (V.obj P))) ≫ ev P) := by
    funext f
    dsimp only [q]
    rw [V.map_comp]
    have ht := tensor_comp T (V.map f) (V.map d)
      (𝟙 (V.obj (F.obj (op M)))) (𝟙 (V.obj (F.obj (op M))))
    simp only [Category.id_comp] at ht
    rw [ht, Category.assoc, hd]
    have hsym := hs (f := V.map f) (g := 𝟙 (V.obj (F.obj (op M))))
    rw [← Category.assoc (T.map _) _ _, hsym, Category.assoc,
      Iso.inv_hom_id_assoc, ← hn f]
  apply (hq.of_comp_iff' (fun f : P ⟶ M ↦ f ≫ d)).mp
  change Function.Bijective (fun f : P ⟶ M ↦ q (f ≫ d))
  rw [heq]
  exact he

private theorem untranspose {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (T P Q : B) (f : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm f = S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q f

private theorem evaluation_natural {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (P Q P' Q' : B) (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫ S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫ S.evaluation P' Q =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q :=
    by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫ S.evaluation P' Q' =
      S.evaluation P' Q ≫ g :=
    by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) = H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op
    P')) g) :=
    by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht := tensor_comp S.tensor (H.map (Prod.mkHom f.op (𝟙 Q))) (H.map (Prod.mkHom (𝟙 (op P'))
    g)) (𝟙 P') (𝟙 P')
  simp only [Category.id_comp] at ht
  rw [ht, Category.assoc, hg, ← Category.assoc, he, Category.assoc]

private theorem evaluation_composite {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) {F K M W O DN : B}
    (j : M ⟶ K) (h : W ⟶ O) (alpha : F ⟶ H.obj (op K, W))
    (c : F ⟶ DN) (beta : DN ⟶ H.obj (op M, O))
    (e : S.tensor.obj (F, K) ⟶ W) (E : S.tensor.obj (DN, M) ⟶ O)
    (hc : c ≫ beta = alpha ≫ H.map (Prod.mkHom j.op h))
    (ha : S.tensor.map (Prod.mkHom alpha (𝟙 K)) ≫ S.evaluation K W = e)
    (hb : S.tensor.map (Prod.mkHom beta (𝟙 M)) ≫ S.evaluation M O = E) :
    S.tensor.map (Prod.mkHom c (𝟙 M)) ≫ E =
      S.tensor.map (Prod.mkHom (𝟙 F) j) ≫ e ≫ h := by
  have tc {U V Z P : B} (a : U ⟶ V) (b : V ⟶ Z) :
      S.tensor.map (Prod.mkHom (a ≫ b) (𝟙 P)) =
        S.tensor.map (Prod.mkHom a (𝟙 P)) ≫ S.tensor.map (Prod.mkHom b (𝟙 P)) := by
    simpa only [Category.id_comp] using tensor_comp S.tensor a b (𝟙 P) (𝟙 P)
  have ht : S.tensor.map (Prod.mkHom alpha (𝟙 M)) ≫
        S.tensor.map (Prod.mkHom (𝟙 _) j) =
      S.tensor.map (Prod.mkHom (𝟙 F) j) ≫
        S.tensor.map (Prod.mkHom alpha (𝟙 K)) := by
    rw [← S.tensor.map_comp, ← S.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [← hb, ← Category.assoc, ← tc, hc, tc, Category.assoc,
    evaluation_natural, ← Category.assoc, ht]
  simp only [Category.assoc]
  rw [reassoc_of% ha]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D) (A : Datum D l R X)

private theorem realized_evaluation_natural (hp : Permitted D l R X A) {M N : C D l X}
    (f : M ⟶ N) :
    (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
          (Prod.mkHom ((rho D l R X).map ((commonDual D l R X A hp).map f.op)) (𝟙 _)) ≫
        realizedEvaluation D l R X A hp M =
      (NativeSectionClosed.ordinaryClosed D l R X).tensor.map (Prod.mkHom (𝟙 _) ((rho D l R X).map
        f)) ≫
        realizedEvaluation D l R X A hp N := by
  let := (R.data (geometric D X)).units
  have hn := (R.data (geometric D X)).hom.naturality
    (pair D l R X A hp N) (pair D l R X A hp M)
    (ObjectProperty.homMk (Prod.mkHom f.op (𝟙 _)))
  have hn' : (rho D l R X).map ((commonDual D l R X A hp).map f.op) ≫
      realizationHom D l R X A hp M =
    realizationHom D l R X A hp N ≫
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
        (Prod.mkHom ((rho D l R X).map f).op (𝟙 _)) := by
    change _ ≫ realizationHom D l R X A hp M =
      realizationHom D l R X A hp N ≫
        (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
          (Prod.mkHom ((rho D l R X).map f).op ((rho D l R X).map (𝟙 _))) at hn
    erw [(rho D l R X).map_id] at hn
    exact hn
  simpa only [Category.comp_id] using
    evaluation_composite (NativeSectionClosed.ordinaryClosed D l R X)
      ((rho D l R X).map f) (𝟙 _)
      (realizationHom D l R X A hp N)
      ((rho D l R X).map ((commonDual D l R X A hp).map f.op))
      (realizationHom D l R X A hp M)
      (realizedEvaluation D l R X A hp N) (realizedEvaluation D l R X A hp M) hn'
      ((R.data (geometric D X)).hom.evaluation (pair D l R X A hp N))
      ((R.data (geometric D X)).hom.evaluation (pair D l R X A hp M))

private theorem realized_evaluation_bijective (hp : Permitted D l R X A)
    (K P : C D l X) :
    Function.Bijective (fun f : P ⟶ (commonDual D l R X A hp).obj (op K) ↦
      (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
          (Prod.mkHom ((rho D l R X).map f) (𝟙 _)) ≫
        realizedEvaluation D l R X A hp K) := by
  let := (R.data (geometric D X)).units
  let S := NativeSectionClosed.ordinaryClosed D l R X
  let e := (realizationFullyFaithful D l R X).homEquiv.trans
    ((realizationHomIso D l R X A hp K).homToEquiv.trans
      (S.transpose ((rho D l R X).obj P) ((rho D l R X).obj K)
        ((rho D l R X).obj (commonOmega D l R X A))).symm)
  have he : (fun f : P ⟶ (commonDual D l R X A hp).obj (op K) ↦
      S.tensor.map (Prod.mkHom ((rho D l R X).map f) (𝟙 _)) ≫
        realizedEvaluation D l R X A hp K) = e := by
    funext f
    change _ = (S.transpose _ _ _).symm
      ((rho D l R X).map f ≫ (realizationHomIso D l R X A hp K).hom)
    rw [untranspose]
    have ht := tensor_comp S.tensor ((rho D l R X).map f)
      (realizationHomIso D l R X A hp K).hom
      (𝟙 ((rho D l R X).obj K)) (𝟙 ((rho D l R X).obj K))
    simp only [Category.id_comp] at ht
    rw [ht, Category.assoc]
    congr 1
    exact ((R.data (geometric D X)).hom.evaluation (pair D l R X A hp K)).symm
  rw [he]
  exact e.bijective

private theorem realized_bid_rule (hp : Permitted D l R X A) (M : C D l X) :
    (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
        (Prod.mkHom ((rho D l R X).map (commonBidual D l R X A hp M)) (𝟙 _)) ≫
      realizedEvaluation D l R X A hp ((commonDual D l R X A hp).obj (op M)) =
    ((NativeSectionClosed.ordinarySymmetry D l R X).braiding ((rho D l R X).obj M)
      ((rho D l R X).obj ((commonDual D l R X A hp).obj (op M)))).hom ≫
      realizedEvaluation D l R X A hp M := by
  let := (R.data (geometric D X)).units
  let S := NativeSectionClosed.ordinaryClosed D l R X
  let DM := (commonDual D l R X A hp).obj (op M)
  let f := (pullbackTensorCommonBraiding l (PadicAlgCl l)
    (geometric D X).base.left M DM).hom
  let g := (podCommonClosed l (PadicAlgCl l)
    (geometric D X).base.left).evaluation (pair D l R X A hp M)
  have ht := (R.data (geometric D X)).hom.transpose M
    (pair D l R X A hp DM) (f ≫ g)
  change S.transpose ((rho D l R X).obj M) ((rho D l R X).obj DM)
    ((rho D l R X).obj (commonOmega D l R X A))
      ((R.data (geometric D X)).tensor.tensor.hom.app (M, DM) ≫
        (rho D l R X).map (f ≫ g)) =
      (rho D l R X).map (commonBidual D l R X A hp M) ≫
        realizationHom D l R X A hp DM at ht
  have hu := congrArg (S.transpose ((rho D l R X).obj M) ((rho D l R X).obj DM)
    ((rho D l R X).obj (commonOmega D l R X A))).symm ht
  rw [Equiv.symm_apply_apply, untranspose] at hu
  have htc := tensor_comp S.tensor ((rho D l R X).map (commonBidual D l R X A hp M))
    (realizationHom D l R X A hp DM)
    (𝟙 ((rho D l R X).obj DM)) (𝟙 ((rho D l R X).obj DM))
  simp only [Category.id_comp] at htc
  change _ = S.tensor.map
    (Prod.mkHom (((rho D l R X).map (commonBidual D l R X A hp M)) ≫
      realizationHom D l R X A hp DM) (𝟙 _)) ≫ S.evaluation _ _ at hu
  have hev : S.tensor.map (Prod.mkHom (realizationHom D l R X A hp DM)
      (𝟙 ((rho D l R X).obj DM))) ≫
        S.evaluation ((rho D l R X).obj DM)
          ((rho D l R X).obj (commonOmega D l R X A)) =
      realizedEvaluation D l R X A hp DM :=
    (R.data (geometric D X)).hom.evaluation (pair D l R X A hp DM)
  rw [htc, Category.assoc, hev] at hu
  have hb : (R.data (geometric D X)).tensor.tensor.hom.app (M, DM) ≫
      (rho D l R X).map (f ≫ g) =
    ((NativeSectionClosed.ordinarySymmetry D l R X).braiding
      ((rho D l R X).obj M) ((rho D l R X).obj DM)).hom ≫
        realizedEvaluation D l R X A hp M := by
    rw [(rho D l R X).map_comp, ← Category.assoc]
    have hs := (R.data (geometric D X)).tensor.symmetric M DM
    simpa only [Category.assoc, realizedEvaluation, f, g, DM,
      NativeSectionClosed.ordinarySymmetry] using
      congrArg (fun q ↦ q ≫ (rho D l R X).map g) hs
  exact hu.symm.trans hb

private def hom_target_iso
    {B : Type*} [Category B] (J : ObjectProperty (Bᵒᵖ × B))
    (H : J.FullSubcategory ⥤ B) {W W' : B} (e : W ≅ W')
    (h : ∀ K : B, J (op K, W)) (h' : ∀ K : B, J (op K, W')) :
    J.lift ((𝟭 Bᵒᵖ).prod' ((Functor.const Bᵒᵖ).obj W)) (fun K ↦ h K.unop) ⋙ H ≅
      J.lift ((𝟭 Bᵒᵖ).prod' ((Functor.const Bᵒᵖ).obj W')) (fun K ↦ h' K.unop) ⋙ H :=
  NatIso.ofComponents
    (fun K ↦ H.mapIso (J.isoMk (Iso.prod (Iso.refl K) e))) (by
      intro K L f
      simp only [Functor.comp_map, Functor.mapIso_hom]
      rw [← H.map_comp, ← H.map_comp]
      congr 1
      apply J.hom_ext
      apply Prod.hom_ext <;> simp)

private theorem common_dual_equivalence (hp : Permitted D l R X A) :
    (commonDual D l R X A hp).IsEquivalence := by
  obtain ⟨B, ⟨I⟩, hB, _⟩ := coef_qbar_verdier D l (Fact.out : l ≠ D.p)
    (PadicAlgCl l) (geometric D X).base.left
  obtain ⟨e⟩ := structural_dualizing_identification D l R X B hB A.system A.compactification
  let := (R.data (geometric D X)).units
  let t := hom_target_iso
    (commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left)
    (commonStageDerivedInternalHom l (PadicAlgCl l) (geometric D X).base.left)
    e I.permitted hp
  let := B.duality.equivalence
  exact Functor.isEquivalence_of_iso (I.comparison ≪≫ t)

/-- The evaluation transpose for the structural exceptional image is invertible at
common algebraically closed coefficients.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, paragraph 1;
sk-prop-sf-biduality-general.proof.md, coefficient transports paragraph.
(blueprint: lem-sf-structural-evaluation-bidual-invertible).

Proof: common-stage Verdier duality supplies an anti-equivalence identified with
internal Hom into its dualizing object. The structural dualizing identification
and functoriality in the target of Hom transport this anti-equivalence to the
specified commonDual. In particular that actual functor is fully faithful.

Realization, its invertible Hom comparison, and the ambient tensor-Hom adjunction
identify maps P to commonDual(K) with pairings rho(P) tensor rho(K) to rho(omega).
The realization's evaluation and naturality laws give naturality of this pairing.
Its transpose and signed-symmetry laws give the actual equation for commonBidual.
For each P, uncurry postcomposition with commonBidual(M) and precompose with the
inverse symmetry. Evaluation naturality identifies the resulting function with
the Hom map f maps to commonDual(f), followed by the evaluation bijection.
Both are bijective, so postcomposition with commonBidual(M) is bijective.
Yoneda proves that this specific arrow is an isomorphism. The argument applies
to zero objects and empty schemes without additional hypotheses. -/
theorem isIso_commonBidual
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (R : Family l D) (X : Space D) (A : Datum D l R X)
    (hp : Permitted D l R X A) (M : C D l X) :
    IsIso (commonBidual D l R X A hp M) := by
  let := common_dual_equivalence D l R X A hp
  let F := commonDual D l R X A hp
  let V := rho D l R X
  let S := NativeSectionClosed.ordinaryClosed D l R X
  let β := NativeSectionClosed.ordinarySymmetry D l R X
  apply bidual_iso_of_fullyFaithful F (Functor.FullyFaithful.ofFullyFaithful F) V
    S.tensor (fun P Q ↦ β.braiding P Q) ?_
    (V.obj (commonOmega D l R X A)) (realizedEvaluation D l R X A hp)
    (realized_evaluation_bijective D l R X A hp)
    (fun f ↦ realized_evaluation_natural D l R X A hp f) M
    (commonBidual D l R X A hp M) (realized_bid_rule D l R X A hp M)
  intro P P' Q Q' f g
  let := S.monoidal
  let := β
  exact CategoryTheory.BraidedCategory.braiding_naturality f g

end WeilConjectures.NativeBidualRealization
