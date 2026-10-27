/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.SixFunctorOrientation
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import Sheaf.Paper.OrientationPerfectLines
import Sheaf.Paper.PerfectDualPairAndTateStability
import Sheaf.Paper.CoefficientEvaluationNaturality
import Sheaf.Paper.OrientedDoubleHomCancellation

/-! # Oriented relative duality of perfect complexes at every coefficient stage

Source: main-20261015, sec-six-functors/sk-thm-sf-dual-perfect/_section.md and its proof
(blueprint: sk-thm-sf-dual-perfect).
The maps below use the existing closed presentations of the actual finite-Tor categories.
The orientation is the component of the recorded coherent family, at each coefficient stage.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The inverse of the specified theta: coefficient evaluation tensored with the oriented
line, followed by gamma, transposed under the recorded tensor-Hom adjunction.
Source: proof Steps 1--2 (blueprint: sk-thm-sf-dual-perfect). -/
def sfPerfectThetaInverse {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    {L W : B} (gamma : L ≅ W) (K : B) :
    M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L) ⟶ H.obj (op K, W) :=
  (s.braiding _ L).hom ≫ M.tensor.map (Prod.mkHom gamma.hom (𝟙 _)) ≫
    CategoryTheory.ringedSiteDualEvaluation M M.monoidal.tensorUnit (Iso.refl _) K W

/-- Tensoring a coefficient-valued Hom with the identity of the line and transposing.
This is the canonical cancellation comparison, not a freely supplied isomorphism.
Source: proof Step 5 (blueprint: sk-thm-sf-dual-perfect). -/
def sfPerfectLineCancellation {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (A L : B) :
    H.obj (op A, M.monoidal.tensorUnit) ⟶ H.obj (op (M.tensor.obj (A, L)), L) :=
  M.transpose _ _ L
    ((M.monoidal.associator _ A L).inv ≫
      M.tensor.map (Prod.mkHom (M.evaluation A M.monoidal.tensorUnit) (𝟙 L)) ≫
      (M.monoidal.leftUnitor L).hom)

/-- The complete conclusion of oriented perfect duality in one of the recorded closed
coefficient categories. Theta is pinned by its inverse, and the comparison of double duals
is pinned by theta and the canonical line-cancellation arrow. Its final equation concerns
precisely the signed evaluation-transpose biduality. The equivalence restricts the actual
internal-Hom functor, through the full-subcategory inclusions.
Source: all clauses and proof Steps 1--6 (blueprint: sk-thm-sf-dual-perfect). -/
def SfOrientedPerfectDuality {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    {L W : B} (gamma : L ≅ W) : Prop :=
  ∃ theta : ∀ (K : B), @IsDualizable B _ M.monoidal K →
      (H.obj (op K, W) ≅ M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L)),
    (∀ (K : B) (hK : @IsDualizable B _ M.monoidal K),
      (theta K hK).inv = sfPerfectThetaInverse M s gamma K) ∧
    (∀ (K K' : B) (hK : @IsDualizable B _ M.monoidal K)
      (hK' : @IsDualizable B _ M.monoidal K') (v : K ⟶ K'),
      H.map (Prod.mkHom v.op (𝟙 W)) ≫ (theta K hK).hom =
        (theta K' hK').hom ≫
          M.tensor.map (Prod.mkHom
            (H.map (Prod.mkHom v.op (𝟙 M.monoidal.tensorUnit))) (𝟙 L))) ∧
    (∃ e : (ObjectProperty.FullSubcategory (@IsDualizable B _ M.monoidal))ᵒᵖ ≌
        ObjectProperty.FullSubcategory (@IsDualizable B _ M.monoidal),
      Nonempty (e.functor ⋙ ObjectProperty.ι (@IsDualizable B _ M.monoidal) ≅
        (ObjectProperty.ι (@IsDualizable B _ M.monoidal)).op ⋙
          (Functor.curry.obj H).flip.obj W)) ∧
    (∀ (K : B) (hK : @IsDualizable B _ M.monoidal K),
      ∃ c : H.obj (op (H.obj (op K, M.monoidal.tensorUnit)), M.monoidal.tensorUnit) ≅
          H.obj (op (M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L)), L),
        c.hom = sfPerfectLineCancellation M (H.obj (op K, M.monoidal.tensorUnit)) L ∧
        CategoryTheory.ringedSiteBidual M s W K ≫
          (((Functor.curry.obj H).flip.obj W).mapIso (theta K hK).op).inv ≫
          (H.map (Prod.mkHom (𝟙 _) gamma.inv)) ≫ c.inv =
            CategoryTheory.ringedSiteBidual M s M.monoidal.tensorUnit K)

/-- Read the preceding conclusion on the actual finite-Tor full subcategory. Membership
of the shifted line and its exceptional image is asserted, rather than imposed as a new
hypothesis. The orientation lifts through the fully faithful inclusion.
Source: the Dctf domain of the theorem (blueprint: sk-thm-sf-dual-perfect). -/
def SfOrientedPerfectDualityOnDomain
    {B : Type a} [Category.{b} B] {P : ObjectProperty B}
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H) {L W : B} (gamma : L ≅ W) : Prop :=
  ∃ (hL : P L) (hW : P W),
    SfOrientedPerfectDuality M.closed M.symmetric
      (ObjectProperty.isoMk P (X := ⟨L, hL⟩) (Y := ⟨W, hW⟩) gamma)

private theorem sf_perfect_inverse_eq
    {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    {L W : B} (gamma : L ≅ W) (K : B) :
    ringedSiteDualEvaluationLeft M s M.monoidal.tensorUnit (Iso.refl _) K L ≫
      H.map (Prod.mkHom (𝟙 (op K)) gamma.hom) = sfPerfectThetaInverse M s gamma K := by
  let _ := M.monoidal
  let _ := s
  unfold sfPerfectThetaInverse ringedSiteDualEvaluationLeft
  rw [Category.assoc, ← ringedSiteDualEvaluation_naturality]

private theorem sf_transpose_target
    {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (T P : B) {Q Q' : B} (f : Q ⟶ Q')
    (g : M.tensor.obj (T, P) ⟶ Q) :
    M.transpose T P Q' (g ≫ f) =
      M.transpose T P Q g ≫ H.map (Prod.mkHom (𝟙 (op P)) f) :=
  (M.adjunction P).homEquiv_naturality_right g f

private theorem sf_perfect_cancellation_eq
    {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (L A : B) :
    orientedHomCancellationInverse M L A = sfPerfectLineCancellation M A L := by
  unfold orientedHomCancellationInverse orientedHomTensorBoth sfPerfectLineCancellation
  simpa only [CoefficientClosedStructure.tensor, tensor_obj, Category.assoc] using
    (sf_transpose_target M (H.obj (op A, M.monoidal.tensorUnit))
      (M.tensor.obj (A, L)) (M.monoidal.leftUnitor L).hom
      ((M.monoidal.associator (H.obj (op A, M.monoidal.tensorUnit)) A L).inv ≫
        M.tensor.map (Prod.mkHom (M.evaluation A M.monoidal.tensorUnit) (𝟙 L)))).symm

private theorem sf_perfect_antiEquivalence
    {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    (W : B)
    (hd : ∀ K : B, @IsDualizable B _ M.monoidal K →
      @IsDualizable B _ M.monoidal (H.obj (op K, W)))
    (hb : ∀ K : B, @IsDualizable B _ M.monoidal K →
      IsIso (ringedSiteBidual M s W K)) :
    ∃ e : (ObjectProperty.FullSubcategory (@IsDualizable B _ M.monoidal))ᵒᵖ ≌
        ObjectProperty.FullSubcategory (@IsDualizable B _ M.monoidal),
      Nonempty (e.functor ⋙ ObjectProperty.ι (@IsDualizable B _ M.monoidal) ≅
        (ObjectProperty.ι (@IsDualizable B _ M.monoidal)).op ⋙
          (Functor.curry.obj H).flip.obj W) := by
  let J : ObjectProperty B := @IsDualizable B _ M.monoidal
  let F : J.FullSubcategoryᵒᵖ ⥤ J.FullSubcategory :=
    J.lift (J.ι.op ⋙ (Functor.curry.obj H).flip.obj W)
      (fun K ↦ hd K.unop.obj K.unop.property)
  have hi (K : J.FullSubcategory) : IsIso (ringedSiteBidual M s W K.obj) :=
    hb K.obj K.property
  let j : 𝟭 J.FullSubcategory ≅ F.rightOp ⋙ F :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk J (asIso (ringedSiteBidual M s W K.obj)))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact ringedSiteBidual_naturality M s W f.hom)
  let k : 𝟭 J.FullSubcategoryᵒᵖ ≅ F ⋙ F.rightOp :=
    NatIso.ofComponents (fun K ↦ (j.app K.unop).symm.op)
      (fun f ↦ by
        apply Quiver.Hom.unop_inj
        change (j.app _).inv ≫ _ = _ ≫ (j.app _).inv
        exact (j.inv.naturality f.unop).symm)
  exact ⟨CategoryTheory.Equivalence.mk F F.rightOp k j.symm, ⟨Iso.refl _⟩⟩

private theorem sf_perfect_assembly
    {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    (laws : SfCoefficientEvaluationLaws M s) (pairs : SfPerfectDualPair M s)
    {L W : B} (gamma : L ≅ W) (hL : @IsInvertible B _ M.monoidal L) :
    SfOrientedPerfectDuality M s gamma := by
  let _ := M.monoidal
  let _ := s
  obtain ⟨I, ⟨a⟩, ⟨b⟩⟩ := hL
  have hL : IsInvertible L := ⟨I, ⟨a⟩, ⟨b⟩⟩
  have hc (K : B) (hK : IsDualizable K) :
      IsIso (ringedSiteDualEvaluationLeft M s M.monoidal.tensorUnit (Iso.refl _) K L) := by
    have hh := sfTwistTensorHomMap_isIso M s K M.monoidal.tensorUnit L hK hL
    have he : ringedSiteDualEvaluationLeft M s M.monoidal.tensorUnit (Iso.refl _) K L =
        sfTwistTensorHomMap M s K M.monoidal.tensorUnit L ≫
          H.map (Prod.mkHom (𝟙 (op K)) (M.monoidal.leftUnitor L).hom) := by
      rw [laws.1 K L]
      unfold sfTwistTensorHomMap
      simpa only [CoefficientClosedStructure.tensor, tensor_obj, Category.assoc] using
        (sf_transpose_target M (M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L)) K
          (M.monoidal.leftUnitor L).hom
          ((M.monoidal.associator _ L K).hom ≫
            M.tensor.map (Prod.mkHom (𝟙 _) (s.braiding L K).hom) ≫
            (M.monoidal.associator _ K L).inv ≫
            M.tensor.map (Prod.mkHom (M.evaluation K M.monoidal.tensorUnit) (𝟙 L))))
    have hm : IsIso (H.map (Prod.mkHom (𝟙 (op K))
        (M.monoidal.leftUnitor L).hom)) :=
      (H.mapIso (Iso.prod (Iso.refl (op K)) (M.monoidal.leftUnitor L))).isIso_hom
    rw [he]
    infer_instance
  let theta (K : B) (hK : IsDualizable K) := sfCoefficientTheta M s gamma K (hc K hK)
  have ht (K : B) (hK : IsDualizable K) :
      (theta K hK).inv = sfPerfectThetaInverse M s gamma K := by
    exact sf_perfect_inverse_eq M s gamma K
  have hn (K K' : B) (hK : IsDualizable K) (hK' : IsDualizable K') (v : K ⟶ K') :
      H.map (Prod.mkHom v.op (𝟙 W)) ≫ (theta K hK).hom =
        (theta K' hK').hom ≫ M.tensor.map (Prod.mkHom
          (H.map (Prod.mkHom v.op (𝟙 M.monoidal.tensorUnit))) (𝟙 L)) := by
    exact (laws.2.2 (@IsDualizable B _ M.monoidal) L W gamma
      (fun K ↦ hc K.obj K.property)).1
        ⟨K, hK⟩ ⟨K', hK'⟩ (ObjectProperty.homMk v)
  obtain ⟨q, hq, _, _, _, he⟩ :=
    sfOrientedCancellation_of_evaluationLaws M s laws L I a b
  have hb (K : B) (hK : IsDualizable K) :
      ∃ c : H.obj (op (H.obj (op K, M.monoidal.tensorUnit)), M.monoidal.tensorUnit) ≅
          H.obj (op (M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L)), L),
        c.hom = sfPerfectLineCancellation M (H.obj (op K, M.monoidal.tensorUnit)) L ∧
        ringedSiteBidual M s W K ≫
          (((Functor.curry.obj H).flip.obj W).mapIso (theta K hK).op).inv ≫
          H.map (Prod.mkHom (𝟙 _) gamma.inv) ≫ c.inv =
            ringedSiteBidual M s M.monoidal.tensorUnit K := by
    refine ⟨(q _).symm, ?_, ?_⟩
    · exact (hq _).trans (sf_perfect_cancellation_eq M L _)
    · have _ := hc K hK
      have hh := he W gamma K hK
      change ringedSiteBidual M s W K ≫
        H.map (Prod.mkHom ((theta K hK).inv).op gamma.inv) ≫
          (q (H.obj (op K, M.monoidal.tensorUnit))).hom = _ at hh
      change ringedSiteBidual M s W K ≫
        H.map (Prod.mkHom ((theta K hK).inv).op (𝟙 W)) ≫
        H.map (Prod.mkHom (𝟙 _) gamma.inv) ≫
          (q (H.obj (op K, M.monoidal.tensorUnit))).hom = _
      rw [← H.map_comp_assoc]
      simpa only [CategoryTheory.prod_comp, Category.id_comp, Category.comp_id] using hh
  have hi (K : B) (hK : IsDualizable K) : IsIso (ringedSiteBidual M s W K) := by
    obtain ⟨c, _, he⟩ := hb K hK
    have _ := (pairs K hK).2.1
    have hm : IsIso (H.map (Prod.mkHom
        (𝟙 (op (M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L)))) gamma.inv)) :=
      (H.mapIso (Iso.prod (Iso.refl _) gamma.symm)).isIso_hom
    have his : IsIso (ringedSiteBidual M s W K ≫
        (((Functor.curry.obj H).flip.obj W).mapIso (theta K hK).op).inv ≫
          H.map (Prod.mkHom (𝟙 _) gamma.inv) ≫ c.inv) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right (ringedSiteBidual M s W K)
      ((((Functor.curry.obj H).flip.obj W).mapIso (theta K hK).op).inv ≫
        H.map (Prod.mkHom (𝟙 _) gamma.inv) ≫ c.inv)
  have hd (K : B) (hK : IsDualizable K) : IsDualizable (H.obj (op K, W)) := by
    exact IsDualizable.of_iso (theta K hK).symm
      (((pairs K hK).1).tensorObj hL.isDualizable)
  exact ⟨theta, ht, hn, sf_perfect_antiEquivalence M s W hd hi, hb⟩

/-- Relative duality at finite, completed integral, rational and common finite-extension
coefficients, with the specified smooth-purity orientation. The base is arbitrary; finite
type and the fixed finite-field/coefficient setting are encoded by SixFunctorSpace and S.
For the absolute case substitute sixFunctorStructure X; the orientation components then
have the names SixFunctorOrientation.finiteStructure, integralStructure, rationalStructure
and commonStructure, and their targets are the absolute dualizing objects.
Source: main-20261015, sk-thm-sf-dual-perfect, entire statement
(blueprint: sk-thm-sf-dual-perfect).

Proof: Step 1 applies internal Hom to gamma inverse and then uses twist interchange with
m=d, n=2d. Step 2 transposes evaluation to identify the inverse of theta and proves its
naturality by the adjunction bijection. Step 3 dualizes a finite projective local model and
tensors with the rank-one Tate line, using the completed unit, scalar localization and a
common finite stage at the respective coefficients; opposite lines and shifts cancel.
Step 4 identifies the dual-pair dual with coefficient internal Hom and proves coefficient
biduality by the two triangle identities. Step 5 cancels the invertible shifted line in
Hom; the explicit cancellation map below sends relative evaluation to coefficient evaluation,
so the signed transpose is precisely coefficient biduality. Step 6 uses naturality of the
invertible biduality to identify the square of relative Hom with the identity on perfect
objects; Equivalence.mk supplies its coherent anti-equivalence. Specializing f to the structure
morphism gives exactly the absolute assertion. -/
theorem sfOrientedPerfectDuality
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) :
    SfOrientedPerfectDualityOnDomain (S.finiteClosed X) (SixFunctorOrientation O f d c) ∧
    SfOrientedPerfectDualityOnDomain (S.integralClosed X)
      (SixFunctorOrientation.integralComponent O f d c) ∧
    SfOrientedPerfectDualityOnDomain (S.rationalClosed X)
      (SixFunctorOrientation.rationalComponent O f d c) ∧
    SfOrientedPerfectDualityOnDomain (S.commonClosed X)
      (SixFunctorOrientation.commonComponent O f d c) := by
  obtain ⟨lf, li, lr, lc⟩ := sfOrientationPerfectLines O f d c
  obtain ⟨ef, ei, er, ec, _⟩ := sfCoefficientEvaluationNaturality S X
  obtain ⟨pf, pi, pr, pc, _⟩ := sfPerfectDualPairAndTateStability S X
  rcases lf with ⟨hLf, hWf, hf⟩
  rcases li with ⟨hLi, hWi, hi⟩
  rcases lr with ⟨hLr, hWr, hr⟩
  rcases lc with ⟨hLc, hWc, hc⟩
  exact ⟨⟨hLf, hWf, sf_perfect_assembly _ _ ef pf _ hf⟩,
    ⟨hLi, hWi, sf_perfect_assembly _ _ ei pi _ hi⟩,
    ⟨hLr, hWr, sf_perfect_assembly _ _ er pr _ hr⟩,
    ⟨hLc, hWc, sf_perfect_assembly _ _ ec pc _ hc⟩⟩

end WeilConjectures
