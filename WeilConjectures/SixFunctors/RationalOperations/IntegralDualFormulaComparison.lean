/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaScalarTranspose
public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # The normalized integral dual-formula comparison

Source: lem-sf-rational-dual-formula-adjunction, proof step 2; the evaluation
and absolute-trace transpose in lem-coef-finite-exceptional and its coherent
integral realization (blueprint: lem-sf-integral-dual-formula-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] PurCompactSupport.completed
  scalarReductionSourceDerived scalarReductionTargetDerived
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  integralTowerHasDerivedCategory integralOperationsCommHasDerivedCategory
  integralCompletedRingHasDerivedCategory coefficientSequenceHasDerived
attribute [local implicit_reducible] IntegralVerdier.restrictedDual IntegralVerdier.dual
  constructibleIntegralPullback IntegralHom.derivedCategory
  IntegralFiniteExtension.tensorModel

private theorem normalized_components_natural
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (G H : B ⥤ A) (adj : L ⊣ G)
    (Pair : A → B → Type*)
    (left : ∀ {K K' : A}, (K' ⟶ K) → ∀ M, Pair K M → Pair K' M)
    (right : ∀ K {M N : B}, (M ⟶ N) → Pair K M → Pair K N)
    (p : ∀ K M, (K ⟶ H.obj M) → Pair K M)
    (q : ∀ K M, (L.obj K ⟶ M) → Pair K M)
    (pl : ∀ {K K' : A} (g : K' ⟶ K) M h,
      p K' M (g ≫ h) = left g M (p K M h))
    (pr : ∀ K {M N : B} (g : M ⟶ N) h,
      p K N (h ≫ H.map g) = right K g (p K M h))
    (ql : ∀ {K K' : A} (g : K' ⟶ K) M h,
      q K' M (L.map g ≫ h) = left g M (q K M h))
    (qr : ∀ K {M N : B} (g : M ⟶ N) h,
      q K N (h ≫ g) = right K g (q K M h))
    (qi : ∀ K M, Function.Injective (q K M))
    (k : ∀ M, G.obj M ≅ H.obj M)
    (hk : ∀ M, p (G.obj M) M (k M).hom = q (G.obj M) M (adj.counit.app M)) :
    ∀ {M N : B} (g : M ⟶ N), G.map g ≫ (k N).hom = (k M).hom ≫ H.map g := by
  have hp (K : A) (M : B) (h : K ⟶ H.obj M) :
      p K M h = q K M ((adj.homEquiv K M).symm (h ≫ (k M).inv)) := by
    calc
      p K M h = p K M ((h ≫ (k M).inv) ≫ (k M).hom) := by simp
      _ = left (h ≫ (k M).inv) M (p (G.obj M) M (k M).hom) := pl _ _ _
      _ = left (h ≫ (k M).inv) M (q (G.obj M) M (adj.counit.app M)) := by rw [hk]
      _ = q K M (L.map (h ≫ (k M).inv) ≫ adj.counit.app M) := (ql _ _ _).symm
      _ = _ := by rw [Adjunction.homEquiv_counit]
  have pi (K : A) (M : B) : Function.Injective (p K M) := by
    intro h h' he
    rw [hp, hp] at he
    have he' := (adj.homEquiv K M).symm.injective (qi K M he)
    exact (cancel_mono (k M).inv).mp he'
  intro M N g
  apply pi (G.obj M) N
  rw [pl, pr, hk, hk, ← ql, ← qr]
  exact congrArg (q (G.obj M) N) (adj.counit.naturality g)

private theorem normalized_identity_transport
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {G H : B ⥤ A} (adj : L ⊣ G)
    (Pair : A → B → Type*)
    (left : ∀ {K K' : A}, (K' ⟶ K) → ∀ M, Pair K M → Pair K' M)
    (p : ∀ K M, (K ⟶ H.obj M) → Pair K M)
    (q : ∀ K M, (L.obj K ⟶ M) → Pair K M)
    (pl : ∀ {K K' : A} (g : K' ⟶ K) M h,
      p K' M (g ≫ h) = left g M (p K M h))
    (ql : ∀ {K K' : A} (g : K' ⟶ K) M h,
      q K' M (L.map g ≫ h) = left g M (q K M h))
    (e : G ≅ H)
    (he : ∀ M, p (G.obj M) M (e.hom.app M) = q (G.obj M) M (adj.counit.app M))
    (M : B) :
    p (H.obj M) M (𝟙 _) = q (H.obj M) M ((adj.ofNatIsoRight e).counit.app M) := by
  calc
    p (H.obj M) M (𝟙 _) = p (H.obj M) M (e.inv.app M ≫ e.hom.app M) := by simp
    _ = left (e.inv.app M) M (p (G.obj M) M (e.hom.app M)) := pl _ _ _
    _ = left (e.inv.app M) M (q (G.obj M) M (adj.counit.app M)) := by rw [he]
    _ = q (H.obj M) M (L.map (e.inv.app M) ≫ adj.counit.app M) := (ql _ _ _).symm
    _ = _ := by
      simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
        Functor.whiskerRight_app]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
  (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
  (pX : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((IntegralVerdier.dual l E X wX.omega.obj).obj (op K.obj)))
  (pY : ∀ K : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E Y ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op K.obj)))

/-- The evaluation-normalized components assemble into a natural comparison with the
integral dual formula. Transport of the supplied adjunction along this comparison makes
the identity the normalized formula component. This is entirely an integral assertion:
the ordinary tensor presentations and the initial compact-support adjunction are supplied.

Source: lem-sf-rational-dual-formula-adjunction, step 2; current blueprint
lem-coef-finite-exceptional.proof.md, the displayed natural Hom bijections and its
last paragraph on evaluation and counits; thm-coef-integral-verdier.proof.md, the
internal-Hom reduction and evaluation argument
(blueprint: lem-sf-integral-dual-formula-comparison).

Proof: apply formula_existsUnique to the supplied adjunction and tensor presentations
at every M. The resulting component is the trace transpose of the ordinary projection
map followed by the specified completion augmentation and evaluation into omega_X.
Its inverse is currying followed by inverse Verdier biduality. In these two operations,
precomposition with an arrow M to N commutes with evaluation, ordinary projection,
completion augmentation and structural trace. The tensor-Hom naturality equations
therefore identify G.map with the double-contravariant dual-pullback-dual map; the
components and their inverses assemble into a natural isomorphism e. This calculation
is made in the coherent integral mapping system used by formula_existsUnique; it is
not deduced from separate equalities of finite reductions. Transport the adjunction
along e. Its new counit at M is compact support of e.inv.app M followed by the old
counit. Substitute this expression in FormulaNormalized. Naturality of the ordinary
projection map and the support realization moves e.inv through its first tensor
factor. Naturality of the signed symmetry moves it to the evaluation factor, where
it cancels e.hom.app M. The old normalization is consequently exactly the new
normalization with the identity component. These are functorial tensor and adjunction
identities, so empty schemes, zero objects, and torsion objects need no exception. -/
theorem integralDualFormulaComparison
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G) :
    ∃ e : G ≅
        (IntegralVerdier.restrictedDual l E Y wY.omega.obj pY).rightOp ⋙
          (@constructibleIntegralPullback l _ E _ _ _ X Y f
            (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).op ⋙
          IntegralVerdier.restrictedDual l E X wX.omega.obj pX,
      ∀ M : sfIntegralConstructibleCategory l E Y,
        CoefDualFormulaScalarTranspose.FormulaNormalized D l hl E f c wX wY aX aZ aY sX
          _ (adj.ofNatIsoRight e) M (Iso.refl _) := by
  classical
  -- F1 normalizes the formula by the canonical evaluation and the natural signed symmetry.
  let adjX := CoefDualFormulaScalarTranspose.canonicalEvaluationAdjunction X
    (completedIntegralCommRingSheafUnrestricted l E X) aX
  let adjY := CoefDualFormulaScalarTranspose.canonicalEvaluationAdjunction Y
    (completedIntegralCommRingSheafUnrestricted l E Y) aY
  let sN := CoefDualFormulaScalarTranspose.normalizedSignedSymmetry X _ aX sX
  have natX (K K' Z : IntegralHom.Derived.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)) (g : K' ⟶ K) :
      aX.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X _).map (Prod.mkHom g.op (𝟙 Z)))) ≫
          (adjX K').counit.app Z =
        aX.tensor.map (Prod.mkHom g (𝟙 _)) ≫ (adjX K).counit.app Z :=
    CoefDualFormulaScalarTranspose.adjunctionOfExchange_natural _ _ _ K K' Z g
  have natY (K K' Z : IntegralHom.Derived.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y)) (g : K' ⟶ K) :
      aY.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} Y _).map (Prod.mkHom g.op (𝟙 Z)))) ≫
          (adjY K').counit.app Z =
        aY.tensor.map (Prod.mkHom g (𝟙 _)) ≫ (adjY K).counit.app Z :=
    CoefDualFormulaScalarTranspose.adjunctionOfExchange_natural _ _ _ K K' Z g
  let J := (sfIntegralConstructible l E Y).ι
  let L := sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c E
  let H := (IntegralVerdier.restrictedDual l E Y wY.omega.obj pY).rightOp ⋙
    (@constructibleIntegralPullback l _ E _ _ _ X Y f
      (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).op ⋙
    IntegralVerdier.restrictedDual l E X wX.omega.obj pX
  let P := PurCompactSupport.image (PurCompactSupport.completed l E) c
  let Q := integralDerivedPullback.{u, u} l E f
  let W := J.op ⋙ IntegralVerdier.dual l E Y wY.omega.obj
  let V := W ⋙ Q
  let T := aX.tensor
  let U := aY.tensor
  let rho := sfQcqsCompactSupportRealization l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c
  let t := rho.hom.app wX.omega ≫
    J.map (CoefDualFormulaScalarTranspose.trace D l hl E f c wX wY)
  let pi := PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c
    (IntegralFiniteExtension.tensorModel X aX)
    (IntegralFiniteExtension.tensorModel c.Z aZ)
    (IntegralFiniteExtension.tensorModel Y aY)
    (PurCompactSupport.completedPull_comp l E c.i c.g)
  let pi0 (K : IntegralHom.Derived.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
      (M : IntegralHom.Derived.{u, u} Y
        (completedIntegralCommRingSheafUnrestricted l E Y)) :
      U.obj (P.obj K, M) ⟶ P.obj (T.obj (K,
        (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj M)) :=
    (pi.app K).app M
  let theta (K : sfIntegralConstructibleCategory l E X)
      (M : (sfIntegralConstructibleCategory l E Y)ᵒᵖ) :
      U.obj (P.obj K.obj, W.obj M) ⟶ P.obj (T.obj (K.obj, V.obj M)) :=
    pi0 K.obj (W.obj M) ≫ P.map
      (T.map (Prod.mkHom (𝟙 K.obj)
        ((CoefDualFormulaScalarTranspose.pullCompletion l E f).app (W.obj M))))
  have theta_l {K K' : sfIntegralConstructibleCategory l E X} (g : K' ⟶ K)
      (M : (sfIntegralConstructibleCategory l E Y)ᵒᵖ) :
      U.map (Prod.mkHom (P.map g.hom) (𝟙 (W.obj M))) ≫ theta K M =
        theta K' M ≫ P.map (T.map (Prod.mkHom g.hom (𝟙 (V.obj M)))) := by
    have hn := congr_app (pi.naturality g.hom) (W.obj M)
    change U.map (Prod.mkHom (P.map g.hom) (𝟙 _)) ≫ pi0 K.obj (W.obj M) =
      pi0 K'.obj (W.obj M) ≫ P.map
        (T.map (Prod.mkHom g.hom (𝟙 _))) at hn
    dsimp only [theta]
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← P.map_comp, ← T.map_comp, prod_comp,
      Category.id_comp, Category.comp_id]
  have theta_r (K : sfIntegralConstructibleCategory l E X)
      {M N : (sfIntegralConstructibleCategory l E Y)ᵒᵖ} (g : M ⟶ N) :
      U.map (Prod.mkHom (𝟙 (P.obj K.obj)) (W.map g)) ≫ theta K N =
        theta K M ≫ P.map (T.map (Prod.mkHom (𝟙 K.obj) (V.map g))) := by
    have hn := (pi.app K.obj).naturality (W.map g)
    change U.map (Prod.mkHom (𝟙 _) (W.map g)) ≫ pi0 K.obj (W.obj N) =
      pi0 K.obj (W.obj M) ≫ P.map
        (T.map (Prod.mkHom (𝟙 _) ((PurCompactSupport.pull
          (PurCompactSupport.completed l E) f).map (W.map g)))) at hn
    have hc := (CoefDualFormulaScalarTranspose.pullCompletion l E f).naturality (W.map g)
    dsimp only [theta]
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← P.map_comp, ← T.map_comp, prod_comp, Category.comp_id]
    rw [hc]
    rfl
  let tau (M : sfIntegralConstructibleCategory l E Y) :
      T.obj ((H.obj M).obj, V.obj (op M)) ⟶ wX.omega.obj :=
    (sN.swap (H.obj M).obj (V.obj (op M))).hom ≫
      (adjX (V.obj (op M))).counit.app wX.omega.obj
  have tau_natural {M N : sfIntegralConstructibleCategory l E Y} (g : M ⟶ N) :
      T.map (Prod.mkHom (H.map g).hom (𝟙 (V.obj (op N)))) ≫ tau N =
        T.map (Prod.mkHom (𝟙 (H.obj M).obj) (V.map g.op)) ≫ tau M := by
    have hs := sN.naturality (H.obj M).obj (V.obj (op N))
      (H.obj N).obj (V.obj (op N)) (H.map g).hom (𝟙 _)
    have hs' := sN.naturality (H.obj M).obj (V.obj (op N))
      (H.obj M).obj (V.obj (op M)) (𝟙 _) (V.map g.op)
    have he := natX
      (V.obj (op M)) (V.obj (op N)) wX.omega.obj (V.map g.op)
    change T.map (Prod.mkHom (𝟙 _) (H.map g).hom) ≫
      (adjX (V.obj (op N))).counit.app wX.omega.obj =
        T.map (Prod.mkHom (V.map g.op) (𝟙 _)) ≫
          (adjX (V.obj (op M))).counit.app wX.omega.obj at he
    dsimp only [tau]
    rw [← Category.assoc, hs, Category.assoc, he]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (adjX (V.obj (op M))).counit.app wX.omega.obj)
        hs'.symm) |>.trans (Category.assoc _ _ _)
  let Pair (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y) :=
    U.obj (P.obj K.obj, W.obj (op M)) ⟶ wY.omega.obj
  let left {K K' : sfIntegralConstructibleCategory l E X} (g : K' ⟶ K)
      (M : sfIntegralConstructibleCategory l E Y) (z : Pair K M) : Pair K' M :=
    U.map (Prod.mkHom (P.map g.hom) (𝟙 (W.obj (op M)))) ≫ z
  let right (K : sfIntegralConstructibleCategory l E X)
      {M N : sfIntegralConstructibleCategory l E Y} (g : M ⟶ N)
      (z : Pair K M) : Pair K N :=
    U.map (Prod.mkHom (𝟙 (P.obj K.obj)) (W.map g.op)) ≫ z
  let p (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y) (h : K ⟶ H.obj M) : Pair K M :=
    theta K (op M) ≫ P.map (T.map (Prod.mkHom h.hom (𝟙 (V.obj (op M)))) ≫ tau M) ≫ t
  let q (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y) (h : L.obj K ⟶ M) : Pair K M :=
    U.map (Prod.mkHom (rho.hom.app K ≫ J.map h) (𝟙 (W.obj (op M)))) ≫
      (adjY M.obj).counit.app wY.omega.obj
  have pl {K K' : sfIntegralConstructibleCategory l E X} (g : K' ⟶ K) M h :
      p K' M (g ≫ h) = left g M (p K M h) := by
    have ht : T.map (Prod.mkHom (g ≫ h).hom (𝟙 (V.obj (op M)))) =
        T.map (Prod.mkHom g.hom (𝟙 (V.obj (op M)))) ≫
          T.map (Prod.mkHom h.hom (𝟙 (V.obj (op M)))) := by
      rw [← T.map_comp]
      simp only [prod_comp, Category.id_comp]
      rfl
    dsimp only [p, left]
    rw [ht]
    simp only [P.map_comp, Category.assoc]
    rw [← Category.assoc (U.map _) (theta K (op M)), theta_l]
    simp only [Category.assoc]
  have pr (K : sfIntegralConstructibleCategory l E X)
      {M N : sfIntegralConstructibleCategory l E Y} (g : M ⟶ N) h :
      p K N (h ≫ H.map g) = right K g (p K M h) := by
    have ht : T.map (Prod.mkHom (h ≫ H.map g).hom (𝟙 (V.obj (op N)))) ≫ tau N =
        T.map (Prod.mkHom (𝟙 K.obj) (V.map g.op)) ≫
          T.map (Prod.mkHom h.hom (𝟙 (V.obj (op M)))) ≫ tau M := by
      have hcomp : T.map (Prod.mkHom (h ≫ H.map g).hom (𝟙 (V.obj (op N)))) =
          T.map (Prod.mkHom h.hom (𝟙 (V.obj (op N)))) ≫
            T.map (Prod.mkHom (H.map g).hom (𝟙 (V.obj (op N)))) := by
        rw [← T.map_comp]
        simp only [prod_comp, Category.id_comp]
        rfl
      rw [hcomp, Category.assoc, tau_natural]
      simp only [← Category.assoc, ← T.map_comp, prod_comp,
        Category.id_comp, Category.comp_id]
    dsimp only [p, right]
    rw [ht, P.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (U.map _) (theta K (op M)), theta_r]
    simp only [Category.assoc]
  have ql {K K' : sfIntegralConstructibleCategory l E X} (g : K' ⟶ K) M h :
      q K' M (L.map g ≫ h) = left g M (q K M h) := by
    have hr := rho.hom.naturality g
    change P.map g.hom ≫ rho.hom.app K =
      rho.hom.app K' ≫ J.map (L.map g) at hr
    dsimp only [q, left]
    rw [J.map_comp]
    simp only [← Category.assoc, ← U.map_comp, prod_comp, Category.comp_id]
    rw [hr]
  have qr (K : sfIntegralConstructibleCategory l E X)
      {M N : sfIntegralConstructibleCategory l E Y} (g : M ⟶ N) h :
      q K N (h ≫ g) = right K g (q K M h) := by
    have he := natY
      N.obj M.obj wY.omega.obj g.hom
    change U.map (Prod.mkHom (𝟙 M.obj) (W.map g.op)) ≫
        (adjY M.obj).counit.app wY.omega.obj =
      U.map (Prod.mkHom g.hom (𝟙 (W.obj (op N)))) ≫
        (adjY N.obj).counit.app wY.omega.obj at he
    dsimp only [q, right]
    have ht : U.map (Prod.mkHom (rho.hom.app K ≫ J.map (h ≫ g))
        (𝟙 (W.obj (op N)))) =
      U.map (Prod.mkHom (rho.hom.app K ≫ J.map h) (𝟙 (W.obj (op N)))) ≫
        U.map (Prod.mkHom g.hom (𝟙 (W.obj (op N)))) := by
      rw [← U.map_comp, J.map_comp]
      simp only [prod_comp, Category.id_comp, Category.assoc]
      rfl
    rw [ht, Category.assoc, ← he]
    simp only [← Category.assoc, ← U.map_comp, prod_comp,
      Category.id_comp, Category.comp_id]
    exact congrArg (fun z : P.obj K.obj ⟶ M.obj ↦
      U.map (Prod.mkHom z (W.map g.op)) ≫
        (adjY M.obj).counit.app wY.omega.obj)
      (Category.comp_id (rho.hom.app K ≫ J.map h))
  have qi (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y) : Function.Injective (q K M) := by
    obtain ⟨_, _, _, _, _, preserves, equivalence, _⟩ :=
      integral_verdier_biduality D l hl E Y wY.omega wY.reduction
    have : (IntegralVerdier.restrictedDual l E Y wY.omega.obj pY).IsEquivalence := equivalence
    intro h h' hh
    have hu : U.map (Prod.mkHom (J.map h) (𝟙 (W.obj (op M)))) ≫
        (adjY M.obj).counit.app wY.omega.obj =
      U.map (Prod.mkHom (J.map h') (𝟙 (W.obj (op M)))) ≫
        (adjY M.obj).counit.app wY.omega.obj := by
      apply (cancel_epi (U.mapIso
        (Iso.prod (rho.app K) (Iso.refl (W.obj (op M))))).hom).mp
      change U.map (Prod.mkHom (rho.hom.app K ≫ J.map h) (𝟙 _)) ≫ _ =
        U.map (Prod.mkHom (rho.hom.app K ≫ J.map h') (𝟙 _)) ≫ _ at hh
      simpa only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Iso.refl_hom,
        ← Category.assoc, ← U.map_comp, prod_comp, Category.id_comp] using hh
    have hd : W.map h.op = W.map h'.op := by
      apply ((adjY (L.obj K).obj).homEquiv (W.obj (op M))
        wY.omega.obj).symm.injective
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
      change U.map (Prod.mkHom (𝟙 (L.obj K).obj) (W.map h.op)) ≫
          (adjY (L.obj K).obj).counit.app wY.omega.obj =
        U.map (Prod.mkHom (𝟙 (L.obj K).obj) (W.map h'.op)) ≫
          (adjY (L.obj K).obj).counit.app wY.omega.obj
      have hn := natY
        M.obj (L.obj K).obj wY.omega.obj h.hom
      have hn' := natY
        M.obj (L.obj K).obj wY.omega.obj h'.hom
      exact hn.trans (hu.trans hn'.symm)
    have hh' : h.op = h'.op :=
      (IntegralVerdier.restrictedDual l E Y wY.omega.obj pY).map_injective
        (ObjectProperty.hom_ext _ hd)
    exact congrArg Quiver.Hom.unop hh'
  have p_eq (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y) (h : K ⟶ H.obj M) :
      p K M h = pi0 K.obj (W.obj (op M)) ≫
        P.map (T.map (Prod.mkHom (𝟙 K.obj)
            ((CoefDualFormulaScalarTranspose.pullCompletion l E f).app (W.obj (op M)))) ≫
          (sN.swap K.obj (V.obj (op M))).hom ≫
          T.map (Prod.mkHom (𝟙 _) h.hom) ≫
          (adjX (V.obj (op M))).counit.app wX.omega.obj) ≫ t := by
    have hs := sN.naturality K.obj (V.obj (op M))
      (H.obj M).obj (V.obj (op M)) h.hom (𝟙 _)
    dsimp only [p, theta, tau]
    simp only [Category.assoc]
    rw [← Category.assoc (T.map _) (sN.swap _ _).hom, hs]
    simp only [P.map_comp, Category.assoc]
    rfl
  let k (M : sfIntegralConstructibleCategory l E Y) : G.obj M ≅ H.obj M :=
    ObjectProperty.isoMk _
      (CoefDualFormulaScalarTranspose.formulaIso D l hl E f c wX wY aX aZ aY sX G adj M)
  have normalized (M : sfIntegralConstructibleCategory l E Y) :
      p (G.obj M) M (k M).hom = q (G.obj M) M (adj.counit.app M) := by
    have hk := (CoefDualFormulaScalarTranspose.formula_existsUnique D l hl E f c
      wX wY aX aZ aY sX G adj M).exists.choose_spec
    rw [p_eq]
    exact hk
  let e : G ≅ H := NatIso.ofComponents k
    (normalized_components_natural L G H adj Pair left right p q
      (fun g M h ↦ pl g M h) (fun K _ _ g h ↦ pr K g h)
      (fun g M h ↦ ql g M h) (fun K _ _ g h ↦ qr K g h) qi k normalized)
  refine ⟨e, ?_⟩
  intro M
  have he := normalized_identity_transport adj Pair left p q
    (fun g N h ↦ pl g N h) (fun g N h ↦ ql g N h) e normalized M
  rw [p_eq] at he
  exact he

end WeilConjectures.RationalOperations
