/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.Paper.PodCtfAdjunctions
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Sheaf.Paper.PodHomChainUncurriedTransport
import Sheaf.Paper.HomChainPairingNaturality

/-! # Counit representative of the inverse tensor-Hom chain

Source: main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md, Step 1 read backwards
(blueprint: lem-pod-hom-chain-counit-formula).

The projection is the actual compactification projection at the selected stage.
Closed presentations are supplied restrictions of the recorded tensor and Hom;
the result quantifies over these choices, as the node specifies a chosen adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u a b
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
namespace PodHomChain

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : PodCtfAdjunctionData (PodCoefficientStage.operations S s)
    (PodCoefficientStage.domain S s) (PodCoefficientStage.homPairs (S := S) s)
    (PodCoefficientStage.internalHom (S := S) s) (PodCoefficientStage.tensor S s) f c)

/-- The canonical projection at the four coefficient stages, in the actual partial
finite-Tor tensor coordinates. Source: the fourth bijection of the Hom chain
(blueprint: lem-pod-hom-chain-counit-formula). -/
def rawProjection
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    ((PodCoefficientStage.tensor S s Y).obj (R.support.obj M).obj).obj T ⟶
      ((PodCoefficientStage.operations S s).support f c).obj
        (((PodCoefficientStage.tensor S s X).obj M.obj).obj (R.pull.obj T)) := by
  cases s with
  | finite =>
    exact CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c M.obj
      ⟨T.obj.obj, T.property⟩
  | integral =>
    exact compactSupportProjectionComponent S.higher.integralExchange f c M.obj T.obj
  | rational =>
    exact compactSupportProjectionComponent S.higher.rationalExchange f c M.obj T.obj
  | common =>
    exact compactSupportProjectionComponent S.closure.commonStageExchange f c M.obj T.obj

/-- The actual projection isomorphism, supplied by the recorded projection theorem.
Source: fix-prop-projection-formula at the four stages
(blueprint: lem-pod-hom-chain-counit-formula). -/
def rawProjectionIso
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    ((PodCoefficientStage.tensor S s Y).obj (R.support.obj M).obj).obj T ≅
      ((PodCoefficientStage.operations S s).support f c).obj
        (((PodCoefficientStage.tensor S s X).obj M.obj).obj (R.pull.obj T)) := by
  cases s with
  | finite =>
    have h := (compactSupportProjectionFormula S).1.isIso f c M.obj
      ⟨T.obj.obj, T.property⟩
    exact @asIso _ _ _ _ (rawProjection S .finite f c R M T) h
  | integral =>
    have h := (compactSupportProjectionFormula S).2.1.isIso f c M.obj T.obj T.property
    exact @asIso _ _ _ _ (rawProjection S .integral f c R M T) h
  | rational =>
    have h := (compactSupportProjectionFormula S).2.2.1.isIso f c M.obj T.obj trivial
    exact @asIso _ _ _ _ (rawProjection S .rational f c R M T) h
  | common =>
    have h := (compactSupportProjectionFormula S).2.2.2.1.isIso f c M.obj T.obj trivial
    exact @asIso _ _ _ _ (rawProjection S .common f c R M T) h

/-- Projection transported through the specified tensor comparisons and full inclusion.
Its direction is C tensor T to f_!(M tensor f^*T).
Source: the fourth bijection and P_T (blueprint: lem-pod-hom-chain-counit-formula). -/
def projectionIso
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).obj T ≅
      R.support.obj
        ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).obj
          (R.pull.obj T)) :=
  (PodCoefficientStage.domain S s Y).ι.preimageIso
    ((R.tensorY (R.support.obj M)).app T ≪≫ rawProjectionIso S s f c R M T ≪≫
      ((PodCoefficientStage.operations S s).support f c).mapIso
        ((R.tensorX M).app (R.pull.obj T)).symm)

/-- The specified forward projection map, rather than its inverse.
Source: P_T in the node (blueprint: lem-pod-hom-chain-counit-formula). -/
def projection
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  (projectionIso S s f c R M T).hom

variable [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

/-- Internal Hom with left input M, using the dependency's restricted Hom functor.
Source: L_N in the Hom chain (blueprint: lem-pod-hom-chain-counit-formula). -/
def homX (M : (PodCoefficientStage.domain S s X).FullSubcategory) :=
  Prod.sectR (op M) _ ⋙ sixFunctorDomainHom _ _ _
    R.closedX.homPermitted R.closedX.homDomain

/-- Internal Hom on Y with left input C, using the same closed restriction.
Source: B_N in the Hom chain (blueprint: lem-pod-hom-chain-counit-formula). -/
def homY (K : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  Prod.sectR (op K) _ ⋙ sixFunctorDomainHom _ _ _
    R.closedY.homPermitted R.closedY.homDomain

/-- A_N, with L_N the chosen restricted internal Hom of M into f^!N.
Source: the definitions preceding p_N (blueprint: lem-pod-hom-chain-counit-formula). -/
def sourceFunctor (M : (PodCoefficientStage.domain S s X).FullSubcategory) :=
  R.exceptional ⋙ (homX S s f c R M) ⋙ R.direct

/-- B_N is the chosen restricted internal Hom of C=f_!M into N.
Source: the definitions preceding p_N (blueprint: lem-pod-hom-chain-counit-formula). -/
def targetFunctor (M : (PodCoefficientStage.domain S s X).FullSubcategory) :=
  (homY S s f c R (R.support.obj M))

/-- The displayed counit-evaluation pairing p_N. The first counit is ordinary,
then evaluation is the counit of the chosen left-factor tensor-Hom adjunction,
and the final counit is exceptional.
Source: the displayed definition of p_N (blueprint: lem-pod-hom-chain-counit-formula). -/
def pairing
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).obj
      ((sourceFunctor S s f c R M).obj N) ⟶ N :=
  projection S s f c R M ((sourceFunctor S s f c R M).obj N) ≫
    R.support.map
      ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).map
          (R.ordinaryAdjunction.counit.app
            ((homX S s f c R M).obj (R.exceptional.obj N))) ≫
        (R.tensorAdjunctionX M).counit.app (R.exceptional.obj N)) ≫
    R.exceptionalAdjunction.counit.app N

/-- The curried representative k_N=curry(p_N), using the same chosen adjunction
as the fifth bijection. Source: the conclusion's curry
(blueprint: lem-pod-hom-chain-counit-formula). -/
def curriedPairing
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  (R.tensorAdjunctionY (R.support.obj M)).homEquiv _ N (pairing S s f c R M N)

/-- The first four arrows: inverse ordinary adjunction, inverse tensor-Hom,
inverse exceptional adjunction, and precomposition with the specified projection.
Source: the displayed chain (blueprint: lem-pod-hom-chain-counit-formula). -/
def uncurriedChain
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (t : T ⟶ (sourceFunctor S s f c R M).obj N) :=
  projection S s f c R M T ≫
    (R.exceptionalAdjunction.homEquiv _ N).symm
      (((R.tensorAdjunctionX M).homEquiv _ _).symm
        ((R.ordinaryAdjunction.homEquiv T _).symm t))

/-- The five specified bijections, with projection precomposition in the fourth
position. The isomorphism evidence concerns the actual canonical projection above.
Source: the displayed Phi (blueprint: lem-pod-hom-chain-counit-formula). -/
def homEquiv
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (T ⟶ (sourceFunctor S s f c R M).obj N) ≃
      (T ⟶ (targetFunctor S s f c R M).obj N) :=
  ((R.ordinaryAdjunction.homEquiv T _).symm.trans
    ((R.tensorAdjunctionX M).homEquiv _ _).symm).trans
      (((R.exceptionalAdjunction.homEquiv _ N).symm.trans
        (Iso.homCongr (projectionIso S s f c R M T).symm
          (Iso.refl N))).trans ((R.tensorAdjunctionY (R.support.obj M)).homEquiv T N))

/-- The inverse Hom chain is postcomposition with curry(p_N), naturally in both
T and N, at each of the four coefficient stages.

Source: main-20261015, fix-lem-tensor-adjunction.proof.md, Step 1 read backwards
(blueprint: lem-pod-hom-chain-counit-formula).

Proof plan:
1. lem-pod-hom-chain-ctf-domains puts C, L_N, A_N, B_N and all tensor inputs
in the stated full finite-Tor categories. Thus P_{A_N} is legitimate and the
five arrows in homEquiv have exactly the node's directions.
2. lem-pod-hom-chain-uncurried-transport identifies the first four arrows with
(1_C tensor t);p_N. The inverse and parameter-naturality laws of
lem-pod-closed-uncurry-laws then identify the fifth arrow with t;curry(p_N).
3. For a:T' to T, associativity gives the test-object equation below; tensor
functoriality gives the corresponding equation before the final curry.
4. For r:N to N', lem-pod-hom-chain-pairing-naturality gives
(1_C tensor A(r));p_{N'}=p_N;r by ordinary counit, evaluation, exceptional
counit and projection naturality. Curry and use source/target naturality of
the same adjunction to obtain A(r);k_{N'}=k_N;B(r). Composing with t gives
the last equation. Integral operations are completed; the other two field
stages rationalize these maps and use a common finite coefficient stage.
-/
theorem counit_formula
    (M : (PodCoefficientStage.domain S s X).FullSubcategory) :
    (∀ (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (t : T ⟶ (sourceFunctor S s f c R M).obj N),
      homEquiv S s f c R M N T t = t ≫ curriedPairing S s f c R M N) ∧
    (∀ (N T T' : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (a : T' ⟶ T) (t : T ⟶ (sourceFunctor S s f c R M).obj N),
      homEquiv S s f c R M N T' (a ≫ t) =
        a ≫ homEquiv S s f c R M N T t) ∧
    (∀ (N N' T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (r : N ⟶ N') (t : T ⟶ (sourceFunctor S s f c R M).obj N),
      homEquiv S s f c R M N' T (t ≫ (sourceFunctor S s f c R M).map r) =
        homEquiv S s f c R M N T t ≫ (targetFunctor S s f c R M).map r) := by
  have formula : ∀ (N T : (PodCoefficientStage.domain S s Y).FullSubcategory)
      (t : T ⟶ (sourceFunctor S s f c R M).obj N),
      homEquiv S s f c R M N T t = t ≫ curriedPairing S s f c R M N := by
    intro N T t
    have h := (uncurried_transport S s f c R M N (R.tensorAdjunctionX M) T t).2.2.2.2.1
    change uncurriedChain S s f c R M N T t =
      (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal
        (R.support.obj M)).map t ≫ pairing S s f c R M N at h
    simp only [homEquiv, Equiv.trans_apply, Iso.homCongr_apply,
      Iso.symm_inv, Iso.refl_hom, Category.comp_id, curriedPairing]
    convert (congrArg ((R.tensorAdjunctionY (R.support.obj M)).homEquiv T N) h).trans
      ((R.tensorAdjunctionY (R.support.obj M)).homEquiv_naturality_left t
        (pairing S s f c R M N)) using 1 <;> rfl
  refine ⟨formula, ?_, ?_⟩
  · intro N T T' a t
    rw [formula, formula, Category.assoc]
  · intro N N' T r t
    have h := (HomChain.pairing_naturality S s f c R M r).2.2.2.2.2
    change (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal
        (R.support.obj M)).map ((sourceFunctor S s f c R M).map r) ≫
        pairing S s f c R M N' = pairing S s f c R M N ≫ r at h
    have k := congrArg ((R.tensorAdjunctionY (R.support.obj M)).homEquiv _ N') h
    rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right] at k
    rw [formula, formula, Category.assoc]
    simpa only [curriedPairing, targetFunctor, homY, Category.assoc] using
      congrArg (fun z ↦ t ≫ z) k

end PodHomChain
end WeilConjectures
