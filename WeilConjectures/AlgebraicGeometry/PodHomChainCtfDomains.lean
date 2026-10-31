/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCtfPairingMaps

/-! # Finite-Tor domains and the five tensor-Hom bijections

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md, Step 1 read backwards
(blueprint: lem-pod-hom-chain-ctf-domains).

The coefficient selector ranges over the finite, completed integral, rational,
and common finite-stage categories. All maps use the supplied restricted
adjunctions and the canonical compactification projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.PodHomChainDomains

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : PodCtfAdjunctionData (PodCoefficientStage.operations S s)
    (PodCoefficientStage.domain S s) (PodCoefficientStage.homPairs (S := S) s)
    (PodCoefficientStage.internalHom (S := S) s) (PodCoefficientStage.tensor S s) f c)

/-- L_N is the recorded restricted internal Hom of M into Rf!N.
Source: Step 1 (blueprint: lem-pod-hom-chain-ctf-domains). -/
abbrev localHom (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  (PodCtfPairing.homX S s f c R M).obj (R.exceptional.obj N)

/-- A_N is the ordinary direct image of L_N, on the full finite-Tor category.
Source: Step 1 (blueprint: lem-pod-hom-chain-ctf-domains). -/
abbrev directHom (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  R.direct.obj (localHom S s f c R M N)

/-- B_N is the recorded internal Hom of C=Rf_!M into N.
Source: Step 1 (blueprint: lem-pod-hom-chain-ctf-domains). -/
abbrev supportHom (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  (PodCtfPairing.homY S s f c R (R.support.obj M)).obj N

/-- The chosen left-factor tensor on the source finite-Tor category.
Source: Step 1 (blueprint: lem-pod-hom-chain-ctf-domains). -/
abbrev tensorX := @MonoidalCategory.curriedTensor _ _ R.closedX.closed.monoidal

/-- The chosen left-factor tensor on the target finite-Tor category.
Source: Step 1 (blueprint: lem-pod-hom-chain-ctf-domains). -/
abbrev tensorY := @MonoidalCategory.curriedTensor _ _ R.closedY.closed.monoidal

/-- Every object in the Hom chain has the stated finite-Tor domain, the projection
at A_N is defined and invertible, and the five specified maps are bijective.
The maps are, in order, inverse ordinary adjunction, inverse left-factor
 tensor-Hom, inverse exceptional adjunction, precomposition by the forward
projection P_T, and forward left-factor tensor-Hom. Their displayed types are
exactly the six successive Hom sets of the node.

Source: current blueprint, fix-lem-tensor-adjunction.proof.md, Step 1 backwards
(blueprint: lem-pod-hom-chain-ctf-domains).

Proof plan:
1. Restrict the supplied exceptional adjunction (fix-prop-adjunctions): support
sends M to C and exceptional sends N to Rf!N in the finite-Tor domains.
Finite pullback stability is thm-sf-ctf-stability(i); at integral coefficients
use the completed construction and Dbc=Dctf, and then rationalization and the
common finite-stage conventions.
2. Tensor and general internal-Hom stability, thm-sf-ctf-stability(ii), put
M tensor f*T, L_N and B_N in those domains. Direct-image stability puts A_N
there. At integral coefficients use lem-sf-integral-direct-image-constructible
and the integral Hom clause of thm-sf-ctf-stability(vii). Pass to the two field
stages on integral objects and at a common finite coefficient field.
3. Apply fix-prop-projection-formula with K=M and L=T, and again with L=A_N.
The map is the def-exchange-projection component, transported through the
specified tensor comparisons, exactly PodCtfPairing.projection.
4. Evaluate the fully faithful restricted ordinary adjunction at (T,L_N),
the chosen left-factor tensor-Hom adjunction at (f*T,Rf!N), and the supplied
exceptional adjunction at (M tensor f*T,N). Take each inverse Hom bijection.
5. Precomposition with P_T is inverse to precomposition with P_T inverse,
by associativity and the two inverse identities. Finally apply the chosen
left-factor tensor-Hom adjunction on Y at (T,N), with left factor C.
These are the five stated bijections, all on the actual full subcategories.
-/
theorem domains_and_bijections
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    PodCoefficientStage.domain S s Y (R.support.obj M).obj ∧
    PodCoefficientStage.domain S s Y (directHom S s f c R M N).obj ∧
    PodCoefficientStage.domain S s Y (supportHom S s f c R M N).obj ∧
    PodCoefficientStage.domain S s X (R.exceptional.obj N).obj ∧
    PodCoefficientStage.domain S s X (localHom S s f c R M N).obj ∧
    PodCoefficientStage.domain S s X (R.pull.obj T).obj ∧
    PodCoefficientStage.domain S s X
      (((tensorX S s f c R).obj M).obj (R.pull.obj T)).obj ∧
    IsIso (PodCtfPairing.projection S s f c R M (directHom S s f c R M N)) ∧
    Function.Bijective
      ((R.ordinaryAdjunction.homEquiv T (localHom S s f c R M N)).symm :
        (T ⟶ directHom S s f c R M N) →
          (R.pull.obj T ⟶ localHom S s f c R M N)) ∧
    Function.Bijective
      (((R.tensorAdjunctionX M).homEquiv (R.pull.obj T) (R.exceptional.obj N)).symm :
        (R.pull.obj T ⟶ localHom S s f c R M N) →
          (((tensorX S s f c R).obj M).obj (R.pull.obj T) ⟶ R.exceptional.obj N)) ∧
    Function.Bijective
      ((R.exceptionalAdjunction.homEquiv
        (((tensorX S s f c R).obj M).obj (R.pull.obj T)) N).symm :
        (((tensorX S s f c R).obj M).obj (R.pull.obj T) ⟶ R.exceptional.obj N) →
          (R.support.obj (((tensorX S s f c R).obj M).obj (R.pull.obj T)) ⟶ N)) ∧
    Function.Bijective
      (fun v : R.support.obj (((tensorX S s f c R).obj M).obj (R.pull.obj T)) ⟶ N ↦
        PodCtfPairing.projection S s f c R M T ≫ v) ∧
    Function.Bijective
      ((R.tensorAdjunctionY (R.support.obj M)).homEquiv T N :
        (((tensorY S s f c R).obj (R.support.obj M)).obj T ⟶ N) →
          (T ⟶ supportHom S s f c R M N)) := by
  refine ⟨(R.support.obj M).property, (directHom S s f c R M N).property,
    (supportHom S s f c R M N).property, (R.exceptional.obj N).property,
    (localHom S s f c R M N).property, (R.pull.obj T).property,
    (((tensorX S s f c R).obj M).obj (R.pull.obj T)).property, ?_,
    (R.ordinaryAdjunction.homEquiv T (localHom S s f c R M N)).symm.bijective,
    ((R.tensorAdjunctionX M).homEquiv (R.pull.obj T)
      (R.exceptional.obj N)).symm.bijective,
    (R.exceptionalAdjunction.homEquiv
      (((tensorX S s f c R).obj M).obj (R.pull.obj T)) N).symm.bijective, ?_,
    ((R.tensorAdjunctionY (R.support.obj M)).homEquiv T N).bijective⟩
  · change IsIso (PodCtfPairing.projectionIso S s f c R M
      (directHom S s f c R M N)).hom
    infer_instance
  · let p := PodCtfPairing.projectionIso S s f c R M T
    change Function.Bijective (fun v ↦ p.hom ≫ v)
    constructor
    · intro v w h
      have h' := congrArg (fun v ↦ p.inv ≫ v) h
      simpa only [← Category.assoc, p.inv_hom_id, Category.id_comp] using h'
    · intro v
      exact ⟨p.inv ≫ v, by simp only [← Category.assoc, p.hom_inv_id,
        Category.id_comp]⟩

end WeilConjectures.PodHomChainDomains
