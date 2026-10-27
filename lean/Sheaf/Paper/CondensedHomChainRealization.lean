module

public import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # The condensed tensor–Hom chain and its specified representative

Source: blueprint, sec-six-functors/sk-thm-sf-tensor-hom, displayed Hom chain,
read in reverse in the condensed bounded constructible categories
(blueprint: lem-pd-condensed-hom-chain-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite Profinite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)
  (K : BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) X.left))
  (L : BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left))

/-- The object W = H_X(K,V L), in the full bounded constructible category.
Source: blueprint tensor–Hom chain (blueprint: lem-pd-condensed-hom-chain-realization). -/
def condensedHomChainInner :
    BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) X.left) :=
  ((boundedConstructibleHom (padicAlgClRingObj ℓ) X).obj (op K)).obj
    ((boundedConstructibleUpperShriek (padicAlgClRingObj ℓ) ℓ f).obj L)

/-- The object E = G W; in particular E itself is an allowed test object.
Source: blueprint tensor–Hom chain (blueprint: lem-pd-condensed-hom-chain-realization). -/
def condensedHomChainSource :
    BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left) :=
  (boundedConstructibleLowerStar (padicAlgClRingObj ℓ) ℓ f).obj
    (condensedHomChainInner ℓ f K L)

/-- The object D = H_Y(F K,L); in particular D itself is an allowed test object.
Source: blueprint tensor–Hom chain (blueprint: lem-pd-condensed-hom-chain-realization). -/
def condensedHomChainTarget :
    BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left) :=
  ((boundedConstructibleHom (padicAlgClRingObj ℓ) Y).obj
    (op ((boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).obj K))).obj L

variable (P :
  (boundedConstructibleTensor (padicAlgClRingObj ℓ) Y).obj
      ((boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).obj K) ≅
    boundedConstructibleUpperStar (padicAlgClRingObj ℓ) ℓ f ⋙
      (boundedConstructibleTensor (padicAlgClRingObj ℓ) X).obj K ⋙
        boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f)

/-- The five specified Hom bijections, in the direction Hom(B,E) → Hom(B,D).
The two geometric bijections and uncurrying are inverses of the specified adjunction
bijections; the fourth precomposes with P_B; the fifth is currying.
Source: blueprint displayed tensor–Hom chain
(blueprint: lem-pd-condensed-hom-chain-realization). -/
def condensedHomChain
    (B : BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left)) :
    (B ⟶ condensedHomChainSource ℓ f K L) ≃ (B ⟶ condensedHomChainTarget ℓ f K L) :=
  ((boundedConstructibleUpperStarLowerStarAdjunction (padicAlgClRingObj ℓ) ℓ f).homEquiv
    B (condensedHomChainInner ℓ f K L)).symm |>.trans
  (((boundedConstructibleTensorHomAdjunction (padicAlgClRingObj ℓ) K).homEquiv
    ((boundedConstructibleUpperStar (padicAlgClRingObj ℓ) ℓ f).obj B)
    ((boundedConstructibleUpperShriek (padicAlgClRingObj ℓ) ℓ f).obj L)).symm) |>.trans
  (((boundedConstructibleUpperShriekAdjunction (padicAlgClRingObj ℓ) ℓ f).homEquiv
    (((boundedConstructibleTensor (padicAlgClRingObj ℓ) X).obj K).obj
      ((boundedConstructibleUpperStar (padicAlgClRingObj ℓ) ℓ f).obj B)) L).symm) |>.trans
  (Iso.homCongr (P.app B).symm (Iso.refl L)) |>.trans
  ((boundedConstructibleTensorHomAdjunction (padicAlgClRingObj ℓ)
    ((boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).obj K)).homEquiv B L)

/-- The specified uncurried representative: P_B, then F(1_K ⊗ (U(h);ε_W)),
then F(evaluation), then the exceptional counit at L, in that order.
Source: blueprint tensor–Hom counit calculation
(blueprint: lem-pd-condensed-hom-chain-realization). -/
def condensedHomChainPairing
    (B : BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left))
    (h : B ⟶ condensedHomChainSource ℓ f K L) :
    ((boundedConstructibleTensor (padicAlgClRingObj ℓ) Y).obj
      ((boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).obj K)).obj B ⟶ L :=
  (P.app B).hom ≫
    (boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).map
      (((boundedConstructibleTensor (padicAlgClRingObj ℓ) X).obj K).map
        ((boundedConstructibleUpperStar (padicAlgClRingObj ℓ) ℓ f).map h ≫
          (boundedConstructibleUpperStarLowerStarAdjunction (padicAlgClRingObj ℓ) ℓ f).counit.app
            (condensedHomChainInner ℓ f K L))) ≫
    (boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).map
      ((boundedConstructibleTensorHomAdjunction (padicAlgClRingObj ℓ) K).counit.app
        ((boundedConstructibleUpperShriek (padicAlgClRingObj ℓ) ℓ f).obj L)) ≫
    (boundedConstructibleUpperShriekAdjunction (padicAlgClRingObj ℓ) ℓ f).counit.app L

/-- Φ is the curry of exactly P_E; F(1_K ⊗ ε_W); F(evaluation); ε!_L.
Source: blueprint tensor–Hom specified pairing
(blueprint: lem-pd-condensed-hom-chain-realization). -/
def condensedHomChainExchange :
    condensedHomChainSource ℓ f K L ⟶ condensedHomChainTarget ℓ f K L :=
  (boundedConstructibleTensorHomAdjunction (padicAlgClRingObj ℓ)
    ((boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).obj K)).homEquiv _ L
      ((P.app (condensedHomChainSource ℓ f K L)).hom ≫
        (boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).map
          (((boundedConstructibleTensor (padicAlgClRingObj ℓ) X).obj K).map
            ((boundedConstructibleUpperStarLowerStarAdjunction
              (padicAlgClRingObj ℓ) ℓ f).counit.app (condensedHomChainInner ℓ f K L))) ≫
        (boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).map
          ((boundedConstructibleTensorHomAdjunction (padicAlgClRingObj ℓ) K).counit.app
            ((boundedConstructibleUpperShriek (padicAlgClRingObj ℓ) ℓ f).obj L)) ≫
        (boundedConstructibleUpperShriekAdjunction (padicAlgClRingObj ℓ) ℓ f).counit.app L)

/-- The five-step equivalence is natural in every bounded constructible test object,
and its value is both the specified curried counit representative and postcomposition
with Φ. Source: blueprint tensor–Hom displayed Hom chain
(blueprint: lem-pd-condensed-hom-chain-realization).

Proof (postponed):
1. The restricted ordinary and exceptional adjunctions and the two left-factor
   tensor–Hom adjunctions give four bijections. Precomposition with P_B is the
   fifth, with inverse precomposition with its inverse. Their composite is the
   defined equivalence. Closure puts W, E and D in the same full categories.
2. Apply Adjunction.homEquiv_counit to the ordinary inverse adjunct of h, obtaining
   U(h);ε_W. Uncurrying is tensoring this map on the left by K, then evaluation.
   Apply homEquiv_counit to the exceptional inverse adjunct, precompose with P_B,
   and curry. Functoriality gives exactly condensedHomChainPairing.
3. Naturality of P at h moves F(1_K ⊗ U(h)) through P_B. Tensor functoriality
   factors the pairing as (1_FK ⊗ h) followed by the pairing at E. Naturality
   of currying gives h;Φ, with exactly the defined Φ and its specified counits.
4. For a : B' → B, associativity gives b_B'(a;h) = a;b_B(h). All B are allowed,
   including E and D. No comparison of coefficient categories is used. -/
theorem condensedHomChain_realization :
    (∀ (B B' : BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left))
      (a : B' ⟶ B) (h : B ⟶ condensedHomChainSource ℓ f K L),
      condensedHomChain ℓ f K L P B' (a ≫ h) = a ≫ condensedHomChain ℓ f K L P B h) ∧
    (∀ (B : BoundedConstructible (condensedRingObj (padicAlgClRingObj ℓ) Y.left))
      (h : B ⟶ condensedHomChainSource ℓ f K L),
      condensedHomChain ℓ f K L P B h =
        (boundedConstructibleTensorHomAdjunction (padicAlgClRingObj ℓ)
          ((boundedConstructibleLowerShriek (padicAlgClRingObj ℓ) ℓ f).obj K)).homEquiv B L
            (condensedHomChainPairing ℓ f K L P B h) ∧
      condensedHomChain ℓ f K L P B h = h ≫ condensedHomChainExchange ℓ f K L P) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
