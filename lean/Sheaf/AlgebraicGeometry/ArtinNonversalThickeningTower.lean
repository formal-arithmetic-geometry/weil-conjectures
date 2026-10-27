/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Non-retractable first order deformation towers

Source: Stacks Project, artin.tex, Tag 0G2S (lemma-infinite-sequence-pre),
conditions (1) and (3), over Spec Z, and Tag 0CXU
(blueprint: lem-sfb-artin-nonversal-thickening-tower).

The positive stages are indexed by `n : ℕ`: `R n` denotes the paper's `R_(n+1)`.
The given zero stage is kept separately, so its object is literally `x`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ArtinCriterion

/-- No local retraction preserving the specified reduction arrow. The two fibre
objects `z` and `y` express restriction to W and to its inverse image in U.
The first equation identifies the restricted marking; the second says that the
putative retraction extends its inverse. In a fibred groupoid every lifted arrow
is cartesian, so this is the arrow formulation of condition (3).
Source: Stacks Project, artin.tex, Tag 0G2S, condition (3)
(blueprint: lem-sfb-artin-nonversal-thickening-tower). -/
def HasNoLocalMarkedRetraction
    {F : BasedCategory.{v, w} (Over Base.{u})} {U T : Scheme.{u}}
    (x : Object F (integerScheme U)) (xt : Object F (integerScheme T))
    (j : U ⟶ T) (mark : Lift (overMap j) x xt) (u₀ : U) : Prop :=
  ∀ W : T.Opens, j u₀ ∈ W →
    ¬ ∃ (r : W.toScheme ⟶ U)
      (z : Object F (integerScheme W.toScheme))
      (a : Lift (overMap W.ι) z xt) (b : Lift (overMap r) z x)
      (y : Object F (integerScheme (j ⁻¹ᵁ W).toScheme))
      (c : Lift (overMap (j ⁻¹ᵁ W).ι) y x)
      (d : Lift (overMap (j ∣_ W)) y z),
      (j ∣_ W) ≫ r = (j ⁻¹ᵁ W).ι ∧
        d.val ≫ a.val = c.val ≫ mark.val ∧ d.val ≫ b.val = c.val

/-- A tower with the fixed zero stage kept separately. Here `R n`, `obj n`, and
`points n` correspond to positive stage n+1. The maps `reduction` are the
composites to the zero stage; the two compatibility equations retain all the
specified reduction identifications. There is no residue-field transition-kernel
condition, which is condition (2) of 0G2S and is omitted by this node.
Source: Stacks Project, artin.tex, Tag 0G2S, conditions (1) and (3), and the
explicit affine fibre products in Tag 0CXU
(blueprint: lem-sfb-artin-nonversal-thickening-tower). -/
structure NonversalThickeningTower
    (F : BasedCategory.{v, w} (Over Base.{u})) (R₀ : CommRingCat.{u})
    (x : Object F (integerScheme (Spec R₀))) (points : ℕ → Spec R₀) where
  R : ℕ → CommRingCat.{u}
  reduction : ∀ n : ℕ, R n ⟶ R₀
  transition : ∀ n : ℕ, R (n + 1) ⟶ R n
  initial_surjective : Function.Surjective (reduction 0).hom
  transition_surjective : ∀ n : ℕ, Function.Surjective (transition n).hom
  reduction_comp : ∀ n : ℕ, transition n ≫ reduction n = reduction (n + 1)
  square_zero : ∀ n : ℕ, RingHom.ker (reduction n).hom ^ 2 = ⊥
  first_order : ∀ n : ℕ, IsFirstOrderThickening (Spec.map (reduction n))
  thickening : ∀ n : ℕ, IsThickening (Spec.map (reduction n))
  obj : ∀ n : ℕ, Object F (integerScheme (Spec (R n)))
  mark : ∀ n : ℕ, Lift (overMap (Spec.map (reduction n))) x (obj n)
  step : ∀ n : ℕ, Lift (overMap (Spec.map (transition n))) (obj n) (obj (n + 1))
  mark_comp : ∀ n : ℕ, (mark n).val ≫ (step n).val = (mark (n + 1)).val
  no_retraction : ∀ n : ℕ,
    HasNoLocalMarkedRetraction x (obj n) (Spec.map (reduction n)) (mark n) (points n)

/-- Nonversality at an antichain of finite-type points gives an affine tower of
first order deformations without local marked retractions. The gluing hypothesis
uses all commutative rings, not just Artinian local rings. Its pushout in the
total category is equivalent to restriction being an equivalence to the groupoid
of pairs with a specified identification: its universal property includes arrows
and their uniqueness, as well as existence of the glued object.
Source: Stacks Project, artin.tex, Tag 0G2S (lemma-infinite-sequence-pre),
conditions (1) and (3), specialized to Spec Z
(blueprint: lem-sfb-artin-nonversal-thickening-tower).

Proof:
1. Apply lem-sfb-artin-single-point-obstruction at each point (the integers are
Noetherian). Obtain S_n surjecting onto R₀ with square-zero kernel isomorphic to
κ(u_n), a deformation y_n, and its specified reduction to x with no local
marked retraction.
2. Form R_n as the subring of the finite product of S_1,...,S_n whose coordinates
have the same image in R₀. Forgetting the last coordinate is surjective by lifting
its common image to S_n. Its composite to R₀ has kernel the product of the
square-zero kernels, hence has square zero. The affine closed immersion is a
first order thickening by def-sbc-first-order-thickening and
def-weil-closed-immersion, and is a homeomorphism on underlying spaces.
3. Since R_n = R_(n-1) ×_(R₀) S_n, the assumed gluing equivalence produces x_n
with restriction arrows to x_(n-1) and y_n that preserve their common reduction.
Choose these successively. Their composites give the coherent markings from x.
4. Pull a hypothetical local marked retraction at stage n back along
Spec S_n → Spec R_n. Its inverse-image open contains u_n and its reduction is
the same open in U. The identification with y_n preserves the marking, so the
pulled-back arrow contradicts lem-sfb-artin-single-point-obstruction.
The stronger residue-field transition-kernel clause is not asserted. -/
theorem exists_nonversalThickeningTower
    (F : BasedCategory.{v, w} (Over Base.{u}))
    (hFibred : IsFibredInGroupoids F)
    (hGluing : ∀ (A B B' : CommRingCat.{u}) (f : A ⟶ B) (g : B' ⟶ B),
      Function.Surjective g.hom → RingHom.ker g.hom ^ 2 = ⊥ →
      ∀ (P : Over Base.{u}) (i : integerScheme (Spec A) ⟶ P)
        (j : integerScheme (Spec B') ⟶ P),
        IsPushout (overMap (Spec.map f)) (overMap (Spec.map g)) i j →
        ∀ (z : Object F (integerScheme (Spec B)))
          (a : Object F (integerScheme (Spec A)))
          (b : Object F (integerScheme (Spec B')))
          (az : Lift (overMap (Spec.map f)) z a)
          (bz : Lift (overMap (Spec.map g)) z b),
          ∃ (c : Object F P) (ac : Lift i a c) (bc : Lift j b c),
            IsPushout az.val bz.val ac.val bc.val)
    (R₀ : CommRingCat.{u})
    (hFiniteType : LocallyOfFiniteType (specULiftZIsTerminal.from (Spec R₀)))
    (x : Object F (integerScheme (Spec R₀))) (points : ℕ → Spec R₀)
    (hPoints : ∀ n : ℕ, FiniteTypePoint (Spec R₀) (points n))
    (hAntichain : ∀ n m : ℕ, n ≠ m → ¬ Specializes (points n) (points m))
    (hNonversal : ∀ n : ℕ, ¬ IsVersalAt F (Spec R₀) x (points n)) :
    Nonempty (NonversalThickeningTower F R₀ x points) := by
  sorry

end AlgebraicGeometry.ArtinCriterion
