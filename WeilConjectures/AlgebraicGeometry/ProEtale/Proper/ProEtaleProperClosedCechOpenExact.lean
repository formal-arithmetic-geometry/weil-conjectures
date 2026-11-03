/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Exactness of the proper closed Čech presentation on the complementary open

Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Over the proper scheme `P = B ×_D W` itself, the closed Čech presentation of a finite
cover with affine Čech intersections is exact after restriction to the open part
`B ×_D E`.

Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`
(the analogue of `closedAffineCech_open_restriction_exact` for the non-affine object `P`).

Remarks: by the corepresenting property and `b^* ⊣ b_*`, this is equivalent to positive
Čech exactness of `P^* z_* z^* b_* J` on the cover `U` for every injective `J` on the open
`B ×_D E`, i.e. to the case `I = b_* J` of `exactAt_proper_closed_injective_cech`. Since all
Čech intersections are affine, this amounts to the vanishing of the positive cohomology of
`z^* b_* J` on the closed fibre `P_Z`, an instance of proper base change for the henselian
pair `(Γ(W), J_W)`; this is why properness, `hW` and `hspecializes` are needed.

Status: not proved here. With `j` the open complement of `z` on `P`, it amounts to
`H^m(P, j_! j^* I) = 0` for `m ≥ 2` and injective `I`. This is proper base change for the
henselian pair `(Γ(W), J_W)` and arbitrary pro-étale sheaves, not only those coming from the
étale site. Approaches that do not suffice:
* dimension shifting with the degree-zero statement `proper_closed_injective_sections_epi`
  only reproduces this statement;
* `z^*` does not preserve injectives;
* the earlier plan compared with the Čech complex of `I` on henselian lifts of the closed
  fibres. It fails because fibre products over `P` of henselian lifts are not henselian lifts:
  they acquire clopen parts with empty closed fibre, from distinct branches over the open part;
* iterating `closedLiftGeneratorAugmentation` needs the higher analogue of
  `proper_closedLift_relations_generated` and the affine statement
  `exactAt_closedCechCoefficientFunctor_obj_of_injective`.

The degree-zero companion `proper_closed_injective_sections_epi` is false. Take `D`, `E`, `W` and
the nodal-cubic family `B` from the warning in `proper_closed_lift_local_chains_nhds`. Let `ω` be
`Spec` of an algebraic closure of the function field of `B`, and let `I = ω_* A^∨`, where
`I(Y) = (A^∨)^{Hom_B(ω, Y)}`. Then `Hom(F, I) = Hom_A(F(ω), A^∨)`, so `I` is injective, and
`I = b_* b^* I`. By Stacks 09BL, a section of `z^* I` on `B_s` is a function of the pairs `(T, a)`.
Here `T` is an affine weakly contractible object over `B_s` and `a : ω ⟶ T^h`. The function must
be invariant under maps `T' ⟶ T`. The tower of `n`-gon covers lifts to a pro-finite-étale
`Ẑ`-torsor `Ŷ ⟶ B`. Its special fibre is a `Ẑ`-gon, whose classes under finite zigzags of
specializations form `Ẑ/ℤ`. Fix a lift `ω ⟶ Ŷ` and send `(T, a)` to the zigzag class of the
image in `Ŷ_s` of the unique closed specialization of `(a, ω ⟶ Ŷ)` in `T^h ×_B Ŷ`. This class is
invariant, and precomposing `a` with Galois elements realizes every class over the node. So
`z^* I` has nonconstant global sections, while `I(B) = A^∨` only gives constant ones.

The same family does not refute this statement. For `J = ω_* Q` and a cover of `B` by opens,
positive Čech cohomology is the cokernel of `H_1` of the zigzag graphs of the pieces of the
normalization `Ỹ_s` of `B_s` in `ω`, mapping to `H_1` of the whole graph. That graph is a forest:
a finite cycle survives to a finite level, and a finite étale cover of that special fibre,
trivial on its components, unwinds the cycle. -/
theorem properClosedCech_open_restriction_exact
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z))
    {n : ℕ} (U : Fin n → Over (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)))
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology ((proEtaleBaseChange p).obj W).left
        (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)))
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A (pullback.fst p i) ((proEtaleBaseChange p).obj W)
        (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)) U) q) :
    (T.complex.map (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i))).Exact := by
  sorry

end AlgebraicGeometry.Scheme
