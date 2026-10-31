/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalGaloisConstruction

/-! # Algebraic reconstruction from rational Galois modules

Source: Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-e7-algebraic-galois-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

set_option maxHeartbeats 1000000 in
-- Dependent normalized coefficient comparisons require a larger elaboration budget.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The algebraic coefficient stage, relative to normalized integral and rational stages.
Source: Weil II (1.1.1) d), (1.1.6); Stanford L19, Proposition 1.1.9, first bullet.
(blueprint: new-e7-algebraic-galois-construction). -/
structure AlgebraicGaloisConstruction
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (i : ∀ E : Padic.FiniteCoefficientFields l Q,
      IntegralGaloisConstruction y G c P δ l E.val)
    (r : ∀ E : Padic.FiniteCoefficientFields l Q,
      RationalGaloisConstruction y G c P δ l E.val (i E)) where
  eA : LisseAlgebraicSheaf l Y Q ≌ galoisAdicRepresentations l Q P δ
  τA : eA.functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} Q G) (ModuleCat.{u + 1} Q) ≅
    lisseAlgebraicFiberFunctor l Y y Q
  /-- Every finite coefficient model enters the algebraic stage by normalized scalar
  extension, with the action determined on all pure tensors. -/
  colimit :
    ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y),
      ∃ η : (TensorProduct E.val Q ((r E).eR.functor.obj F).obj.V) ≃ₗ[Q]
          (eA.functor.obj (lisseAlgebraicOfModel l Y Q E F)).obj.V,
        (∀ (g : G) (a : Q) (z : ((r E).eR.functor.obj F).obj.V),
          η (TensorProduct.tmul _ a (((r E).eR.functor.obj F).obj.ρ g z)) =
            (eA.functor.obj (lisseAlgebraicOfModel l Y Q E F)).obj.ρ g
              (η (TensorProduct.tmul _ a z))) ∧
        ∀ (a : Q) (z : ((r E).eR.functor.obj F).obj.V),
          eqToHom (lisseAlgebraicFiber_ofModel l Y y Q E F)
            (eqToHom (lisseAlgebraicFiberFunctor_obj l Y y Q
              (lisseAlgebraicOfModel l Y Q E F))
                (τA.hom.app _ (η (TensorProduct.tmul _ a z)))) =
            TensorProduct.tmul _ a
              (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F)
                ((r E).τR.hom.app F z))
/-- Pass the normalized rational correspondences to the algebraic coefficient colimit.
Source: Weil II (1.1.1) d), (1.1.6); Stanford L19, Proposition 1.1.9, first bullet.
(blueprint: new-e7-algebraic-galois-construction).

Use the existing integral, rational and algebraic fibre-path families on the actual
fibres. Their laws already provide naturality and coefficient coherence. Evaluating
the algebraic family at c.γ gives an action on the actual algebraic fibre, natural in
the sheaf, hence a representation functor with the identity underlying comparison.

Compare the supplied integral stage with the canonical integral path action through
its τI: both actions agree after every finite projection by their evaluation formulas,
so joint injectivity of those projections identifies them. The supplied rational
pure-tensor normalization then identifies the rational actions. The existing algebraic
path evaluation formula identifies the action on each displayed model with scalar
extension of that rational action. Conjugate by τR on the tensor factor and by the
fixed algebraic fibre object identifications to obtain the required equivariant model
comparison and its exact pure-tensor formula. Every algebraic sheaf is a recorded
finite coefficient model, so this comparison and rational continuity give its IsLAdic
witness. Equivalently, the coherently compared rational representation functors descend
through the defining coefficient-pair localization.

Every algebraic representation has a continuous finite coefficient model by IsLAdic;
rational essential surjectivity and the preceding comparison supply its sheaf model.
For maps put both objects over a common finite field. Finitely many entries of a
Q-linear matrix lie in one finite extension. All equivariance equations already hold
over that field because its inclusion in Q is injective, even for an infinite group.
Rational full faithfulness supplies the sheaf morphism at that stage. The localization
map gives the algebraic sheaf morphism; the equality relation in the coefficient-model
localization, and injectivity after field extension, prove uniqueness. Thus the actual
fibre representation functor is fully faithful and essentially surjective. Turn it
into eA, retaining the identity underlying comparison τA and the already normalized
model comparison as colimit. -/
theorem algebraic_galois_construction_from_rational
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (i : ∀ E : Padic.FiniteCoefficientFields l Q,
      IntegralGaloisConstruction y G c P δ l E.val)
    (r : ∀ E : Padic.FiniteCoefficientFields l Q,
      RationalGaloisConstruction y G c P δ l E.val (i E)) :
    Nonempty (AlgebraicGaloisConstruction y G c P δ l Q i r) := by
  sorry

end AlgebraicGeometry.Scheme
