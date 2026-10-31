/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FibreFunctorBasepointTransportData
import WeilConjectures.AlgebraicGeometry.IntegralGaloisReconstructionEquivalence

/-! # Integral reconstruction from finite Galois modules

Source: Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-e7-integral-galois-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The integral stage alone: a normalized equivalence and its finite stalk evaluation.
Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9, third bullet.
(blueprint: new-e7-integral-galois-construction). -/
structure IntegralGaloisConstruction
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] where
  eI : LisseIntegralSheaf l E Y ≌ galoisIntegralRepresentations l E P δ
  τI : eI.functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
    lisseIntegralFiberFunctor l E Y y
  /-- The limit action is the supplied finite evaluation action on every stalk projection. -/
  evaluation :
    ∀ (F : LisseIntegralSheaf l E Y) (n : ℕ),
      ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
        (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))),
      ∀ (g : G) (z : (eI.functor.obj F).obj.V),
        pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
            ((τI.hom.app F ≫
              limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n))
                ((eI.functor.obj F).obj.ρ g z)) =
          (c.γ g).hom.app (galoisUnderlyingFLC
            (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n)) h)
            (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
              ((τI.hom.app F ≫
                limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)) z))

/-- Construct the integral correspondence by inverse limits of the supplied finite one.
Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9, third bullet.
(blueprint: new-e7-integral-galois-construction).

The canonical continuous integral fibre functor is constructed on the actual module
fibres by applying the inverse-limit functor to the linear path family. Its finite
generation, joint continuity and finite evaluation formula are proved in
canonical_integral_galois_functor_exists. Apply the reconstruction equivalence theorem
to precisely that forward data. Faithfulness is already part of the forward data.
That theorem proves fullness by lifting compatible equivariant quotient maps through
the given finite correspondence, and
essential surjectivity by reconstructing the finite quotient-sheaf tower of a
continuous integral module. Turn the resulting IsEquivalence instance into an
equivalence. Its forward functor is unchanged, so the constructed fibre comparison
and finite action evaluation are exactly the required τI and evaluation fields. -/
theorem integral_galois_construction_from_finite
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Nonempty (IntegralGaloisConstruction y G c P δ l E) := by
  classical
  obtain ⟨d⟩ := canonical_integral_galois_functor_exists
    (y := y) (G := G) (c := c) (l := l) (E := E) (P := P) (δ := δ)
  let : d.T.IsEquivalence := integral_galois_functor_isEquivalence y G c P δ l E d
  exact ⟨{ eI := d.T.asEquivalence, τI := d.τ, evaluation := d.evaluation }⟩

end AlgebraicGeometry.Scheme
