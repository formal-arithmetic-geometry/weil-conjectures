/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import Sheaf.Paper.SystemScalarProjectionData

/-! # Restriction of refinement factors

Source: proof of lem-coef-system-scalar-projection-identification, Steps 6--7.
(blueprint: lem-coef-system-scalar-refinement-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftAdjoint
  HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.SemilinearSections WeilConjectures.FiniteFreeSystemRestriction
namespace WeilConjectures.SystemScalarProjection

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L) {K : FiniteFieldDatum.{u}} {d : ℕ}
  {b : Fin d → Padic.coefficientExtensionIntegers l L} {ramification : ℕ}
  (s : Assertions l E L i K d b ramification)

/-- Restriction preserves refinement factors, and lower refinement is natural and coherent.
Source: scalar projection identification, Step 6 and the lower-tower part of Step 7.
(blueprint: lem-coef-system-scalar-refinement-restriction).
Proof: apply the system compactification refinement theorem to the lower DVR tower.
Its calculus agrees with the published section-normalized operations by adjunction
uniqueness; the levelwise bounded constructible input follows from hM. This gives
lower gamma invertibility and lower coherence. Reduced basis coordinates identify
U T M with a finite sum of M; normalization and bounded constructible finite-Tor
levels are preserved by this finite sum. Apply the same lower theorem to U T M.
The restriction compatibility package preserves the gamma word, including the
identity direct-image comparison, and the direct-image compositor. Exact restriction
reflects isomorphisms on cohomology, so upper gamma at T M is invertible even for a
ramified tower. Restriction therefore preserves its inverse and gives the displayed
theta square, which involves no scalar comparison. Naturality of gamma and its
inverse on their isomorphism domains, and of the compositor, gives the final
naturality square at the scalar unit. Bounds are chosen separately at every level. -/
theorem scalar_refinement_restriction (hl : l ≠ K.p)
    (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left)
    [f.IsOver (Spec (.of K.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : Derived (A l E) (aTransition l E) X.val.left) (hM : domain l E L i s X M) :
    RefinementCoherence (A l E) (aTransition l E) (f := f) M ∧
    ∀ {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂),
      IsIso (refinementGamma (A l E) (aTransition l E) r M) ∧
      IsIso (refinementGamma (B l E L i) (bTransition l E L i) r
        ((T l E L i s X).obj M)) ∧
      ((U l E L i Y.val.left).map
          (theta (B l E L i) (bTransition l E L i) r ((T l E L i s X).obj M)) ≫
        (s.geometry.compactIso l E L i X (ambient Y c₂) Y c₂.i c₂.g).hom.app
          ((T l E L i s X).obj M) =
        (s.geometry.compactIso l E L i X (ambient Y c₁) Y c₁.i c₁.g).hom.app
            ((T l E L i s X).obj M) ≫
          theta (A l E) (aTransition l E) r
            ((U l E L i X.val.left).obj ((T l E L i s X).obj M))) ∧
      ((compact (A l E) (aTransition l E) c₁.i c₁.g).map
          ((s.scalars X).scalar.adjunction.unit.app M) ≫
        theta (A l E) (aTransition l E) r
          ((U l E L i X.val.left).obj ((T l E L i s X).obj M)) =
        theta (A l E) (aTransition l E) r M ≫
          (compact (A l E) (aTransition l E) c₂.i c₂.g).map
            ((s.scalars X).scalar.adjunction.unit.app M)) := by sorry

end WeilConjectures.SystemScalarProjection
