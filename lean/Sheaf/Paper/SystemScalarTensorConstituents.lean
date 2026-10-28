/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import Sheaf.Paper.SystemScalarProjectionData

/-! # Normalized scalar and tensor constituents

Source: proof of lem-coef-system-scalar-projection-identification, Steps 1--4.
(blueprint: lem-coef-system-scalar-tensor-constituents).
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

/-- Normalized proper and open constituents, and their independently constructed finite words.
Source: scalar projection identification, Steps 1--4.
(blueprint: lem-coef-system-scalar-tensor-constituents).
Proof: reduce the fixed integral basis simultaneously at all quotient levels. Identify
restricted ordinary extension with tensor by the restricted unit on pure sections, and
apply the same degreewise map on total K-flat representatives. The coefficient factor
is finite free, so this gives TensorNormalization. Construct geometric pullback on the
constant coefficient towers by the semilinear section calculus and pin its tensorator
and adjunctions to the published operations. Restriction preserves geometric units and
counits. Consequently the transpose of restricted properScalar is mu followed by
counit tensor coefficientPull. On the open, both balancing maps preserve x tensor b
and vanish on the complement; the open-unit transpose is openTensorInv and is invertible.
Compose these two equations to get the projection equation. Inserting 1 on each
constituent and using counit naturality gives the scalar-adjunction equation. Finally
use the canonical restriction evaluation, pullback evaluation and their adjunction
mates to construct LevelData. Evaluation of a transpose is the finite transpose, so
it gives Equation; the finite tensor word uses the same pure-section normalization.
All identities are established before evaluation, which is never used to detect equality. -/
theorem normalized_scalar_tensor_constituents (hl : l ≠ K.p)
    (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left)
    [f.IsOver (Spec (.of K.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : Derived (A l E) (aTransition l E) X.val.left) (hM : domain l E L i s X M) :
    ∃ (ω : TensorPresentation l E L i s) (g : GeometryFamily l E L i s),
      (∀ c : Compactification f,
        ((U l E L i Y.val.left).map (comparison l E L i s X Y c M) ≫
          (s.geometry.compactIso l E L i X (ambient Y c) Y c.i c.g).hom.app
            ((T l E L i s X).obj M) =
          (ω Y).derived.hom.app ((compact (A l E) (aTransition l E) c.i c.g).obj M) ≫
            projection l E L i s g X Y c M ≫
            (compact (A l E) (aTransition l E) c.i c.g).map ((ω X).derived.inv.app M)) ∧
        (((s.scalars Y).scalar.adjunction.homEquiv _ _)
          (comparison l E L i s X Y c M) =
          (compact (A l E) (aTransition l E) c.i c.g).map
              ((s.scalars X).scalar.adjunction.unit.app M) ≫
            (s.geometry.compactIso l E L i X (ambient Y c) Y c.i c.g).inv.app
              ((T l E L i s X).obj M)) ∧
        IsIso (openTensorInv l E L i s g X (ambient Y c) c.i M)) ∧
      (∀ (c : Compactification f) (n : ℕ),
        ∃ z : LevelData l E L i s X Y c n, z.Equation l E L i s g M) := by sorry

end WeilConjectures.SystemScalarProjection
