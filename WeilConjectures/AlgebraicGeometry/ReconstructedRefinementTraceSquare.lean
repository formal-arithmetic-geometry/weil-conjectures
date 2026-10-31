/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Native supplied-pair counit square

The categorical calculation applies directly to the native condensed categories
`Dctf(X, Λ)` and `Dctf(Y, Λ)`. Take `Fc` and `Fd` to be their compactification
compact-support functors and `q` to be the canonical comparison supplied by
`lem-route-reconstructed-refinement-common`. No coefficient-system realization
or comparison with a completed category is used.

Source: current blueprint sk-thm-purity-transport Step 3 and
sk-prop-sp-unique-adjoint, Transposes, Naturality and Inverse.
(blueprint: lem-route-reconstructed-refinement-trace-square).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂ u

open CategoryTheory

namespace WeilConjectures.ReconstructedPairRefinement

/-- The native refinement comparison has an invertible right-adjoint transpose,
and compatible supplied representing pairs have the same transported counit.
We state the calculation for arbitrary categories, so it applies to every
admissible condensed coefficient ring and its native `Dctf` categories.

Proof: the mate of `q.hom` is invertible, since the inverse is the mate of
`q.inv`. Its counit equation identifies its component with the prescribed
`Fc`-adjoint transpose by injectivity of the Hom equivalence. Apply `Fc` to
the supplied compatibility square, use this counit equation, and then use
naturality of `q` at `theta₂`. The two traces are exactly the inverse Hom
images of `theta₁` and `theta₂`, respectively.
(blueprint: lem-route-reconstructed-refinement-trace-square). -/
private theorem suppliedPairCounitSquare
    {CX : Type u₁} {CY : Type u₂} [Category.{v₁} CX] [Category.{v₂} CY]
    {Fc Fd : CX ⥤ CY} {Gc Gd : CY ⥤ CX}
    (adjc : Fc ⊣ Gc) (adjd : Fd ⊣ Gd) (q : Fc ≅ Fd) (L : CY) :
    let rho := adjc.homEquiv (Gd.obj L) L (q.hom.app (Gd.obj L) ≫ adjd.counit.app L)
    IsIso rho ∧
      ∀ (M₁ M₂ : CX) (theta₁ : M₁ ≅ Gc.obj L) (theta₂ : M₂ ≅ Gd.obj L)
        (s : M₂ ≅ M₁),
        s.hom ≫ theta₁.hom = theta₂.hom ≫ rho →
        Fc.map s.hom ≫ (Fc.map theta₁.hom ≫ adjc.counit.app L) =
          q.hom.app M₂ ≫ (Fd.map theta₂.hom ≫ adjd.counit.app L) := by
  have hr : adjc.homEquiv (Gd.obj L) L
      (q.hom.app (Gd.obj L) ≫ adjd.counit.app L) =
      (conjugateEquiv adjd adjc q.hom).app L := by
    apply (adjc.homEquiv (Gd.obj L) L).symm.injective
    simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] using
      (conjugateEquiv_counit adjd adjc q.hom L).symm
  dsimp only
  rw [hr]
  constructor
  · infer_instance
  · intro M₁ M₂ theta₁ theta₂ s hs
    rw [← Fc.map_comp_assoc, hs, Fc.map_comp]
    simp only [Category.assoc]
    rw [conjugateEquiv_counit adjd adjc q.hom L, ← q.hom.naturality_assoc]

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open CategoryTheory.Limits

/-- Native condensed compactification counit compatibility. The two preservation
hypotheses merely allow restricting the actual compactification composites to
`Dctf`; the native compact-support comparison supplies `q`. The assertion is
valid for any such comparison, in particular the canonical one of
`lem-route-reconstructed-refinement-common`.

The right-adjoint map is the transpose specified by the node, rather than
chosen comparison data. Its invertibility and the supplied-pair trace equation
follow from `suppliedPairCounitSquare`, applied within the actual native full
subcategories. Source: current purity-transport Step 3 and unique-right-adjoint
Transposes, Inverse and Naturality.
(blueprint: lem-route-reconstructed-refinement-trace-square). -/
theorem reconstructedRefinementTraceSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c d : Compactification f)
    (hc : ∀ A : ConstantModelConstructibleFiniteTor Λ X,
      (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _)
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj A.obj))
    (hd : ∀ A : ConstantModelConstructibleFiniteTor Λ X,
      (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _)
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).obj A.obj)) :
    let Fc : ConstantModelConstructibleFiniteTor Λ X ⥤
        ConstantModelConstructibleFiniteTor Λ Y :=
      (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _).lift
        ((constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification Λ c) hc
    let Fd : ConstantModelConstructibleFiniteTor Λ X ⥤
        ConstantModelConstructibleFiniteTor Λ Y :=
      (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _).lift
        ((constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification Λ d) hd
    ∀ (Gc Gd : ConstantModelConstructibleFiniteTor Λ Y ⥤
        ConstantModelConstructibleFiniteTor Λ X)
      (adjc : Fc ⊣ Gc) (adjd : Fd ⊣ Gd) (q : Fc ≅ Fd)
      (L : ConstantModelConstructibleFiniteTor Λ Y),
      let rho := adjc.homEquiv (Gd.obj L) L
        (q.hom.app (Gd.obj L) ≫ adjd.counit.app L)
      IsIso rho ∧
        ∀ (M₁ M₂ : ConstantModelConstructibleFiniteTor Λ X)
          (theta₁ : M₁ ≅ Gc.obj L) (theta₂ : M₂ ≅ Gd.obj L) (s : M₂ ≅ M₁),
          s.hom ≫ theta₁.hom = theta₂.hom ≫ rho →
          Fc.map s.hom ≫ (Fc.map theta₁.hom ≫ adjc.counit.app L) =
            q.hom.app M₂ ≫ (Fd.map theta₂.hom ≫ adjd.counit.app L) := by
  intro Fc Fd Gc Gd adjc adjd q L
  exact suppliedPairCounitSquare adjc adjd q L

end WeilConjectures.ReconstructedPairRefinement
