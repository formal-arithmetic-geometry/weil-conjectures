/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer

/-! # Finite coefficient cup products

Source: Milne, Lectures on Étale Cohomology, §22 (cup products) and §14
(blueprint: def-wf-finite-etale-cup).

## Main definitions

- `finiteEtaleUnitMap`: the sheafified constant-section comparison.
- `IsFiniteEtaleCup`: the Yoneda description of the coefficient-action cup product.

The constant module, exact forgetful functor, integral generator and cohomology comparison
are the existing `Etale.ordinaryFiniteConstant`, `Etale.RawModuleScalarComparison.forget`,
`Etale.ordinaryFiniteIntegralGenerator` and `Etale.ordinaryFiniteClass`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Canonical constant-section comparison, obtained by sheafifying the unit on the
constant presheaf. Source: Milne §22 (blueprint: def-wf-finite-etale-cup). -/
noncomputable def finiteEtaleUnitMap (X : Scheme.{u}) (N : ℕ) :
    X.constantZMod N ⟶
      (Etale.RawModuleScalarComparison.forget (ULift.{u + 1} (ZMod N)) X).obj
      (Etale.ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) X) :=
  ⟨sheafifyLift X.smallEtaleTopology
    (whiskerRight (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N)))))
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) AddCommGrpCat.{u + 1}))
    ((Etale.RawModuleScalarComparison.forget (ULift.{u + 1} (ZMod N)) X).obj
      (Etale.ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) X)).property⟩

/-- The action cup product, specified on all module-extension representatives.
The module action on an N-torsion abelian sheaf is unique. The comparison
`Etale.ordinaryFiniteClass` is the canonical ordinary-cohomology comparison. Yoneda composition
is tensoring the two derived global-section classes followed by coefficient evaluation:
the first coefficient is the free rank-one Z/N-module, so evaluation is its unit action.
This characterization includes all degrees and uses the order x then y (no sign swap).
Source: Milne §22 and §14 (blueprint: def-wf-finite-etale-cup). -/
def IsFiniteEtaleCup (X : Scheme.{u}) (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (cup : ∀ i j : ℕ, Sheaf.H (X.constantZMod N) i → Sheaf.H F j →
      Sheaf.H F (i + j)) : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))))
    (e : (Etale.RawModuleScalarComparison.forget (ULift.{u + 1} (ZMod N)) X).obj M ≅ F) (i j : ℕ)
    (x₀ : Sheaf.H (X.constantZMod N) i)
    (x : Ext (Etale.ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) X)
      (Etale.ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) X) i)
    (y : Ext (Etale.ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) X) M j),
    Sheaf.H.map (finiteEtaleUnitMap X N) i x₀ =
      Etale.ordinaryFiniteClass (ULift.{u + 1} (ZMod N)) X _ i x.hom →
    cup i j x₀
      (Sheaf.H.map e.hom j
        (Etale.ordinaryFiniteClass (ULift.{u + 1} (ZMod N)) X M j y.hom)) =
    Sheaf.H.map e.hom (i + j)
      (Etale.ordinaryFiniteClass (ULift.{u + 1} (ZMod N)) X M (i + j)
        (x.comp y rfl).hom)

end AlgebraicGeometry
end
