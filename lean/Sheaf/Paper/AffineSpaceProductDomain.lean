/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.AffineSpaceProductConstructions
import Sheaf.Paper.RelativeKunneth
import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.SfProEtaleProjectionFormula

/-! # Finite-Tor domains for repeated relative compact-support products

Source: blueprint prop-pur-affine-space-composition-law, product-domain induction,
and the relative Kunneth construction (blueprint: lem-pur-affine-space-product-domain).
Index j denotes j+1 factors; all constructions are owned by the definition prerequisite.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures.AffineSpaceProduct

/-- Finite-Tor admissibility and the canonical comparisons for every positive power.
Source: blueprint prop-pur-affine-space-composition-law, Steps 3--4 as expanded in
its product-domain induction (blueprint: lem-pur-affine-space-product-domain).

Proof:
1. For one factor use the given u. The coefficient unit has Tor interval [0,0].
2. Apply lem-pur-relative-external-power-regrouping to m+1 copies. Its canonical rho
identifies the tensor of the two pullbacks with external at the next stage, and
its geometric and finite-Tor conclusions give all source and projection domains.
3. By lem-pur-relative-product-geometric-factors the composition and exchange factors
are invertible on their etale-origin classes. For the first projection transformation
its base coefficient is M; for the second it is V_m. The latter has Tor interval [0,0]
by induction and is bounded constructible by thm-sf-ctf-stability(iv).
thm-sf-pf-proetale makes both concrete projection transformations invertible. Compose
their inverses with composition, exchange and tensor symmetries in the order of
thm-sf-kunneth-relative. This is step; no six-functor datum is assumed.
4. Tensor the inductive unit identification with u and use the unit constraints.
The tensor interval is [0+0,0+0]=[0,0], invariant under isomorphism.
5. The recursion defining comparison starts with the identity and tensors each preceding
comparison with the identity. Functoriality proves that it, and then unitPower composed
with it, are isomorphisms. The earlier domain induction applies at every stage. -/
theorem affine_space_product_domain (P : PurityFiniteSetting.{u})
    (B X : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : D P X)
    (_hM : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) X M)
    (c : ∀ j, Compactification (space f j).hom)
    (u : image P f M c 0 ≅ 𝟙_ (D P B)) :
    ∃ d : ∀ j, StageDomain P f M c j, ∀ j : ℕ,
      ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} P.Coefficient) (space f j).left (external P f M j) ∧
      Nonempty (image P f M c j ≅ 𝟙_ (D P B)) ∧
      ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} P.Coefficient) B 0 0 (image P f M c j) ∧
      IsIso (step P f M c j (d j)) ∧
      IsIso (comparison P f M c d j) ∧
      IsIso (comparison P f M c d j ≫ unitPower P B u j) := by
  sorry

end WeilConjectures.AffineSpaceProduct
