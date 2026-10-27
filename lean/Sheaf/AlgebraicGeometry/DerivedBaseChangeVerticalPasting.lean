/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint

/-!+# Vertical pasting of derived base-change maps

Source: Stacks Project, cohomology.tex, Tag 0ATL, remark-compose-base-change
(blueprint: lem-sfb-derived-base-change-vertical-pasting).

The fibre products are specified by their universal properties. The composition
comparisons are the fixed right-derived-unit-normalized comparisons, not arbitrary
isomorphisms supplied as additional data.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Canonical derived base-change maps compose for two stacked cartesian squares.
Here `top` specifies `X' = X ×_Y Y'` and `bot` specifies `Y' = Y ×_Z Z'`, with their
given projections. The inverse of `schemeNormalizedDirectImageCompIso` is the
comparison denoted by rho in the node. No base-change morphism is inverted.

Source: Stacks Project, cohomology.tex, Tag 0ATL, remark-compose-base-change
(blueprint: lem-sfb-derived-base-change-vertical-pasting).

Proof:
1. The two fibre-product universal properties show that the outer rectangle is
   cartesian: a compatible pair into X and Z' first lifts uniquely to Y', then X'.
   The qcqs direct-image theorem lem-pc-derived-direct-image-preserves-qcoh puts
   Rf_*E in D_QCoh, so the lower base-change map has the stated domain.
2. Use lem-pc-derived-direct-image-composition and its normalized comparisons to
   identify the direct images of composites. The associativity theorem
   lem-pc-derived-direct-image-composition-associativity identifies the outer
   square comparison with the paste of the two inner square comparisons, after
   the source and target composition isomorphisms. Equality transports are natural.
3. Under the adjunctions of lem-pc-ringed-spaces-derived-adjoint, the defining unit
   formula def-pc-derived-base-change-map says S_l(beta_top) eta_l = S_f(eta_k)
   and S_m(beta_bot) eta_m = S_g(eta_l), with the comparisons of step 2 retained.
4. Transpose the pasted map under Lm^* adjoint to Rm_*. Functoriality and naturality
   turn its transpose into S_g(S_l(beta_top) eta_l) = S_g S_f(eta_k).
   The outer map has the same transpose by step 2. Naturality of eta_m at rho_E
   and of rho at eta_k inserts the displayed source and target comparisons.
   Injectivity of the adjunction Hom bijection gives the equality below.
Only the canonical composition comparisons are inverted; neither flatness nor
Tor independence nor invertibility of a base-change map occurs. -/
theorem schemeDerivedBaseChange_vertical_pasting
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : Z' ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (k : X' ⟶ X) (f' : X' ⟶ Y') (l : Y' ⟶ Y) (g' : Y' ⟶ Z')
    (top : IsPullback k f' f l) (bot : IsPullback l g' g m)
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (hRf : schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E)) :
    IsPullback k (f' ≫ g') (f ≫ g) m ∧
      schemeDerivedBaseChangeMap (f ≫ g) (f' ≫ g') m k (top.paste_vert bot).w E ≫
          (schemeNormalizedDirectImageCompIso f' g').inv.app ((derivedPullback k).obj E) =
        (derivedPullback m).map ((schemeNormalizedDirectImageCompIso f g).inv.app E) ≫
          schemeDerivedBaseChangeMap g g' m l bot.w ((schemeDerivedDirectImage f).obj E) ≫
          (schemeDerivedDirectImage g').map (schemeDerivedBaseChangeMap f f' l k top.w E) := by
  sorry

end AlgebraicGeometry
