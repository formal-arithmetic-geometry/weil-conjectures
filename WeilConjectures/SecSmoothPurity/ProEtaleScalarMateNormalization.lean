/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalScalarMateProjection

/-!
# Native condensed scalar mate restricts to the projection map

Source: blueprint `sec-smooth-purity/sk-lem-sp-tower/`
`lem-fix-compact-support-coefficient-change.proof.md`,
first proof paragraph (blueprint: lem-fix-proetale-scalar-mate-normalization).

The normalized extension/restriction comparison is the counit transpose of the
normalized scalar/pullback comparison.  The first conjunct below is the
native projection identity; `tX.derived` and `tY.derived` are the normalized
scalar/tensor maps `e_X` and `e_Y`, `restrictPush` is `d`, and
`scalarProjection` is the module-object projection followed by the canonical
coefficient identification `c_u`.  The second conjunct is the same identity
under the fixed section equivalences.  The third is the defining counit
identity of the mate, and the final conjunct records naturality.  All
categories are the ordinary unbounded derived categories; no boundedness,
constructibility, finite-Tor, or flatness assumption is made.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
    (ModuleRingedComparison.modules Λ T)]

/-- Native scalar-mate normalization and its projection, section, counit, and
naturality clauses.

Source: blueprint `sec-smooth-purity/sk-lem-sp-tower/`
`lem-fix-compact-support-coefficient-change.proof.md`,
first proof paragraph (blueprint: lem-fix-proetale-scalar-mate-normalization).

Proof: specialize internal_scalar_mate_projection to the given normalized data.
Its restricted mate equation is the first clause, since restrictPush is the
canonical adjunction-compatible restriction comparison. Transport the native
projection through the fixed section, tensor, and geometric comparisons.
These comparisons preserve the canonical tensor-pullback comparison and counit;
therefore its transpose is scalarSectionProjection, giving the second clause.
The counit equation is mateEquiv_counit for the two geometric adjunctions and
lam.hom. Finally the naturality square is the naturality of the natural
transformation rho. These arguments apply in the unbounded derived categories
and require no flatness of the coefficient morphism.
-/
theorem proEtaleScalarMateNormalization
    (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (u : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' u ≅ L Λ u ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a u lam) :
    (∀ M : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a u lam).app M) ≫
          (restrictPush a u lam).hom.app ((D a X).obj M) ≫
          (F Λ u).map (tX.derived.hom.app M) =
        tY.derived.hom.app ((F Λ u).obj M) ≫ scalarProjection a u M) ∧
    (∀ M : DerivedCategory (Modules Λ X),
      (ModuleRingedComparison.derivedEquivalence Λ Y).functor.map (scalarProjection a u M) ≫
          (scalarSectionPushComparison Λ u).hom.app
            (((CondensedRing.derivedTensor Λ X).obj M).obj (B a X)) ≫
          (ModuleRingedComparison.derivedPushforward Λ u).map
            (scalarSectionTensor X M (B a X)).hom =
        (scalarSectionTensor Y ((F Λ u).obj M) (B a Y)).hom ≫
          (ModuleRingedComparison.tensor Λ Y).map
            (Prod.mkHom ((scalarSectionPushComparison Λ u).hom.app M) (𝟙 _)) ≫
          scalarSectionProjection a u M) ∧
    (∀ M : DerivedCategory (Modules Λ X),
      (L Λ' u).map ((rho a u lam).app M) ≫
          (adj Λ' u).counit.app ((D a X).obj M) =
        lam.hom.app ((F Λ u).obj M) ≫
          (D a X).map ((adj Λ u).counit.app M)) ∧
    (∀ (M N : DerivedCategory (Modules Λ X)) (q : M ⟶ N),
      (D a Y).map ((F Λ u).map q) ≫ (rho a u lam).app N =
        (rho a u lam).app M ≫ (F Λ' u).map ((D a X).map q)) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientChange
