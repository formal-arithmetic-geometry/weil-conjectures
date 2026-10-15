/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-!
# Coherence of the composition law and the projection formula

Three coherence properties of the compactly supported direct image `Rf_!` on the unbounded
derived categories of the small étale sites, with finite coefficients, recorded here without
proof as the corresponding blueprint nodes of the six-functor chapters:

* the projection map `PF : Rf_!M ⊗ᴸ N ⟶ Rf_!(M ⊗ᴸ Lf^*N)` is compatible with the associativity
  of the derived tensor product
  (`AlgebraicGeometry.Etale.projectionMapAssociativity`, `sk-prop-sf-pf-coherence`);
* there is a composition law `Rh_! ≅ Rf_! ⋙ Rg_!` for `h = f ≫ g` (`sk-thm-sf-comp-composition`)
  compatible with the projection maps (`sk-prop-sf-pf-coherence`) and with the compactly
  supported base change maps `Ex_!` of pasted cartesian squares (`sk-thm-sf-package` (2))
  (`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`);
* for an étale `u`, the derived pullback commutes with the derived internal hom
  (`AlgebraicGeometry.Etale.isIso_ihomComparison_leftDerivedUpperStar_of_etale`,
  `def-weil-derived-pullback-tensor-hom`).

They are the inputs of the composition and étale-locality statements for cohomologically smooth
morphisms (`lem-pur-co-smooth-composition`, `lem-pur-co-smooth-etale-locality`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula.

The projection map `PF : Rf_!M ⊗ᴸ N ⟶ Rf_!(M ⊗ᴸ Lf^*N)` is compatible with the associativity of
the derived tensor product: the two maps
`(Rf_!M ⊗ᴸ N) ⊗ᴸ N' ⟶ Rf_!(M ⊗ᴸ (Lf^*N ⊗ᴸ Lf^*N'))`, applying the projection map twice or once
to `N ⊗ᴸ N'` followed by the tensor comparison `Lf^*(N ⊗ᴸ N') ≅ Lf^*N ⊗ᴸ Lf^*N'`, agree. This is
the identification of "the two tensor reassociations" in the blueprint proof of the coherence of
the projection formula. -/
theorem projectionMapAssociativity {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    ProjectionMapAssociativity (ModuleCat.{u + 1} Λ) f :=
  sorry

/-- Blueprints `sk-thm-sf-comp-composition`, `sk-prop-sf-pf-coherence` and `sk-thm-sf-package`
(clause (2)): the composition law for `Rf_!` and its coherence with the projection formula and
with base change.

There is a composition isomorphism `E f g h w : Rh_! ≅ Rf_! ⋙ Rg_!` for all `f`, `g` and
`h = f ≫ g` admitting compactifications (`sk-thm-sf-comp-composition`) such that
1. (`sk-prop-sf-pf-coherence`, the pentagon for composable `f`, `g`, compatible with the
   composition law) the projection maps compose: for `M` on `X` and `N` on `Z`,
   ```
   Rh_!M ⊗ᴸ N ──E ▷ N──▶ Rg_!Rf_!M ⊗ᴸ N ──PF_g──▶ Rg_!(Rf_!M ⊗ᴸ Lg^*N)
          │PF_h                                         │Rg_! PF_f
          ▼                                                    ▼
   Rh_!(M ⊗ᴸ Lh^*N) ──E──▶ Rg_!Rf_!(M ⊗ᴸ Lh^*N) ≅ Rg_!Rf_!(M ⊗ᴸ Lf^*Lg^*N)
   ```
   commutes;
2. (`sk-thm-sf-package` (2), the compact-support base change is compatible with the composition
   law) for cartesian squares `a ≫ f = f' ≫ b` and `b ≫ g = g' ≫ c` with quasi-compact `f'`,
   `g'` and `f' ≫ g'`, the base change map of the pasted square is the pasting of the base
   change maps: `Ex_h ≫ E f' g' = Lc^* (E f g) ≫ Ex_g ≫ Rg'_! Ex_f`. -/
theorem exists_rightDerivedLowerShriekCompIso :
    ∃ E : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z), f ≫ g = h →
        ∀ [HasCompactification f] [HasCompactification g] [HasCompactification h],
        R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
        [HasCompactification f] [HasCompactification g] [HasCompactification h],
        Adjunction.ProjectionCompCompatible
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) h).app M).app N)
          (fun N ↦ (leftDerivedUpperStarComp _ f g h w.symm).hom.app N) (E f g h w)) ∧
      (∀ {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
        {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
        (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
        (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
        [HasCompactification h] [HasCompactification f'] [HasCompactification g']
        [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h'],
        Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
          (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqh)
          (E f g h w) (E f' g' h' w')) :=
  sorry

/-- Blueprint `def-weil-derived-pullback-tensor-hom`: Derived pullback, tensor product, and
internal Hom.

For an étale morphism `u : U ⟶ X`, the derived pullback commutes with the derived internal hom:
the comparison `Lu^* RHom(M, N) ⟶ RHom(Lu^* M, Lu^* N)` of the monoidal functor `Lu^*`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is an isomorphism. The pullback along `u`
is the restriction to the slice site `X_ét/U`, which has an exact left adjoint, so it preserves
K-injective complexes, and the sheaf internal hom commutes with restriction to `U`. -/
theorem isIso_ihomComparison_leftDerivedUpperStar_of_etale {U X : Scheme.{u}} (u : U ⟶ X)
    [Etale u] (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) u
    IsIso (Functor.LaxMonoidal.ihomComparison L((u)^*[ModuleCat.{u + 1} Λ]) M).natTrans :=
  sorry

end Etale

end AlgebraicGeometry
