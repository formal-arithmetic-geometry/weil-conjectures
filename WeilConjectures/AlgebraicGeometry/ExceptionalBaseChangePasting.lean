/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandingExceptionalBaseChangeCompared
public import WeilConjectures.AlgebraicGeometry.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.ConstructibleTensorComposition
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.AlgebraicGeometry.CompactifiableCompatibleTower
import WeilConjectures.AlgebraicGeometry.StrictTowerCompositionPasting
import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.CanonicalFiniteLevelCompactSupportBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Dualizing base change under composition

Source: current blueprint, lem-pur-co-smooth-composition.proof.md, final base-change
sentence; Stacks, Tag 0F7L, lemma-base-change-shriek, compatibility with Tag 0F7J
(blueprint: lem-pur-exceptional-base-change-pasting).

The equality is in the small pro-etale derived category, in the exact comparison
coordinates used by def-pur-co-smoothness and pur9-cs-def-bc. The functor applied to
both sides is the specified comparison inverse image. Canonical pullback-comparison
isomorphisms identify its source with Ls* omega_(gf). The right adjoints occurring
inside these coordinates are ordinary etale adjoints; no ambient pro-etale exceptional
adjunction is assumed. All three primed compactifications are actual base changes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- The displayed equality beta_(gf) = Ls*(c) ; b_f ; G_f'(beta_g) ; c' inverse,
with the canonical unit pullback identifications already in dualizingComplexBaseChangeMap.
This proposition only expands that equality using the existing maps: its let-instances
retain the chosen compactifications and their literal base changes. In particular it
neither chooses a comparison map nor assumes the desired pasting equation.
Source: current blueprint, lem-pur-co-smooth-composition.proof.md, final sentence;
Stacks Tag 0F7L, lemma-base-change-shriek, vertical stacking paragraph
(blueprint: lem-pur-exceptional-base-change-pasting). -/
def exceptionalBaseChangePastingEquation (P : PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (s : X' ⟶ X) (h : Y' ⟶ Y) (t : Z' ⟶ Z)
    (sqf : IsPullback s f' f h) (sqg : IsPullback h g' g t)
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) [QuasiCompact f] [QuasiCompact g] : Prop :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  letI := (cf.ofIsPullback sqf).hasCompactification
  letI := (cg.ofIsPullback sqg).hasCompactification
  letI := (cfg.ofIsPullback (sqf.paste_vert sqg)).hasCompactification
  letI : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sqf
    inferInstance
  letI : QuasiCompact g' := MorphismProperty.of_isPullback (P := @QuasiCompact) sqg
    inferInstance
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      (Etale.dualizingComplexBaseChangeMap P.Coefficient (sqf.paste_vert sqg)) =
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) s).leftDerivedFunctor.map
          ((PurityFiniteSetting.finiteExceptionalComposition P.Coefficient f g).hom.app
            (𝟙_ _)) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sqf).app
          (Etale.dualizingComplex P.Coefficient g) ≫
        (Etale.rightDerivedUpperShriek P.Coefficient f').map
          (Etale.dualizingComplexBaseChangeMap P.Coefficient sqg) ≫
        (PurityFiniteSetting.finiteExceptionalComposition P.Coefficient f' g').inv.app
          (𝟙_ _))

/-- The actual dualizing base-change mate pastes with the counit-preserving exceptional
compositors, without a cohomological-smoothness or beta-invertibility assumption.
The six objects are arbitrary finite-type schemes over the fixed algebraic closure;
their over-category arrows are precisely k-morphisms. No absolute separatedness occurs.
The Cartesian witnesses permit any presentation of the two fibre products.

Source: current blueprint, lem-pur-co-smooth-composition.proof.md, final base-change
sentence; Stacks Tags 0F7L (lemma-base-change-shriek) and 0F7J
(blueprint: lem-pur-exceptional-base-change-pasting).

Proof:
1. Constructible exceptional preservation and proEtaleConstructibleOrigin supply
bounded-below etale origins for the unit and all exceptional images. Finite-type
ambient dimension bounds make the specifiedExceptionalHomEquiv transposes available.
2. Choose the compatible compactification tower and its pullback. Apply the strict
constant-tower compositionPastingCoherence at constant finite coefficients, using
normalizedProperOpenCalculus and evaluation comparisons. Finite-level compact-support
base change identifies these exchanges with the prescribed proper/open exchanges.
Refinement coherence moves this equality to cf, cg, cfg and their base changes.
3. Invert only those compact-support exchanges. The resulting inverse-exchange square
is C(alpha) after the two inverse exchanges = the composite inverse exchange after
alpha'. No exceptional base-change map is inverted.
4. Take the two counit mates. mateEquiv_hcomp and conjugateEquiv compatibility give
c' at CK after b_(gf) = G_f'(b_g) after b_f at G_g K after A(c_K). These computations
transport through the class-restricted Hom bijections; their injectivity suffices.
5. Put K = the coefficient unit. Each beta is b at the unit followed by the exceptional
image of the pullback-unit isomorphism. Naturality of c' at that isomorphism and
cancellation of c' give exactly exceptionalBaseChangePastingEquation. Apply the
comparison inverse-image functor, preserving the specified source and target
identifications. This proves equality of the specified maps, not merely invertibility.
-/
theorem exceptional_base_change_pasting (P : PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : SixFunctorSpace P.field}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (s : X' ⟶ X) (h : Y' ⟶ Y) (t : Z' ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (sqf : IsPullback s.hom.left f'.hom.left f.hom.left h.hom.left)
    (sqg : IsPullback h.hom.left g'.hom.left g.hom.left t.hom.left)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f.hom.left ≫ g.hom.left)) :
    exceptionalBaseChangePastingEquation P f.hom.left g.hom.left f'.hom.left g'.hom.left
      s.hom.left h.hom.left t.hom.left sqf sqg cf cg cfg := by
  sorry

end AlgebraicGeometry.ProEtale
