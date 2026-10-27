/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.StandingExceptionalComposition
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.StandingExceptionalBaseChangeCompared
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.Paper.ConstructibleTensorComposition
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange

/-! # Exceptional dualizing base-change pasting

Source: current blueprint, sk-prop-cohsm, lem-pur-co-smooth-composition.proof.md,
final base-change sentence; Stacks Project, Tag 0F7L, lemma-base-change-shriek,
compatibility with Tag 0F7J (blueprint: lem-pur-exceptional-base-change-pasting).

The equality is written in the canonical etale-origin coordinates already used by
`finiteComparedBaseChangeClause` and `standingExceptionalBaseChangeCompared`.
Comparison inverse image places both sides in the actual small pro-etale derived
category. The compositor is the published counit-preserving adjunction conjugate,
not a choice of an isomorphism between its endpoints. The original compactifications
are arbitrary; each primed compactification is their specified base change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The displayed beta-pasting equation in the dependency's canonical comparison
coordinates. `sqf.paste_vert sqg` is the outer cartesian square. All local instances
only install the retained compactifications, their actual base changes, and the
quasi-compactness inherited by base change. The four right-hand factors are
Ls*(c), b_f at omega_g, G_f'(beta_g), and c' inverse, in that order.
The beta maps include the canonical pullback-unit identification by their definition.
Source: sk-prop-cohsm, final base-change sentence and Stacks Tag 0F7L
(blueprint: lem-pur-exceptional-base-change-pasting). -/
def exceptionalDualizingBaseChangePastingEquation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {s : X' ⟶ X} {h : Y' ⟶ Y} {t : Z' ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (sqf : IsPullback s f' f h) (sqg : IsPullback h g' g t)
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) : Prop :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  letI := (cf.ofIsPullback sqf).hasCompactification
  letI := (cg.ofIsPullback sqg).hasCompactification
  letI := (cfg.ofIsPullback (sqf.paste_vert sqg)).hasCompactification
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sqf inferInstance
  letI : QuasiCompact g' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sqg inferInstance
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      (Etale.dualizingComplexBaseChangeMap P.Coefficient (sqf.paste_vert sqg)) =
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) s).leftDerivedFunctor.map
          ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
            P.Coefficient f g).hom.app (𝟙_ _))) ≫
      standingExceptionalBaseChangeCompared P sqf cf (cf.ofIsPullback sqf)
        (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) g) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f').map
          (Etale.dualizingComplexBaseChangeMap P.Coefficient sqg)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
        ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
          P.Coefficient f' g').inv.app (𝟙_ _))

/-- The actual dualizing base-change mate of a composite equals the specified pasted
mates, with coefficient-unit identifications and the normalized compositors inserted.
There is no absolute separatedness, smoothness, or invertibility hypothesis on beta.
Source: current blueprint, sk-prop-cohsm, final base-change sentence; Stacks Tag 0F7L
(blueprint: lem-pur-exceptional-base-change-pasting).

Proof:
1. Exceptional preservation and constructible origin put all objects in the
bounded-below etale-origin Hom domains. The dimension bounds exist for finite-type
schemes. Use specifiedExceptionalHomEquiv, not an ambient pro-etale adjunction.
2. Choose a compatible compactification tower and its pullback. Evaluate the constant
strict-tower compositionPastingCoherence. NormalizedProperOpenCalculus and the
constant-tower evaluation comparisons identify its compositors and exchanges with
those of originComposition and finite-level compact-support base change. Refinement
coherence moves the equation to cf, cg, cfg and their specified base changes.
3. Invert only the compact-support exchanges and cancel the compositors. This gives
the inverse-exchange square; no exceptional base-change map has been inverted.
4. Transpose twice. Mate pasting and conjugation identify its two sides with c' b_gf
and G_f'(b_g) b_f Ls*(c). Naturality and injectivity of the restricted Hom bijections
suffice. The compositor finiteExceptionalComposition is this normalized conjugate
in etale-origin coordinates, as in standingExceptionalComposition.
5. Evaluate at the coefficient unit. Postcompose by G_f'G_g' of the pullback-unit
map, use naturality of c', and cancel c'. By dualizingComplexBaseChangeMap these
unit-specialized mates are precisely beta_g and beta_gf. Comparison inverse image
then gives the displayed pro-etale equality, including the same counit normalization. -/
theorem exceptionalDualizingBaseChangePasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))] [Z'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z' ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (s : X' ⟶ X) (h : Y' ⟶ Y) (t : Z' ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [f'.IsOver (Spec (.of P.field.k))] [g'.IsOver (Spec (.of P.field.k))]
    [s.IsOver (Spec (.of P.field.k))] [h.IsOver (Spec (.of P.field.k))]
    [t.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (sqf : IsPullback s f' f h) (sqg : IsPullback h g' g t)
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    exceptionalDualizingBaseChangePastingEquation P sqf sqg cf cg cfg := by
  sorry

end AlgebraicGeometry.ProEtale
