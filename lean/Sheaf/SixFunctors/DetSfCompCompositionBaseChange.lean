/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.CompactificationCoherenceCocycle
public import Sheaf.Paper.CondensedAmbientExchange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.UnboundedBaseChangeExtension
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Compactification.CommonDenseRefinement
import Sheaf.Compactification.DenseRefinementMorphisms
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.ProEtaleProperOpenInterchange
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Base change for `Rf_!` on the localizing category

Source: the blueprint of the Weil conjectures, chapter `sec-six-functors-basics`, unit
`sk-thm-sf-comp-composition` (blueprint: det-sf-comp-composition-base-change); Stacks Project,
Tag 09AH.

The statement uses the published module-object definitions of derived pullback and derived
lower shriek, the literal compactification base-change construction, and the localizing closure
of bounded constructible finite-Tor objects. The coefficient parameter is a commutative
condensed ring satisfying the published `IsLocalizingAdmissibleCoefficient ℓ Λ` predicate.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

/-- The module-object derived pullback used in the base-change statement.
Source: the module-object six-functor definitions
(blueprint: det-sf-comp-composition-base-change). -/
noncomputable abbrev detSfDerivedPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} (h : A ⟶ B) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)) :=
  L((h)^*⟦Λ⟧)

/-- The derived lower-shriek functor attached to a compactification.
Source: the module-object six-functor definitions
(blueprint: det-sf-comp-composition-base-change). -/
noncomputable abbrev detSfCompactSupport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} {h : A ⟶ B}
    (d : Compactification h) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)) :=
  rightDerivedLowerShriekOfCompactification Λ d

/-- The published ambient base-change mate for the literal proper pullback square.
This abbreviation only supplies the identity identification with the chosen fibre product;
it makes no new choice of exchange map. Source: blueprint
 det-sf-comp-composition-base-change, proof step 4
(blueprint: det-sf-comp-composition-base-change). -/
noncomputable abbrev detSfProperBaseChangeMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z Y Y' : Scheme.{u}} (p : Z ⟶ Y) (v : Y' ⟶ Y) :
    (R((p)_*⟦Λ⟧) ⋙ detSfDerivedPullback Λ v) ⟶
      (detSfDerivedPullback Λ (pullback.fst p v) ⋙ R((pullback.snd p v)_*⟦Λ⟧)) :=
  condensedAmbientExchange Λ
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }

/-- The canonical open exchange arrow, in the inverse direction to clause (1).
Source: blueprint det-sf-comp-composition-base-change, proof steps 1--2. Insert the open
unit, transport the pullback square, and contract the base-changed open counit. Thus an
isomorphism whose inverse equals this arrow has a specified normalization
(blueprint: det-sf-comp-composition-base-change). -/
def detSfOpenBaseChangeMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    (detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧)) ⟶
      (D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v)) :=
  let sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  let θ := condensedAmbientPullbackComparison Λ
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).unit
      (detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧)) ≫
    (Functor.squareTransport D((c.i)_!open⟦Λ⟧) D(((c.baseChange v).i)_!open⟦Λ⟧)
      (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ c.i).symm
          (detSfDerivedPullback Λ (pullback.fst f v)) ≪≫
        θ.symm ≪≫
        Functor.isoWhiskerLeft (detSfDerivedPullback Λ (pullback.fst c.g v))
          (leftDerivedUpperStarIsoMapDerivedCategory Λ (c.baseChange v).i))).hom ≫
    Functor.whiskerLeft (D((c.i)_!open⟦Λ⟧) ⋙
        detSfDerivedPullback Λ (pullback.fst c.g v))
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (c.baseChange v).i).counit ≫
    (Functor.rightUnitor _).hom

/-- Regard a compactification of a quasi-compact morphism as an object of the published
boundary-refinement category. Its open is quasi-compact by the existing factorization lemma.
Source: blueprint det-sf-comp-composition-base-change, proof step 5
(blueprint: det-sf-comp-composition-base-change). -/
def detSfBoundaryCompactification
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    Compactification.BoundaryCompactification f :=
  ⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩

/-- The canonical, common-dense-refinement-normalized comparison family of the recorded
coherence theorem, evaluated on the existing compactification objects. The theorem determines
this family uniquely by its equation against every common dense refinement; identity and
cocycle laws alone would not determine it. No comparison on the whole unbounded category is
chosen. Source: blueprint det-sf-comp-coherence-cocycle and
 det-sf-comp-composition-base-change, proof steps 5 and 8
(blueprint: det-sf-comp-composition-base-change). -/
noncomputable def detSfCanonicalCompactificationComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) :
    ((localizingClosureProEtale Λ X).ι ⋙ detSfCompactSupport Λ c₁) ≅
      ((localizingClosureProEtale Λ X).ι ⋙ detSfCompactSupport Λ c₂) :=
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  Classical.choose (compactification_coherence_cocycle Λ ℓ hΛ f)
    (detSfBoundaryCompactification c₁) (detSfBoundaryCompactification c₂)

/-- The specified compact-support exchange composite: the published proper-base-change mate
followed by `Rp'_*` applied to the normalized open/base-change comparison.
Source: blueprint det-sf-comp-composition-base-change, clause (2) and proof steps 3--4
(blueprint: det-sf-comp-composition-base-change). -/
noncomputable def detSfCompactSupportBaseChangeComposite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (c : Compactification f) (o :
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙
          D(((c.baseChange v).i)_!open⟦Λ⟧)) :
    (detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ v) ⟶
      (detSfDerivedPullback Λ (pullback.fst f v) ⋙
        detSfCompactSupport Λ (c.baseChange v)) := by
  exact
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft D((c.i)_!open⟦Λ⟧)
        (detSfProperBaseChangeMap Λ c.g v) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight o.hom R(((c.baseChange v).g)_*⟦Λ⟧)

/-- Base change for compactly supported direct image on the localizing category.
Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
node det-sf-comp-composition-base-change, clauses (1)--(3)
(blueprint: det-sf-comp-composition-base-change).

The family o is normalized by the canonical open exchange arrow. For every compactification
and every object of Loc(Dctf), both values of the specified composite belong to Loc(Dctf),
and that component is invertible. These are precisely an isomorphism of the restricted
functors, since both subcategories are full. The last equation uses only the published
refinement-normalized comparisons, evaluated at K and its pullback.

Proof, following the eight DAG steps:
1. In the cartesian open square the right adjoints of v'^* j! and j'! u^* agree on sections:
V ×_X X' = V ×_Z Z', with the same coefficient action. Use open-site localization and the
module pushforward/pullback adjunctions.
2. Conjugate that identification by the open and pullback adjunctions. The resulting
isomorphism is the inverse of detSfOpenBaseChangeMap, and restricts to the identity on X'.
Exactness of pullback and extension by zero descends the construction termwise.
3. Pullback preserves Dctf, sums and its localizing closure. Open extension preserves the
closure, and compactification proper image preserves it on both bases, by
 det-sf-comp-coherence-single. Proper base change on finite, integral and rational
constructible coefficients, followed by det-proper-base-change-unbounded-extension,
makes the mate invertible on j!K. Its composite with Rp'_* of the open comparison is β.
4. Normalize derived composition by the underived compositors on K-injective resolutions.
The derived adjunction normalization and mate-pasting lemmas identify the mate for a
composite with the pasted mates used here.
5. Choose a common dense refinement of two compactifications on Y. After arbitrary base
change choose a further common dense refinement on Y'; density of the first pullback is
not assumed. Uniqueness of refinement morphisms identifies the two paths to each target.
6. The refinement/open maps and the precise base-change mate restrict to the identity on
the distinguished open (lem-sfb-base-change-identity-open-restriction). Uniqueness in
 det-sf-comp-composition-interchange equates the two maps to the further dense refinement.
7. Apply proper pushforward, precompose with the proper mate, and use naturality and
mate-pasting. This gives ρ_kₐ β_cₐ = ρ_k β_d v^*(ρ_hₐ) for each projection.
8. Cancel the invertible refinement maps and use the common-refinement formulas of
 det-sf-comp-coherence-cocycle. The resulting equation is the final displayed equality. -/
theorem det_sf_comp_composition_base_change
    (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] (_hkp : ringChar k = p) [Fact (p ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ o : ∀ c : Compactification f,
        D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
          detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧),
      (∀ c : Compactification f, (o c).inv = detSfOpenBaseChangeMap Λ f v c) ∧
      (∀ (c : Compactification f) (K : (localizingClosureProEtale Λ X).FullSubcategory),
        localizingClosureProEtale Λ Y'
            ((detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ v).obj K.obj) ∧
          localizingClosureProEtale Λ Y'
            ((detSfDerivedPullback Λ (pullback.fst f v) ⋙
              detSfCompactSupport Λ (c.baseChange v)).obj K.obj) ∧
          IsIso ((detSfCompactSupportBaseChangeComposite Λ f v c (o c)).app K.obj)) ∧
      ∃ hU : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          localizingClosureProEtale Λ (pullback f v)
            ((detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj),
        ∀ (c₁ c₂ : Compactification f)
          (K : (localizingClosureProEtale Λ X).FullSubcategory),
          (detSfDerivedPullback Λ v).map
              ((detSfCanonicalCompactificationComparison Λ ℓ hΛ k f c₁ c₂).hom.app K) ≫
                (detSfCompactSupportBaseChangeComposite Λ f v c₂ (o c₂)).app K.obj =
            (detSfCompactSupportBaseChangeComposite Λ f v c₁ (o c₁)).app K.obj ≫
              (detSfCanonicalCompactificationComparison Λ ℓ hΛ k (pullback.snd f v)
                (c₁.baseChange v) (c₂.baseChange v)).hom.app
                  ⟨(detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj, hU K⟩ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
