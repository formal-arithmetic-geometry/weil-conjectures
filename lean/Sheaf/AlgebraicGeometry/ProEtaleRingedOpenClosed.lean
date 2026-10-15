/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero
import Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation
import Sheaf.RingTheory.WContractibleClosedLocalization
import Sheaf.RingTheory.BoundedWContractibleExtension

/-!
# Ringed pro-etale open-closed localization

Source: Stacks Project, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03DI, 03DJ and 0738
(blueprint: lem-weil-pbc-proetale-ringed-open-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The underlying ring sheaf of arbitrary commutative pro-etale coefficients.
Source: Stacks, Modules on Sites, Tag 03D1
(blueprint: lem-weil-pbc-proetale-ringed-open-closed). -/
noncomputable abbrev proEtaleModuleCoefficients {X : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

/-- Direct image with action through the inverse-image adjunction unit. On sections
it is evaluation on the base change; on morphisms it retains the same linear components.
Source: Stacks, Tags 09A5 and 03D6
(blueprint: lem-weil-pbc-proetale-ringed-open-closed). -/
noncomputable def proEtaleRingedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := proEtaleModuleCoefficients A)
    (R := proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A))
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Extension by zero in the localized presentation of the open site's ringed topos.
The presheaf is the sum over factorizations through `U`, with its actual module action;
sheafification is the existing module sheafification. For a monic open immersion the
index set is empty or a singleton. No finiteness restriction is placed on coefficients.
Source: Stacks, Tags 03DI and 03DJ
(blueprint: lem-weil-pbc-proetale-ringed-open-closed). -/
noncomputable def proEtaleRingedExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.extensionByZeroPresheaf.{u + 1} (proEtaleModuleCoefficients A) U ⋙
    PresheafOfModules.sheafification (𝟙 (proEtaleModuleCoefficients A).obj)

/-- Open-closed localization with arbitrary ring-sheaf coefficients. The open part
is presented on the slice `X.ProEt / U`, as in the weakly-etale localization theorem:
its ring is `A.over U`, and inverse image is `overFunctor`. The closed part uses the
actual inverse-image ring and the base-change direct image.

Source: Stacks, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03DI, 03DJ and 0738
(blueprint: lem-weil-pbc-proetale-ringed-open-closed).

Proof:
1. Identify the open site with the slice using
   lem-weil-proetale-weakly-etale-localization. The module extension presheaf has a
   unique summand over an object mapping to U and no summands otherwise. Its
   sheafification is left adjoint to restriction and exact by Tags 03DI and 03DJ.
   The unit is invertible after restriction. Base change of an object over U to Z
   is empty, giving the first zero composite.
2. On affine ind-etale bases use the closed-site lift and its adjunction
   (lem-weil-pbc-ind-etale-basis, lem-exc-closed-site-adjunction,
   def-exc-closed-site-lift). The inverse-image colimit has the terminal evaluation
   object given by the lift. The closed counit is therefore the identity on the basis
   and globally invertible. Naturality with multiplication makes the maps linear.
3. Refine to the bounded w-contractible affine covering family. Quasi-compactness
   of the open complement selects finitely many basic opens. The closed-localization
   covering consists of these opens and the specialization neighbourhood of the
   closed fibre. On the opens the counit is the identity and the closed term is zero.
   On the neighbourhood the shriek term is zero by Tag 09AG and the closed unit is
   the identity by specialization restriction. Thus the actual unit/counit sequence
   is locally short exact, hence short exact as module sheaves (Tag 09AH).
4. Apply that sequence to an extended module and the open triangle identity to obtain
   the other zero composite. For an epimorphism on Z, its direct-image cokernel has
   zero restrictions on both parts, hence vanishes by the sequence. Direct image is
   already left exact as a right adjoint, so it is exact (Tag 09BM).
5. If X is qcqs, test filtered colimits on affine objects V. Both V and V times_X Z
   are qcqs. Tag 0738 identifies their sections of filtered colimits with the colimits
   of sections. Underlying abelian filtered colimits compute module filtered colimits:
   the action on a representative is a[s]=[as], followed by module sheafification.
   The canonical direct-image colimit comparison is the identity on these sections,
   hence an isomorphism on a covering basis. -/
theorem proEtale_ringed_open_closed {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ q : SheafOfModules.{u + 1} (proEtaleModuleCoefficients
        ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)) ≌
          SheafOfModules.{u + 1} ((proEtaleModuleCoefficients A).over U),
      Nonempty (proEtaleModuleInverseImage U.hom A ⋙ q.functor ≅
        SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients A) U) ∧
    ∃ (ai : proEtaleModuleInverseImage i A ⊣ proEtaleRingedDirectImage i A)
      (aj : proEtaleRingedExtensionByZero U A ⊣
        SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients A) U),
      (∀ H, IsIso (ai.counit.app H)) ∧
      (∀ G, IsIso (aj.unit.app G)) ∧
      (∀ H, IsZero ((SheafOfModules.overFunctor.{u + 1}
        (proEtaleModuleCoefficients A) U).obj ((proEtaleRingedDirectImage i A).obj H))) ∧
      (∀ G, IsZero ((proEtaleModuleInverseImage i A).obj
        ((proEtaleRingedExtensionByZero U A).obj G))) ∧
      PreservesFiniteLimits (proEtaleRingedExtensionByZero U A) ∧
      PreservesFiniteColimits (proEtaleRingedExtensionByZero U A) ∧
      PreservesFiniteLimits (proEtaleRingedDirectImage i A) ∧
      PreservesFiniteColimits (proEtaleRingedDirectImage i A) ∧
      (∀ M, Mono (aj.counit.app M) ∧ Epi (ai.unit.app M) ∧
        (ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)).Exact) ∧
      (CompactSpace X → QuasiSeparatedSpace X →
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
          PreservesColimitsOfShape I (proEtaleRingedDirectImage i A)) := by
  sorry

end AlgebraicGeometry.Scheme
