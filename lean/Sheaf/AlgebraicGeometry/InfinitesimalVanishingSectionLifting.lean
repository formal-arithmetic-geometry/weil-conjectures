/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.PQFCohomology

import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.SectionBoundaryExact
import Sheaf.Paper.MLCohomologyPowersIdeal
import WeilConjectures.AlgebraicGeometry.FormalFunctionsLocalStalkComparison
import Sheaf.Paper.HigherDirectImagePresheaf

/-! # Infinitesimal vanishing and neighbourhood lifting of fibre sections

Source: Stacks Project, Cohomology of Schemes, Tag 0D2M, proof of
lemma-ample-on-fibre, local-base-change and degree-zero lifting paragraphs;
Tag 02OB(3) and Tag 02OD, the comparison before completion.
(blueprint: lem-trf-infinitesimal-vanishing-section-lifting).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The concrete layer `(J^n / J^(n+1)) ⊗ E_X` on
`X = Z ×_S Spec O_{S,s}`, with `J = m_s O_X` and `E_X` the tensor pullback of `E`.
The quotient is the existing `formalModuleQuotient J 1` applied to `J^n`:
its denominator is the multiplication image `J J^n = J^(n+1)`.
Source: Stacks Project, Tag 0D2M, successive quotient exact sequences.
(blueprint: lem-trf-infinitesimal-vanishing-section-lifting). -/
noncomputable def infinitesimalSectionLiftingLayer {Z S : Scheme.{u}}
    (f : Z ⟶ S) (s : S) (E : Z.Modules) (n : ℕ) :
    (Limits.pullback f (S.fromSpecStalk s)).Modules :=
  let J := (Scheme.IdealSheafData.ofIdealTop
    ((IsLocalRing.maximalIdeal (S.presheaf.stalk s)).map
      (Scheme.ΓSpecIso (S.presheaf.stalk s)).inv.hom)).comap
        (pullback.snd f (S.fromSpecStalk s))
  formalModuleQuotient J 1 (Scheme.idealSheafPower J.toModulesι n).1 ⊗
    (tensorPullback (pullback.fst f (S.fromSpecStalk s))).obj E

/-- Vanishing of the positive infinitesimal layers lifts every fibre section to a
neighbourhood of the base point. The section equation is written on the inverse image
of `f ⁻¹ᵁ U` in the fibre; this is the whole fibre because `s ∈ U`.
Source: Stacks Project, Tag 0D2M, local-base-change and degree-zero lifting argument,
with Tag 02OB(3) and the uncompleted comparison of Tag 02OD.
(blueprint: lem-trf-infinitesimal-vanishing-section-lifting).

Proof:
1. Choose an affine neighbourhood of s. Its ring is Noetherian by
   pqf-lem-affine-open-locnoeth, and its localization O_{S,s} is Noetherian by
   lem-weil-pbc-localization-noetherian and
   lem-weil-pbc-spec-local-ring-canonical-morphism.
2. Proper base change and pqf-lem-locnoeth-lft make Z and X locally Noetherian.
   Pullback preserves invertibility; the coherent finite-type criterion
   pqf-lem-coherent-ft-locnoeth makes E and its pullback F coherent.
3. Put Q_n = F/J^n F. Trivialize F locally to identify the kernel of
   Q_(n+1) → Q_n with (J^n/J^(n+1)) ⊗ F. The multiplication and quotient maps
   glue, giving a short exact sequence with this kernel.
4. The canonical local-ring morphism factors the residue-field morphism.
   The fibre-product universal property identifies Z_s with the closed fibre of X.
   lem-weil-pbc-quotient-base-change-closed-immersion-ideal identifies its ideal
   with J. lem-weil-pbc-closed-immersion-unit-quotient identifies Q_1 with
   the direct image of E_s, and its quotient map with restriction of sections.
5. By lem-sc-module-section-boundary-exact and the H^1 hypothesis, the maps
   Γ(Q_(n+1)) → Γ(Q_n) are surjective for n ≥ 1. Finite induction lifts any
   prescribed section of Q_1 to each fixed finite level.
6. Apply lem-weil-pbc-ml-cohomology-powers-ideal in degree zero. For some c,
   the image from level 1+c in Γ(Q_1) equals the image from Γ(X,F).
   Step 5 therefore yields u in Γ(X,F) restricting to the prescribed fibre section.
7. lem-weil-pbc-formal-functions-local-stalk-comparison identifies Γ(X,F) with
   (R^0 f_* E)_s and respects neighbourhood sections. The degree-zero clause of
   lem-weil-pbc-higher-direct-image-presheaf identifies R^0 f_* E with f_* E.
   Represent the resulting stalk element by a section on some U containing s,
   using def-weil-pbc-module-stalk. Its pullback to X equals u.
8. Pull back further to the closed fibre. Functoriality of tensor pullback
   identifies the composite with the canonical pullback of the neighbourhood
   section to Z_s, which equals the prescribed section by step 6. -/
theorem exists_neighbourhood_section_of_infinitesimal_vanishing
    {Z S : Scheme.{u}} (f : Z ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] [CompactSpace S] (s : S)
    (E : Z.Modules) [E.IsInvertible]
    (hvanishing : ∀ n : ℕ, 1 ≤ n →
      IsZero ((RingedSpace.moduleCohomology
        (Limits.pullback f (S.fromSpecStalk s)).toRingedSpace 1).obj
          (infinitesimalSectionLiftingLayer f s E n)))
    (t : Γ((tensorPullback (f.fiberι s)).obj E, ⊤)) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ σ : Γ(E, f ⁻¹ᵁ U),
      tensorPullbackSection (f.fiberι s) E (f ⁻¹ᵁ U) σ =
        ((tensorPullback (f.fiberι s)).obj E).presheaf.map
          (homOfLE (le_top : (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ ⊤)).op t := by
  sorry

end AlgebraicGeometry.Scheme.Modules
