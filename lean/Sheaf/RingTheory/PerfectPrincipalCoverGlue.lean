/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.RingTheory.FiniteProjectiveComplexFreeModel
import Sheaf.RingTheory.RingPseudoCoherent
import Sheaf.RingTheory.RingPseudoCoherentLocalizationGlue
import Sheaf.Algebra.Homology.TorAmplitudeFlatModel
import Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Sheaf.Algebra.Homology.TorAmplitudePrincipalCover
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Perfect complexes glue over finite principal covers

Source: Stacks Project, More on Algebra, Tag 066Y, lemma-glue-perfect
(blueprint: lem-weil-pbc-perfect-ring-principal-cover-glue).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace DerivedCategory

/-- Perfectness descends across a finite principal cover, including the empty cover.
The functors `L i`, with universal counits `ε i`, are derived extension of scalars
along `R → R[1 / f i]`. Their universal property specifies the usual derived scalar
extension independently of a choice of resolution.

Source: Stacks Project, More on Algebra, Tag 066Y, lemma-glue-perfect
(blueprint: lem-weil-pbc-perfect-ring-principal-cover-glue).

Proof:
1. Choose a complex representing `C`. Localization is flat
   (lem-weil-pbc-localization-flat), so tensor is exact
   (lem-weil-pbc-flat-tensor-exact). Apply lem-pur-derived-change-of-rings and
   lem-pc-kflat-resolution on the one-object site: termwise localization computes `L i`.
2. Replace each bounded finite-projective local model by a bounded-above finite-free
   model using lem-pc-finite-projective-complex-free-model. These witness local
   pseudo-coherence (def-pc-ring-pseudo-coherent-complex); descend it by
   lem-pc-ring-pseudo-coherent-localization-glue.
3. Projective modules are flat (lem-weil-pbc-projective-module-flat). Apply the
   bounded-flat-model implication of lem-pc-module-tor-amplitude-flat-model to obtain
   local Tor intervals. Take the minimum of their lower endpoints together with zero,
   and the maximum of their upper endpoints together with zero. The resulting interval
   works for every localization; for the empty family use [0,0].
4. Descend these common bounds by lem-weil-pbc-tor-amplitude-principal-cover-glue.
5. The global bounded-above finite-free model is finite projective termwise.
   Apply lem-pc-ring-pseudo-coherent-finite-tor-perfect to pseudo-coherence and the
   global Tor bounds. Its bounded finite-projective model witnesses `IsPerfect C`. -/
theorem isPerfect_of_principal_cover
    {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (r : ℕ) (f : Fin r → R)
    [∀ i : Fin r, HasDerivedCategory.{u} (ModuleCat.{u} (Localization.Away (f i)))]
    (hf : ∃ v : Fin r → R, ∑ i : Fin r, v i * f i = 1)
    (L : ∀ i : Fin r, DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} (Localization.Away (f i))))
    (ε : ∀ i : Fin r, Qh ⋙ L i ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))))
        (ModuleCat.extendRestrictScalarsAdj
          (algebraMap R (Localization.Away (f i)))).left_adjoint_additive (.up ℤ) ⋙ Qh)
    [∀ i : Fin r, (L i).IsLeftDerivedFunctor (ε i)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (hlocal : ∀ i : Fin r, IsPerfect ((L i).obj C)) : IsPerfect C := by
  sorry

end DerivedCategory
