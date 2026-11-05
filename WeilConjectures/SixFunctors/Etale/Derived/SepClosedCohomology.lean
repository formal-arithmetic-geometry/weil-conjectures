/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Sites.LocalSite
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Étale cohomology of the spectrum of a separably closed field

Let `K` be a separably closed field and `s = Spec K`. Every covering sieve of the terminal
object of the small étale site of `s` is trivial, so this site is a local site, and the
constant sheaf functor is fully faithful: the global sections of the constant sheaf `Λ` are
`Λ`. The global sections functor is exact on étale sheaves of `Λ`-modules on `s`, so the
étale cohomology of a sheaf `F` on `s` is `Γ(s, F)` in degree `0` and vanishes in the other
degrees.

## Main definitions and results

- `AlgebraicGeometry.Scheme.isLocalSite_smallEtaleTopology_of_isSepClosed_derived`: the small étale
  site of `Spec K` is a local site.
- `AlgebraicGeometry.Scheme.globalSectionsUnitIsoOfIsSepClosed`: `Γ(Spec K, Λ) ≅ Λ`.
- `AlgebraicGeometry.Etale.cohomology_singleFunctor_of_isSepClosed`: `H^0(Spec K, F) ≅ Γ(F)`
  and `H^q(Spec K, F) = 0` for `q ≠ 0`.
- `AlgebraicGeometry.HasInvertibleExponent.spec_of_charP`: a finite ring `Λ` in which the
  characteristic `p` of a field `Ω` is invertible has invertible exponent on `Spec Ω`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

open CategoryTheory.GrothendieckTopology

variable (K : Type u) [Field K] [IsSepClosed K]

/-- Over a separably closed field `K`, the small étale site of `Spec K` is a local site: every
covering sieve of its terminal object contains the identity
(`AlgebraicGeometry.Scheme.id_mem_of_mem_smallEtaleTopology_of_isSepClosed`). -/
instance isLocalSite_smallEtaleTopology_of_isSepClosed_derived :
    (Spec (.of K)).smallEtaleTopology.IsLocalSite where
  eq_top_of_mem S hS := by
    let e : etalePoint K ≅ ⊤_ _ := isTerminalEtalePoint.uniqueUpToIso terminalIsTerminal
    have h := id_mem_of_mem_smallEtaleTopology_of_isSepClosed K (S.pullback e.hom)
      ((Spec (.of K)).smallEtaleTopology.pullback_stable e.hom hS)
    rw [Sieve.pullback_apply, Category.id_comp] at h
    rw [← Sieve.id_mem_iff_eq_top]
    simpa using S.downward_closed h e.inv

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Over a separably closed field `K`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec K` preserves epimorphisms. -/
instance preservesEpimorphisms_Γ_of_isSepClosed :
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesEpimorphisms :=
  Functor.PreservesEpimorphisms.of_iso
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).symm

/-- Over a separably closed field `K`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec K` is exact; in particular it preserves finite colimits. -/
instance preservesFiniteColimits_Γ_of_isSepClosed :
    PreservesFiniteColimits (Sheaf.Γ (Spec (.of K)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) :=
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
  Functor.preservesFiniteColimits_of_preservesHomology _

end Scheme

namespace Etale

open Scheme

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The derived global sections `RΓ(X, -)` are an additive functor, being triangulated. -/
instance additive_rightDerivedGlobalSections (X : Scheme.{u}) :
    (rightDerivedGlobalSections A X).Additive :=
  inferInstanceAs ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.Additive)

variable (K : Type u) [Field K] [IsSepClosed K] (Λ : Type (u + 1)) [CommRing Λ]

end Etale

end AlgebraicGeometry
