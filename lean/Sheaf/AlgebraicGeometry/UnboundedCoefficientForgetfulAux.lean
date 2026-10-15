/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Restriction of scalars preserves the invertibility test for the canonical unbounded
exchange, after identifying its source and target with the restricted-coefficient versions.
Source: Stacks Project, Tag 0D6J(3), and the canonical mate coherence of
`lem-kun-unbounded-abelian-exchange-comparison`.
(blueprint: lem-kun-proper-base-change-forgetful-aux)

Proof in words: write U_R and U_S for forgetting R- and S-module structure to abelian
sheaves. Termwise restriction gives U_R Res = U_S, including on complexes and their
localizations. Inverse-image commutes with this identification. For direct images,
Tag 0D6J(3) gives canonical isomorphisms from the forgotten unbounded derived direct
images to the abelian derived direct image. The canonical mate coherence of
lem-kun-unbounded-abelian-exchange-comparison identifies both forgotten exchange
morphisms with the same abelian exchange, conjugated by their invertible endpoint
comparisons. Hence one forgotten exchange is invertible exactly when the other is.
Forgetting R-module structure reflects isomorphisms, because homology commutes with
this exact functor and isomorphisms of sheaves are tested sectionwise. Applying this
test to the two R-derived morphisms gives the stated equivalence. No cyclic-coefficient,
properness, flatness, boundedness, or exchange-invertibility hypothesis is used. -/
theorem isIso_restricted_derivedBaseChangeMap_iff
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    IsIso ((CategoryTheory.Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).map
      ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} S) sq.toCommSq).app K)) ↔
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq.toCommSq).app
      ((CategoryTheory.Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K)) := by
  sorry

end AlgebraicGeometry
