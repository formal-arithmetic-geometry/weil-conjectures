/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Paper.LocalHomTowerCriterion
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Localization detects vanishing of the multiplication tower

Source: Stacks Project, More on Algebra, Tag 091P, equivalence (1) and (3)
(blueprint: lem-weil-pbc-module-localization-tower-vanishing).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Vanishing of any derived limit of the multiplication-by-`f` tower is equivalent to
vanishing of every Hom group from the shifted degree-zero localization.
`ULift` only places the localization in the chosen module universe; it is linearly
isomorphic to the original localization by `ULift.moduleEquiv`.

Source: Stacks Project, More on Algebra, Tag 091P, equivalence (1) and (3)
(blueprint: lem-weil-pbc-module-localization-tower-vanishing).

Proof: Identify modules with module sheaves on the one-object identity-only site with
trivial topology. Evaluation and the one-value sheaf construction identify complexes,
quasi-isomorphisms, derived categories, products, and the Roos triangles. The localized
sheaf is precisely the module `A[1/f]`. Choose a K-injective representative `I` of `K`
using prop-pur-kinjective-resolutions-exist. Its complex `C = Hom(A[1/f], I)` is the Hom
complex of def-pur-hom-complex and represents the derived internal Hom of
def-pur-derived-internal-hom. For each integer `q`, the bijection of
lem-weil-pbc-kinjective-hom-derived identifies maps from `A[1/f][0][q]` to `K` with
homotopy classes of maps to `I`. These are cycles in degree `-q` of `C` modulo boundaries:
a chain map is a linear map to `I` in degree `-q` killed by its differential, and a homotopy
changes it by the differential of a map into degree `-q-1`. Thus the Hom group vanishes
exactly when `H^(-q)(C)` vanishes. By lem-weil-pbc-local-hom-tower-criterion, the derived
internal Hom is zero exactly when the prescribed derived limit is zero. Finally a complex
represents zero in the derived category exactly when all its cohomology vanishes, since
its map to zero is then a quasi-isomorphism. All integer degrees occur, so no boundedness
or nonzerodivisor hypothesis is needed. -/
theorem module_localization_tower_vanishing_iff {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A)
    (K : DerivedCategory (ModuleCat.{max u v} A)) [HasProduct (fun _ : ℕ ↦ K)]
    (T : DerivedCategory (ModuleCat.{max u v} A))
    (hT : IsDerivedLimit (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K) T) :
    IsZero T ↔ ∀ (q : ℤ), ∀ (g :
      ((singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A (ULift.{v} (Localization.Away f))))⟦q⟧ ⟶ K), g = 0 := by
  sorry

end DerivedCategory
