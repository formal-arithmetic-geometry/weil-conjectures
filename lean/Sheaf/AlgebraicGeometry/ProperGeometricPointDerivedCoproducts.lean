/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.CategoryTheory.CoproductsOfCopowers

/-! # Coproducts for proper direct image over a geometric point

Source: Stacks Project, Tags 0F11 and 0F12.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Proper direct image over an algebraically closed field preserves arbitrary coproducts
at finite coefficients.
Source: Stacks Project, Lemma 59.96.3 (Tag 0F11), used in Lemma 59.96.5 (Tag 0F12).
(blueprint: lem-etale-proper-geometric-point-derived-coproducts)

Proof in words: properness makes X a quasi-compact separated finite-type k-scheme. Its
finite dimension and the torsion cohomological-dimension bound give a uniform bound on
higher cohomology of finite-coefficient sheaves. Module sheaves on Spec k are canonically
constant, so sections identify these bounds with the higher-direct-image bounds. The
module-cohomology forgetful comparison transfers the torsion bound to Λ-modules. Higher
direct images commute with
filtered colimits, hence with sums. Represent each input complex by a K-injective complex
with injective terms. Their termwise direct sum represents the coproduct in the derived
category, and each of its terms is direct-image-acyclic: higher direct images commute
with sums and vanish on the injective summands. Finite cohomological dimension permits
computing the unbounded right derived functor by this complex of acyclic terms. Taking
direct image termwise commutes with the sums, so the resulting complex represents the
coproduct of the direct images. The construction identifies the comparison map with the
canonical coproduct comparison. The finite ring is killed by its positive additive
characteristic; the same argument works for its module category, including the zero ring.
The empty index set and empty X are included. -/
theorem proper_geometricPoint_pushforward_preservesCoproducts
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] :
    ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (R((p)_*[ModuleCat.{u + 1} Λ])) := by
  intro I
  let : HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  let : HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  exact preservesCoproducts_of_preservesCopowers
    (R((p)_*[ModuleCat.{u + 1} Λ])) I (proper_geometricPoint_preservesCopowers Λ p I)

end AlgebraicGeometry.Etale
