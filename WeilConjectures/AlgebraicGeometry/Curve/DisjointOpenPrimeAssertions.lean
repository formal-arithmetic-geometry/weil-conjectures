/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import WeilConjectures.AlgebraicGeometry.Curve.PrimeBiproductAssertions
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Decomposition of extension by zero on disjoint opens -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Assertions for extension from a finite union of disjoint opens are componentwise.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph, and Lemma 0A5C. -/
theorem assertions_iff_disjoint_open_prime (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (n : ℕ) (U : Fin n → X.Opens)
    (hU : Pairwise (fun a b ↦ Disjoint (U a : Set X) (U b))) :
    IsCurve.Assertions Λ f
      (((⨆ a, U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
        (((⨆ a, U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ↔
      ∀ a, IsCurve.Assertions Λ f
        (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
          (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) := by
  classical
  let G : Fin n → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun a ↦
    (((U a).ι)_!open[ModuleCat.{u + 1} Λ]).obj
      ((((U a).ι)^*[ModuleCat.{u + 1} Λ]).obj F)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hGc (a : Fin n) : Scheme.IsConstructibleSheaf (G a) := by
    have : Scheme.IsConstructibleSheaf
        ((((U a).ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      Scheme.IsConstructibleSheaf.upperStar _ _
    have : TopologicalSpace.NoetherianSpace (U a) :=
      (U a).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U a).ι :=
      ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    exact Scheme.IsConstructibleSheaf.openImmersionLowerShriek
      (U a).ι (U a).closedComplement
      (by rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]) _
  have hGr (a : Fin n) : r • 𝟙 (G a) = 0 := by
    let T := ((U a).ι)^*[ModuleCat.{u + 1} Λ] ⋙
      ((U a).ι)_!open[ModuleCat.{u + 1} Λ]
    simpa [T, G, Functor.map_nsmul] using congrArg T.map hF
  obtain ⟨e⟩ := Etale.disjointOpenExtension_biproduct_iso Λ F n U hU
  exact assertions_iff_of_prime_biproduct_iso Λ f r G hGc hGr e

end AlgebraicGeometry.IsCurve
