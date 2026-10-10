/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Local cocycles of complexes of pro-étale sheaves of modules

Draft.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Exactness of a short complex of pro-étale sheaves of modules is local: a section `z` of the
middle term with `g z = 0` is locally of the form `f w`. -/
lemma exists_sieve_eq_of_exact
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hS : S.Exact)
    {U : X.ProEt} (z : S.X₂.obj.obj (op U)) (hz : S.g.hom.app (op U) z = 0) :
    ∃ R ∈ Scheme.ProEt.topology X U, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U), R f →
      ∃ w : S.X₁.obj.obj (op V), S.f.hom.app (op V) w = S.X₂.obj.map f.op z := by
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := hS.epi_kernelLift
  have := (Sheaf.isLocallySurjective_iff_epi' p).2 this
  have : PreservesLimits ((sheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)).obj (op U)) :=
    inferInstanceAs (PreservesLimits (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)))
  obtain ⟨k, hk⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((ShortComplex.exact_kernel S.g).map_of_mono_of_preservesKernel
      ((sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj (op U))
      inferInstance inferInstance) z hz
  refine ⟨_, Presheaf.imageSieve_mem _ p.hom k, fun V f ⟨w, hw⟩ ↦ ⟨w, ?_⟩⟩
  sorry

end AlgebraicGeometry.ProEtale
