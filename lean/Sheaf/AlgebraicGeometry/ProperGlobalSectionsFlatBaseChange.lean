/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections

/-!
# Flat base change for global sections of a proper scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 30.5.2, Tag 02KH,
with the structure sheaf in degree zero
(blueprint: lem-weil-pbc-stein-flat-base-change-global-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flat base change for the structure sheaf in degree zero. The square of global-section
maps of the cartesian square `X ×_{Spec R} Spec S` is a pushout of commutative rings, i.e.
the canonical map `Γ(X, ⊤) ⊗_{Γ(Spec R)} Γ(Spec S) → Γ(X ×_{Spec R} Spec S, ⊤)` is an
isomorphism. The last clause says that if the canonical map `R → Γ(X, ⊤)` is an isomorphism,
then so is the canonical map `S → Γ(X ×_{Spec R} Spec S, ⊤)`.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), specialized to a proper morphism and
`i = 0` (blueprint: lem-weil-pbc-stein-flat-base-change-global-sections).

Proof: Properness makes X quasi-compact and quasi-separated. Apply the proved
`isPushout_appTop_of_flat` to f and the flat morphism Spec S → Spec R. This is the
degree-zero flat-base-change theorem of Mathlib, specialized to the top opens.
If GammaSpecIso.inv followed by f.appTop is an isomorphism, cancel GammaSpecIso.inv
to see that f.appTop is an isomorphism. The opposite arrow of the pushout is then
an isomorphism by IsPushout.isIso_inr_of_isIso, and composition with GammaSpecIso.inv
over S gives the final clause. -/
theorem Scheme.Hom.globalSections_flat_base_change
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    IsPushout f.appTop (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop ∧
      (IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) →
        IsIso ((Scheme.ΓSpecIso (.of S)).inv ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have h := isPushout_appTop_of_flat
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) f
  refine ⟨h, ?_⟩
  intro hi
  have : IsIso f.appTop := by
    exact (isIso_comp_left_iff (Scheme.ΓSpecIso (.of R)).inv f.appTop).mp hi
  have := h.isIso_inr_of_isIso
  infer_instance

end AlgebraicGeometry
