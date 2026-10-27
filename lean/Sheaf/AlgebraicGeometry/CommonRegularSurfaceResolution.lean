/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import Sheaf.AlgebraicGeometry.SurfaceRationalMapPointResolution
import Sheaf.AlgebraicGeometry.ProperBirationalSurfaceFactorization

/-!
# Common resolution of regular proper surfaces

Source: Stacks Project, Resolution of Surfaces, Tag 0C5S,
`lemma-birational-regular-surfaces`
(blueprint: lem-sfb-common-regular-surface-resolution).

The ordinary towers are the existing `OrdinaryBlowupTower`. Their centers are required
to be the vanishing ideals of closed singletons, hence have the reduced point structure.
Agreement on a dense open of the common source keeps the specified birational map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Two regular integral proper surfaces over a Noetherian base admit a common regular
integral model by finite sequences of blowups of reduced closed points, inducing a
specified dense-open identification over the base. Towers of length zero are allowed.

Source: Stacks Project, Tag 0C5S, `lemma-birational-regular-surfaces`
(blueprint: lem-sfb-common-regular-surface-resolution).

Proof plan:
1. Properness makes both surfaces Noetherian, by
   lem-weil-pbc-finite-type-over-noetherian, and makes the second structural map separated.
2. Apply lem-sfb-surface-rational-map-point-resolution to the first surface and the map
   from its given dense open into the second. This gives a regular integral point-blowup
   tower and an extension g to the second surface, agreeing with the specified map.
3. The top is proper over the base by lem-weil-pbc-proper-composition. Its extension g
   is proper by lem-weil-pbc-proper-over-separated, and is birational because on the
   inverse image of the given open it agrees with the given dense-open isomorphism.
4. Apply lem-sfb-proper-birational-surface-factorization to g. Its factorization gives
   the second point-blowup tower, up to isomorphism over the second surface. Give every
   level its structural map by composing to that surface and then to the base. The
   common top W is regular and integral, both tower composites are over the base,
   and their restrictions agree with the original identification on a dense open.
-/
theorem exists_common_regular_surface_resolution
    (S T₁ T₂ : Scheme.{u}) [IsNoetherian S] [IsIntegral T₁] [IsIntegral T₂]
    (s₁ : T₁ ⟶ S) (s₂ : T₂ ⟶ S) [IsProper s₁] [IsProper s₂]
    (hT₁ : IsRegularScheme T₁) (hT₂ : IsRegularScheme T₂)
    (hdim₁ : topologicalKrullDim T₁ = 2) (hdim₂ : topologicalKrullDim T₂ = 2)
    (U₁ : T₁.Opens) (U₂ : T₂.Opens)
    (hU₁ : Dense (U₁ : Set T₁)) (hU₂ : Dense (U₂ : Set T₂))
    (α : U₁.toScheme ≅ U₂.toScheme)
    (hα : α.hom ≫ U₂.ι ≫ s₂ = U₁.ι ≫ s₁) :
    ∃ (W : Scheme.{u}) (w : W ⟶ S) (q₁ : W ⟶ T₁) (q₂ : W ⟶ T₂),
      IsRegularScheme W ∧ IsIntegral W ∧ q₁ ≫ s₁ = w ∧ q₂ ≫ s₂ = w ∧
      (∃ (A : OrdinaryBlowupTower T₁) (e : W ≅ A.level (Fin.last A.length)),
        e.hom ≫ A.toBase (Fin.last A.length) = q₁ ∧
        ∀ i : Fin A.length, ∃ (p : A.level i.castSucc) (hp : IsClosed ({p} : Set _)),
          A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∧
      (∃ (A : OrdinaryBlowupTower T₂) (e : W ≅ A.level (Fin.last A.length)),
        e.hom ≫ A.toBase (Fin.last A.length) = q₂ ∧
        ∀ i : Fin A.length, ∃ (p : A.level i.castSucc) (hp : IsClosed ({p} : Set _)),
          A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∧
      ∃ V : W.Opens, Dense (V : Set W) ∧ ∃ hV : V ≤ q₁ ⁻¹ᵁ U₁,
        q₁.resLE U₁ V hV ≫ α.hom ≫ U₂.ι = V.ι ≫ q₂ := by
  have : IsNoetherian T₁ :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian s₁
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace s₁ }
  have : IsNoetherian T₂ :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian s₂
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace s₂ }
  obtain ⟨A, g, hcenters, hlevels, hp, hpU, hg, hagree⟩ :=
    exists_surface_rational_map_point_resolution S T₁ T₂ s₁ s₂ hT₁ hdim₁ U₁ hU₁
      (α.hom ≫ U₂.ι) (by simpa only [Category.assoc] using hα)
  let W := A.level (Fin.last A.length)
  let p := A.toBase (Fin.last A.length)
  have : IsIntegral W := (hlevels (Fin.last A.length)).1
  have hW : IsRegularScheme W := (hlevels (Fin.last A.length)).2.1
  have : IsNoetherian W := (hlevels (Fin.last A.length)).2.2.1
  have hdimW : topologicalKrullDim W = 2 := (hlevels (Fin.last A.length)).2.2.2
  have : IsProper p := hp
  have : IsIso (p ∣_ U₁) := hpU
  have : IsProper (g ≫ s₂) := by
    rw [hg]
    infer_instance
  have : IsProper g := IsProper.of_comp g s₂
  let V := p ⁻¹ᵁ U₁
  have hV : Dense (V : Set W) := by
    apply V.isOpen.dense
    obtain ⟨x, hx⟩ := hU₁.nonempty
    let z := (inv (p ∣_ U₁)) ⟨x, hx⟩
    exact ⟨z.1, z.2⟩
  have hbirational : ∃ (V : W.Opens) (U : T₂.Opens),
      Dense (V : Set W) ∧ Dense (U : Set T₂) ∧
      ∃ e : V.toScheme ≅ U.toScheme, V.ι ≫ g = e.hom ≫ U.ι := by
    refine ⟨V, U₂, hV, hU₂, asIso (p ∣_ U₁) ≪≫ α, ?_⟩
    simpa only [Iso.trans_hom, asIso_hom, Category.assoc] using hagree
  obtain ⟨B, eB, heB, hB⟩ :=
    exists_point_blowup_factorization_of_proper_birational W T₂ hW hT₂
      hdimW hdim₂ g hbirational
  refine ⟨W, p ≫ s₁, p, g, hW, inferInstance, rfl, hg, ?_,
    ⟨B, eB, heB, hB⟩, V, hV, le_rfl, ?_⟩
  · refine ⟨A, Iso.refl W, ?_, ?_⟩
    · exact Category.id_comp p
    · intro i
      obtain ⟨x, hx, hc, _⟩ := hcenters i
      exact ⟨x, hx, hc⟩
  · rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hagree.symm

end AlgebraicGeometry
