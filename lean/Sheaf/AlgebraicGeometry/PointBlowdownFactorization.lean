/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Blowup.Gluing
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper
import Sheaf.AlgebraicGeometry.RegularPointBlowupFunctions

/-! # Factorization through a regular surface point blowdown

Source: Stacks Project, Resolution of Surfaces, Tag 0C5J,
Lemma `lemma-factor-through-contraction`, applied to a regular surface point blowup
(blueprint: lem-sfb-point-blowdown-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Descend the sheaf map along an invertible canonical direct-image map.
This is the ringed-space construction in Stacks, Tag 0C5J. -/
private theorem factor_presheafedSpace
    {X Y Z : PresheafedSpace CommRingCat.{u}} (b : X ⟶ Y) [IsIso b.c]
    (f : X ⟶ Z) (g : (Y : TopCat) ⟶ (Z : TopCat)) (h : b.base ≫ g = f.base) :
    ∃ k : Y ⟶ Z, k.base = g ∧ b ≫ k = f := by
  obtain ⟨fbase, fc⟩ := f
  dsimp at h
  subst fbase
  let k : Y ⟶ Z :=
    ⟨g, fc ≫ (TopCat.Presheaf.pushforward _ g).map (inv b.c)⟩
  refine ⟨k, rfl, ?_⟩
  refine PresheafedSpace.hext (b ≫ k) ⟨b.base ≫ g, fc⟩ rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext V
  rw [PresheafedSpace.comp_c_app]
  change (fc.app V ≫ (inv b.c).app
    (Opposite.op ((TopologicalSpace.Opens.map g).obj V.unop))) ≫
      b.c.app (Opposite.op ((TopologicalSpace.Opens.map g).obj V.unop)) = fc.app V
  rw [Category.assoc, ← NatTrans.comp_app, IsIso.inv_hom_id]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity identifies base maps, and cancellation of the direct-image
isomorphism then identifies sheaf maps (Stacks, Tag 0C5J). -/
private theorem cancel_presheafedSpace
    {X Y Z : PresheafedSpace CommRingCat.{u}} (b : X ⟶ Y) [IsIso b.c]
    (hsurj : Function.Surjective b.base) (g h : Y ⟶ Z) (heq : b ≫ g = b ≫ h) :
    g = h := by
  have hb : g.base = h.base := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    exact congrArg (fun k : X ⟶ Z => k.base x) heq
  obtain ⟨gb, gc⟩ := g
  obtain ⟨hb', hc⟩ := h
  dsimp at hb
  subst hb'
  have : gc = hc := by
    apply NatTrans.ext
    funext V
    have hh := PresheafedSpace.congr_app heq V
    apply (cancel_mono
      (b.c.app (Opposite.op ((TopologicalSpace.Opens.map gb).obj V.unop)))).mp
    simpa using hh
  subst hc
  rfl

/-- A morphism constant on the exceptional fibre of a regular surface point blowup
factors uniquely through its structure morphism. The centre is the reduced closed
subscheme defined by the vanishing ideal of the closed singleton.
Source: Stacks Project, Resolution of Surfaces, Tag 0C5J
(blueprint: lem-sfb-point-blowdown-factorization).

Proof plan:
1. Write the exceptional image as {z}; the exceptional fibre is nonempty.
   By thm-nagata-global-blowup-complement the blowup is an isomorphism away from x,
   hence is surjective. The point ideal is finitely generated on each affine open
   because T is locally Noetherian. By lemma-nagata-blowup-proper and
   def-weil-proper-morphism the blowup map is proper and closed. Apply
   lem-sfb-regular-point-blowup-functions to identify O_T with the direct image of
   O_W by its canonical map beta, compatibly with restriction. That auxiliary
   lemma retains points of local dimension less than two.
2. Define g(x) = z and use the unique preimage under b away from x to define g
   elsewhere. Then f = g composed with b. For every open V of Z, the complement
   of g inverse V is b(W minus f inverse V), which is closed. Thus g is continuous;
   surjectivity of b also gives uniqueness on underlying points.
3. On each open V of Z put U = g inverse V and define g-sharp as beta_U inverse
   composed with f-sharp. Compatibility with restriction follows from that of
   beta and f-sharp. The composition formula in
   def-weil-locally-ringed-space-morphism gives g composed with b = f as ringed maps.
4. For any t choose w over t. On stalks f-sharp_w = b-sharp_w composed with
   g-sharp_t. If a lies in the maximal ideal at g(t), locality of f-sharp_w makes
   its image a nonunit. If g-sharp_t(a) were a unit, its image under b-sharp_w
   would be a unit. Thus g-sharp_t is local and g is a scheme morphism.
5. Any other factorization agrees on points by surjectivity. On every open,
   cancel beta_U in the equality of composites to identify its sheaf map with
   g-sharp. This proves uniqueness as a morphism of schemes. -/
theorem existsUnique_factor_through_point_blowup
    (T : Scheme.{u}) [CompactSpace T] (hregular : IsRegularScheme T)
    (hdim : topologicalKrullDim T = 2) (x : T) (hx : IsClosed ({x} : Set T))
    (Z : Scheme.{u}) (f : (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowup ⟶ Z)
    (himage : ∃ z : Z,
      f '' ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap ⁻¹' {x}) = {z}) :
    ∃! g : T ⟶ Z, (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap ≫ g = f := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  let b := I.blowupMap
  have : IsLocallyNoetherian T := hregular.1
  obtain ⟨z, hz⟩ := himage
  have hfibre : Set.Nonempty (b ⁻¹' {x}) := by
    obtain ⟨w, hw, _⟩ := hz.symm.subset (Set.mem_singleton z)
    exact ⟨w, hw⟩
  have : IsIso b.toLRSHom.toHom.c :=
    isIso_structureSheafMap_point_blowup T hregular (le_of_eq hdim) x hx hfibre
  let U := I.support.compl
  have : IsIso (b ∣_ U) := I.isIso_blowupMap_restrict_support_compl
  have hU (t : T) : t ∈ U ↔ t ≠ x := by
    change t ∉ (I.support : Set T) ↔ t ≠ x
    simp [I]
  have hsurj : Function.Surjective b := by
    intro t
    by_cases ht : t = x
    · obtain ⟨w, hw⟩ := hfibre
      exact ⟨w, ht ▸ hw⟩
    · obtain ⟨w, hw⟩ := (b ∣_ U).surjective ⟨t, (hU t).mpr ht⟩
      exact ⟨w.1, (morphismRestrict_base_coe b U w).symm.trans
        (congrArg Subtype.val hw)⟩
  have hconstant : Function.FactorsThrough f b := by
    intro w v hwv
    by_cases hw : b w = x
    · have hv : b v = x := hwv.symm.trans hw
      have hwz : f w = z := hz.subset ⟨w, hw, rfl⟩
      have hvz : f v = z := hz.subset ⟨v, hv, rfl⟩
      exact hwz.trans hvz.symm
    · have hv : b v ≠ x := hwv ▸ hw
      have he : (b ∣_ U) ⟨w, (hU _).mpr hw⟩ =
          (b ∣_ U) ⟨v, (hU _).mpr hv⟩ := by
        apply Subtype.ext
        simpa only [morphismRestrict_base_coe] using hwv
      have : w = v := congrArg Subtype.val ((b ∣_ U).homeomorph.injective he)
      exact congrArg f this
  have hquot := b.isClosedMap.isQuotientMap b.continuous hsurj
  let g := TopCat.ofHom (hquot.lift f.base.hom hconstant)
  have hg : b.base ≫ g = f.base := by
    apply TopCat.hom_ext
    exact hquot.lift_comp f.base.hom hconstant
  obtain ⟨k, _, hk⟩ := factor_presheafedSpace b.toLRSHom.toHom
    f.toLRSHom.toHom g hg
  have hlocal : ∀ t : T, IsLocalHom (k.stalkMap t).hom := by
    intro t
    obtain ⟨w, rfl⟩ := hsurj t
    have he := PresheafedSpace.stalkMap.congr_hom _ _ hk w
    have : IsLocalHom ((b.toLRSHom.toHom ≫ k).stalkMap w).hom := by
      rw [he]
      infer_instance
    rw [PresheafedSpace.stalkMap.comp] at this
    exact isLocalHom_of_comp (k.stalkMap (b w)).hom
      (b.toLRSHom.toHom.stalkMap w).hom
  let g' : T ⟶ Z := ⟨⟨k, hlocal⟩⟩
  have hfac : b ≫ g' = f := by
    apply Scheme.Hom.ext'
    apply LocallyRingedSpace.Hom.ext'
    exact hk
  refine ⟨g', hfac, ?_⟩
  intro h hh
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  apply cancel_presheafedSpace b.toLRSHom.toHom hsurj
  exact congrArg (fun q => q.toLRSHom.toHom) (hh.trans hfac.symm)

end AlgebraicGeometry
