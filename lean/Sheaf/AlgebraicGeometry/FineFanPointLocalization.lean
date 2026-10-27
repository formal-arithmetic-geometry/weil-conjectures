/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.AffineFanHomUniversal
import Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood
import Sheaf.AlgebraicGeometry.FineFanChartStalkCoordinates
import Sheaf.AlgebraicGeometry.FineFanChartMinimalAffine
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Data.Fintype.EquivFin

/-!
# Canonical affine localization of a fine fan at a point

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.2--3.1.4, 3.1.8(ii),
3.1.10(ii), printed pp.98--100, and the stalk coordinates in the proof of 3.3.15,
printed p.109 (blueprint: lem-trf-fine-fan-point-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.FineFan

/-- Identify global sections of a restricted space with sections on its defining open.
This is transport along the equality that the image of the whole subspace is the open.
Source: ILO VIII 3.1.6, restriction of the monoid sheaf
(blueprint: lem-trf-fine-fan-point-localization). -/
noncomputable def restrictedGlobalSections (X : SheafedSpace CommMonCat.{u}) (U : Opens X) :
    (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) →* X.presheaf.obj (op U) :=
  (X.presheaf.map (eqToHom (Opens.isOpenEmbedding_obj_top U).symm).op).hom

/-- The actual germ of a canonical chart section, pulled back through the chart and
then identified with a section on the chart open. No coordinate map is chosen.
Source: ILO VIII 3.1.3, 3.1.6 and 3.1.8(ii)
(blueprint: lem-trf-fine-fan-point-localization). -/
noncomputable def Chart.sectionGerm {X : SheafedSpace CommMonCat.{u}} (c : Chart X)
    (z : X) (hz : z ∈ c.openSet) : c.monoid →* stalk X.presheaf z :=
  (germ X.presheaf c.openSet z hz).hom.comp
    ((restrictedGlobalSections X c.openSet).comp (affinePullback c.iso.hom))

/-- The product of the members of a finite generating tuple outside the chart prime.
This is the sum in the source's additive notation; the empty product is the identity.
Source: ILO VIII 3.1.2--3.1.4
(blueprint: lem-trf-fine-fan-point-localization). -/
noncomputable def Chart.localizationElement {X : SheafedSpace CommMonCat.{u}}
    (c : Chart X) (x : c.openSet) {r : ℕ} (a : Fin r → c.monoid) : c.monoid := by
  classical
  exact ∏ i ∈ Finset.univ.filter (fun i ↦ a i ∉ (c.iso.hom.hom.base x).carrier), a i

private noncomputable def chartHomeo {X : SheafedSpace CommMonCat.{u}} (c : Chart X) :
    c.openSet ≃ₜ MonoidPrime c.monoid :=
  TopCat.homeoOfIso
    ((PresheafedSpace.forget CommMonCat).mapIso
      (SheafedSpace.forgetToPresheafedSpace.mapIso c.iso))

private theorem chart_minimal_open {X : SheafedSpace CommMonCat.{u}} (c : Chart X)
    (z : c.openSet) :
    ∃ W : Opens (MonoidPrime c.monoid), chartHomeo c z ∈ W ∧
      ∀ V : Opens (MonoidPrime c.monoid), chartHomeo c z ∈ V → W ≤ V := by
  classical
  obtain ⟨s, hs⟩ := (Monoid.fg_def.mp c.fine.1)
  let a : Fin s.card → c.monoid := fun i ↦ (s.equivFin.symm i).val
  have ha : Set.range a = (s : Set c.monoid) := by
    ext b
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).property
    · intro hb
      exact ⟨s.equivFin ⟨b, hb⟩, by simp [a]⟩
  have hgen : Submonoid.closure (Set.range a) = ⊤ := by rw [ha]; exact hs
  let b := c.localizationElement z a
  have h := monoidPrime_minimal_neighborhood c.monoid c.fine s.card a hgen
    (chartHomeo c z) b rfl
  exact ⟨basicOpen b, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

private theorem fan_minimal_open (F : Fan.{u}) (z : F.space) :
    ∃ (U : Opens F.space) (_hz : z ∈ U),
      (∀ V : Opens F.space, z ∈ V → U ≤ V) := by
  obtain ⟨c, hc⟩ := F.locallyAffine z
  obtain ⟨W, hz, hW⟩ := chart_minimal_open c ⟨z, hc⟩
  let V := (Opens.map c.iso.hom.hom.base).obj W
  let U := c.openSet.isOpenEmbedding.functor.obj V
  refine ⟨U, ⟨⟨z, hc⟩, hz, rfl⟩, ?_⟩
  intro T ht x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let T' := (Opens.map c.iso.inv.hom.base).obj
    ((Opens.map (Opens.inclusion' c.openSet)).obj T)
  have hzT : chartHomeo c ⟨z, hc⟩ ∈ T' := by
    change ((chartHomeo c).symm (chartHomeo c ⟨z, hc⟩)).val ∈ T
    simpa using ht
  have hyT := hW T' hzT hy
  change ((chartHomeo c).symm (chartHomeo c y)).val ∈ T at hyT
  simpa using hyT

private theorem mem_minimal_open_iff {X : TopCat.{u}} (U : Opens X) (z : X)
    (hz : z ∈ U) (hU : ∀ V : Opens X, z ∈ V → U ≤ V) (x : X) :
    x ∈ U ↔ x ⤳ z := by
  constructor
  · intro hx
    exact specializes_iff_forall_open.mpr fun V hV hzV ↦ hU ⟨V, hV⟩ hzV hx
  · intro hx
    exact hx.mem_open U.isOpen hz

private theorem germ_bijective_of_minimal {X : TopCat.{u}}
    (M : TopCat.Presheaf CommMonCat.{u} X) (U : Opens X) (z : X) (hz : z ∈ U)
    (hU : ∀ V : Opens X, z ∈ V → U ≤ V) : Function.Bijective (germ M U z hz) := by
  let j : (OpenNhds z)ᵒᵖ := op ⟨U, hz⟩
  have hj : Limits.IsTerminal j := Limits.IsTerminal.ofUniqueHom
    (fun V ↦ (homOfLE (hU V.unop.1 V.unop.2)).op)
    (fun _ _ ↦ Subsingleton.elim _ _)
  have hi : IsIso (germ M U z hz) :=
    Limits.isIso_ι_of_isTerminal hj (stalkDiagram M z)
  exact ConcreteCategory.bijective_of_isIso (germ M U z hz)

private theorem restrict_sharp (F : Fan.{u}) (U : Opens F.space)
    (x : F.space.restrict U.isOpenEmbedding) :
    IsSharp (stalk (F.space.restrict U.isOpenEmbedding).presheaf x) := by
  have := Functor.initial_of_adjunction (U.isOpenEmbedding.adjunctionNhds x)
  let e : stalk (F.space.restrict U.isOpenEmbedding).presheaf x ≅
      stalk F.space.presheaf x.val :=
    Functor.Final.colimitIso (U.isOpenEmbedding.functorNhds x).op
      (stalkDiagram F.space.presheaf x.val)
  intro p hp
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  exact (F.sharp x.val (e.hom p) (hp.map e.hom.hom)).trans (map_one e.hom.hom).symm

private theorem normalized_iso_unique (F : Fan.{u}) (z : F.space)
    (U : Opens F.space) (hz : z ∈ U)
    (hU : ∀ V : Opens F.space, z ∈ V → U ≤ V)
    (hP : IsFine (stalk F.space.presheaf z))
    (i j : F.space.restrict U.isOpenEmbedding ≅ affine (stalk F.space.presheaf z))
    (hi : IsLocalMorphism i.hom) (hj : IsLocalMorphism j.hom)
    (ni : ∀ p, germ F.space.presheaf U z hz
      (restrictedGlobalSections F.space U (affinePullback i.hom p)) = p)
    (nj : ∀ p, germ F.space.presheaf U z hz
      (restrictedGlobalSections F.space U (affinePullback j.hom p)) = p) : i = j := by
  have hγ := (germ_bijective_of_minimal F.space.presheaf U z hz hU).1
  have ht : Function.Injective (restrictedGlobalSections F.space U) :=
    ConcreteCategory.bijective_of_isIso
      (F.space.presheaf.map (eqToHom (Opens.isOpenEmbedding_obj_top U).symm).op) |>.1
  have hpull : affinePullback i.hom = affinePullback j.hom := by
    ext p
    exact ht (hγ ((ni p).trans (nj p).symm))
  have hu := (affine_hom_universal (stalk F.space.presheaf z) hP (F.sharp z)).1
    (F.space.restrict U.isOpenEmbedding) (restrict_sharp F U)
  have hij : (⟨i.hom, hi⟩ : {f : _ ⟶ _ // IsLocalMorphism f}) = ⟨j.hom, hj⟩ :=
    hu.1 hpull
  apply Iso.ext
  exact congrArg Subtype.val hij

private theorem chart_minimal_formulas (F : Fan.{u}) (z : F.space)
    (U : Opens F.space) (hz : z ∈ U)
    (hU : ∀ V : Opens F.space, z ∈ V → U ≤ V)
    (c : Chart F.space) (hc : z ∈ c.openSet) (r : ℕ) (a : Fin r → c.monoid)
    (ha : Submonoid.closure (Set.range a) = ⊤) :
    (∀ q : MonoidPrime c.monoid,
      (c.iso.inv.hom.base q).val ∈ U ↔
        q ∈ basicOpen (c.localizationElement ⟨z, hc⟩ a)) ∧
    ((basicOpen (c.localizationElement ⟨z, hc⟩ a) : Set (MonoidPrime c.monoid)) =
      {q | q.carrier ⊆ (c.iso.hom.hom.base ⟨z, hc⟩).carrier}) ∧
    Algebra.faceLocalization c.monoid
        (Submonoid.powers (c.localizationElement ⟨z, hc⟩ a)) =
      Algebra.faceLocalization c.monoid
        (Submonoid.closure {b | b ∉ (c.iso.hom.hom.base ⟨z, hc⟩).carrier}) := by
  classical
  have h := monoidPrime_minimal_neighborhood c.monoid c.fine r a ha
    (c.iso.hom.hom.base ⟨z, hc⟩) (c.localizationElement ⟨z, hc⟩ a) rfl
  have hmem := h.2.2.2.2.2.2.1
  have hmin := h.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, h.2.2.2.2.2.2.2.2.1⟩
  · intro q
    rw [mem_minimal_open_iff U z hz hU,
      mem_minimal_open_iff (X := TopCat.of (MonoidPrime c.monoid))
        (basicOpen (c.localizationElement ⟨z, hc⟩ a))
        (c.iso.hom.hom.base ⟨z, hc⟩) hmem hmin q]
    change (((chartHomeo c).symm q).val ⤳ z) ↔ q ⤳ chartHomeo c ⟨z, hc⟩
    constructor
    · intro hq
      have hs := (subtype_specializes_iff ((chartHomeo c).symm q) ⟨z, hc⟩).mpr hq
      simpa using hs.map (chartHomeo c).continuous
    · intro hq
      have hs := hq.map (chartHomeo c).symm.continuous
      have ht := (subtype_specializes_iff ((chartHomeo c).symm q) ⟨z, hc⟩).mp
        (by simpa using hs)
      exact ht
  · rw [h.2.2.2.2.2.1]
    ext q
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change (∀ b, b ∉ (c.iso.hom.hom.base ⟨z, hc⟩).carrier → b ∉ q.carrier) ↔
      q.carrier ⊆ (c.iso.hom.hom.base ⟨z, hc⟩).carrier
    constructor
    · intro hq b hb
      by_contra hn
      exact hq b hn hb
    · exact fun hq b hb hqb ↦ hb (hq hqb)

/-- The generalizations of a fan point form its smallest open neighborhood. Its actual
stalk is fine sharp, and its affine sharp spectrum is canonically this restricted fan.
The normalization is the composite of canonical-section pullback and the actual germ.
The chart formulas hold for every finite generating tuple, including the empty tuple.
The equivalence with the sharpened face localization is fixed on all numerators by
`Chart.sectionGerm`. The last equality is an equality of sheafed-space morphisms:
it identifies the inverse coordinate isomorphism followed by the open inclusion with
the localization-and-sharpening map in every chart, including all structure-sheaf maps.
Multiplicative notation renders additive zero as `1`, sums as products, and the quotient
by units as `Associates`; no saturation or torsion-freeness is assumed.

Source: ILO VIII 3.1.2--3.1.4, 3.1.8(ii), 3.1.10(ii), pp.98--100, and the canonical
stalk coordinates in the proof of 3.3.15, p.109
(blueprint: lem-trf-fine-fan-point-localization).

Proof:
1. Choose a fine affine chart about z. By lem-trf-monoid-prime-minimal-neighborhood,
invert the product of the generators outside its prime. The resulting basic open
consists exactly of the smaller primes and is the smallest neighborhood in the chart.
Every generalization lies in the chart, so this is intrinsically the set of
all generalizations of z and the smallest open neighborhood in the whole fan.
2. By lem-trf-affine-fan-localization-sections, sections on this open and the stalk
are both the localization at the prime modulo units. The germ map is the identity
under these canonical descriptions, hence is an isomorphism.
3. Localization is integral and generated by the given generators and the inverse
of their selected product. By lem-trf-integral-sharpening-group-exactness its quotient
by units is integral and finitely generated. That quotient is sharp: a representative
whose class has an inverse must itself be a unit. Thus the actual stalk is fine sharp.
4. Extension and contraction of primes identify the localized spectrum with the
basic open. Fractions have the same membership in an extended prime as their
numerators, since the denominators are units. Basic opens therefore correspond.
5. Every ideal is invariant under multiplication by units. Taking its image in the
unit quotient and taking inverse image are inverse operations on prime ideals,
again preserving basic opens. This gives the point map to the sharp stalk spectrum.
6. Localizing and then sharpening commutes with sharpening and then localizing:
send each numerator to its unit class. The inverse exists since inverted elements
map to units and units map to the identity. Both composites fix numerator classes,
and the maps commute with all further localizations.
7. Apply lem-trf-affine-fan-localization-sections on each basic open and use step 6
to obtain inverse restriction-compatible section maps. Extend them to inverse sheaf
maps by lem-weil-pbc-sheaf-morphism-on-basis. Their stalk maps are isomorphisms,
so both resulting morphisms are local. This yields the stated chart square as an
equality of full sheafed-space morphisms, not just of continuous maps.
8. The numerator formula gives the germ normalization. By
lem-trf-affine-fan-hom-universal, a local map into the fine sharp stalk spectrum is
uniquely determined by its canonical-section pullback. The germ isomorphism makes
this pullback the inverse germ map. Thus the isomorphism is unique, independent of
the chart and generating tuple, and all displayed coordinate identifications agree.
-/
theorem fineFan_point_localization (F : Fan.{u}) (z : F.space) :
    IsFine (stalk F.space.presheaf z) ∧ IsSharp (stalk F.space.presheaf z) ∧
    ∃ (U : Opens F.space) (hz : z ∈ U),
      (∀ x : F.space, x ∈ U ↔ x ⤳ z) ∧
      (∀ V : Opens F.space, z ∈ V → U ≤ V) ∧
      Function.Bijective (germ F.space.presheaf U z hz) ∧
      ∃! ι : F.space.restrict U.isOpenEmbedding ≅ affine (stalk F.space.presheaf z),
        IsLocalMorphism ι.hom ∧ IsLocalMorphism ι.inv ∧
        (∀ p : stalk F.space.presheaf z,
          germ F.space.presheaf U z hz
            (restrictedGlobalSections F.space U (affinePullback ι.hom p)) = p) ∧
        ∀ (c : Chart F.space) (hc : z ∈ c.openSet) (r : ℕ) (a : Fin r → c.monoid),
          Submonoid.closure (Set.range a) = ⊤ →
          (∀ q : MonoidPrime c.monoid,
            (c.iso.inv.hom.base q).val ∈ U ↔
              q ∈ basicOpen (c.localizationElement ⟨z, hc⟩ a)) ∧
          ((basicOpen (c.localizationElement ⟨z, hc⟩ a) : Set (MonoidPrime c.monoid)) =
            {q | q.carrier ⊆ (c.iso.hom.hom.base ⟨z, hc⟩).carrier}) ∧
          (Algebra.faceLocalization c.monoid
              (Submonoid.powers (c.localizationElement ⟨z, hc⟩ a)) =
            Algebra.faceLocalization c.monoid
              (Submonoid.closure {b | b ∉ (c.iso.hom.hom.base ⟨z, hc⟩).carrier})) ∧
          ∃ e : stalk F.space.presheaf z ≃*
              Associates (Algebra.faceLocalization c.monoid
                (Submonoid.closure {b | b ∉ (c.iso.hom.hom.base ⟨z, hc⟩).carrier})),
            (∀ b : c.monoid,
              ∃ q : Algebra.faceLocalization c.monoid
                  (Submonoid.closure {b | b ∉ (c.iso.hom.hom.base ⟨z, hc⟩).carrier}),
                q.val = Algebra.GrothendieckGroup.of b ∧
                e (c.sectionGerm z hc b) = Associates.mk q) ∧
            ∃ k : affine (stalk F.space.presheaf z) ⟶ affine c.monoid,
              IsAffineMap (c.sectionGerm z hc) k ∧
              k ≫ c.iso.inv ≫ F.space.ofRestrict c.openSet.isOpenEmbedding =
                ι.inv ≫ F.space.ofRestrict U.isOpenEmbedding := by
  obtain ⟨c₀, hc₀⟩ := F.locallyAffine z
  have hP := (fineFan_chart_stalk_coordinates F.space c₀ z hc₀).1
  obtain ⟨U, hz, hU⟩ := fan_minimal_open F z
  obtain ⟨ι, hι, hιinv, nι, _⟩ :=
    fineFan_chart_minimal_affine F.space F.sharp c₀ z hc₀ U hz hU hP
  refine ⟨hP, F.sharp z, U, hz, mem_minimal_open_iff U z hz hU, hU,
    germ_bijective_of_minimal F.space.presheaf U z hz hU, ι, ?_, ?_⟩
  · refine ⟨hι, hιinv, nι, ?_⟩
    intro c hc r a ha
    obtain ⟨hmem, hprimes, hloc⟩ := chart_minimal_formulas F z U hz hU c hc r a ha
    obtain ⟨e, he⟩ := (fineFan_chart_stalk_coordinates F.space c z hc).2
    obtain ⟨j, hj, hjinv, nj, k, hk, hsq⟩ :=
      fineFan_chart_minimal_affine F.space F.sharp c z hc U hz hU hP
    have hji := normalized_iso_unique F z U hz hU hP j ι hj hι nj nι
    refine ⟨hmem, hprimes, hloc, e, he, k, hk, ?_⟩
    simpa only [hji] using hsq
  · intro j hj
    exact normalized_iso_unique F z U hz hU hP j ι hj.1 hι hj.2.2.1 nι

end AlgebraicGeometry.FineFan
