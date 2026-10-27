module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection

/-! # Trivializing an invertible module upstairs over a finite morphism

Source: Stacks Project, Tag 0BUT, `divisors-lemma-finite-trivialize-invertible-upstairs`
in `literature/stacks-project/divisors.tex`.
(blueprint: lem-sfb-finite-trivialize-invertible-upstairs)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on the source of a finite morphism is trivial over the inverse image
of some open neighbourhood of any prescribed point of the target.

Source: Stacks Project, Tag 0BUT, `divisors-lemma-finite-trivialize-invertible-upstairs`.

Proof:
1. Choose an affine open neighbourhood U of z. Its inverse image X is affine because p is
   finite. The restricted morphism q : X → U is finite, and the restriction L of M is
   invertible by restriction of its local rank-one trivializations.
2. By `lem-weil-pbc-finite-closed-map-finite-fibres`, the fibre E over z is finite. Apply
   `lem-sfb-affine-invertible-finite-set-section` to X, L and E to find a global section s
   nonvanishing at every point of E. This includes E empty and nonclosed fibre points.
3. By `lem-weil-pbc-nonvanishing-section-trivializes`, the nonvanishing locus W of s is open,
   contains E, and carries the multiplication-by-s trivialization of L. Let C = X \ W.
4. A finite morphism is closed by `lem-weil-pbc-finite-closed-map-finite-fibres`. Thus
   V = U \ q(C) is open. Since E is contained in W, z is in V. Every point of q⁻¹(V) lies
   in W, since otherwise its image would belong to q(C).
5. Restrict the trivialization on W and its inverse to q⁻¹(V). Since U is open in the
   original target, V is an open neighbourhood there, and q⁻¹(V) is p⁻¹(V). This is the
   required isomorphism of modules on that open subscheme.

(blueprint: lem-sfb-finite-trivialize-invertible-upstairs) -/
theorem exists_trivialization_over_preimage_of_isFinite
    {Y Z : AlgebraicGeometry.Scheme.{u}} (p : Y ⟶ Z) [AlgebraicGeometry.IsFinite p]
    (M : Y.Modules) [M.IsInvertible] (z : Z) :
    ∃ V : Z.Opens, z ∈ V ∧
      Nonempty (M.restrict (p ⁻¹ᵁ V).ι ≅
        SheafOfModules.unit (p ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  classical
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z)
    (U := ⊤) (x := z) trivial
  let X := (p ⁻¹ᵁ U).toScheme
  let i : X ⟶ Y := (p ⁻¹ᵁ U).ι
  have : IsAffine X := hU.preimage p
  let L := M.restrict i
  have : L.IsInvertible :=
    IsInvertible.of_iso ((restrictFunctorIsoPullback i).app M).symm
  let E : Set X := i ⁻¹' (p ⁻¹' {z})
  have hE : E.Finite := (p.finite_preimage_singleton z).preimage
    i.isOpenEmbedding.injective.injOn
  obtain ⟨s, hs⟩ := exists_section_nonvanishing_on_finite_set X L E hE
  obtain ⟨W, hW, -, hcoeff⟩ := nonvanishing_section_trivializes X L s
  have hgen : IsFreeGenerator (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) := by
    intro A hA
    constructor
    · intro a b hab
      obtain ⟨c, hc, huniq⟩ := hcoeff A hA
        (a • L.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op s)
      have ha := huniq a rfl
      have hb := huniq b (by simpa [presheaf_map_map_apply] using hab)
      exact ha.trans hb.symm
    · intro t
      obtain ⟨a, ha, -⟩ := hcoeff A hA t
      exact ⟨a, by simpa [presheaf_map_map_apply] using ha.symm⟩
  let e : L.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
    ((overFunctorEquiv W).app L).symm ≪≫
      (overEquiv W).functor.mapIso hgen.overIso ≪≫ (overEquivFunctorObjUnitIso W).symm
  let O : Y.Opens := i ''ᵁ W
  have hfibre : p ⁻¹' {z} ⊆ (O : Set Y) := by
    intro y hy
    have hyU : y ∈ p ⁻¹ᵁ U := by
      change p y ∈ U
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
      simpa only [hy] using hzU
    let x : X := ⟨y, hyU⟩
    have hxW : x ∈ W := by
      rw [← SetLike.mem_coe, hW]
      exact hs x hy
    exact ⟨x, hxW, rfl⟩
  let V : Z.Opens := ⟨(p '' (O : Set Y)ᶜ)ᶜ,
    (p.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩
  have hzV : z ∈ V := by
    rintro ⟨y, hyO, hyz⟩
    exact hyO (hfibre (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hyz))
  have hpre : (p ⁻¹ᵁ V : Set Y) ⊆ O := by
    intro y hy
    by_contra hyO
    exact hy ⟨y, hyO, rfl⟩
  let j : W.toScheme ⟶ Y := W.ι ≫ i
  have hrange : Set.range (p ⁻¹ᵁ V).ι ⊆ Set.range j := by
    rintro y ⟨x, rfl⟩
    obtain ⟨w, hw, heq⟩ := hpre x.property
    exact ⟨⟨w, hw⟩, heq⟩
  let k := IsOpenImmersion.lift j (p ⁻¹ᵁ V).ι hrange
  let e' : (pullback j).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
    ((pullbackComp W.ι i).app M).symm ≪≫
      (pullback W.ι).mapIso ((restrictFunctorIsoPullback i).app M).symm ≪≫
      ((restrictFunctorIsoPullback W.ι).app L).symm ≪≫ e
  refine ⟨V, hzV, ⟨(restrictFunctorIsoPullback (p ⁻¹ᵁ V).ι).app M ≪≫ ?_⟩⟩
  exact (pullbackCongr (IsOpenImmersion.lift_fac j (p ⁻¹ᵁ V).ι hrange).symm).app M ≪≫
    ((pullbackComp k j).app M).symm ≪≫ (pullback k).mapIso e' ≪≫ pullbackObjUnitIso k

end AlgebraicGeometry.Scheme.Modules
