/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Defs.Filter

import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine-base quasi-compact lifts of fibre opens

Source: Stacks Project, Tag 055W, proof of
`lemma-fibre-geometrically-connected-reduced`, first paragraph.
(blueprint: lem-trf-fibre-open-affine-reduction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

set_option autoImplicit false

private theorem exists_compact_open_between {X : Scheme.{u}} {K : Set X}
    (hK : IsCompact K) (O : X.Opens) (hKO : K ⊆ O) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ K ⊆ U ∧ U ≤ O := by
  classical
  choose U hUa hxU hUO using
    fun x : K ↦ exists_isAffineOpen_mem_and_subset (hKO x.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  refine ⟨⨆ x ∈ s, U x, ?_, ?_, ?_⟩
  · simpa only [Opens.coe_iSup, Finset.mem_coe] using
      s.finite_toSet.isCompact_biUnion (fun x _ ↦ (hUa x).isCompact)
  · simpa only [Opens.coe_iSup] using hs
  · exact iSup₂_le fun x _ ↦ hUO x

private theorem geometricallyReduced_comp_open {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [GeometricallyReduced g] :
    GeometricallyReduced (f ≫ g) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have : IsReduced (pullback g y) :=
    pullback_of_geometrically (GeometricallyReduced.geometrically_isReduced (f := g)) K y
  let l : pullback (f ≫ g) y ⟶ pullback g y :=
    pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _)
      (by simp [pullback.condition])
  have hl : IsPullback (pullback.fst (f ≫ g) y) l f (pullback.fst g y) :=
    IsPullback.of_bot (by simpa [l] using IsPullback.of_hasPullback (f ≫ g) y)
      (by simp [l]) (IsPullback.of_hasPullback g y)
  have : IsOpenImmersion l := MorphismProperty.of_isPullback hl inferInstance
  exact isReduced_of_isOpenImmersion l

/-- Any open of a fibre of a flat finitely presented family with geometrically reduced fibres
extends to a quasi-compact open after restricting to an affine neighbourhood of the base point.
The restricted family remains flat and finitely presented, with geometrically reduced fibres.

The last equality is an equality in the lattice of opens of `h.fiber s`. The map
`W.ι ≫ pullback.fst h S₀.ι` is the canonical open immersion from `W` into `Y`.
Pulling back its open image along `h.fiberι s` is the open subscheme `W_s`, under the
canonical identification of the localized fibre with `h.fiber s`. Thus this equality fixes
the open subscheme and its inclusion, rather than merely giving an abstract isomorphism.

Proof:
1. Choose an affine open neighbourhood `S₀` of `s`, using
   `lem-weil-pbc-affine-opens-basis`. Put `X = Y ×[S] S₀`. Flatness and finite presentation
   persist by `lem-weil-pbc-flat-morphism-base-change` and
   `lem-weil-pbc-qcqs-morphism-permanence`. Affineness makes `S₀` qcqs by
   `lem-weil-pbc-affine-scheme-qcqs`, so `X` is qcqs by the same permanence lemma.
   Open restriction preserves residue fields, so the fibres of `X → S₀` identify with
   those of `h`; in particular they are geometrically reduced.
2. The fibre `F = h.fiber s` is quasi-compact and locally of finite type over its residue
   field, by `lem-weil-pbc-qcqs-morphism-permanence` and the definition of finite
   presentation. A field is Noetherian, so `pqf-lem-locnoeth-lft` makes `F` locally
   Noetherian. By `lem-sfb-noetherian-open-immersion-qc`, the open immersion `T → F` is
   quasi-compact, and hence `T` is quasi-compact.
3. The fibre projection identifies `F` with its image as a topological subspace, by
   `def-pc-scheme-fibre`. Lift `T` to an open `O` of `X`. Use the affine-open basis to
   cover `T` by inverse images of affine opens contained in `O`. Choose a finite subcover
   by quasi-compactness. Their union `W` is quasi-compact by
   `lem-weil-pbc-affine-scheme-qcqs` and has inverse image exactly `T`.
   `lem-weil-pbc-open-fibre-product` identifies this inverse image with the open
   subscheme `W_s`. For empty `T`, take the empty union.
4. Open restriction preserves local rings, so `W → S₀` is flat. At each point choose
   affine neighbourhoods in `W` and `S₀`; these are also affine neighbourhoods in `X`.
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` shows that their section-ring
   maps are finitely presented. Thus the restricted map is locally of finite presentation.
5. Intersections of the finitely many affine opens defining `W` are quasi-compact since
   `X` is quasi-separated. Both directions of
   `lem-weil-pbc-quasi-separated-affine-cover-criterion` make `W` quasi-separated.
   `lem-weil-pbc-qcqs-morphism-permanence` now makes `W → S₀` quasi-compact and
   quasi-separated. Together with step 4, this gives finite presentation.
6. After any residue-field extension, each fibre of `W → S₀` is an open subscheme
   of the corresponding reduced base change of a fibre of `X → S₀`, by
   `lem-weil-pbc-open-fibre-product`. Its local rings are therefore reduced by
   `def-pc-reduced-scheme`. By `def-pc-geometrically-irreducible`, this is geometric
   reducedness, including for empty fibres.

Source: Stacks Project, Tag 055W, first paragraph of the proof of
`lemma-fibre-geometrically-connected-reduced`; the finite-subcover and restriction
details use Tags 01K1, 01T6, 01OX, 01TQ, 01KO and 03GI.
(blueprint: lem-trf-fibre-open-affine-reduction) -/
theorem exists_affine_neighbourhood_quasiCompact_open_of_fiber_open
    {Y S : Scheme.{u}} (h : Y ⟶ S) [Flat h] [LocallyOfFinitePresentation h]
    [QuasiCompact h] [QuasiSeparated h]
    (hred : ∀ t : S, GeometricallyReduced (h.fiberToSpecResidueField t))
    (s : S) (T : (h.fiber s).Opens) :
    ∃ S₀ : S.Opens, s ∈ S₀ ∧ IsAffineOpen S₀ ∧
      ∃ W : (pullback h S₀.ι).Opens,
        CompactSpace W ∧
        Flat (W.ι ≫ pullback.snd h S₀.ι) ∧
        LocallyOfFinitePresentation (W.ι ≫ pullback.snd h S₀.ι) ∧
        QuasiCompact (W.ι ≫ pullback.snd h S₀.ι) ∧
        QuasiSeparated (W.ι ≫ pullback.snd h S₀.ι) ∧
        (∀ t : S₀, GeometricallyReduced
          ((W.ι ≫ pullback.snd h S₀.ι).fiberToSpecResidueField t)) ∧
        (h.fiberι s) ⁻¹ᵁ (W.ι ≫ pullback.fst h S₀.ι).opensRange = T := by
  classical
  obtain ⟨S₀, hS₀, hsS₀, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) trivial
  have : IsAffine S₀ := hS₀
  have : LocallyOfFiniteType (h.fiberToSpecResidueField s) := by
    delta Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : IsLocallyNoetherian (h.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (h.fiberToSpecResidueField s)
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace T.ι
  have hT : IsCompact (T : Set (h.fiber s)) := by
    simpa only [Scheme.Opens.range_ι] using isCompact_range T.ι.continuous
  obtain ⟨O, hO, hOT⟩ := (h.fiberι s).isEmbedding.isInducing.isOpen_iff.mp T.isOpen
  let V : Y.Opens := ⟨O, hO⟩ ⊓ h ⁻¹ᵁ S₀
  have hTV : (h.fiberι s) '' (T : Set (h.fiber s)) ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp hOT x).mpr hx
    · have hx' : h (h.fiberι s x) = s := by
        have := (h.range_fiberι s).subset ⟨x, rfl⟩
        exact this
      change h (h.fiberι s x) ∈ S₀
      rwa [hx']
  obtain ⟨U, hUc, hTU, hUV⟩ := exists_compact_open_between
    (hT.image (h.fiberι s).continuous) V hTV
  have hUS₀ : U ≤ h ⁻¹ᵁ S₀ := hUV.trans inf_le_right
  have hUT : (h.fiberι s) ⁻¹ᵁ U = T := by
    apply Opens.ext
    apply Set.Subset.antisymm
    · intro x hx
      exact (Set.ext_iff.mp hOT x).mp (hUV hx).1
    · intro x hx
      exact hTU ⟨x, hx, rfl⟩
  let W : (pullback h S₀.ι).Opens := pullback.fst h S₀.ι ⁻¹ᵁ U
  have hUr : (U : Set Y) ⊆ Set.range (pullback.fst h S₀.ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hUS₀
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    ((pullback.fst h S₀.ι).isOpenEmbedding.isInducing.isCompact_preimage' hUc hUr)
  have : QuasiSeparatedSpace (pullback h S₀.ι : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd h S₀.ι)
  have : GeometricallyReduced h := by
    rw [geometricallyReduced_iff, geometrically_iff_forall_fiberToSpecResidueField]
    exact fun t ↦ (geometricallyReduced_iff _).mp (hred t)
  have : GeometricallyReduced (W.ι ≫ pullback.snd h S₀.ι) :=
    geometricallyReduced_comp_open _ _
  refine ⟨S₀, hsS₀, hS₀, W, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, (fun t ↦ inferInstance), ?_⟩
  have hWU : (W.ι ≫ pullback.fst h S₀.ι).opensRange = U := by
    apply Opens.ext
    change Set.range (W.ι ≫ pullback.fst h S₀.ι) = (U : Set Y)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset hUr
  rwa [hWU]

end AlgebraicGeometry
