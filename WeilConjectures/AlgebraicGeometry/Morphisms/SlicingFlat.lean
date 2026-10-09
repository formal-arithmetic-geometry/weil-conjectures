/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Slicing a flat morphism with geometrically reduced fibres

A flat morphism `f : X ⟶ S`, locally of finite presentation, with geometrically reduced fibres
becomes, after an étale covering of `X`, a flat morphism of finite presentation with
geometrically connected and geometrically reduced fibres over a scheme étale over `S`
(Stacks `0EY5`).

The proof follows the smooth case `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`.
Let `x : X` lie over `s : S`. The smooth locus of `f` is dense in the fibre over `s`, so the
connected component of `x` in that fibre contains a point `x'` at which `f` is smooth and whose
residue field is finite separable over `κ(s)`. Through `x'` passes an étale slice `ι : Z ⟶ X`,
and the base change `X ×_S Z ⟶ Z` acquires the section `(ι, 𝟙)`. The relative connected
component of this section is, near the fibre through `x'`, a quasi-compact open with connected
fibres (Stacks `057I`), and it contains a point over `x`.

## Main statements

- `AlgebraicGeometry.GeometricallyConnected.of_isPreconnected_preimage_singleton`: a morphism
  with a section and topologically connected fibres has geometrically connected fibres.
- `AlgebraicGeometry.GeometricallyReduced.dense_smoothLocus`: over a field, the smooth locus of
  a scheme locally of finite presentation and geometrically reduced is dense.
- `AlgebraicGeometry.exists_mem_smoothLocus_of_geometricallyReduced`: smooth points are dense in
  the fibres of a flat morphism, locally of finite presentation, with geometrically reduced
  fibres.
- `AlgebraicGeometry.isOpen_setOf_mem_connectedComponentIn_preimage_singleton`: the relative
  connected component of a section of a flat morphism of finite presentation with geometrically
  reduced fibres is open (Stacks `055R`).
- `AlgebraicGeometry.isLocallyConstructible_setOf_mem_connectedComponentIn_preimage_singleton`:
  the relative connected component of a section of a morphism of finite presentation is locally
  constructible (Stacks `055P`).
- `AlgebraicGeometry.exists_etaleCover_factorization`: the slicing.

## References

- Stacks Project, Tag `0EY5`, <https://stacks.math.columbia.edu/tag/0EY5>
- Stacks Project, Tags `055W`, `057I`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A morphism `q : U ⟶ V`, locally of finite type, with a section and with topologically
connected fibres, has geometrically connected fibres: each fibre is a connected scheme over the
residue field with a rational point, hence geometrically connected (Stacks `04KV`). -/
theorem GeometricallyConnected.of_isPreconnected_preimage_singleton {U V : Scheme.{u}}
    (q : U ⟶ V) [LocallyOfFiniteType q] (s : V ⟶ U) (hs : s ≫ q = 𝟙 V)
    (h : ∀ v : V, _root_.IsPreconnected (q ⁻¹' {v})) : GeometricallyConnected q := by
  rw [geometricallyConnected_iff, geometrically_iff_forall_fiberToSpecResidueField]
  intro v
  have hv : s v ∈ q ⁻¹' {v} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, hs]
    rfl
  have : Nonempty (q ⁻¹' {v}) := ⟨⟨s v, hv⟩⟩
  have : PreconnectedSpace (q ⁻¹' {v}) := isPreconnected_iff_preconnectedSpace.mp (h v)
  have : ConnectedSpace (q ⁻¹' {v}) := ⟨inferInstance⟩
  have : ConnectedSpace (q.fiber v) := (q.fiberHomeo v).connectedSpace_iff.mpr inferInstance
  let s' : Spec (V.residueField v) ⟶ q.fiber v :=
    pullback.lift (V.fromSpecResidueField v ≫ s) (𝟙 _) (by simp [hs])
  exact (GeometricallyConnected.of_connectedSpace_of_section (q.fiberToSpecResidueField v) s'
    (pullback.lift_snd _ _ _)).geometrically_connectedSpace

/-- Over a field `K`, the smooth locus of a morphism `f : X ⟶ Spec K`, locally of finite
presentation, with geometrically reduced fibres is dense, given a perfect purely inseparable
extension `L / K`. The base change `X_L` is reduced, so its smooth locus over the perfect field
`L` is dense (`AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField`). As `X_L ⟶ X`
is a homeomorphism, the image of this smooth locus is a dense open of `X` whose base change to
`L` is smooth, hence it is smooth over `K` by flat descent. -/
theorem GeometricallyReduced.dense_smoothLocus_of_isPurelyInseparable {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [PerfectField L] [IsPurelyInseparable K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    [GeometricallyReduced f] : Dense (f.smoothLocus : Set X) := by
  let g : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : IsReduced (pullback f g) :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced L g
  have hW := (pullback.snd f g).dense_smoothLocus_of_perfectField
  have hh : IsHomeomorph (pullback.fst f g) := (pullback.fst f g).isHomeomorph
  let O : X.Opens := ⟨pullback.fst f g '' (pullback.snd f g).smoothLocus,
    hh.isOpenMap _ (pullback.snd f g).smoothLocus.2⟩
  have hO : Smooth (O.ι ≫ f) := by
    refine MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
      ⟨⟨?_, inferInstance⟩, inferInstance⟩ ?_
    · exact ⟨fun _ ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
    · rw [← pullbackRightPullbackFstIso_inv_snd_snd]
      suffices Smooth (pullback.snd O.ι (pullback.fst f g) ≫ pullback.snd f g) from inferInstance
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
      rintro z -
      obtain ⟨w, hw, hwz⟩ := (pullback.fst O.ι (pullback.fst f g) z).2
      have hzw : pullback.fst f g (pullback.snd O.ι (pullback.fst f g) z) =
          pullback.fst f g w := by
        rw [hwz, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
        rfl
      rwa [Scheme.Hom.mem_preimage, hh.injective hzw]
  refine (hh.surjective.denseRange.dense_image hh.continuous hW).mono fun x hx ↦ ?_
  have := (Scheme.Hom.smoothLocus_eq_top_iff.mpr hO).ge (Set.mem_univ ⟨x, hx⟩)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

/-- **Smooth points are dense over a field**: the smooth locus of a morphism `X ⟶ Spec K`,
locally of finite presentation, with geometrically reduced fibres is dense. We apply
`AlgebraicGeometry.GeometricallyReduced.dense_smoothLocus_of_isPurelyInseparable` to the perfect
closure of `K` in an algebraic closure. -/
theorem GeometricallyReduced.dense_smoothLocus {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    Dense (f.smoothLocus : Set X) :=
  dense_smoothLocus_of_isPurelyInseparable (perfectClosure K (AlgebraicClosure K)) f

/-- **Smooth points are dense in the fibres** of a flat morphism, locally of finite
presentation, with geometrically reduced fibres: every open `U` of `X` meeting the fibre
through `x` contains a point of that fibre at which `f` is smooth. -/
theorem exists_mem_smoothLocus_of_geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] (U : X.Opens) {x : X}
    (hx : x ∈ U) : ∃ x' ∈ U, f x' = f x ∧ x' ∈ f.smoothLocus := by
  obtain ⟨w, hwU, hw⟩ := (GeometricallyReduced.dense_smoothLocus (K := S.residueField (f x))
    (f.fiberToSpecResidueField (f x))).inter_open_nonempty (f.fiberι (f x) ⁻¹ᵁ U)
    (f.fiberι (f x) ⁻¹ᵁ U).2 ⟨f.asFiber x, by simpa using hx⟩
  exact ⟨f.fiberι _ w, hwU, (f.range_fiberι _).subset ⟨w, rfl⟩,
    f.fiberι_mem_smoothLocus hw⟩

/-- **The relative connected component of a section is open** (Stacks `055R`). Let `f : X ⟶ Y`
be flat, of finite presentation, with geometrically reduced fibres, and let `σ` be a section of
`f`. The points `x` lying in the connected component of `σ (f x)` in their fibre form an open
subset of `X`. -/
@[stacks 055R]
theorem isOpen_setOf_mem_connectedComponentIn_preimage_singleton {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [GeometricallyReduced f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (σ (f x))} :=
  sorry

/-- **The relative connected component of a section is locally constructible** (Stacks `055P`).
Let `f : X ⟶ Y` be of finite presentation with a section `σ`. The points `x` lying in the
connected component of `σ (f x)` in their fibre form a locally constructible subset of `X`. -/
@[stacks 055P]
theorem isLocallyConstructible_setOf_mem_connectedComponentIn_preimage_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    Topology.IsLocallyConstructible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (σ (f x))} :=
  sorry

/-- The slicing of `f` near a point, for `X` and `S` affine; see
`AlgebraicGeometry.exists_etaleCover_factorization`. -/
private theorem exists_etale_factorization_of_mem_aux {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] [IsAffine X] [IsAffine S] (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (V : Scheme.{u}) (q : U ⟶ V) (r : V ⟶ S),
      Etale p ∧ x ∈ Set.range p ∧ Etale r ∧ Flat q ∧ LocallyOfFinitePresentation q ∧
      QuasiCompact q ∧ QuasiSeparated q ∧ GeometricallyConnected q ∧ GeometricallyReduced q ∧
      q ≫ r = p ≫ f := by
  -- a smooth point `x'` with finite separable residue field in the connected component of `x`
  obtain ⟨W, hxW, hW⟩ := f.exists_opens_inter_preimage_subset_connectedComponentIn x
  obtain ⟨x₁, hx₁W, hfx₁, hx₁⟩ := exists_mem_smoothLocus_of_geometricallyReduced f W hxW
  let L := f.smoothLocus
  have : Smooth (L.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext y
    simp [L]
  obtain ⟨x₂, hx₂W, hfx₂, hx₂⟩ := Smooth.exists_mem_etale_residueFieldMap (L.ι ≫ f) (L.ι ⁻¹ᵁ W)
    (x := ⟨x₁, hx₁⟩) hx₁W
  set x' := L.ι x₂
  have hfx' : f x' = f x := by
    rw [← hfx₁, ← Scheme.Hom.comp_apply, hfx₂]
    rfl
  have hxx' : x ∈ connectedComponentIn (f ⁻¹' {f x}) x' := by
    rw [← connectedComponentIn_eq (hW ⟨hx₂W, hfx'⟩)]
    exact mem_connectedComponentIn rfl
  -- an étale slice `ι : Z ⟶ X` through `x'`, and the section `σ` of `X ×_S Z ⟶ Z`
  obtain ⟨Z, ι₀, z, hZ, hιf, hι₀z⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap _ hx₂
  set ι := ι₀ ≫ L.ι
  have hιz : ι z = x' := by simp [ι, hι₀z, x']
  have : Etale (ι ≫ f) := by simpa [ι] using hιf
  let σ : Z ⟶ pullback f (ι ≫ f) := pullback.lift ι (𝟙 Z) (by rw [Category.id_comp])
  have hσ : σ ≫ pullback.snd f (ι ≫ f) = 𝟙 Z := pullback.lift_snd _ _ _
  rw [← hfx', ← hιz] at hxx'
  have hσz : pullback.snd f (ι ≫ f) (σ z) = z := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  have hσx : pullback.fst f (ι ≫ f) (σ z) = ι z := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨p₀, hp₀, hp₀x⟩ := connectedComponentIn_subset_image_pullback_fst f (ι ≫ f) (σ z) hσz
    (by rwa [hσx, Scheme.Hom.comp_apply])
  have hp₀z : pullback.snd f (ι ≫ f) p₀ = z :=
    connectedComponentIn_subset (pullback.snd f (ι ≫ f) ⁻¹' {z}) _ hp₀
  -- the relative connected component `W` of `σ`, an open with connected fibres over `Z`
  set g := pullback.snd f (ι ≫ f)
  have : IsAffine Z := hZ
  let W : (pullback f (ι ≫ f)).Opens :=
    ⟨{p | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))},
      isOpen_setOf_mem_connectedComponentIn_preimage_singleton g σ hσ⟩
  have hgσ (n : Z) : g (σ n) = n := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  have hW (n : Z) : (W : Set _) ∩ g ⁻¹' {n} = connectedComponentIn (g ⁻¹' {n}) (σ n) := by
    ext p
    refine ⟨fun ⟨hp, hpn⟩ ↦ ?_, fun hp ↦ ?_⟩
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hpn
      subst hpn
      exact hp
    · have hpn : g p = n := connectedComponentIn_subset (g ⁻¹' {n}) _ hp
      subst hpn
      exact ⟨hp, rfl⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    (isLocallyConstructible_setOf_mem_connectedComponentIn_preimage_singleton g σ hσ
      ).isConstructible.isCompact
  have hσW : Set.range σ ⊆ Set.range W.ι := by
    rintro _ ⟨n, rfl⟩
    refine ⟨⟨σ n, ?_⟩, rfl⟩
    change σ n ∈ connectedComponentIn (g ⁻¹' {g (σ n)}) (σ (g (σ n)))
    rw [hgσ]
    exact mem_connectedComponentIn (by simp [hgσ])
  have hp₀W : p₀ ∈ W := by
    change p₀ ∈ connectedComponentIn (g ⁻¹' {g p₀}) (σ (g p₀))
    rwa [hp₀z]
  have : GeometricallyReduced g :=
    MorphismProperty.of_isPullback (P := @GeometricallyReduced) (.of_hasPullback _ _) ‹_›
  have : GeometricallyReduced (W.ι ≫ g) := GeometricallyReduced.comp_of_etale _ _
  refine ⟨W, W.ι ≫ pullback.fst f (ι ≫ f), Z, W.ι ≫ g, ι ≫ f, inferInstance,
    ⟨⟨p₀, hp₀W⟩, hp₀x⟩, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ‹_›, ?_⟩
  · refine GeometricallyConnected.of_isPreconnected_preimage_singleton _
      (IsOpenImmersion.lift W.ι σ hσW) (by rw [IsOpenImmersion.lift_fac_assoc, hσ]) fun n ↦ ?_
    rw [← W.ι.isOpenEmbedding.isInducing.isPreconnected_image]
    convert (isPreconnected_connectedComponentIn (F := g ⁻¹' {n}) (x := σ n)) using 1
    rw [← hW]
    ext p
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hpW, hpn⟩
      exact ⟨⟨p, hpW⟩, hpn, rfl⟩
  · simp only [Category.assoc]
    exact (W.ι ≫= pullback.condition).symm

/-- **Slicing at a point.** Let `f : X ⟶ S` be flat, locally of finite presentation, with
geometrically reduced fibres, and let `x : X`. There are an étale `p : U ⟶ X` with `x` in its
image and a factorisation `p ≫ f = q ≫ r` with `r : V ⟶ S` étale and `q : U ⟶ V` flat of finite
presentation with geometrically connected and geometrically reduced fibres. -/
theorem exists_etale_factorization_of_mem {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (V : Scheme.{u}) (q : U ⟶ V) (r : V ⟶ S),
      Etale p ∧ x ∈ Set.range p ∧ Etale r ∧ Flat q ∧ LocallyOfFinitePresentation q ∧
      QuasiCompact q ∧ QuasiSeparated q ∧ GeometricallyConnected q ∧ GeometricallyReduced q ∧
      q ≫ r = p ≫ f := by
  obtain ⟨S', hS', hxS', -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) trivial
  obtain ⟨X', hX', hxX', hX'S'⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ S') (x := x) hxS'
  replace hX'S' : X' ≤ f ⁻¹ᵁ S' := hX'S'
  have : IsAffine S' := hS'
  have : IsAffine X' := hX'
  have : GeometricallyReduced (f ∣_ S') := MorphismProperty.of_isPullback
    (P := @GeometricallyReduced) (isPullback_morphismRestrict f S').flip ‹_›
  have : GeometricallyReduced (f.resLE S' X' hX'S') :=
    GeometricallyReduced.comp_of_etale (X.homOfLE hX'S') (f ∣_ S')
  obtain ⟨U, p, V, q, r, hp, ⟨u, hu⟩, hr, hq, hq', hqc, hqs, hqg, hqr, hqf⟩ :=
    exists_etale_factorization_of_mem_aux (f.resLE S' X' hX'S') ⟨x, hxX'⟩
  refine ⟨U, p ≫ X'.ι, V, q, r ≫ S'.ι, inferInstance, ⟨u, by simp [hu]⟩, inferInstance, hq, hq',
    hqc, hqs, hqg, hqr, ?_⟩
  rw [← Category.assoc, hqf, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- **Slicing a flat morphism with geometrically reduced fibres.** Let `f : X ⟶ S` be flat,
locally of finite presentation and with geometrically reduced fibres. Then there is an étale
covering `p i : U i ⟶ X` of `X`, that is, a family of étale morphisms whose images cover `X`,
such that each composite `p i ≫ f` factors as `q i ≫ r i` with `r i : V i ⟶ S` étale and
`q i : U i ⟶ V i` flat of finite presentation (locally of finite presentation, quasi-compact and
quasi-separated), with geometrically connected and geometrically reduced fibres:

```
U i --q i--> V i
 |            |
p i          r i
 v            v
 X ----f----> S
```

For a smooth morphism the first leg can moreover be taken to be a smooth morphism of affine
schemes admitting a section; that is Stacks `0EY4`,
`AlgebraicGeometry.Smooth.exists_etaleCover_factorization`. -/
@[stacks 0EY5]
theorem exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Flat (q i)) ∧ (∀ i, LocallyOfFinitePresentation (q i)) ∧
      (∀ i, QuasiCompact (q i)) ∧ (∀ i, QuasiSeparated (q i)) ∧
      (∀ i, GeometricallyConnected (q i)) ∧ (∀ i, GeometricallyReduced (q i)) ∧
      (∀ i, q i ≫ r i = p i ≫ f) := by
  choose U p V q r hp hx hr hq hq' hqc hqs hqg hqr hqf using exists_etale_factorization_of_mem f
  exact ⟨X, U, p, V, q, r, hp, fun x ↦ ⟨x, hx x⟩, hr, hq, hq', hqc, hqs, hqg, hqr, hqf⟩

end AlgebraicGeometry
