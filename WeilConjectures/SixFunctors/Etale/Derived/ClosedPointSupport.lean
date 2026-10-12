/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleIsGE
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Complexes supported on closed points

A morphism of bounded constructible complexes on a scheme of finite type over an algebraically
closed field which is an isomorphism on the geometric stalks at the nonclosed points and after
`Ra_*` is an isomorphism.

The cone `Δ` of such a morphism has vanishing derived direct image `Ra_* Δ` and homology sheaves
supported on finitely many closed points. If `Δ` were nonzero, its lowest nonzero homology sheaf
`G = Hⁿ(Δ)` would receive a nonzero morphism from `a^* a_* G` (`G` being a finite sum of
skyscraper sheaves at points with separably closed residue fields), hence `Δ` would receive a
nonzero morphism from `a^*(a_* G)[-n]`, which is impossible as `a^* ⊣ Ra_*` and `Ra_* Δ = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Topology ZeroObject TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- In a noetherian scheme, a subset which is closed in the constructible topology and consists
of closed points is finite: it is compact in the constructible topology, in which every closed
point is open (its complement being quasi-compact). -/
lemma Scheme.finite_of_isClosed_constructibleTopology {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [NoetherianSpace X] {Z : Set X}
    (hZ : IsClosed[constructibleTopology X] Z)
    (hcl : ∀ z ∈ Z, IsClosed ({z} : Set X)) : Z.Finite := by
  let Z' : Set (WithConstructibleTopology X) := WithTopology.ofTopology ⁻¹' Z
  have hc : IsCompact Z' := (WithConstructibleTopology.isClosed_iff (s := Z').2 hZ).isCompact
  have ho (w : Z') : IsOpen ({w.1} : Set (WithConstructibleTopology X)) := by
    rw [WithConstructibleTopology.isOpen_iff, WithTopology.preimage_toTopology,
      Set.image_singleton]
    exact (NoetherianSpace.isCompact _).isOpen_constructibleTopology_of_isClosed (hcl _ w.2)
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun w : Z' ↦ {w.1}) ho
    (fun w hw ↦ Set.mem_iUnion.2 ⟨⟨w, hw⟩, rfl⟩)
  have hZ' : Z'.Finite := (t.finite_toSet.image Subtype.val).subset fun w hw ↦ by
    obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 (ht hw)
    exact ⟨i, hi, hwi.symm⟩
  rw [← Set.image_preimage_eq Z (WithTopology.ofTopology_surjective (constructibleTopology X))]
  exact hZ'.image _

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- An étale sheaf on `X` all of whose geometric stalks vanish is zero. -/
lemma isZero_of_isZero_sheafFiber {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ x : X, IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj F)) : IsZero F := by
  have : IsIso (0 : F ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
    have : PreservesFiniteLimits ((X.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)) := inferInstance
    have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact ⟨⟨0, (h x).eq_of_src _ _, (Functor.map_isZero _ (isZero_zero _)).eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

/-- Over separably closed fields, the pushforward along a morphism `g : Spec K ⟶ Spec k`
reflects zero objects: the pullback `g^*` is an equivalence, both constant sheaf functors being
equivalences. -/
lemma isZero_of_isZero_lowerStar_of_isSepClosed {k K : Type u} [Field k] [IsSepClosed k]
    [Field K] [IsSepClosed K] (g : Spec (.of K) ⟶ Spec (.of k))
    (H : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : IsZero ((g)_*[ModuleCat.{u + 1} Λ].obj H)) : IsZero H := by
  let cs := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let e : (g)^*[ModuleCat.{u + 1} Λ] ≅
      cs.inv ⋙ constantSheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight cs.asEquivalence.counitIso.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (constantSheafCompUpperStarIso Λ g)
  have : (g)^*[ModuleCat.{u + 1} Λ].IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let e' := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).rightAdjointUniq
    (g)^*[ModuleCat.{u + 1} Λ].asEquivalence.toAdjunction
  exact (Functor.map_isZero (g)^*[ModuleCat.{u + 1} Λ] (hH.of_iso (e'.app H).symm)).of_iso
    ((g)^*[ModuleCat.{u + 1} Λ].asEquivalence.counitIso.app H).symm

/-- **Sheaves supported on finitely many closed points with separably closed residue fields are
detected by their pushforward to a separably closed field.** Let `a : X ⟶ Spec k` with `k`
separably closed, `U` an open subset of `X` whose complement is a finite set of closed points
with separably closed residue fields, and `G` a sheaf vanishing on `U`. If `a_* G = 0` then
`G = 0`.

Writing `iₓ : Spec κ(x) ⟶ X` for the points `x ∉ U`, the units assemble to an isomorphism
`G ≅ ⨁ₓ iₓ_* iₓ^* G` (as in `AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar`), so
each `(iₓ ≫ a)_* iₓ^* G` is a summand of `a_* G`, hence zero, and the pushforward along a
morphism of spectra of separably closed fields reflects zero objects. -/
theorem isZero_of_isZero_lowerStar_of_isZero_upperStar {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite)
    (hcl : ∀ x ∉ U, IsClosed ({x} : Set X))
    (hsep : ∀ x ∉ U, IsSepClosed (X.residueField x))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj G))
    (haG : IsZero ((a)_*[ModuleCat.{u + 1} Λ].obj G)) : IsZero G := by
  let ι := {x : X // x ∉ U}
  have : Finite ι := hfin.to_subtype
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have (x : ι) : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.1 (hcl x.1 x.2)
  let adj (x : ι) :=
    upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (X.fromSpecResidueField x.1)
  let G' (x : ι) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (X.fromSpecResidueField x.1)_*[ModuleCat.{u + 1} Λ].obj
      ((X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ].obj G)
  let φ : G ⟶ ⨁ G' := biproduct.lift fun x ↦ (adj x).unit.app G
  -- the family consisting of `U` and of the points `x ∉ U` is jointly surjective
  let V : Option ι → Scheme.{u} := fun o ↦ o.elim (U : Scheme.{u})
    fun x ↦ Spec (X.residueField x.1)
  let b : ∀ o, V o ⟶ X := fun o ↦ match o with
    | none => U.ι
    | some x => X.fromSpecResidueField x.1
  have hφ : IsIso φ := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) b
      (fun y ↦ ?_) φ fun o ↦ ?_
    · by_cases hy : y ∈ U
      · exact ⟨none, ⟨y, hy⟩, rfl⟩
      · exact ⟨some ⟨y, hy⟩, IsLocalRing.closedPoint _, X.fromSpecResidueField_apply _ _⟩
    rcases o with _ | x
    · let P := (U.ι)^*[ModuleCat.{u + 1} Λ]
      have hz (x : ι) : IsZero (P.obj (G' x)) :=
        isZero_upperStar_lowerStar_of_disjoint_range _ U.ι (X.fromSpecResidueField x.1)
          (by
            rw [Scheme.range_fromSpecResidueField, Set.disjoint_singleton_right]
            simpa using x.2) _
      have : IsZero (P.obj (⨁ G')) := by
        rw [IsZero.iff_id_eq_zero, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'),
          P.map_sum]
        exact Finset.sum_eq_zero fun j _ ↦ by
          rw [P.map_comp, (hz j).eq_of_tgt (P.map (biproduct.π G' j)) 0, zero_comp]
      exact (hG.eq_of_src (P.map φ) (hG.iso this).hom) ▸ Iso.isIso_hom _
    · let P := (X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ]
      have hz (y : ι) (hxy : y ≠ x) : IsZero (P.obj (G' y)) := by
        -- `iₓ` factors through the open complement `V` of `y`, over which `G' y` vanishes
        let V : X.Opens := ⟨{y.1}ᶜ, (hcl y.1 y.2).isOpen_compl⟩
        have hV : Set.range (X.fromSpecResidueField x.1) ⊆ Set.range V.ι := by
          rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
          exact fun h ↦ hxy (Subtype.ext h).symm
        have h0 := isZero_upperStar_lowerStar_of_disjoint_range _ V.ι
          (X.fromSpecResidueField y.1)
          (by rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]; simp [V])
          ((X.fromSpecResidueField y.1)^*[ModuleCat.{u + 1} Λ].obj G)
        exact (Functor.map_isZero (IsOpenImmersion.lift V.ι _ hV)^*[ModuleCat.{u + 1} Λ]
          h0).of_iso ((upperStarComp (ModuleCat.{u + 1} Λ) (IsOpenImmersion.lift V.ι _ hV)
            V.ι _ (IsOpenImmersion.lift_fac _ _ _).symm).app _)
      have hπ : IsIso (P.map (biproduct.π G' x)) := by
        refine ⟨P.map (biproduct.ι G' x), ?_, ?_⟩
        · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'), P.map_sum,
            Finset.sum_eq_single x (fun y _ hxy ↦ ?_) (by simp)]
          rw [P.map_comp, (hz y hxy).eq_zero_of_tgt (P.map (biproduct.π G' y)), zero_comp]
        · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
      have hunit : IsIso (P.map ((adj x).unit.app G)) := by
        have : IsIso (P.map ((adj x).unit.app G) ≫ (adj x).counit.app (P.obj G)) := by
          rw [(adj x).left_triangle_components G]
          exact IsIso.id _
        exact IsIso.of_isIso_comp_right _ ((adj x).counit.app (P.obj G))
      have : IsIso (P.map φ ≫ P.map (biproduct.π G' x)) := by
        rw [← P.map_comp, biproduct.lift_π]
        exact hunit
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this
  -- each summand `G' x` is zero, its pushforward being a summand of `a_* G = 0`
  let Pa := (a)_*[ModuleCat.{u + 1} Λ]
  have hB : IsZero (Pa.obj (⨁ G')) := haG.of_iso (Pa.mapIso (asIso φ)).symm
  have hG' (x : ι) : IsZero (G' x) := by
    have : IsSepClosed (IsLocalRing.ResidueField (X.presheaf.stalk x.1)) := hsep x.1 x.2
    have h1 : IsZero (Pa.obj (G' x)) := by
      rw [IsZero.iff_id_eq_zero, ← Pa.map_id, ← biproduct.ι_π_self G' x, Pa.map_comp,
        hB.eq_of_tgt (Pa.map (biproduct.ι G' x)) 0, zero_comp]
    have h2 : IsZero ((X.fromSpecResidueField x.1)^*[ModuleCat.{u + 1} Λ].obj G) :=
      isZero_of_isZero_lowerStar_of_isSepClosed (X.fromSpecResidueField x.1 ≫ a) _
        (h1.of_iso ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) _ a).app _).symm)
    exact Functor.map_isZero _ h2
  have : IsZero (⨁ G') := by
    rw [IsZero.iff_id_eq_zero, ← IsBilimit.total (biproduct.isBilimit G')]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [(hG' j).eq_of_tgt ((biproduct.bicone G').π j) 0,
      zero_comp]
  exact this.of_iso (asIso φ)

end Etale
namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Detection on closed points and global sections.** Let `X` be of finite type over an
algebraically closed field `k`, with structure morphism `a`, and let `f : K ⟶ L` be a morphism
of bounded constructible complexes on `X_ét` whose geometric stalks are isomorphisms at every
nonclosed point. Then the cone of `f` is supported on finitely many closed points, and `f` is an
isomorphism as soon as `Ra_* f` is. -/
theorem isIso_of_isIso_rightDerivedLowerStar_map_of_not_isClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a]
    [QuasiCompact a]
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) X L) (f : K ⟶ L)
    (hf : ∀ (x : X), ¬ IsClosed ({x} : Set X) → ∀ q : ℤ,
      IsIso ((X.uliftPointSmallEtale x).sheafFiber.map
        ((_root_.DerivedCategory.homologyFunctor _ q).map f)))
    (ha : IsIso ((R((a)_*[ModuleCat.{u + 1} Λ])).map f)) :
    IsIso f := by
  obtain ⟨Δ, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  -- `Ra_* Δ = 0`
  have hRΔ : IsZero ((R((a)_*[ModuleCat.{u + 1} Λ])).obj Δ) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((R((a)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT)).2 ha
  obtain ⟨⟨⟨m, hm⟩, -⟩, hc⟩ :=
    (boundedConstructible (ModuleCat.{u + 1} Λ) X).ext_of_isTriangulatedClosed₃ _ hT hK hL
  -- the homology sheaves of `Δ` vanish at the nonclosed points
  have hstalk (x : X) (hx : ¬ IsClosed ({x} : Set X)) (q : ℤ) :
      IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj Δ)) := by
    have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
    have : PreservesFiniteLimits ((X.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)) := inferInstance
    have : PreservesFiniteColimits ((X.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)) := inferInstance
    have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact _root_.DerivedCategory.isZero_map_homologyFunctor_obj₃_of_isIso _ _ hT q
      (hf x hx q) (hf x hx (q + 1))
  by_contra hne
  -- the lowest nonzero homology sheaf `G = Hⁿ(Δ)`
  have hex : ∃ q, ¬ IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj Δ) := by
    by_contra! h0
    have : IsIso (0 : Δ ⟶ 0) := (_root_.DerivedCategory.isIso_iff _ _).2 fun n ↦
      isIso_of_source_target_iso_zero _ (h0 n).isoZero
        ((Functor.map_isZero _ (isZero_zero _)).isoZero)
    exact hne (IsZero.of_iso (isZero_zero _) (asIso (0 : Δ ⟶ 0)))
  obtain ⟨n, hn, hmin⟩ := Int.exists_least_of_bdd ⟨m, fun q hq ↦ by
    by_contra h
    exact hq ((_root_.DerivedCategory.isGE_iff Δ m).1 hm q (by omega))⟩ hex
  have : Δ.IsGE n := (_root_.DerivedCategory.isGE_iff Δ n).2 fun i hi ↦ by
    by_contra h
    exact absurd (hmin i h) (by omega)
  set G := (_root_.DerivedCategory.homologyFunctor _ n).obj Δ with hG
  have : IsConstructibleSheaf G := hc n
  -- `G` is supported on a finite set `Z` of closed points
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : IsNoetherian X := {}
  let Z := (stalkZeroLocus G)ᶜ
  have hZcl (z : X) (hz : z ∈ Z) : IsClosed ({z} : Set X) := by
    by_contra hz'
    refine hz ?_
    have h' : IsZero ((pointSmallEtale (X.algClosurePoint z)).sheafFiber.obj G) :=
      (hstalk z hz' n).of_iso
        (((pointSmallEtale (X.algClosurePoint z)).uliftSheafFiberIso _).app G).symm
    simpa using mem_stalkZeroLocus_of_isZero_sheafFiber G (X.algClosurePoint z) h'
  have hZfin : Z.Finite := Scheme.finite_of_isClosed_constructibleTopology
    (@IsOpen.isClosed_compl X (constructibleTopology X) _
      (isOpen_constructibleTopology_stalkZeroLocus G)) hZcl
  have hZ : IsClosed Z := by
    rw [← Set.biUnion_of_singleton Z]
    exact hZfin.isClosed_biUnion hZcl
  let U : X.Opens := ⟨stalkZeroLocus G, by
    rw [← compl_compl (stalkZeroLocus G)]
    exact hZ.isOpen_compl⟩
  have hsep (x : X) (hx : x ∉ U) : IsSepClosed (X.residueField x) := by
    have := isAlgClosed_residueField_of_isClosed a x (hZcl x hx)
    infer_instance
  -- `G` vanishes on `U`
  have hGU : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj G) := by
    refine isZero_of_isZero_sheafFiber _ fun y ↦ ?_
    let s := (U : Scheme.{u}).algClosurePoint y
    exact (y.2 _ (s ≫ U.ι) (by simp [s])).of_iso
      ((upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) U.ι s).app G ≪≫
        ((pointSmallEtale (s ≫ U.ι)).uliftSheafFiberIso _).app G)
  -- `a_* G = 0`
  have haG : IsZero ((a)_*[ModuleCat.{u + 1} Λ].obj G) := by
    by_contra hN
    let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a
    have hε : adj.counit.app G ≠ 0 := fun h0 ↦ hN (by
      rw [IsZero.iff_id_eq_zero, ← adj.right_triangle_components G, h0, Functor.map_zero,
        comp_zero])
    obtain ⟨g, hg⟩ := _root_.DerivedCategory.exists_ne_zero_hom_singleFunctor_of_isGE _ hε
    let e := (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor n).app
      ((a)_*[ModuleCat.{u + 1} Λ].obj G)
    let adjD := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a
    refine hg ?_
    rw [← cancel_epi e.hom, comp_zero]
    exact (adjD.homEquiv _ _).injective (hRΔ.eq_of_tgt _ _)
  exact hn (isZero_of_isZero_lowerStar_of_isZero_upperStar a U hZfin (fun x hx ↦ hZcl x hx)
    hsep G hGU haG)

end Etale

end AlgebraicGeometry
