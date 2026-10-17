/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologicalFilteredColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedContinuity
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseIhomColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.SectionsWithSupportStratum

/-!
# Continuity of `Hom` out of an extension by zero from a stratum

Let `X` be a quasi-compact quasi-separated scheme, `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j : U ⟶ X`, `u : S ⟶ Z` a quasi-compact open immersion and `L` a
lisse sheaf of `ℚ̄_ℓ,S`-modules. For a filtered diagram `(K_i)` of complexes of sheaves of
`ℚ̄_ℓ,X`-modules vanishing in degrees `< b`, with colimit `K`, the natural maps
`colim_i Hom(a_! L, K_i[q]) ⟶ Hom(a_! L, K[q])` are bijective, `a_! = i_* u_!`
(`AlgebraicGeometry.ProEtale.isContinuousOn_stratum`, blueprint
`det-lem-constructible-ext-continuity-stratum`).

By `AlgebraicGeometry.ProEtale.homEquivStratum`, `Hom(a_! L, K[q]) = H^q(S, Φ(RΓ_Z K))` with
`Φ = 𝓗om(L, u^* -)`, and `i_* RΓ_Z K ⟶ K ⟶ Rj_* j^* K ⟶` is distinguished. With
`Ψ = 𝓗om(L, u^* i^* -)`, exact and commuting with colimits, `H^q(S, Ψ(K_i))` is continuous by
bounded-below continuity of cohomology on `S` (blueprint `det-lem-bounded-continuity-sections`),
and `H^q(S, Ψ(Rj_* j^* K_i))` is continuous by the continuity of `R^r j_*`
(`det-lem-bounded-continuity-direct-image`) and an induction on the truncations, in place of the
hypercohomology spectral sequence of the blueprint (`DerivedCategory.isContinuousOn_of_isGE'`);
the two out of three property for triangles (`CategoryTheory.Functor.IsContinuousOn.of_triangle₁`)
concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Hypercohomology

variable (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y] {I : Type (u + 1)}
  [SmallCategory I] [IsFiltered I]

/-- Bounded-below continuity of hypercohomology, as continuity of the homological functor
`H^0(Y, -)`. -/
lemma isContinuousOn_adicHypercohomology (K : I ⥤ CochainComplex (AdicSheaf l Y) ℤ) (a : ℤ)
    (hK : ∀ i, (K.obj i).IsStrictlyGE a) (c : Cocone K) (hc : IsColimit c) :
    (adicHypercohomology (l := l) Y).IsContinuousOn (DerivedCategory.Q.mapCocone c) :=
  fun q ↦ isIso_colimitDesc_hypercohomology Y K a hK c hc q

/-- Continuity of hypercohomology on filtered colimits of sheaves placed in degree `m`. -/
lemma isContinuousOn_adicHypercohomology_single (m : ℤ) {F : I ⥤ AdicSheaf l Y} (c : Cocone F)
    (hc : IsColimit c) :
    (adicHypercohomology (l := l) Y).IsContinuousOn
      ((DerivedCategory.singleFunctor (AdicSheaf l Y) m).mapCocone c) :=
  have : HasColimitsOfShape I (AdicSheaf l Y) := inferInstance
  have : PreservesColimitsOfShape I
      (HomologicalComplex.single (AdicSheaf l Y) (ComplexShape.up ℤ) m) := inferInstance
  isContinuousOn_adicHypercohomology Y (F ⋙ CochainComplex.singleFunctor _ m) m
    (fun _ ↦ by dsimp; infer_instance) ((CochainComplex.singleFunctor _ m).mapCocone c)
    (isColimitOfPreserves (HomologicalComplex.single (AdicSheaf l Y) (ComplexShape.up ℤ) m) hc)

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- `H^n(Y, X) = 0` for `X ∈ D^{≥ n+1}`. -/
lemma isZero_adicHypercohomology_shift_obj (n : ℤ) (X : DerivedCategory (AdicSheaf l Y))
    (hX : X.IsGE (n + 1)) : IsZero (((adicHypercohomology (l := l) Y).shift n).obj X) := by
  have : DerivedCategory.TStructure.t.IsGE (X⟦n⟧) 1 :=
    DerivedCategory.TStructure.t.isGE_shift X (n + 1) n 1 (by omega)
  have hs : Subsingleton (((adicHypercohomology (l := l) Y).shift n).obj X) := ⟨fun f g ↦ by
    change (_ ⟶ X⟦n⟧) at f g
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f 0 1 (by omega) inferInstance this,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g 0 1 (by omega) inferInstance this]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

end Hypercohomology

variable {Z U X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base)) (v : S ⟶ Z) [IsOpenImmersion v]
  [QuasiCompact v] (L : AdicSheaf l S) [Fact (IsAdicLisseSheaf L)]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

set_option maxHeartbeats 1000000 in
include hij in
/-- Blueprint `det-lem-constructible-ext-continuity-stratum`: **continuity of `Hom` out of
`a_! L`.** For a filtered diagram `(K_i)` of complexes of sheaves of `ℚ̄_ℓ,X`-modules vanishing in
degrees `< b`, with colimit `K`, the natural map
`colim_i Hom(a_! L, K_i[q]) ⟶ Hom(a_! L, K[q])` is an isomorphism for every `q`, where
`a_! L = i_* u_! L` for the stratum `a = i ∘ u : S ⟶ X` and a lisse sheaf `L` on `S`. -/
theorem isContinuousOn_stratum (K : I ⥤ CochainComplex (AdicSheaf l X) ℤ) (b : ℤ)
    (hK : ∀ i, (K.obj i).IsStrictlyGE b) (c : Cocone K) (hc : IsColimit c) :
    have := preservesFiniteColimits_adicLowerStar_of_isCompl (l := l) i j hij
    (preadditiveCoyoneda.obj (op (((i)_*ᵃ[l]).mapDerivedCategory.obj
      (((v)_!ᵃ[l]).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (AdicSheaf l S) 0).obj L))))).IsContinuousOn
      (DerivedCategory.Q.mapCocone c) := by
  intro _
  have : CompactSpace Z := (i.isClosedEmbedding).compactSpace
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace v
  have : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated (v ≫ i)
  -- the functor `Ψ = 𝓗om(L, v^* i^* -)`
  let Ψsh : AdicSheaf l X ⥤ AdicSheaf l S := (i)^*ᵃ[l] ⋙ (v)^*ᵃ[l] ⋙ AdicSheaf.ihom L
  have : (AdicSheaf.ihom L).Additive := inferInstance
  have := (adicUpperStarLowerStarAdjunction l i).leftAdjoint_preservesColimits
  have := (adicUpperStarLowerStarAdjunction l v).leftAdjoint_preservesColimits
  have := (Fact.out : IsAdicLisseSheaf L).preservesColimitsOfShape_ihom I
  have : PreservesColimitsOfShape I Ψsh := inferInstance
  let Ψ := Ψsh.mapDerivedCategory
  let s0 := DerivedCategory.Q.mapCocone c
  -- Step 1: `H^q(S, Ψ K_i)` is continuous
  have h₁ : (adicHypercohomology (l := l) S).IsContinuousOn (Ψ.mapCocone s0) := by
    have h := isContinuousOn_adicHypercohomology S
      (K ⋙ Ψsh.mapHomologicalComplex (ComplexShape.up ℤ)) b
      (fun k ↦ by
        have := hK k
        rw [CochainComplex.isStrictlyGE_iff] at this ⊢
        exact fun n hn ↦ Ψsh.map_isZero (this n hn))
      ((Ψsh.mapHomologicalComplex (ComplexShape.up ℤ)).mapCocone c)
      (isColimitOfPreserves _ hc)
    exact (Functor.isContinuousOn_mapCocone_iff_of_iso Ψsh.mapDerivedCategoryFactors c).2 h
  -- Step 2: `H^q(S, Ψ Rj_* j^* K_i)` is continuous
  let RJ : DerivedCategory (AdicSheaf l X) ⥤ DerivedCategory (AdicSheaf l X) :=
    ((j)^*ᵃ[l]).mapDerivedCategory ⋙ ((j)_*ᵃ[l]).rightDerivedFunctor
  have hGE (M : DerivedCategory (AdicSheaf l X)) (hM : M.IsGE b) : (Ψ.obj (RJ.obj M)).IsGE b := by
    have := ((j)^*ᵃ[l]).isGE_mapDerivedCategory_obj M b
    have h2 : (RJ.obj M).IsGE b :=
      ((j)_*ᵃ[l]).isGE_rightDerivedFunctor_obj (((j)^*ᵃ[l]).mapDerivedCategory.obj M) b
    exact Ψsh.isGE_mapDerivedCategory_obj _ b
  have hQ (k : I) : (DerivedCategory.Q.obj (K.obj k)).IsGE b := by
    have := hK k
    infer_instance
  have hQc : (DerivedCategory.Q.obj c.pt).IsGE b := by
    have : c.pt.IsStrictlyGE b := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      have hev := isColimitOfPreserves
        (HomologicalComplex.eval (AdicSheaf l X) (ComplexShape.up ℤ) n) hc
      exact (IsZero.iff_id_eq_zero _).2 (hev.hom_ext fun k ↦ by
        have := hK k
        exact ((K.obj k).isZero_of_isStrictlyGE b n hn).eq_of_src _ _)
    infer_instance
  have h₂ : (adicHypercohomology (l := l) S).IsContinuousOn (Ψ.mapCocone (RJ.mapCocone s0)) := by
    refine DerivedCategory.isContinuousOn_of_isGE' (isZero_adicHypercohomology_shift_obj S)
      (fun m _ c' hc' ↦ isContinuousOn_adicHypercohomology_single S m c' hc') b _
      (fun k ↦ hGE _ (hQ k)) (hGE _ hQc) ?_
    have := (adicUpperStarLowerStarAdjunction l j).leftAdjoint_preservesColimits
    let jcx := ((j)^*ᵃ[l]).mapHomologicalComplex (ComplexShape.up ℤ)
    have hB (q : ℤ) := isIso_colimitDesc_homology_rightDerivedLowerStar j (K ⋙ jcx) b
        (fun k ↦ by
          have := hK k
          rw [CochainComplex.isStrictlyGE_iff] at this ⊢
          exact fun n hn ↦ ((j)^*ᵃ[l]).map_isZero (this n hn))
        (jcx.mapCocone c) (isColimitOfPreserves jcx hc) q
    let e' : DerivedCategory.Q ⋙ RJ ≅ jcx ⋙ DerivedCategory.Q ⋙ ((j)_*ᵃ[l]).rightDerivedFunctor :=
      Functor.isoWhiskerRight ((j)^*ᵃ[l]).mapDerivedCategoryFactors
        ((j)_*ᵃ[l]).rightDerivedFunctor
    have hB' (q : ℤ) : IsIso (colimit.desc (((K ⋙ DerivedCategory.Q) ⋙ RJ) ⋙
        DerivedCategory.homologyFunctor _ q)
        ((DerivedCategory.homologyFunctor _ q).mapCocone (RJ.mapCocone s0))) :=
      (Functor.isIso_colimitDesc_iff_of_iso (Functor.isoWhiskerLeft K e') (e'.app c.pt)
        (fun k ↦ e'.hom.naturality (c.ι.app k)) (DerivedCategory.homologyFunctor _ q)).2 (hB q)
    intro q
    change IsIso (colimit.desc (((K ⋙ DerivedCategory.Q) ⋙ RJ) ⋙
      (Ψ ⋙ DerivedCategory.homologyFunctor _ q))
      ((Ψ ⋙ DerivedCategory.homologyFunctor _ q).mapCocone (RJ.mapCocone s0)))
    refine (Functor.isIso_colimitDesc_iff_of_natIso _
      (Ψsh.mapDerivedCategoryHomologyFunctorIso q).symm).2 ?_
    exact Functor.isIso_colimitDesc_comp_of_preserves (K := ((K ⋙ DerivedCategory.Q) ⋙ RJ) ⋙
      DerivedCategory.homologyFunctor _ q)
      (c := (DerivedCategory.homologyFunctor _ q).mapCocone (RJ.mapCocone s0)) Ψsh (hB' q)
  sorry

end AlgebraicGeometry.ProEtale
