/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Pro-étale cohomology of a qcqs scheme commutes with filtered colimits

Let `X` be a quasi-compact quasi-separated scheme and `c` a colimit cocone of a filtered diagram
`D : K ⥤ Sh(X_proét, Ab)` of abelian pro-étale sheaves, indexed by a `u + 1`-small category.
Then `colim_k Hᵠ(X_proét, D_k) ⟶ Hᵠ(X_proét, c.pt)` is bijective for every `q`
(`AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_of_isFiltered_small`), the pro-étale analogue
of [Stacks 03Q6] for the étale site
(`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_small`).

The proof is that of the étale case
(`WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit`), whose only site-specific
inputs are replaced by their pro-étale counterparts: on an object of the pro-étale site with
quasi-compact underlying space every covering sieve contains a finite jointly surjective family
of affine objects (`AlgebraicGeometry.Scheme.ProEt.exists_finite_affine_of_mem_topology`), and
such a family is covering over a quasi-separated object
(`AlgebraicGeometry.Scheme.ProEt.ofArrows_mem_topology`), since it is a quasi-compact cover.
Hence sections over quasi-compact quasi-separated objects commute with filtered colimits
(`AlgebraicGeometry.Scheme.ProEt.exists_app_eq_of_isColimit_ab`,
`AlgebraicGeometry.Scheme.ProEt.exists_map_eq_of_isColimit_ab`), filtered colimits of injective
sheaves are Čech-acyclic, hence acyclic
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_succ_of_isColimit_of_injective`), and dimension
shifting concludes.

This is the input for the commutation of `ℓ`-adic cohomology with the colimits
`E_X = 𝒪_{E,X}[1/ℓ]` and `ℚ̄_ℓ,X = colim_E E_X`
(`WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldSheafColimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-- On an object `W` of the pro-étale site with quasi-compact underlying space, every covering
sieve contains a finite jointly surjective family of objects with affine underlying schemes. -/
lemma exists_finite_affine_of_mem_topology {W : X.ProEt} [CompactSpace W.left]
    {R : Sieve W} (hR : R ∈ ProEt.topology X W) :
    ∃ (n : ℕ) (U : Fin n → X.ProEt) (g : ∀ a, U a ⟶ W), (∀ a, R (g a)) ∧
      (∀ a, IsAffine (U a).left) ∧ ⋃ a, Set.range (g a).left = Set.univ := by
  rw [mem_topology_iff] at hR
  obtain ⟨R', hR', hle⟩ := hR
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR'
  obtain ⟨E, rfl⟩ := hR'
  have hmem : (E.toPreZeroHypercover.map (ProEt.forget X ⋙ Over.forget X)).presieve₀ ∈
      Scheme.proetalePrecoverage W.left := by
    rw [PreZeroHypercover.presieve₀_map]
    exact E.mem₀
  have hqc : QuasiCompactCover (E.toPreZeroHypercover.map (ProEt.forget X ⋙ Over.forget X)) := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact hmem.1
  have : CompactSpace ((ProEt.forget X ⋙ Over.forget X).obj W) := ‹CompactSpace W.left›
  obtain ⟨n, a, Vo, hVo, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (E.toPreZeroHypercover.map (ProEt.forget X ⋙ Over.forget X)) (U := ⊤) isCompact_univ
  refine ⟨n, fun k ↦ AlgebraicGeometry.ProEtale.overOpens (P := @WeaklyEtale)
      (fun _ _ ↦ inferInstance) (E.X (a k)) (Vo k),
    fun k ↦ AlgebraicGeometry.ProEtale.overOpensι (P := @WeaklyEtale)
      (fun _ _ ↦ inferInstance) (E.X (a k)) (Vo k) ≫
      E.f (a k), fun k ↦ R.downward_closed (hle _ _ (Presieve.ofArrows.mk (a k))) _,
    fun k ↦ hVo k, ?_⟩
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hx := hcov.symm ▸ (show x ∈ ((⊤ : W.left.Opens) : Set W.left) from trivial)
  obtain ⟨k, y, hy, hyx⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨k, ⟨y, hy⟩, hyx⟩

/-- A finite jointly surjective family of morphisms with quasi-compact sources to an object of
the pro-étale site with quasi-separated underlying space generates a covering sieve. -/
lemma ofArrows_mem_topology {W : X.ProEt} [QuasiSeparatedSpace W.left] {n : ℕ}
    {U : Fin n → X.ProEt} [∀ a, CompactSpace (U a).left] (g : ∀ a, U a ⟶ W)
    (hg : ⋃ a, Set.range (g a).left = Set.univ) :
    Sieve.ofArrows U g ∈ ProEt.topology X W := by
  rw [mem_topology_iff]
  refine ⟨Presieve.ofArrows U g, ?_, Sieve.le_generate _⟩
  rw [mem_precoverage_iff, Presieve.map_ofArrows]
  let E : PreZeroHypercover.{0} W.left :=
    { I₀ := Fin n
      X a := (U a).left
      f a := (g a).left }
  have : ∀ a, QuasiCompact (E.f a) := fun a ↦ quasiCompact_of_compactSpace _
  have hsurj (x : W.left) : ∃ a, x ∈ Set.range (E.f a) :=
    Set.mem_iUnion.1 (hg.symm ▸ Set.mem_univ x)
  have hE : QuasiCompactCover E :=
    ⟨fun {V} hV ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun a ↦ (E.f a).isSpectralMap) (fun x _ ↦ hsurj x) V.2 hV.isCompact⟩
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hE,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr
      ⟨hsurj, fun a ↦ inferInstanceAs (WeaklyEtale (g a).left)⟩⟩

/-- A finite jointly surjective family of morphisms with quasi-compact sources to an object with
quasi-separated underlying space is a covering family for every abelian pro-étale sheaf. -/
lemma isSheafFor_ofArrows (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) {W : X.ProEt}
    [QuasiSeparatedSpace W.left] {n : ℕ} {U : Fin n → X.ProEt} [∀ a, CompactSpace (U a).left]
    (g : ∀ a, U a ⟶ W) (hg : ⋃ a, Set.range (g a).left = Set.univ) :
    Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget _) (Presieve.ofArrows U g) := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (CategoryTheory.forget AddCommGrpCat) F.property)
  rw [Presieve.isSheafFor_iff_generate]
  exact this _ (ofArrows_mem_topology g hg)


/-- Quasi-compactness and quasi-separatedness of the underlying scheme are invariant under
isomorphisms of pro-étale `X`-schemes. -/
lemma compactSpace_and_quasiSeparatedSpace_of_iso {A B : X.ProEt} (e : A ≅ B)
    (h : CompactSpace A.left ∧ QuasiSeparatedSpace A.left) :
    CompactSpace B.left ∧ QuasiSeparatedSpace B.left := by
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((ProEt.forget X ⋙ Over.forget X).mapIso e))
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h.1 φ, (quasiSeparatedSpace_congr φ).1 h.2⟩

/-- A fibre product of pro-étale `X`-schemes with quasi-compact quasi-separated underlying schemes
over one with quasi-separated underlying scheme has quasi-compact quasi-separated underlying
scheme. -/
lemma compactSpace_and_quasiSeparatedSpace_pullback {V A B : X.ProEt} (f : A ⟶ V) (g : B ⟶ V)
    [QuasiSeparatedSpace V.left] [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let iso := PreservesPullback.iso (ProEt.forget X ⋙ Over.forget X) f g
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› φ, (quasiSeparatedSpace_congr φ).1 ‹_›⟩

/-- A finite product in `Over V` of pro-étale `X`-schemes with quasi-compact quasi-separated
underlying schemes has quasi-compact quasi-separated underlying scheme, if `V` has. -/
lemma compactSpace_and_quasiSeparatedSpace_piObj {V : X.ProEt} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, CompactSpace (U j).left.left ∧ QuasiSeparatedSpace (U j).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦
    CompactSpace A.left.left ∧ QuasiSeparatedSpace A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B :=
    compactSpace_and_quasiSeparatedSpace_of_iso ((Over.forget V).mapIso e) h
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) ⟨‹_›, ‹_›⟩⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.right⟩
    exact compactSpace_and_quasiSeparatedSpace_of_iso (Over.prodLeftIsoPullback _ _).symm
      (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU


section Sections

variable {X : Scheme.{u}} {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
  {F : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

omit [IsFiltered K] in
/-- The presheaf colimit of a diagram of abelian pro-étale sheaves, with its comparison map to the
sheaf colimit: the comparison is locally surjective and locally injective, being the
sheafification map. -/
lemma exists_presheafColimit_ab (hc : IsColimit c) :
    ∃ (E : Cocone (F ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      Presheaf.IsLocallySurjective (ProEt.topology X) φ ∧
      Presheaf.IsLocallyInjective (ProEt.topology X) φ ∧
      ∀ k, E.ι.app k ≫ φ = (c.ι.app k).hom := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
  let hE : IsColimit E := colimit.isColimit _
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  refine ⟨E, hE, toSheafify _ E.pt ≫ e.hom.hom, ?_, ?_, fun k ↦ ?_⟩
  · infer_instance
  · infer_instance
  · rw [← Category.assoc, ← Sheaf.sheafifyCocone_ι_app_val,
      ← ObjectProperty.FullSubcategory.comp_hom,
      IsColimit.comp_coconePointUniqueUpToIso_hom]

/-- **Sections of a filtered colimit of abelian sheaves are locally lifted.** Every section of
`c.pt` over `W` is, on the members of a covering sieve of `W`, the image of a section of some
`F k`. -/
lemma exists_mem_forall_exists_app_eq_ab (hc : IsColimit c) {W : X.ProEt}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ (ProEt.topology X) W, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ W), R f →
      ∃ (k : K) (t : (F.obj k).obj.obj (op V)),
        (c.ι.app k).hom.app (op V) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, -, hφ⟩ := exists_presheafColimit_ab hc
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  obtain ⟨k, t, rfl⟩ := Concrete.isColimit_exists_rep _ hEV p
  refine ⟨k, t, Eq.trans ?_ hp⟩
  rw [← hφ k]
  rfl

/-- **Sections of a filtered colimit of abelian sheaves are locally separated.** Two sections
of `F k` over `W` with the same image in `c.pt` agree, on the members of a covering sieve of
`W`, in some later `F k'`. -/
lemma exists_mem_forall_exists_map_eq_ab (hc : IsColimit c) {W : X.ProEt} {k : K}
    (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ R ∈ (ProEt.topology X) W, ∀ ⦃V : X.ProEt⦄ (f : V ⟶ W), R f →
      ∃ (k' : K) (a : k ⟶ k'),
        (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t) =
          (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t') := by
  obtain ⟨E, hE, φ, -, hi, hφ⟩ := exists_presheafColimit_ab hc
  have h' : φ.app (op W) ((E.ι.app k).app (op W) t) =
      φ.app (op W) ((E.ι.app k).app (op W) t') := by
    change (E.ι.app k ≫ φ).app _ t = (E.ι.app k ≫ φ).app _ t'
    rw [hφ]
    exact h
  refine ⟨_, Presheaf.equalizerSieve_mem _ φ _ _ h', fun V f hf ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  have hf' : (E.ι.app k).app (op V) ((F.obj k).obj.map f.op t) =
      (E.ι.app k).app (op V) ((F.obj k).obj.map f.op t') := by
    have hn := (E.ι.app k).naturality f.op
    have e1 := ConcreteCategory.congr_hom hn t
    have e2 := ConcreteCategory.congr_hom hn t'
    simp only [ConcreteCategory.comp_apply] at e1 e2
    erw [e1, e2]
    exact hf
  obtain ⟨k', a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hEV _ _ hf'
  refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
  let q := IsFiltered.coeqHom a b
  calc (F.map (a ≫ q)).hom.app (op V) ((F.obj k).obj.map f.op t)
      = (F.map q).hom.app (op V) ((F.map a).hom.app (op V) ((F.obj k).obj.map f.op t)) := by
        rw [F.map_comp]; rfl
    _ = (F.map q).hom.app (op V) ((F.map b).hom.app (op V) ((F.obj k).obj.map f.op t')) :=
        congrArg _ hab
    _ = (F.map (b ≫ q)).hom.app (op V) ((F.obj k).obj.map f.op t') := by
        rw [F.map_comp]; rfl
    _ = _ := by rw [← IsFiltered.coeq_condition a b]

/-- **Sections over a quasi-compact `W` of a filtered colimit of abelian sheaves are separated
at a finite stage.** Two sections of `F k` over `W` with the same image in `c.pt` agree in some
later `F k'`. -/
theorem exists_map_eq_of_isColimit_ab (hc : IsColimit c) {W : X.ProEt} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left]
    {k : K} (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = (F.map a).hom.app (op W) t' := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_map_eq_ab hc t t' h
  obtain ⟨n, U, g, hRg, hU, hcov⟩ := exists_finite_affine_of_mem_topology hR
  have : ∀ a, CompactSpace (U a).left := fun a ↦ by have := hU a; infer_instance
  choose k₁ a₁ ha₁ using fun i ↦ hloc (g i) (hRg i)
  obtain ⟨k', A, b, hb⟩ := IsFiltered.exists_comp_eq_of_finite a₁
  refine ⟨k', A, (isSheafFor_ofArrows (F.obj k') g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change (F.obj k').obj.map (g i).op _ = (F.obj k').obj.map (g i).op _
  have hnat (z : (F.obj k).obj.obj (op W)) : (F.obj k').obj.map (g i).op ((F.map A).hom.app _ z) =
      (F.map (b i)).hom.app _ ((F.map (a₁ i)).hom.app _ ((F.obj k).obj.map (g i).op z)) := by
    rw [← hb i, F.map_comp]
    exact (NatTrans.naturality_apply (F.map (a₁ i) ≫ F.map (b i)).hom (g i).op z).symm
  rw [hnat, hnat, ha₁ i]

/-- **Sections over a quasi-compact `W` of a filtered colimit of abelian sheaves vanish at a
finite stage.** A section of `F k` over `W` which vanishes in `c.pt` vanishes in some later
`F k'`. -/
theorem exists_map_eq_zero_of_isColimit_ab (hc : IsColimit c) {W : X.ProEt}
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] {k : K} (t : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = 0) :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = 0 := by
  obtain ⟨k', a, ha⟩ := exists_map_eq_of_isColimit_ab hc t 0 (by rw [h, map_zero])
  exact ⟨k', a, by rw [ha, map_zero]⟩

/-- **Sections over a quasi-compact quasi-separated `W` of a filtered colimit of abelian
sheaves come from a finite stage.** Every section of `c.pt` over `W` is the image of a section
of some `F k` (Stacks 0738). -/
theorem exists_app_eq_of_isColimit_ab (hc : IsColimit c) {W : X.ProEt} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (k : K) (t : (F.obj k).obj.obj (op W)), (c.ι.app k).hom.app (op W) t = s := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_app_eq_ab hc s
  obtain ⟨n, U, g, hRg, hU, hcov⟩ := exists_finite_affine_of_mem_topology hR
  have : ∀ a, CompactSpace (U a).left := fun a ↦ by have := hU a; infer_instance
  choose k₁ t₁ ht₁ using fun i ↦ hloc (g i) (hRg i)
  obtain ⟨k, ⟨b⟩⟩ := IsFiltered.exists_cocone_of_finite k₁
  let t₂ (i : Fin n) : (F.obj k).obj.obj (op (U i)) := (F.map (b i)).hom.app _ (t₁ i)
  have ht₂ (i : Fin n) : (c.ι.app k).hom.app _ (t₂ i) = c.pt.obj.map (g i).op s := by
    rw [← ht₁ i, ← c.w (b i)]
    rfl
  -- on the overlaps the local lifts agree at a later stage
  have hpair (ij : Fin n × Fin n) : ∃ (k' : K) (a : k ⟶ k'),
      (F.map a).hom.app _ ((F.obj k).obj.map (pullback.fst (g ij.1) (g ij.2)).op (t₂ ij.1)) =
        (F.map a).hom.app _ ((F.obj k).obj.map (pullback.snd (g ij.1) (g ij.2)).op
          (t₂ ij.2)) := by
    have := hU ij.1
    have := hU ij.2
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback (g ij.1) (g ij.2)
    refine exists_map_eq_of_isColimit_ab hc _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht₂, ht₂]
    change c.pt.obj.map _ (c.pt.obj.map _ s) = c.pt.obj.map _ (c.pt.obj.map _ s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition]
  choose k₂ a₂ ha₂ using hpair
  obtain ⟨k', A, b', hb'⟩ := IsFiltered.exists_comp_eq_of_finite a₂
  let z (i : Fin n) : (F.obj k').obj.obj (op (U i)) := (F.map A).hom.app _ (t₂ i)
  have hz (i : Fin n) : (c.ι.app k').hom.app _ (z i) = c.pt.obj.map (g i).op s := by
    rw [← ht₂ i, ← c.w A]
    rfl
  have hA (ij : Fin n × Fin n) :
      (F.obj k').obj.map (pullback.fst (g ij.1) (g ij.2)).op (z ij.1) =
        (F.obj k').obj.map (pullback.snd (g ij.1) (g ij.2)).op (z ij.2) := by
    have e (j : Fin n) (r : pullback (g ij.1) (g ij.2) ⟶ U j) :
        (F.obj k').obj.map r.op (z j) =
          (F.map (b' ij)).hom.app _
            ((F.map (a₂ ij)).hom.app _ ((F.obj k).obj.map r.op (t₂ j))) := by
      change (F.obj k').obj.map r.op ((F.map A).hom.app _ (t₂ j)) = _
      rw [← hb' ij, F.map_comp]
      exact (NatTrans.naturality_apply (F.map (a₂ ij) ≫ F.map (b' ij)).hom r.op (t₂ j)).symm
    rw [e, e, ha₂ ij]
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows (F.obj k') g hcov)) z fun i j ↦ hA (i, j)
  refine ⟨k', y, (isSheafFor_ofArrows c.pt g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← hz i]
  erw [← hy i]
  exact (NatTrans.naturality_apply (c.ι.app k').hom (g i).op y).symm

end Sections

section Cech

open Presheaf

variable {X : Scheme.{u}} {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
  {F : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- Let `c` be a colimit of a filtered diagram of abelian pro-étale sheaves `F k` whose Čech
complexes on a finite family `U` of pro-étale `X`-schemes over `V` are exact in positive degrees.
If the Čech nerve of `U` has quasi-compact quasi-separated members, then the Čech complex of
`c.pt` on `U` is exact in positive degrees: Čech cochains of `c.pt` come from a finite stage,
and so do the relations between them. -/
lemma exactAt_cechComplex_of_isColimit (hc : IsColimit c) {V : X.ProEt} {n : ℕ}
    (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      CompactSpace (cechNerveObj U y).left.left ∧ QuasiSeparatedSpace (cechNerveObj U y).left.left)
    (q : ℕ) (hF : ∀ k, ((cechComplex U).obj (F.obj k).obj).ExactAt (q + 1)) :
    ((cechComplex U).obj c.pt.obj).ExactAt (q + 1) := by
  rw [exactAt_cechComplex_iff]
  intro z hz
  -- the cochain `z` comes from a finite stage `k`
  choose k₁ t₁ ht₁ using fun y : Fin (q + 2) → Fin n ↦
    have := (hU (q + 1) y).1
    have := (hU (q + 1) y).2
    exists_app_eq_of_isColimit_ab hc (z y)
  obtain ⟨k, ⟨b⟩⟩ := IsFiltered.exists_cocone_of_finite k₁
  let z' : ((cechComplex U).obj (F.obj k).obj).X (q + 1) := fun y ↦
    (F.map (b y)).hom.app _ (t₁ y)
  have hz' : ((cechComplex U).map (c.ι.app k).hom).f (q + 1) z' = z := by
    funext y
    rw [cechComplex_map_f_apply, ← ht₁ y, ← c.w (b y)]
    rfl
  -- its differential vanishes at a later stage `k'`
  have hd (y : Fin (q + 3) → Fin n) : ∃ (k' : K) (a : k ⟶ k'),
      (F.map a).hom.app _ (((cechComplex U).obj (F.obj k).obj).d (q + 1) (q + 2) z' y) = 0 := by
    have := (hU (q + 2) y).1
    have := (hU (q + 2) y).2
    refine exists_map_eq_zero_of_isColimit_ab hc _ ?_
    rw [← cechComplex_map_f_apply, cechComplex_map_f_d_apply, hz']
    change ((cechComplex U).obj c.pt.obj).d (q + 1) (q + 2) z y = 0
    rw [hz]
    rfl
  choose k₂ a₂ ha₂ using hd
  obtain ⟨k', A, b', hb'⟩ := IsFiltered.exists_comp_eq_of_finite a₂
  let z'' := ((cechComplex U).map (F.map A).hom).f (q + 1) z'
  have hz'' : ((cechComplex U).obj (F.obj k').obj).d (q + 1) (q + 2) z'' = 0 := by
    funext y
    rw [← cechComplex_map_f_d_apply, cechComplex_map_f_apply, ← hb' y, F.map_comp]
    change (F.map (b' y)).hom.app _ ((F.map (a₂ y)).hom.app _ _) = 0
    rw [ha₂ y, map_zero]
  obtain ⟨e, he⟩ := (exactAt_cechComplex_iff U _ q).1 (hF k') z'' hz''
  refine ⟨((cechComplex U).map (c.ι.app k').hom).f q e,
    (cechComplex_map_f_d_apply U (c.ι.app k').hom q e).symm.trans ?_⟩
  rw [he, ← hz']
  funext y
  rw [cechComplex_map_f_apply, cechComplex_map_f_apply, ← c.w A]
  rfl

variable (X) in
/-- On a quasi-compact quasi-separated scheme `X`, a filtered colimit of injective abelian pro-étale
sheaves has no higher cohomology. This follows from the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` applied to the pro-étale
`X`-schemes with quasi-compact quasi-separated underlying scheme, by
`AlgebraicGeometry.Scheme.ProEt.exactAt_cechComplex_of_isColimit`. -/
theorem subsingleton_H_succ_of_isColimit_of_injective [CompactSpace X]
    [QuasiSeparatedSpace X] [∀ k, Injective (F.obj k)] (hc : IsColimit c) (q : ℕ) :
    Subsingleton (Sheaf.H c.pt (q + 1)) := by
  let T : X.ProEt := ProEt.mk (𝟙 X)
  have hT : IsTerminal T := isTerminalMkId X
  let B : X.ProEt → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.ProEt) (hV : B V) (R : Sieve V) (hR : R ∈ (ProEt.topology X) V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ (ProEt.topology X) V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_topology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      have : ∀ a, CompactSpace (U a).left := fun a ↦ by have := hU a; infer_instance
      ofArrows_mem_topology g hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  exact Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov c.pt
    (fun V hV n U hU _ q ↦ exactAt_cechComplex_of_isColimit hc U hU q
      fun k ↦ Sheaf.exactAt_cechComplex_of_injective (F.obj k) U q) q

end Cech

section DimensionShifting

variable {X : Scheme.{u}} {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]

/-- The pointwise short complex `D k ⟶ I k ⟶ Q k` of a composable pair of morphisms of
diagrams with vanishing composite. -/
noncomputable abbrev shortComplexApp {D I Q : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (ι : D ⟶ I) (π : I ⟶ Q) (h : ι ≫ π = 0) (k : K) :
    ShortComplex (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (ι.app k) (π.app k) (by rw [← NatTrans.comp_app, h, NatTrans.app_zero])

/-- The transition morphisms between the pointwise short complexes
`AlgebraicGeometry.Scheme.shortComplexApp`. -/
noncomputable def shortComplexAppMap
    {D I Q : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (ι : D ⟶ I) (π : I ⟶ Q) (h : ι ≫ π = 0) {k k' : K} (a : k ⟶ k') :
    shortComplexApp ι π h k ⟶ shortComplexApp ι π h k' where
  τ₁ := D.map a
  τ₂ := I.map a
  τ₃ := Q.map a
  comm₁₂ := ι.naturality a
  comm₂₃ := π.naturality a

/-- **Dimension shifting for filtered colimits.** Let `0 → D → I → Q → 0` be a short exact
sequence of diagrams of abelian sheaves with `I` pointwise injective, mapping to a short exact
sequence `0 → c.pt → cI.pt → cQ.pt → 0` of cocone points with `H^{n + 1}(cI.pt) = 0`. If
`Hⁿ(cI.pt)` is covered by the `Hⁿ(I k)` and `colim_k Hⁿ(Q k) ⟶ Hⁿ(cQ.pt)` is bijective, then
`colim_k H^{n + 1}(D k) ⟶ H^{n + 1}(c.pt)` is bijective. -/
lemma H_map_isColimit_succ_of_shortExact
    {D I Q : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} (ι : D ⟶ I) (π : I ⟶ Q)
    (h : ι ≫ π = 0) (hS : ∀ k, (shortComplexApp ι π h k).ShortExact)
    [∀ k, Injective (I.obj k)] {c : Cocone D} {cI : Cocone I} {cQ : Cocone Q}
    (f : c.pt ⟶ cI.pt) (g : cI.pt ⟶ cQ.pt) (hfg : f ≫ g = 0)
    (hS' : (ShortComplex.mk f g hfg).ShortExact)
    (hf : ∀ k, c.ι.app k ≫ f = ι.app k ≫ cI.ι.app k)
    (hg : ∀ k, cI.ι.app k ≫ g = π.app k ≫ cQ.ι.app k) (n : ℕ)
    (hI : Subsingleton (Sheaf.H cI.pt (n + 1)))
    (surjI : ∀ x : Sheaf.H cI.pt n, ∃ (k : K) (y : Sheaf.H (I.obj k) n),
      Sheaf.H.map (cI.ι.app k) n y = x)
    (surjQ : ∀ x : Sheaf.H cQ.pt n, ∃ (k : K) (y : Sheaf.H (Q.obj k) n),
      Sheaf.H.map (cQ.ι.app k) n y = x)
    (injQ : ∀ (k : K) (y : Sheaf.H (Q.obj k) n), Sheaf.H.map (cQ.ι.app k) n y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (Q.map a) n y = 0) :
    (∀ x : Sheaf.H c.pt (n + 1), ∃ (k : K) (y : Sheaf.H (D.obj k) (n + 1)),
      Sheaf.H.map (c.ι.app k) (n + 1) y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) (n + 1)), Sheaf.H.map (c.ι.app k) (n + 1) y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) (n + 1) y = 0 := by
  let S' := ShortComplex.mk f g hfg
  -- the morphisms from the pointwise short exact sequences to the colimit one
  let φ (k : K) : shortComplexApp ι π h k ⟶ S' :=
    { τ₁ := c.ι.app k
      τ₂ := cI.ι.app k
      τ₃ := cQ.ι.app k
      comm₁₂ := hf k
      comm₂₃ := hg k }
  have : Subsingleton (Sheaf.H S'.X₂ (n + 1)) := hI
  refine ⟨fun x ↦ ?_, fun k y hy ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := Sheaf.H.δSucc_surjective hS' n x
    obtain ⟨k, z', rfl⟩ := surjQ z
    exact ⟨k, Sheaf.H.δSucc (hS k) n z', Sheaf.H.map_δSucc (hS k) hS' (φ k) n z'⟩
  · have : Subsingleton (Sheaf.H (shortComplexApp ι π h k).X₂ (n + 1)) :=
      inferInstanceAs (Subsingleton (Sheaf.H (I.obj k) (n + 1)))
    obtain ⟨w, rfl⟩ := Sheaf.H.δSucc_surjective (hS k) n y
    have hw : Sheaf.H.δSucc hS' n (Sheaf.H.map (cQ.ι.app k) n w) = 0 := by
      rw [← hy]
      exact (Sheaf.H.map_δSucc (hS k) hS' (φ k) n w).symm
    obtain ⟨v, hv⟩ := ((Sheaf.H.exact_map_δSucc hS' n) _).1 hw
    obtain ⟨k₁, v₁, rfl⟩ := surjI v
    -- the images of `w` and of `v₁` agree in `Hⁿ(cQ.pt)`, hence at a finite stage
    let m := IsFiltered.max k k₁
    let a : k ⟶ m := IsFiltered.leftToMax k k₁
    let b : k₁ ⟶ m := IsFiltered.rightToMax k k₁
    have hm : Sheaf.H.map (cQ.ι.app m) n
        (Sheaf.H.map (Q.map a) n w - Sheaf.H.map (Q.map b) n (Sheaf.H.map (π.app k₁) n v₁)) =
          0 := by
      rw [map_sub, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
        ← Sheaf.H.map_comp_apply, cQ.w a, cQ.w b,
        ← hg, Sheaf.H.map_comp_apply]
      exact sub_eq_zero.2 hv.symm
    obtain ⟨k', a', ha'⟩ := injQ m _ hm
    refine ⟨k', a ≫ a', ?_⟩
    change Sheaf.H.map (shortComplexAppMap ι π h (a ≫ a')).τ₁ (n + 1) _ = 0
    rw [Sheaf.H.map_δSucc (hS k) (hS k') (shortComplexAppMap ι π h (a ≫ a')) n w]
    change Sheaf.H.δSucc (hS k') n (Sheaf.H.map (Q.map (a ≫ a')) n w) = 0
    rw [map_sub, sub_eq_zero, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← Q.map_comp, ← Q.map_comp, ← Sheaf.H.map_comp_apply, ← π.naturality,
      Sheaf.H.map_comp_apply] at ha'
    rw [ha']
    exact ((Sheaf.H.exact_map_δSucc (hS k') n) _).2 ⟨_, rfl⟩

variable (X) in
/-- **Global sections of a qcqs scheme commute with filtered colimits**, in terms of `H⁰`. -/
lemma H_zero_map_isColimit [CompactSpace X] [QuasiSeparatedSpace X]
    {D : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) :
    (∀ x : Sheaf.H c.pt 0, ∃ (k : K) (y : Sheaf.H (D.obj k) 0),
      Sheaf.H.map (c.ι.app k) 0 y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) 0), Sheaf.H.map (c.ι.app k) 0 y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) 0 y = 0 := by
  let T : X.ProEt := ProEt.mk (𝟙 X)
  have hT : IsTerminal T := isTerminalMkId X
  have : CompactSpace T.left := ‹CompactSpace X›
  have : QuasiSeparatedSpace T.left := ‹QuasiSeparatedSpace X›
  refine ⟨fun x ↦ ?_, fun k y hy ↦ ?_⟩
  · obtain ⟨k, t, ht⟩ := exists_app_eq_of_isColimit_ab hc (Sheaf.H.equiv₀ c.pt hT x)
    refine ⟨k, (Sheaf.H.equiv₀ _ hT).symm t, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality, ht]
    exact (Sheaf.H.equiv₀ c.pt hT).symm_apply_apply x
  · have h0 : (c.ι.app k).hom.app (op T) (Sheaf.H.equiv₀ _ hT y) = 0 := by
      rw [Sheaf.H.equiv₀_naturality, hy, map_zero]
    obtain ⟨k', a, ha⟩ := exists_map_eq_zero_of_isColimit_ab hc _ h0
    refine ⟨k', a, (Sheaf.H.equiv₀ _ hT).injective ?_⟩
    rw [← Sheaf.H.equiv₀_naturality, ha, map_zero]

end DimensionShifting

/-- **Pro-étale cohomology commutes with `u + 1`-small filtered colimits on a qcqs scheme.** Let
`X` be quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram
`D : K ⥤ Sh(X_ét, Ab)` indexed by a `u + 1`-small category. Then for every `q` the canonical
map `colim_k Hᵠ(X, D_k) ⟶ Hᵠ(X, c.pt)` is bijective, spelled out elementwise.

Degree zero is `AlgebraicGeometry.Scheme.ProEt.H_zero_map_isColimit`. In higher degrees, we
embed `D` into the diagram of injective sheaves `D.injectiveExtension` with cokernel `Q`; since
filtered colimits are exact, the colimit sequence `0 → c.pt → colim I → colim Q → 0` is short exact,
`colim I` has no higher cohomology
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_succ_of_isColimit_of_injective`), and we conclude by
`AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_succ_of_shortExact`. -/
@[stacks 03Q6]
theorem H_map_isColimit_of_isFiltered_small (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (k : K) (y : Sheaf.H (D.obj k) q),
      Sheaf.H.map (c.ι.app k) q y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) q), Sheaf.H.map (c.ι.app k) q y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) q y = 0 := by
  induction q generalizing D c with
  | zero => exact H_zero_map_isColimit X hc
  | succ n ih =>
    let I := D.injectiveExtension
    let ι := D.toInjectiveExtension
    let π := cokernel.π ι
    have h : ι ≫ π = 0 := cokernel.condition ι
    have : Mono ι := NatTrans.mono_of_mono_app ι
    have hSf : (ShortComplex.mk ι π h).ShortExact :=
      .mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance
    have hS (k : K) : (shortComplexApp ι π h k).ShortExact :=
      hSf.map_of_exact ((CategoryTheory.evaluation K _).obj k)
    let f : c.pt ⟶ colimit I := hc.desc ((Cocone.precompose ι).obj (colimit.cocone I))
    let g : colimit I ⟶ colimit (cokernel ι) := colimMap π
    have hf (k : K) : c.ι.app k ≫ f = ι.app k ≫ colimit.ι I k := hc.fac _ k
    have hg (k : K) : colimit.ι I k ≫ g = π.app k ≫ colimit.ι _ k := ι_colimMap π k
    have hfg : f ≫ g = 0 := hc.hom_ext fun k ↦ by
      rw [reassoc_of% (hf k), hg, ← NatTrans.comp_app_assoc, h, NatTrans.app_zero, zero_comp,
        comp_zero]
    let e₁ : colimit D ≅ c.pt := (colimit.isColimit D).coconePointUniqueUpToIso hc
    have hS' : (ShortComplex.mk f g hfg).ShortExact := by
      let e : (ShortComplex.mk ι π h).map colim ≅ ShortComplex.mk f g hfg :=
        ShortComplex.isoMk e₁ (Iso.refl _) (Iso.refl _) (colimit.hom_ext fun k ↦ ?_)
          (colimit.hom_ext fun k ↦ ?_)
      · exact ShortComplex.shortExact_of_iso e (hSf.map_of_exact colim)
      · simp only [colimit.comp_coconePointUniqueUpToIso_hom_assoc, hf, ShortComplex.map_f,
          colim_map, Iso.refl_hom, Category.comp_id, ι_colimMap, e₁]
        rfl
      · simp only [Iso.refl_hom, Category.id_comp, ι_colimMap, ShortComplex.map_g, colim_map,
          Category.comp_id, g]
    exact H_map_isColimit_succ_of_shortExact ι π h hS f g hfg hS' hf hg n
      (subsingleton_H_succ_of_isColimit_of_injective X (colimit.isColimit I) n)
      (ih (colimit.isColimit I)).1 (ih (colimit.isColimit _)).1 (ih (colimit.isColimit _)).2

end AlgebraicGeometry.Scheme.ProEt
