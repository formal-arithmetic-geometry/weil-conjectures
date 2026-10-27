/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-! # The relative affine criterion for fpqc sheaves

Source: Stacks Project, Tag 022H; the relative-site reduction in Tag 0APL
(blueprint: lem-a1-relative-fpqc-affine-criterion).
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry

private def totalPresheaf {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    Scheme.{u}ᵒᵖ ⥤ Type u where
  obj X := Σ s : X.unop ⟶ S, F.obj (op (Over.mk s))
  map f := ↾fun x ↦ ⟨f.unop ≫ x.1, F.map (Over.homMk f.unop rfl).op x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨s, x⟩
    dsimp
    congr 1
    change F.map (𝟙 (op (Over.mk s))) x = x
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨s, x⟩
    dsimp
    congr 1
    rw [← Functor.map_comp_apply]
    rfl

private theorem totalPresheaf_ext {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    {T : Scheme.{u}} {x y : (totalPresheaf F).obj (op T)} (h : x.1 = y.1)
    (h' : F.map (Over.homMk (U := Over.mk x.1) (V := Over.mk y.1)
      (𝟙 T) (by simpa using h.symm)).op y.2 = x.2) : x = y := by
  rcases x with ⟨s, x⟩
  rcases y with ⟨t, y⟩
  dsimp at h
  subst t
  change F.map (𝟙 (op (Over.mk s))) y = x at h'
  exact congrArg (Sigma.mk s) (by simpa only [Functor.map_id_apply] using h'.symm)

private def includeSection {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (T : Over S) (x : F.obj (op T)) : (totalPresheaf F).obj (op T.left) :=
  ⟨T.hom, F.map (Over.homMk (U := Over.mk T.hom) (V := T) (𝟙 T.left)
    (by simp)).op x⟩

private theorem includeSection_injective {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (T : Over S) : Function.Injective (includeSection F T) := by
  obtain ⟨T, s, rfl⟩ := T.mk_surjective
  intro x y h
  have h' := Sigma.mk.inj_iff.mp h
  have hxy := eq_of_heq h'.2
  change F.map (𝟙 (op (Over.mk s))) x = F.map (𝟙 (op (Over.mk s))) y at hxy
  simpa only [Functor.map_id_apply] using hxy

private theorem includeSection_naturality {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    {T U : Over S} (f : T ⟶ U) (x : F.obj (op U)) :
    (totalPresheaf F).map f.left.op (includeSection F U x) =
      includeSection F T (F.map f.op x) := by
  apply totalPresheaf_ext F (Over.w f)
  dsimp [includeSection, totalPresheaf]
  simp only [← Functor.map_comp_apply, ← op_comp]
  apply congrArg (fun k : Over.mk (f.left ≫ U.hom) ⟶ U ↦ F.map k.op x)
  ext
  simp

private theorem exists_includeSection {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (T : Over S) (z : (totalPresheaf F).obj (op T.left)) (h : z.1 = T.hom) :
    ∃ x, includeSection F T x = z := by
  obtain ⟨T, s, rfl⟩ := T.mk_surjective
  rcases z with ⟨t, z⟩
  dsimp at h
  subst t
  refine ⟨z, ?_⟩
  apply congrArg (Sigma.mk s)
  change F.map (𝟙 (op (Over.mk s))) z = z
  rw [Functor.map_id_apply]

private theorem total_isSheafFor {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    {T : Scheme.{u}} {I : Type w} (U : I → Scheme.{u}) (v : ∀ i, U i ⟶ T)
    (hS : Presieve.IsSheafFor (yoneda.obj S) (Presieve.ofArrows U v))
    (hF : ∀ s : T ⟶ S, Presieve.IsSheafFor F
      (Presieve.ofArrows (fun i ↦ Over.mk (v i ≫ s))
        (fun i ↦ (Over.homMk (v i) rfl : Over.mk (v i ≫ s) ⟶ Over.mk s)))) :
    Presieve.IsSheafFor (totalPresheaf F) (Presieve.ofArrows U v) := by
  classical
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  obtain ⟨s, hs, huniq⟩ := ((Presieve.isSheafFor_arrows_iff _ _).mp hS)
    (fun i ↦ (x i).1) (fun i j Z f g hfg ↦ congrArg Sigma.fst (hx i j Z f g hfg))
  choose y hy using fun i ↦ exists_includeSection F (Over.mk (v i ≫ s)) (x i) (hs i).symm
  let v' (i : I) : Over.mk (v i ≫ s) ⟶ Over.mk s := Over.homMk (v i) rfl
  obtain ⟨a, ha, hau⟩ := ((Presieve.isSheafFor_arrows_iff _ _).mp (hF s)) y (by
    intro i j Z f g hfg
    apply includeSection_injective F Z
    rw [← includeSection_naturality, ← includeSection_naturality, hy, hy]
    exact hx i j Z.left f.left g.left (congrArg (fun k ↦ k.left) hfg))
  refine ⟨includeSection F (Over.mk s) a, ?_, ?_⟩
  · intro i
    exact (includeSection_naturality F (v' i) a).trans
      ((congrArg (includeSection F _) (ha i)).trans (hy i))
  · intro b hb
    have hbs : b.1 = s := huniq b.1 (fun i ↦ congrArg Sigma.fst (hb i))
    obtain ⟨b', rfl⟩ := exists_includeSection F (Over.mk s) b hbs
    congr 1
    apply hau
    intro i
    apply includeSection_injective F (Over.mk (v i ≫ s))
    rw [← includeSection_naturality, hy]
    exact hb i

private theorem relative_isSheafFor {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (T : Over S) {I : Type w} (U : I → Over S) (v : ∀ i, U i ⟶ T)
    (hS : Presieve.IsSeparatedFor (yoneda.obj S)
      (Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (v i).left)))
    (hF : Presieve.IsSheafFor (totalPresheaf F)
      (Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (v i).left))) :
    Presieve.IsSheafFor F (Presieve.ofArrows U v) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hc : Presieve.Arrows.Compatible (totalPresheaf F) (fun i ↦ (v i).left)
      (fun i ↦ includeSection F (U i) (x i)) := by
    intro i j Z f g hfg
    let Z' : Over S := Over.mk (f ≫ (U i).hom)
    let f' : Z' ⟶ U i := Over.homMk f rfl
    let g' : Z' ⟶ U j := Over.homMk g (by
      dsimp [Z']
      rw [← Over.w (v j), ← Category.assoc, ← hfg, Category.assoc, Over.w])
    have hfg' : f' ≫ v i = g' ≫ v j := by ext; exact hfg
    exact (includeSection_naturality F f' (x i)).trans
      ((congrArg (includeSection F Z') (hx i j Z' f' g' hfg')).trans
        (includeSection_naturality F g' (x j)).symm)
  obtain ⟨a, ha, hau⟩ := ((Presieve.isSheafFor_arrows_iff _ _).mp hF) _ hc
  have has : a.1 = T.hom := by
    apply hS.ext
    rintro Z f ⟨i⟩
    exact (congrArg Sigma.fst (ha i)).trans (Over.w (v i)).symm
  obtain ⟨a', rfl⟩ := exists_includeSection F T a has
  refine ⟨a', ?_, ?_⟩
  · intro i
    apply includeSection_injective F (U i)
    rw [← includeSection_naturality]
    exact ha i
  · intro b hb
    apply includeSection_injective F T
    apply hau
    intro i
    rw [includeSection_naturality, hb i]

private theorem total_isSheaf {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hF : Presieve.IsSheaf (J.over S) F) : Presieve.IsSheaf J (totalPresheaf F) := by
  intro T R hR
  obtain ⟨I, U, v, hv⟩ := R.arrows.exists_eq_ofArrows
  have hcover : Sieve.ofArrows U v ∈ J T := by
    simpa only [Sieve.ofArrows, ← hv, Sieve.generate_sieve] using hR
  rw [hv]
  apply total_isSheafFor F U v
  · exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _ hcover
  · intro s
    apply hF.isSheafFor
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hcover

/-- The affine criterion for an fppf sheaf on schemes over a fixed base.
It suffices to check singleton flat surjections between spectra, with every structure
map to the base. Source: Stacks Project, Tag 022H, and the relative-site reduction
in the proof of Tag 0APL (blueprint: lem-a1-relative-fpqc-affine-criterion).

Proof: form the absolute presheaf of pairs consisting of a structure map to the base
and a section of the relative presheaf. For any covering, the structure maps glue
uniquely by subcanonicity. Once that structure map is fixed, the remaining gluing
problem is the given relative sheaf problem. Thus the total presheaf is an fppf,
hence Zariski, sheaf, and satisfies the affine singleton condition by the hypothesis.
Apply the absolute affine criterion. Finally, the structure map of an fpqc amalgamation
of pairs equals the prescribed one by subcanonicity, so it gives a relative section.
-/
theorem isSheaf_fpqc_over_of_affine {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F)
    (haff : ∀ {R A : CommRingCat.{u}} (f : R ⟶ A), Flat (Spec.map f) →
      Surjective (Spec.map f) → ∀ s : Spec R ⟶ S,
      Presieve.IsSheafFor F (Presieve.singleton
        (Over.homMk (U := Over.mk (Spec.map f ≫ s)) (V := Over.mk s) (Spec.map f) rfl))) :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S) F := by
  have htotal : Presieve.IsSheaf Scheme.fpqcTopology (totalPresheaf F) := by
    rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
    refine ⟨?_, ?_⟩
    · exact Presieve.isSheaf_of_le _
        (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
        (total_isSheaf F Scheme.fppfTopology hF)
    · intro R A f hf hs
      have := hf
      have := hs
      have hbase : Presieve.IsSheafFor (yoneda.obj S) (.singleton (Spec.map f)) :=
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
          (Precoverage.generate_mem_toGrothendieck (Spec.map f).singleton_mem_fpqcPrecoverage)
      rw [← Presieve.ofArrows_pUnit.{0}] at hbase ⊢
      apply total_isSheafFor F _ _ hbase
      intro s
      simpa only [Presieve.ofArrows_pUnit] using haff f hf hs s
  intro T R hR
  obtain ⟨I, U, v, hv⟩ := R.arrows.exists_eq_ofArrows
  have hcover : Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (v i).left) ∈
      Scheme.fpqcTopology T.left := by
    rw [← Sieve.overEquiv_ofArrows]
    simpa only [Sieve.ofArrows, ← hv, Sieve.generate_sieve] using
      (GrothendieckTopology.mem_over_iff _ _).mp hR
  rw [hv]
  apply relative_isSheafFor F T U v
  · exact ((GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      hcover).isSeparatedFor
  · exact htotal.isSheafFor _ hcover

end AlgebraicGeometry
