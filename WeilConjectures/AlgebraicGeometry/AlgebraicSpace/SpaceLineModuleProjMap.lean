/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLineModuleProjInput
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLineGenerationOpen
import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.GradedLineMap.SpaceLineTestMap
import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLineTestBaseChange

/-!
# The canonical relative-Proj map attached to a line module on an algebraic space

Source: Stacks Project, Divisors on Spaces, Tag 0D2Z, opening construction and parts
(2), (3); Constructions, Tag 01O9 (blueprint: lem-trf-space-line-module-proj-map).

`GradedAlgebraData` is the affine-basis presentation of the quasi-coherent graded
algebra used by the existing relative-Proj construction. Scheme tests describe the
small-etale graded map by its canonical tensor pullbacks; they also express arbitrary
base-change squares without assuming that those squares are Cartesian.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem existsUnique_space_line_canonical_map {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (hL : L.IsCoherent) (ψ : GradedLineMap f A L)
    (U : Subfunctor F) (hU : ψ.IsGenerationOpen U) :
    ∃! r : U.toFunctor ⟶ yoneda.obj (projOver T A), ψ.IsCanonicalMap U r := by
  classical
  let test (W : Over S) (a : U.toFunctor.obj (op W)) : SchemeTests F :=
    CostructuredArrow.mk (yonedaEquiv.symm a.val)
  have ht (W : Over S) (a : U.toFunctor.obj (op W)) :
      ψ.generationSet (test W a) = Set.univ := (hU W a.val).1 a.property
  choose q hq hu using fun W a ↦ existsUnique_space_line_test_map hL ψ (test W a) (ht W a)
  have hp {W V : SchemeTests F} (j : V ⟶ W) (r : W.left ⟶ projOver T A)
      (hr : ψ.IsCanonicalTestMap W r) : ψ.IsCanonicalTestMap V (j.left ≫ r) := by
    constructor
    · change j.left.left ≫ r.left ≫ A.relProjHom = _
      rw [hr.1]
      have he : j.left ≫ testToBase f W = testToBase f V := by
        apply yoneda.map_injective
        simp only [Functor.map_comp, testToBase, Functor.map_preimage, ← Category.assoc]
        rw [CostructuredArrow.w j]
      exact congrArg Over.Hom.left he
    · intro B k C h e α hα hi
      exact hr.2 B (k ≫ j) C h e α hα hi
  let r : U.toFunctor ⟶ yoneda.obj (projOver T A) :=
    { app W := ↾fun a ↦ q W.unop a
      naturality {W V} i := by
        ext a
        let j : test V.unop (U.toFunctor.map i a) ⟶ test W.unop a :=
          CostructuredArrow.homMk i.unop
            (yonedaEquiv_symm_naturality_left i.unop F a.val)
        exact (hu V.unop (U.toFunctor.map i a) (i.unop ≫ q W.unop a)
          (hp j _ (hq W.unop a))).symm }
  have hr : ψ.IsCanonicalMap U r := by
    constructor
    · intro W a
      exact (hq W a).1
    · intro W a C h e α hα hi
      change (q W a).left = _
      simpa only [CostructuredArrow.id_left, Over.id_left, Category.id_comp] using
        (hq W a).2 (test W a) (𝟙 _) C h e α hα hi
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  ext W a
  apply hu W.unop a
  constructor
  · exact hr'.1 W.unop a
  · intro V j C h e α hα hi
    let b : U.toFunctor.obj (op V.left) := U.toFunctor.map j.left.op a
    have hb : yonedaEquiv.symm b.val = V.hom := by
      change yonedaEquiv.symm (F.map j.left.op a.val) = V.hom
      rw [← yonedaEquiv_symm_naturality_left]
      exact CostructuredArrow.w j
    have hv := hr'.2 V.left b C
    have hn := r'.naturality_apply j.left.op a
    change r'.app (op V.left) b = j.left ≫ r'.app W a at hn
    rw [hn] at hv
    rw [hb] at hv
    exact hv h e α hα hi

private theorem space_line_proj_pullback {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (hL : L.IsCoherent) (ψ : GradedLineMap f A L)
    (U : Subfunctor F) (hU : ψ.IsGenerationOpen U)
    (r : U.toFunctor ⟶ yoneda.obj (projOver T A)) (hr : ψ.IsCanonicalMap U r)
    (X' T' : Over S) (g : T' ⟶ T) (f' : X' ⟶ T')
    (k : yoneda.obj X' ⟶ F) (hcomm : k ≫ f = yoneda.map f' ≫ yoneda.map g)
    (A' : T'.left.GradedAlgebraData)
    (D : Scheme.GradedAlgebraData.PullbackData g.left A A')
    (ψ' : GradedLineMap (yoneda.map f') A' (L.pullback k))
    (hψ' : ψ.IsBaseChange k g D ψ') :
    ψ'.IsGenerationOpen (U.preimage k) ∧
      ∃ r' : (U.preimage k).toFunctor ⟶ yoneda.obj (projOver T' A'),
        ψ'.IsCanonicalMap (U.preimage k) r' ∧
        ∀ (W : Over S) (a : (U.preimage k).toFunctor.obj (op W)),
          (r'.app (op W) a).left ≫ D.relProjComparison =
            (r.app (op W) ((U.fromPreimage k).app (op W) a)).left := by
  obtain ⟨hgen, hmap⟩ := space_line_test_base_change hL ψ k g hcomm D ψ' hψ'
  have hgen' : ψ'.IsGenerationOpen (U.preimage k) := by
    intro W a
    change k.app (op W) a ∈ U.obj (op W) ↔ _
    rw [hU W (k.app (op W) a), hgen]
    change _ ↔ ψ.generationSet
      (CostructuredArrow.mk (yonedaEquiv.symm a ≫ k)) = Set.univ
    rw [yonedaEquiv_symm_naturality_right]
  have hL' : (L.pullback k).IsCoherent := by
    constructor
    · intro W
      exact hL.1 ((CostructuredArrow.map k).obj W)
    · intro W V Z j l
      exact hL.2 _ _ _ ((CostructuredArrow.map k).map j)
        ((CostructuredArrow.map k).map l)
  obtain ⟨r', hr', _⟩ :=
    existsUnique_space_line_canonical_map hL' ψ' (U.preimage k) hgen'
  have ht {H : (Over S)ᵒᵖ ⥤ Type u} {B : Over S} {a : H ⟶ yoneda.obj B}
      {A₀ : B.left.GradedAlgebraData} {M : TestLineFamily H}
      (φ : GradedLineMap a A₀ M) (V : Subfunctor H)
      (t : V.toFunctor ⟶ yoneda.obj (projOver B A₀)) (ht : φ.IsCanonicalMap V t)
      (W : Over S) (b : V.toFunctor.obj (op W)) :
      φ.IsCanonicalTestMap (CostructuredArrow.mk (yonedaEquiv.symm b.val))
        (t.app (op W) b) := by
    constructor
    · exact ht.1 W b
    · intro Z j C h e α hα hi
      let c : V.toFunctor.obj (op Z.left) := V.toFunctor.map j.left.op b
      have hc : yonedaEquiv.symm c.val = Z.hom := by
        change yonedaEquiv.symm (H.map j.left.op b.val) = Z.hom
        rw [← yonedaEquiv_symm_naturality_left]
        exact CostructuredArrow.w j
      have hv := ht.2 Z.left c C
      have hn := t.naturality_apply j.left.op b
      change t.app (op Z.left) c = j.left ≫ t.app (op W) b at hn
      rw [hn, hc] at hv
      exact hv h e α hα hi
  refine ⟨hgen', r', hr', ?_⟩
  intro W a
  apply hmap (CostructuredArrow.mk (yonedaEquiv.symm a.val))
    ((hgen' W a.val).1 a.property)
  · change ψ.IsCanonicalTestMap
      (CostructuredArrow.mk (yonedaEquiv.symm a.val ≫ k)) _
    rw [yonedaEquiv_symm_naturality_right]
    exact ht ψ U r hr W ((U.fromPreimage k).app (op W) a)
  · exact ht ψ' (U.preimage k) r' hr' W a

/-- The positive-degree generation locus is an open algebraic subspace, and the graded
homomorphism determines its canonical morphism to relative Proj over the scheme base.
For every commutative square with scheme corners on the left, the generation locus is
the inverse image of this open, and the canonical maps commute with the unrestricted
relative-Proj base-change comparison. The `IsCanonicalMap` clause specifies the usual
scheme morphism on every trivializing scheme chart, including the scheme specialization.

Source: Stacks, Divisors on Spaces, Tag 0D2Z, opening construction and parts (2), (3);
Constructions, Tag 01O9 (blueprint: lem-trf-space-line-module-proj-map).

Proof:
1. Choose a representable surjective etale scheme atlas of X. Refine it by affine opens
lying above affine opens of T and by trivializations of L. The image of a homogeneous
section of positive degree is then an ordinary regular function. Its nonvanishing
locus is a principal open and is exactly where that image generates the tensor power
of L. Their union is the surjectivity locus of the homogeneous maps. On double
intersections the opens agree, since they are defined by the same pulled-back map.
They descend to an open subspace. The scheme-test condition IsGenerationOpen is this
same union, checked on every scheme mapping to X, including non-quasi-compact schemes.
2. On each principal open the homogeneous-fraction construction of Tag 01O9 gives the
map to the local Proj. The existing relative-Proj chart identifications identify these
targets with the restriction of A.relProj. After a common affine refinement the local
maps have the same fraction formulas, hence agree. Scheme morphism gluing followed by
the sheaf condition for the target descends them to r. The structural map to T agrees
on the atlas, so agrees globally. The chart formula in IsCanonicalMap fixes the map
on a cover; the jointly surjective atlas detects equality and proves uniqueness.
3. In an arbitrary commutative square with scheme source corners, pulling back the
line module, graded coefficients and their maps gives the same local functions.
Their nonvanishing loci pull back to their inverse images, with no flatness condition.
Thus IsGenerationOpen holds for U.preimage k. Apply the same chart construction to the
pulled-back graded homomorphism. The coefficientwise relative-Proj base-change datum
D gives the unrestricted comparison and its canonical isomorphism to the fibre
product. On the pulled-back affine charts the fraction formulas commute with
D.relProjComparison. Gluing gives the displayed equality of scheme maps. This is the
base-change compatibility under D.relProjIsoPullback, by its two projection identities.
4. For a scheme source, tensor pullback is Scheme.Modules.tensorPullback, and the
trivializing-chart equation is exactly Proj.fromOfGlobalSections followed by the
relative-Proj chart embedding. Hence the morphism is the usual scheme construction.
All arguments allow empty schemes, an empty generation locus, and graded algebras
with no positive-degree generators or with degree-zero piece different from O_T. -/
theorem space_line_module_proj_map (S : Scheme.{u}) (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T) (A : T.left.GradedAlgebraData)
    (L : X.Modules) (hL : X.IsLineModule L)
    (ψ : GradedLineMap f A (lineTestFamily X L hL)) :
    ∃ (U : Subfunctor X.obj.obj)
      (hU : Presheaf.IsSheaf (Scheme.fppfTopology.over S) U.toFunctor),
      IsAlgebraicSpace ⟨U.toFunctor, hU⟩ ∧
      IsRepresentableWith (fun _ _ j ↦ IsOpenImmersion j.left) U.ι ∧
      ψ.IsGenerationOpen U ∧
      ∃! r : U.toFunctor ⟶ yoneda.obj (projOver T A),
        ψ.IsCanonicalMap U r ∧
        ∀ (X' T' : Over S) (g : T' ⟶ T) (f' : X' ⟶ T')
          (k : yoneda.obj X' ⟶ X.obj.obj)
          (_hcomm : k ≫ f = yoneda.map f' ≫ yoneda.map g)
          (A' : T'.left.GradedAlgebraData)
          (D : Scheme.GradedAlgebraData.PullbackData g.left A A')
          (ψ' : GradedLineMap (yoneda.map f') A' ((lineTestFamily X L hL).pullback k)),
          ψ.IsBaseChange k g D ψ' →
            ψ'.IsGenerationOpen (U.preimage k) ∧
            ∃! r' : (U.preimage k).toFunctor ⟶ yoneda.obj (projOver T' A'),
              ψ'.IsCanonicalMap (U.preimage k) r' ∧
              ∀ (W : Over S) (a : (U.preimage k).toFunctor.obj (op W)),
                (r'.app (op W) a).left ≫ D.relProjComparison =
                  (r.app (op W) ((U.fromPreimage k).app (op W) a)).left  := by
  have hcoh : (lineTestFamily X L hL).IsCoherent :=
    (linePresentation X L hL).coherent
  obtain ⟨U, hU, hspace, hopen, hgen⟩ :=
    exists_space_line_generation_open T X f A (lineTestFamily X L hL) ψ
  obtain ⟨r, hr, huniq⟩ :=
    existsUnique_space_line_canonical_map hcoh ψ U hgen
  refine ⟨U, hU, hspace, hopen, hgen, r, ⟨hr, ?_⟩, ?_⟩
  · intro X' T' g f' k hcomm A' D ψ' hψ'
    obtain ⟨hgen', r', hr', hc⟩ :=
      space_line_proj_pullback hcoh ψ U hgen r hr X' T' g f' k hcomm A' D ψ' hψ'
    have hcoh' : ((lineTestFamily X L hL).pullback k).IsCoherent := by
      constructor
      · intro W
        exact hcoh.1 ((CostructuredArrow.map k).obj W)
      · intro W V Z j l
        exact hcoh.2 _ _ _ ((CostructuredArrow.map k).map j)
          ((CostructuredArrow.map k).map l)
    obtain ⟨r₀, hr₀, huniq'⟩ :=
      existsUnique_space_line_canonical_map hcoh' ψ' (U.preimage k) hgen'
    refine ⟨hgen', r', ⟨hr', hc⟩, ?_⟩
    intro r'' hr''
    exact (huniq' r'' hr''.1).trans (huniq' r' hr').symm
  · intro r' hr'
    exact huniq r' hr'.1


end AlgebraicGeometry.AlgebraicSpace
