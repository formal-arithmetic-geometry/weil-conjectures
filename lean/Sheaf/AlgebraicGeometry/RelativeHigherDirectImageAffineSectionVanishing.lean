/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageFiniteRawVanishing
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit

/-! # Eventual vanishing on an affine etale chart
Source: Stacks Project, Tag 0EYM, second proof, part (2). -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AbelianComparison.freeSheaf
  Functor.mapDerivedCategoryPlusHomologyFunctorIso

attribute [local irreducible] upperStar rightDerivedLowerStarPlus
  relativeHigherDirectImageExchange relativeHigherDirectImageDerivedMap

private theorem comparison_local_zero_sieve
    (S : Scheme.{u}) (q : ℤ)
    {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : K ⟶ L) (U : S.Etale)
    (x : ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.obj (op U))
    (hx : ((DerivedCategory.Plus.homologyFunctor _ q).map m).hom.app (op U) x = 0) :
    ∃ R : Sieve U, R ∈ S.smallEtaleTopology U ∧
      ∀ (V : S.Etale) (r : V ⟶ U), R r →
        ∃ z : ((derivedHomologySectionsFunctor S q).obj K).obj (op V),
          (derivedHomologySectionsComparison S q K).app (op V) z =
              ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map r.op x ∧
            ((derivedHomologySectionsFunctor S q).map m).app (op V) z = 0 := by
  let P := (derivedHomologySectionsFunctor S q).obj K
  let Q := (derivedHomologySectionsFunctor S q).obj L
  let ν := (derivedHomologySectionsFunctor S q).map m
  let τ := derivedHomologySectionsComparison S q K
  let υ := derivedHomologySectionsComparison S q L
  obtain ⟨_, hτ⟩ := (derivedHomologySectionsComparison_spec S q).1 K
  obtain ⟨hυ, _⟩ := (derivedHomologySectionsComparison_spec S q).1 L
  let R : Sieve U :=
    { arrows := fun V r ↦ ∃ z : P.obj (op V),
        τ.app (op V) z =
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map r.op x ∧
          ν.app (op V) z = 0
      downward_closed := by
        intro V W r hr g
        obtain ⟨z, hz, hm⟩ := hr
        refine ⟨P.map g.op z, ?_, ?_⟩
        · rw [NatTrans.naturality_apply, hz, op_comp,
            ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map_comp]
          rfl
        · rw [NatTrans.naturality_apply, hm, map_zero] }
  refine ⟨R, ?_, fun V r hr ↦ hr⟩
  apply S.smallEtaleTopology.transitive
    (Presheaf.imageSieve_mem S.smallEtaleTopology τ x) R
  intro V r hr
  obtain ⟨z, hz⟩ := hr
  have hy : υ.app (op V) (ν.app (op V) z) = υ.app (op V) 0 := by
    rw [map_zero, ← (derivedHomologySectionsComparison_spec S q).2, hz,
      NatTrans.naturality_apply, hx, map_zero]
  apply S.smallEtaleTopology.superset_covering _
    (Presheaf.equalizerSieve_mem S.smallEtaleTopology υ _ _ hy)
  intro W g hg
  refine ⟨P.map g.op z, ?_, ?_⟩
  · rw [NatTrans.naturality_apply, hz, op_comp,
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map_comp]
    rfl
  · change Q.map g.op (ν.app (op V) z) = Q.map g.op 0 at hg
    rw [NatTrans.naturality_apply]
    simpa only [map_zero] using hg

/-- A section on an affine etale test object whose limit image vanishes becomes
zero at a later stage. This concerns sections of a fixed chart, not arbitrary
stalks or the colimit comparison.
Source: Stacks Project, Tag 0EYM, second proof, part (2).
(blueprint: lem-kun-relative-higher-image-affine-section-vanishing).

Proof: At each point of the affine test scheme, choose a stage affine open of
the base containing its image, and restrict to its inverse images on a tail.
The pulled-back higher-image section locally comes from a stage higher-image
section, by the inverse-image construction. Lift this section locally to the
cohomology presheaf using 03Q8. Choose affine etale refinements and descend them
to a common later stage by 0EYL. Vanishing of the limit higher-image section
means that after a second etale refinement its representing cohomology class
is zero, by local injectivity of sheafification. Descend this further refinement
too; this second refinement is essential and cannot be omitted. The fibre
products of these charts with the source schemes are qcqs, have affine
transitions, and have the indicated fibre product as limit. Restriction and
inverse-image composition identify their coefficient colimit. Cohomology
continuity 09YQ then kills each of these cohomology classes at a finite stage.
The chart exchange identity and coefficient naturality identify the resulting
zero sections with H.map of the original section. The neighbourhoods so
obtained cover the affine test scheme. Its quasi-compactness gives a finite
subcover; directedness supplies one common later index. The naturality law hH
propagates all these zeros to that index, and the sheaf axiom gives global zero
on the test object. This uses only quasi-compactness of the affine test scheme,
not of its morphism to the possibly non-quasi-separated limit base. Empty
test objects and degree zero cause no exception. -/
theorem relativeHigherDirectImage_affine_section_eventually_zero
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DV.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DB.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cV : Cone DV) (hcV : IsLimit cV) (cB : Cone DB) (hcB : IsLimit cB)
    (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i : Iᵒᵖ, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DV.map a.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DV.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
          (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map b.op)).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i : I, A.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map (φ a) ≫ (eA j).inv)
    (cA : Cocone A) (hcA : IsColimit cA) (q : ℕ)
    (H : I ⥤ Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              (F i)))))
    (hH : ∀ (i j : I) (a : i ⟶ j), H.map a =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j)) (DB.map a.op)
          (cB.π.app (op i)) (cB.w a.op).symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                (F i)))) ≫
        (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op j))).map
          (relativeHigherDirectImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q) ≫
        (eH j).inv)
    (legs : H ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} v).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))))
    (hlegs : ∀ i : I, legs.app i = (eH i).hom ≫
      relativeHigherDirectImageExchange ⟨hu (op i)⟩ (F i) cA.pt
        ((eA i).inv ≫ cA.ι.app i) q)
    (W : cB.pt.Etale) [IsAffine W.left]
    (i : I) (z : (H.obj i).obj.obj (op W))
    (hz : (legs.app i).hom.app (op W) z = 0) :
    ∃ (j : I) (a : i ⟶ j), (H.map a).hom.app (op W) z = 0 := by
  classical
  let S := cB.pt
  let Kᵢ := (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).mapDerivedCategoryPlus.obj
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i))).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))
  let E : H.obj i ≅ (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj Kᵢ :=
    eH i ≪≫ relativeHigherDirectImageHomologyIso (η.app (op i))
      (cB.π.app (op i)) (F i) q
  let m := relativeHigherDirectImageDerivedMap ⟨hu (op i)⟩ (F i) cA.pt
    ((eA i).inv ≫ cA.ι.app i)
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  have hleg : legs.app i = E.hom ≫ Hq.map m := by
    rw [hlegs, relativeHigherDirectImageExchange_eq_homology]
    simp only [E, Hq, m, S, Iso.trans_hom, Category.assoc]
  have hx : (Hq.map m).hom.app (op W) (E.hom.hom.app (op W) z) = 0 := by
    change (E.hom ≫ Hq.map m).hom.app (op W) z = 0
    rw [← hleg]
    exact hz
  obtain ⟨R, hR, hlocal⟩ := comparison_local_zero_sieve S (q : ℤ) m W
    (E.hom.hom.app (op W) z) hx
  obtain ⟨n, V, r, hr, hV, hcover⟩ :=
    Scheme.exists_finite_affine_of_mem_smallEtaleTopology hR
  let J := ULift.{u} (Fin n)
  let _ : Fintype J := Fintype.ofFinite J
  let V' : J → S.Etale := fun t ↦ V t.down
  let r' : ∀ t, V' t ⟶ W := fun t ↦ r t.down
  let (t : J) : IsAffine (V' t).left := hV t.down
  have hraw : ∀ t : J, ∃ z₀ :
      ((derivedHomologySectionsFunctor S (q : ℤ)).obj Kᵢ).obj (op (V' t)),
      (derivedHomologySectionsComparison S (q : ℤ) Kᵢ).app (op (V' t)) z₀ =
        (Hq.obj Kᵢ).obj.map (r' t).op (E.hom.hom.app (op W) z) ∧
      ((derivedHomologySectionsFunctor S (q : ℤ)).map m).app (op (V' t)) z₀ = 0 := by
    intro t
    exact hlocal (V' t) (r' t) (hr t.down)
  choose z₀ hz₀ hzm using hraw
  obtain ⟨j, a, ha⟩ := relativeHigherDirectImage_finite_raw_eventually_zero
    DV DB η cV hcV cB hcB v hu F φ hφid hφcomp A eA hA cA hcA q H eH hH i
    J V' z₀ hzm
  have hsection : ∀ t : J,
      (H.map a).hom.app (op (V' t)) ((H.obj i).obj.map (r' t).op z) = 0 := by
    intro t
    have he : E.inv.hom.app (op (V' t))
        ((derivedHomologySectionsComparison S (q : ℤ) Kᵢ).app (op (V' t)) (z₀ t)) =
        (H.obj i).obj.map (r' t).op z := by
      rw [hz₀ t, ← NatTrans.naturality_apply E.hom.hom]
      change (E.hom ≫ E.inv).hom.app (op (V' t)) ((H.obj i).obj.map (r' t).op z) = _
      rw [Iso.hom_inv_id]
      rfl
    have ht := ha t
    change (H.map a).hom.app (op (V' t))
      (E.inv.hom.app (op (V' t))
        ((derivedHomologySectionsComparison S (q : ℤ) Kᵢ).app (op (V' t)) (z₀ t))) = 0 at ht
    rwa [he] at ht
  have hcover' : Sieve.ofArrows V' r' ∈ S.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r').2
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨t, y', hy'⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨ULift.up t, y', hy'⟩
  refine ⟨j, a, ?_⟩
  let G := H.obj j
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let G' := (sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj G
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 G'.property).isSeparated _ hcover').ext
  intro T g hg
  obtain ⟨t, l, rfl⟩ := (Sieve.mem_ofArrows_iff V' r' g).mp hg
  change G.obj.map (l ≫ r' t).op ((H.map a).hom.app (op W) z) =
    G.obj.map (l ≫ r' t).op 0
  rw [map_zero, op_comp, G.obj.map_comp]
  change G.obj.map l.op (G.obj.map (r' t).op ((H.map a).hom.app (op W) z)) = 0
  rw [← NatTrans.naturality_apply, hsection t, map_zero]

end AlgebraicGeometry.Etale
