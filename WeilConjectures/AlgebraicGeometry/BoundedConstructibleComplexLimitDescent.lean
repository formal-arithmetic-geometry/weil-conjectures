/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.ConstructibleLimitDescentGeneral
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleEventualHomLift
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Int.Interval

/-!
# Descent of bounded complexes of constructible sheaves along surjective limits

Source: Stacks Project, Lemma 09YU (3), proof, essential surjectivity.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A morphism `t^* F ⟶ t^* G` at a stage which is compatible, through the composition
isomorphisms, with a morphism `φ` on the limit remains compatible after pulling back along a
further transition.

Source: Stacks Project, Lemma 09YU (3), proof (enlarging the stage). -/
lemma exists_upperStar_map_comp_inv_app_eq_of_comp {Z S S' S'' : Scheme.{u}}
    (pi : Z ⟶ S) (pj : Z ⟶ S') (pk : Z ⟶ S'') (tij : S' ⟶ S) (tjk : S'' ⟶ S') (tik : S'' ⟶ S)
    (hij : pi = pj ≫ tij) (hjk : pj = pk ≫ tjk) (hik : pi = pk ≫ tik) (htik : tik = tjk ≫ tij)
    (F G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : (upperStar (ModuleCat.{u + 1} Λ) pi).obj F ⟶ (upperStar (ModuleCat.{u + 1} Λ) pi).obj G)
    (a : (upperStar (ModuleCat.{u + 1} Λ) tij).obj F ⟶ (upperStar (ModuleCat.{u + 1} Λ) tij).obj G)
    (ha : (upperStar (ModuleCat.{u + 1} Λ) pj).map a ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) pj tij pi hij).inv.app G =
      (upperStarComp (ModuleCat.{u + 1} Λ) pj tij pi hij).inv.app F ≫ φ) :
    ∃ a' : (upperStar (ModuleCat.{u + 1} Λ) tik).obj F ⟶
        (upperStar (ModuleCat.{u + 1} Λ) tik).obj G,
      (upperStar (ModuleCat.{u + 1} Λ) pk).map a' ≫
          (upperStarComp (ModuleCat.{u + 1} Λ) pk tik pi hik).inv.app G =
        (upperStarComp (ModuleCat.{u + 1} Λ) pk tik pi hik).inv.app F ≫ φ := by
  subst htik hjk
  have hA := upperStarComp_assoc (ModuleCat.{u + 1} Λ) pk tjk tij pi hik
  have h₁ := congrArg (fun e ↦ e.hom.app F) hA
  have h₂ := congrArg (fun e ↦ e.inv.app G) hA
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp] at h₁ h₂
  refine ⟨(upperStarComp (ModuleCat.{u + 1} Λ) tjk tij).hom.app F ≫
    (upperStar (ModuleCat.{u + 1} Λ) tjk).map a ≫
    (upperStarComp (ModuleCat.{u + 1} Λ) tjk tij).inv.app G, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h₂,
    ← Functor.comp_map, (upperStarComp (ModuleCat.{u + 1} Λ) pk tjk).inv.naturality_assoc, ha,
    ← cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) pk (tjk ≫ tij) pi
      hik).hom.app F), reassoc_of% h₁]
  simp

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open ZeroObject

/-- The finitely many nonzero terms of a strictly bounded complex of constructible sheaves on
the limit of a directed inverse system of qcqs schemes with affine transitions descend to
constructible sheaves at a common stage; the other terms are replaced by zero.

Source: Stacks Project, Lemma 09YU (3), proof, essential surjectivity. -/
lemma exists_stage_constructible_terms
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (P : CochainComplex (Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ q, IsConstructibleSheaf (P.X q)) :
    ∃ (j : I) (X : ℤ → Sheaf (D.obj (op j)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ q, IsConstructibleSheaf (X q)) ∧ (∀ q, q < a ∨ b < q → IsZero (X q)) ∧
      ∀ q, Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op j))).obj (X q) ≅
        P.X q) := by
  classical
  have hin : ∀ q ∈ Finset.Icc a b, ∀ᶠ k in Filter.atTop,
      ∃ X : Sheaf (D.obj (op k)).smallEtaleTopology (ModuleCat.{u + 1} Λ),
        IsConstructibleSheaf X ∧ (q < a ∨ b < q → IsZero X) ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).obj X ≅ P.X q) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have := hP q
    obtain ⟨i, F, hF, ⟨e⟩⟩ := exists_constructible_limit_descent_general D c hc Λ (P.X q)
    refine Filter.eventually_atTop.2 ⟨i, fun k hik ↦ ?_⟩
    refine ⟨(Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE hik).op)).obj F,
      IsConstructibleSheaf.upperStar _ F, fun h ↦ by omega,
      ⟨((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE hik).op)
        (c.π.app (op i)) (c.w (homOfLE hik).op).symm).app F).symm ≪≫ e⟩⟩
  have hout : ∀ᶠ k in Filter.atTop, ∀ q ∉ Finset.Icc a b,
      ∃ X : Sheaf (D.obj (op k)).smallEtaleTopology (ModuleCat.{u + 1} Λ),
        IsConstructibleSheaf X ∧ (q < a ∨ b < q → IsZero X) ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).obj X ≅ P.X q) := by
    refine Filter.Eventually.of_forall fun k q hq ↦ ⟨0,
      IsConstructibleSheaf.of_isZero (isZero_zero _), fun _ ↦ isZero_zero _,
      ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero _)) ?_⟩⟩
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
    rcases hq with hq | hq
    · exact P.isZero_of_isStrictlyGE a q hq
    · exact P.isZero_of_isStrictlyLE b q hq
  obtain ⟨k, hk₁, hk₂⟩ := (((Filter.eventually_all_finset _).2 hin).and hout).exists
  have hall (q : ℤ) : ∃ X : Sheaf (D.obj (op k)).smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsConstructibleSheaf X ∧ (q < a ∨ b < q → IsZero X) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).obj X ≅ P.X q) :=
    if hq : q ∈ Finset.Icc a b then hk₁ q hq else hk₂ q hq
  choose X hX using hall
  exact ⟨k, X, fun q ↦ (hX q).1, fun q ↦ (hX q).2.1, fun q ↦ (hX q).2.2⟩

/-- Let `X` be a family of constructible sheaves at a stage `j` of a directed inverse system
with surjective limit projections, zero outside `[a, b]`, whose pullbacks to the limit are the
terms of a complex `P`. Then the differentials of `P` descend, after pulling back `X` to a later
stage `k`, compatibly with the composition isomorphisms.

Source: Stacks Project, Lemma 09YU (3), proof, essential surjectivity (descent of the finitely
many differentials using full faithfulness). -/
lemma exists_stage_differentials
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (hsurj : ∀ i, Function.Surjective (c.π.app i).base)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (P : CochainComplex (Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    (j : I) (X : ℤ → Sheaf (D.obj (op j)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ q, IsConstructibleSheaf (X q)] (hX : ∀ q, q < a ∨ b < q → IsZero (X q))
    (e : ∀ q, (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op j))).obj (X q) ≅ P.X q) :
    ∃ (k : I) (h : j ≤ k)
      (d : ∀ q, (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj (X q) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj (X (q + 1))),
      ∀ q, (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).map (d q) ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
            (c.π.app (op j)) (c.w (homOfLE h).op).symm).inv.app (X (q + 1)) =
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
            (c.π.app (op j)) (c.w (homOfLE h).op).symm).inv.app (X q) ≫
          (e q).hom ≫ P.d q (q + 1) ≫ (e (q + 1)).inv := by
  classical
  have hin : ∀ q ∈ Finset.Icc a b, ∀ᶠ k in Filter.atTop, ∀ h : j ≤ k,
      ∃ d : (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj (X q) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj (X (q + 1)),
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).map d ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
            (c.π.app (op j)) (c.w (homOfLE h).op).symm).inv.app (X (q + 1)) =
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
            (c.π.app (op j)) (c.w (homOfLE h).op).symm).inv.app (X q) ≫
          (e q).hom ≫ P.d q (q + 1) ≫ (e (q + 1)).inv := by
    intro q _
    obtain ⟨k₀, h₀, d₀, hd₀⟩ := exists_constructible_etaleModule_eventual_hom_lift D c hc hsurj
      Λ j (X q) (X (q + 1)) ((e q).hom ≫ P.d q (q + 1) ≫ (e (q + 1)).inv)
    refine Filter.eventually_atTop.2 ⟨k₀, fun k hk h ↦ ?_⟩
    exact Etale.exists_upperStar_map_comp_inv_app_eq_of_comp Λ (c.π.app (op j))
      (c.π.app (op k₀)) (c.π.app (op k)) (D.map (homOfLE h₀).op) (D.map (homOfLE hk).op)
      (D.map (homOfLE h).op) (c.w _).symm (c.w _).symm (c.w _).symm
      (by rw [← D.map_comp]; rfl) _ _ _ d₀ hd₀
  have hout : ∀ᶠ k in Filter.atTop, ∀ q ∉ Finset.Icc a b, ∀ h : j ≤ k,
      ∃ d : (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj (X q) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj (X (q + 1)),
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).map d ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
            (c.π.app (op j)) (c.w (homOfLE h).op).symm).inv.app (X (q + 1)) =
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
            (c.π.app (op j)) (c.w (homOfLE h).op).symm).inv.app (X q) ≫
          (e q).hom ≫ P.d q (q + 1) ≫ (e (q + 1)).inv := by
    refine Filter.Eventually.of_forall fun k q hq h ↦ ⟨0, ?_⟩
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
    exact (Functor.map_isZero _ (Functor.map_isZero _ (hX q hq))).eq_of_src _ _
  obtain ⟨k, ⟨hk₁, hk₂⟩, hjk⟩ :=
    ((((Filter.eventually_all_finset _).2 hin).and hout).and (Filter.eventually_ge_atTop j)).exists
  have hall (q : ℤ) :
      ∃ d : (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE hjk).op)).obj (X q) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE hjk).op)).obj (X (q + 1)),
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))).map d ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE hjk).op)
            (c.π.app (op j)) (c.w (homOfLE hjk).op).symm).inv.app (X (q + 1)) =
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE hjk).op)
            (c.π.app (op j)) (c.w (homOfLE hjk).op).symm).inv.app (X q) ≫
          (e q).hom ≫ P.d q (q + 1) ≫ (e (q + 1)).inv :=
    if hq : q ∈ Finset.Icc a b then hk₁ q hq hjk else hk₂ q hq hjk
  choose d hd using hall
  exact ⟨k, hjk, d, hd⟩

/-- **Descent of bounded complexes of constructible sheaves.** Let `D` be a directed inverse
system of qcqs schemes with affine transitions, `c` a limit cone whose projections are
surjective, and `Λ` Noetherian. A complex `P` of constructible sheaves on the limit, strictly
concentrated in degrees `[a, b]`, is the termwise pullback of a complex of constructible sheaves
at some stage, strictly concentrated in the same degrees.

Source: Stacks Project, Lemma 09YU (3), proof, essential surjectivity.

Proof: descend the finitely many nonzero terms to a common stage
(`exists_stage_constructible_terms`), then the finitely many differentials to a later stage
(`exists_stage_differentials`). The squares of the descended differentials vanish because the
pullback along the surjective projection is faithful, and the termwise comparison isomorphisms
commute with the differentials by construction. -/
theorem exists_boundedComplex_constructible_limit_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (hsurj : ∀ i, Function.Surjective (c.π.app i).base)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (P : CochainComplex (Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ q, IsConstructibleSheaf (P.X q)) :
    ∃ (i : I) (Pᵢ : CochainComplex (Sheaf (D.obj (op i)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) ℤ),
      Pᵢ.IsStrictlyGE a ∧ Pᵢ.IsStrictlyLE b ∧ (∀ q, IsConstructibleSheaf (Pᵢ.X q)) ∧
        Nonempty (((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Pᵢ ≅ P) := by
  obtain ⟨j, X, hXc, hXz, he⟩ := exists_stage_constructible_terms D c hc Λ P a b hP
  let e q := (he q).some
  obtain ⟨k, h, d, hd⟩ := exists_stage_differentials D c hc hsurj Λ P a b j X hXz e
  let Φ := Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op k))
  let E := Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op k)) (D.map (homOfLE h).op)
    (c.π.app (op j)) (c.w (homOfLE h).op).symm
  have := Etale.faithful_upperStar_of_surjective Λ (c.π.app (op k)) (hsurj _)
  have sq (q : ℤ) : d q ≫ d (q + 1) = 0 := by
    apply Φ.map_injective
    rw [Functor.map_comp, Functor.map_zero, ← cancel_mono (E.inv.app (X (q + 1 + 1))),
      Category.assoc, hd, reassoc_of% (hd q)]
    simp
  refine ⟨k, CochainComplex.of _ d sq,
    (CochainComplex.isStrictlyGE_iff _ a).2 fun q hq ↦
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map_isZero (hXz q (.inl hq)),
    (CochainComplex.isStrictlyLE_iff _ b).2 fun q hq ↦
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map_isZero (hXz q (.inr hq)),
    fun q ↦ IsConstructibleSheaf.upperStar _ (X q),
    ⟨HomologicalComplex.Hom.isoOfComponents (fun q ↦ (E.app (X q)).symm ≪≫ e q) ?_⟩⟩
  rintro q _ rfl
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
    Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
  rw [reassoc_of% (hd q)]
  simp [E]

end AlgebraicGeometry.Scheme
