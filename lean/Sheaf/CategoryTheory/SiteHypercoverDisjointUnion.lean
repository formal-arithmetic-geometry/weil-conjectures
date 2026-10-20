/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import Sheaf.CategoryTheory.FormalCoproductSheafRealization
import Sheaf.CategoryTheory.FormalCoproductSheafCoverEpi
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Disjoint unions of semirepresentable hypercovers

Source: Stacks Project, Hypercoverings, Tags 0DB1 and 0DB2, in the slice over `T`
(blueprint: lem-weil-pbc-site-hypercover-disjoint-union).

The helper characterizes matching arrows by their proper-face projections, independently of
choices of limits. In a slice category its degree-zero target is the identity of the base,
and its degree-one target is the fibre product over the base.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- An arrow is the proper-face matching arrow if its target, with the indicated projections,
is the boundary limit. Degree zero uses a terminal object, degree one a binary product,
and degree `n + 2` the recorded finite boundary diagram. In a slice these are the augmented
matching objects. The isomorphism in the last branch merely permits any choice of limit;
the equations specify the canonical arrow, rather than an arbitrary map to that limit.
Source: Stacks Project, Tags 0186, 0DB1 and 0DB2
(blueprint: lem-weil-pbc-site-hypercover-disjoint-union). -/
def IsProperFaceMatchingArrow {D : Type u} [Category.{v} D]
    (K : SimplicialObject D) (n : ℕ) (M : D) (μ : K _⦋n⦌ ⟶ M) : Prop :=
  match n with
  | 0 => Nonempty (IsTerminal M)
  | 1 => ∃ p : Fin 2 → (M ⟶ K _⦋0⦌),
      Nonempty (IsLimit (Fan.mk M p)) ∧ ∀ i : Fin 2, μ ≫ p i = K.δ i
  | n + 2 => ∃ c : Cone (matchingBoundaryIndex K n).multicospan,
      Nonempty (IsLimit c) ∧ ∃ e : M ≅ c.pt,
        ∀ i : Fin (n + 3), μ ≫ e.hom ≫ c.π.app (WalkingMulticospan.left i) = K.δ i

private def boundaryDiagramIso
    {D : Type u} [Category.{v} D] {E : Type*} [Category* E]
    (K : SimplicialObject D) (F : D ⥤ E) (L : SimplicialObject E)
    (e : K ⋙ F ≅ L) (n : ℕ) :
    (matchingBoundaryIndex K n).multicospan ⋙ F ≅
      (matchingBoundaryIndex L n).multicospan :=
  NatIso.ofComponents
    (fun j ↦ match j with
      | .left _ => e.app (Opposite.op ⦋n + 1⦌)
      | .right _ => e.app (Opposite.op ⦋n⦌))
    (by
      rintro _ _ (j | j | j)
      · simp
      · exact e.hom.naturality _
      · exact e.hom.naturality _)

private theorem exists_properFaceMatchingArrow
    {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (K : SimplicialObject D) (n : ℕ) :
    ∃ (M : D) (μ : K _⦋n⦌ ⟶ M), IsProperFaceMatchingArrow K n M μ := by
  classical
  rcases n with _ | _ | n
  · exact ⟨⊤_ D, terminal.from _, ⟨terminalIsTerminal⟩⟩
  · let c : Fan (fun _ : Fin 2 ↦ K _⦋0⦌) :=
      limit.cone (Discrete.functor (fun _ : Fin 2 ↦ K _⦋0⦌))
    have hc : Nonempty (IsLimit c) := ⟨limit.isLimit _⟩
    let μ : K _⦋1⦌ ⟶ c.pt := Fan.IsLimit.lift hc.some (fun i ↦ K.δ i)
    have hμ : ∀ i : Fin 2, μ ≫ c.proj i = K.δ i :=
      fun i ↦ Fan.IsLimit.fac hc.some _ i
    exact ⟨c.pt, μ, c.proj, hc, hμ⟩
  · let : Fintype (SimplicialObject.matchingBoundaryShape n).L :=
      inferInstanceAs (Fintype (Fin (n + 3)))
    let : Fintype (SimplicialObject.matchingBoundaryShape n).R :=
      inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
    let : DecidableEq (SimplicialObject.matchingBoundaryShape n).L :=
      inferInstanceAs (DecidableEq (Fin (n + 3)))
    let : DecidableEq (SimplicialObject.matchingBoundaryShape n).R :=
      inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
    let c : Multifork (SimplicialObject.matchingBoundaryIndex K n) :=
      Multiequalizer.multifork _
    have hc : Nonempty (IsLimit c) := ⟨limit.isLimit _⟩
    have hδ : ∀ p : (SimplicialObject.matchingBoundaryShape n).R,
        K.δ p.val.1 ≫ (SimplicialObject.matchingBoundaryIndex K n).fst p =
          K.δ p.val.2 ≫ (SimplicialObject.matchingBoundaryIndex K n).snd p := by
      rintro ⟨⟨a, b⟩, h⟩
      dsimp [SimplicialObject.matchingBoundaryIndex]
      have hb : b = (b.pred (Fin.ne_zero_of_lt h)).succ := (Fin.succ_pred _ _).symm
      have H : a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt)) ≤
          b.pred (Fin.ne_zero_of_lt h) := by
        rw [Fin.le_iff_val_le_val]
        have h' : a.val < b.val := h
        simp only [Fin.val_castLT, Fin.val_pred]
        omega
      have hface := (SimplicialObject.δ_comp_δ K H).symm
      rw [← hb] at hface
      exact hface
    let μ : K _⦋n + 2⦌ ⟶ c.pt :=
      Multifork.IsLimit.lift hc.some (fun i ↦ K.δ i) hδ
    have hμ : ∀ i : Fin (n + 3),
        μ ≫ c.π.app (WalkingMulticospan.left i) = K.δ i :=
      fun i ↦ Multifork.IsLimit.fac hc.some _ hδ i
    exact ⟨c.pt, μ, c, hc, Iso.refl _, by simpa using hμ⟩

private theorem matching_epi_transport
    {D : Type u} [Category.{v} D] {E : Type*} [Category* E]
    (K : SimplicialObject D) (F : D ⥤ E) [PreservesFiniteLimits F]
    (L : SimplicialObject E) (e : K ⋙ F ≅ L)
    (n : ℕ) (B : D) (κ : K _⦋n⦌ ⟶ B)
    (hκ : IsProperFaceMatchingArrow K n B κ) [Epi (F.map κ)]
    (M : E) (μ : L _⦋n⦌ ⟶ M) (hμ : IsProperFaceMatchingArrow L n M μ) :
    Epi μ := by
  classical
  rcases n with _ | _ | n
  · obtain ⟨hB⟩ := hκ
    obtain ⟨hM⟩ := hμ
    let b : F.obj B ≅ M := (hB.isTerminalObj F).uniqueUpToIso hM
    have h : μ = (e.app (Opposite.op ⦋0⦌)).inv ≫ F.map κ ≫ b.hom := hM.hom_ext _ _
    rw [h]
    infer_instance
  · obtain ⟨p, ⟨hp⟩, hκ⟩ := hκ
    obtain ⟨q, ⟨hq⟩, hμ⟩ := hμ
    let c := Fan.mk (F.obj B) (fun i ↦ F.map (p i))
    let hc : IsLimit c := isLimitFanMkObjOfIsLimit F _ p hp
    let ei : Discrete.functor (fun _ : Fin 2 ↦ F.obj (K _⦋0⦌)) ≅
        Discrete.functor (fun _ : Fin 2 ↦ L _⦋0⦌) :=
      Discrete.natIso (fun _ ↦ e.app (Opposite.op ⦋0⦌))
    let d := (Cone.postcompose ei.hom).obj c
    let hd : IsLimit d := (IsLimit.postcomposeHomEquiv _ c).symm hc
    let b := hd.conePointUniqueUpToIso hq
    have h : μ = (e.app (Opposite.op ⦋1⦌)).inv ≫ F.map κ ≫ b.hom := by
      apply Fan.IsLimit.hom_ext hq
      intro i
      change μ ≫ q i = ((e.app (Opposite.op ⦋1⦌)).inv ≫ F.map κ ≫ b.hom) ≫
        (Fan.mk M q).π.app ⟨i⟩
      rw [hμ i]
      simp only [Category.assoc, b, IsLimit.conePointUniqueUpToIso_hom_comp]
      change L.δ i = (e.app (Opposite.op ⦋1⦌)).inv ≫ F.map κ ≫ F.map (p i) ≫
        (e.app (Opposite.op ⦋0⦌)).hom
      rw [← F.map_comp_assoc, hκ i]
      have he := e.hom.naturality (SimplexCategory.δ i).op
      simpa only [Functor.comp_map, δ, Iso.app_hom, Iso.app_inv,
        Iso.inv_hom_id_app_assoc] using
        congrArg (fun f ↦ (e.app (Opposite.op ⦋1⦌)).inv ≫ f) he.symm
    rw [h]
    infer_instance
  · let : Fintype (matchingBoundaryShape n).L := by
      dsimp [matchingBoundaryShape]; infer_instance
    let : Fintype (matchingBoundaryShape n).R := by
      dsimp [matchingBoundaryShape]; infer_instance
    obtain ⟨c, ⟨hc⟩, ec, hκ⟩ := hκ
    obtain ⟨d, ⟨hd⟩, ed, hμ⟩ := hμ
    let c' := (Cone.postcompose (boundaryDiagramIso K F L e n).hom).obj (F.mapCone c)
    let hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv _ _).symm
      (isLimitOfPreserves F hc)
    let b := hc'.conePointUniqueUpToIso hd
    have h : μ ≫ ed.hom =
        (e.app (Opposite.op ⦋n + 2⦌)).inv ≫ F.map κ ≫ F.map ec.hom ≫ b.hom := by
      apply Multifork.IsLimit.hom_ext hd
      intro i
      change Fin (n + 3) at i
      change (μ ≫ ed.hom) ≫ d.π.app (.left i) =
        ((e.app (Opposite.op ⦋n + 2⦌)).inv ≫ F.map κ ≫ F.map ec.hom ≫
          b.hom) ≫ d.π.app (.left i)
      rw [Category.assoc, hμ i]
      simp only [Category.assoc, b, IsLimit.conePointUniqueUpToIso_hom_comp]
      change L.δ i = (e.app (Opposite.op ⦋n + 2⦌)).inv ≫ F.map κ ≫ F.map ec.hom ≫
        F.map (c.π.app (.left i)) ≫ (e.app (Opposite.op ⦋n + 1⦌)).hom
      rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hκ i]
      have he := e.hom.naturality (SimplexCategory.δ i).op
      simpa only [Functor.comp_map, δ, Iso.app_hom, Iso.app_inv,
        Iso.inv_hom_id_app_assoc] using
        congrArg (fun f ↦ (e.app (Opposite.op ⦋n + 2⦌)).inv ≫ f) he.symm
    have h' : μ = ((e.app (Opposite.op ⦋n + 2⦌)).inv ≫ F.map κ ≫
        F.map ec.hom ≫ b.hom) ≫ ed.inv := by
      rw [← h]
      simp
    rw [h']
    infer_instance

/-- Taking the disjoint unions of the terms of a semirepresentable hypercover over `T`
gives a simplicial object over `T` whose representable-sheaf matching arrows are epimorphisms.
The cofans specify the given coproducts. Their Yoneda-image cofans being colimiting is
exactly the hypothesis that the canonical sheaf-coproduct maps are isomorphisms. The
isomorphisms `e` identify the constructed simplicial terms with those specified coproducts;
the component equations say that every operator is the one induced by disjoint union.
Source: Stacks Project, Hypercoverings, Tags 0DB1 and 0DB2, in the slice over `T`
(blueprint: lem-weil-pbc-site-hypercover-disjoint-union).

Proof: (1) Use each coproduct universal property to induce every simplicial operator from
its component maps. Equality on all summands gives identity, composition and augmentation.
(2) Formal coproducts over `T` have finite limits
[lem-weil-pbc-semi-representable-finite-limits]. Realization as coproducts of representable
sheaves preserves finite limits [lem-weil-pbc-formal-coproduct-sheaf-finite-limits], hence
preserves matching cones [lem-weil-pbc-simplicial-matching-object].
(3) Componentwise covers become epimorphisms
[lem-weil-pbc-formal-coproduct-sheaf-cover-epi]: equality of maps out of the target is tested
on each representable summand, where sheaf separatedness reduces it to equality on the
covering source summands. This includes degree zero and empty covering families.
(4) The assumed canonical coproduct isomorphisms commute
with all operators because they agree on each representable summand. The induced
isomorphisms of matching limits commute with their projections; conjugating the epi matching
arrows by these isomorphisms proves the conclusion. At degree zero the target is `h_T`,
and at degree one it is `h_A₀ ×[h_T] h_A₀`. -/
theorem site_hypercover_disjoint_union
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (T : C) (K : SimplicialObject (FormalCoproduct.{u} (Over T)))
    (hcover : ∀ (n : ℕ) (M : FormalCoproduct.{u} (Over T)) (μ : K _⦋n⦌ ⟶ M),
      IsProperFaceMatchingArrow K n M μ →
        ∀ j : M.I,
          Presieve.ofArrows
            (fun i : {i : (K _⦋n⦌).I // μ.f i = j} => ((K _⦋n⦌).obj i.val).left)
            (fun i => (μ.φ i.val ≫ eqToHom (congrArg M.obj i.property)).left) ∈
              J (M.obj j).left)
    (a : ∀ n : ℕ, Cofan (K _⦋n⦌).obj)
    (ha : ∀ n : ℕ, IsColimit (a n))
    (hsheaf : ∀ n : ℕ,
      IsColimit (Cofan.mk (J.toGrothendieck.yoneda.obj (a n).pt.left)
        (fun i : (K _⦋n⦌).I => J.toGrothendieck.yoneda.map ((a n).inj i).left))) :
    ∃ A : SimplicialObject (Over T), ∃ e : ∀ n : ℕ, A _⦋n⦌ ≅ (a n).pt,
      (∀ (m n : ℕ) (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
        (i : (K _⦋n⦌).I),
        (a n).inj i ≫ (e n).inv ≫ A.map φ.op ≫ (e m).hom =
          (K.map φ.op).φ i ≫ (a m).inj ((K.map φ.op).f i)) ∧
      (∀ (n : ℕ) (M : Over (J.toGrothendieck.yoneda.obj T))
        (μ : (A ⋙ Over.post J.toGrothendieck.yoneda) _⦋n⦌ ⟶ M),
        IsProperFaceMatchingArrow (A ⋙ Over.post J.toGrothendieck.yoneda) n M μ →
          Epi μ.left) := by
  let A : SimplicialObject (Over T) :=
    { obj := fun n ↦ (a n.unop.len).pt
      map := fun {n m} φ ↦ (ha n.unop.len).desc
        (Cofan.mk (a m.unop.len).pt
          (fun i ↦ (K.map φ).φ i ≫ (a m.unop.len).inj ((K.map φ).f i)))
      map_id := by
        intro n
        apply Cofan.IsColimit.hom_ext (ha n.unop.len)
        intro i
        simp only [Cofan.IsColimit.inj_desc]
        change (K.map (𝟙 n)).φ i ≫ _ = _
        rw [K.map_id]
        simp
      map_comp := by
        intro n m l φ ψ
        apply Cofan.IsColimit.hom_ext (ha n.unop.len)
        intro i
        simp only [Cofan.IsColimit.inj_desc]
        change (K.map (φ ≫ ψ)).φ i ≫ _ = _
        rw [K.map_comp]
        simp [Category.assoc] }
  let F := FormalCoproduct.sheafRealization J.toGrothendieck T
  let : PreservesFiniteLimits F :=
    FormalCoproduct.sheafRealization_preservesFiniteLimits _ _
  let b (n : ℕ) : F.obj (K _⦋n⦌) ≅
      (Over.post J.toGrothendieck.yoneda).obj (a n).pt :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso
      (FormalCoproduct.isColimitSheafCofan _ _ _ (hsheaf n))
  have hb (n : ℕ) (i : (K _⦋n⦌).I) :
      Sigma.ι (fun i ↦ (Over.post J.toGrothendieck.yoneda).obj ((K _⦋n⦌).obj i)) i ≫
        (b n).hom = (Over.post J.toGrothendieck.yoneda).map ((a n).inj i) := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct _)
      (FormalCoproduct.isColimitSheafCofan _ _ _ (hsheaf n)) (Discrete.mk i)
  let e : K ⋙ F ≅ A ⋙ Over.post J.toGrothendieck.yoneda :=
    NatIso.ofComponents (fun n ↦ b n.unop.len) (by
      intro n m φ
      rcases n with ⟨⟨n⟩⟩
      rcases m with ⟨⟨m⟩⟩
      apply Sigma.hom_ext
      intro i
      simp only [Functor.comp_map, F, FormalCoproduct.sheafRealization,
        FormalCoproduct.eval_obj_map, Sigma.ι_desc_assoc, Function.comp_def, Category.assoc]
      rw [hb m]
      rw [← Category.assoc, hb n]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp [A])
  refine ⟨A, fun n ↦ Iso.refl _, ?_, ?_⟩
  · intro m n φ i
    simp [A]
  · intro n M μ hμ
    have : HasFiniteLimits (FormalCoproduct.{u} (Over T)) :=
      hasFiniteLimits_of_hasTerminal_and_pullbacks
    obtain ⟨B, κ, hκ⟩ := exists_properFaceMatchingArrow K n
    have : Epi (F.map κ) := FormalCoproduct.sheafRealization_map_epi J κ
      (hcover n B κ hκ)
    have : Epi μ := matching_epi_transport K F _ e n B κ hκ M μ hμ
    exact Over.epi_left_of_epi μ

end CategoryTheory.SimplicialObject
