/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.ComponentRelativeProfiniteSite
public import Sheaf.RingTheory.StoneanCoverSecondStage
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Sheaf.Paper.CommonStoneanHypercoverExistence
import Sheaf.Paper.CommonComponentHypercoverSingleLift
import Sheaf.AlgebraicGeometry.StalkIsomorphismLifting

/-!
# Compatible hypercovers over a common component space

Source: Hemo--Richarz--Scholbach, before (4.1) and Proposition 4.3(1);
Bhatt--Scholze, Lemmas 2.2.8 and 2.4.8, Example 2.4.6; Stacks, Tags 0DAV and 097D.
(blueprint: lem-sfb-wstrict-common-component-hypercovers).

The auxiliary predicates only package the matching cones and the conclusion for
one of the two bases. Ring models use the existing clopen-restriction and
finite-partition diagrams; their comparison is normalized on finite-stage functions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial

namespace AlgebraicGeometry.ProEtale

/-- The component augmentation in affine-spectrum coordinates.
Source: Bhatt--Scholze, Lemma 2.2.8; Stacks, Tag 097D.
(blueprint: lem-sfb-wstrict-common-component-hypercovers). -/
def commonHypercoverBaseMap (T : Scheme.{u}) [IsAffine T]
    {P : Profinite.{u}} (a : P ≃ₜ ConnectedComponents T) (E : Over P) :
    C(E.left, ConnectedComponents (PrimeSpectrum Γ(T, ⊤))) :=
  ⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap (a (E.hom s)),
    T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
      (a.continuous.comp E.hom.hom.hom.continuous)⟩

/-- Matching cones, including the degree-zero base, for a profinite hypercover.
Source: Stacks, Tag 0DAV, and proper-face matching objects, Tag 0186.
(blueprint: lem-sfb-wstrict-common-component-hypercovers). -/
def IsCommonProfiniteHypercover {P : Profinite.{u}}
    (S : SimplicialObject (Over P)) : Prop :=
  ∃ (M : ∀ n : ℕ, Cone (S.properFaceDiagram n))
    (μ : ∀ n : ℕ, S _⦋n⦌ ⟶ (M n).pt),
    (M 0).pt = Over.mk (𝟙 P) ∧
    (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
    (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
      μ n ≫ (M n).π.app (op b) = S.map b.obj.hom.op) ∧
    (∀ n : ℕ, Function.Surjective (μ n).left) ∧
    (∀ n : ℕ, ExtremallyDisconnected (S _⦋n⦌).left) ∧
    (∀ n : ℕ, Function.Surjective (S _⦋n⦌).hom)

/-- The full conclusion for one lifted hypercover. The pullback homeomorphism and
stalk isomorphisms specify the inverse-image locally ringed space, hence the relative
component lift of `component_relative_profinite_site`. The finite-stage normalization
specifies the canonical comparison with the displayed partition colimit, over both
base and profinite space.

Source: Bhatt--Scholze, Lemmas 2.2.8 and 2.4.8; Stacks, Tag 097D.
(blueprint: lem-sfb-wstrict-common-component-hypercovers). -/
def IsCommonComponentHypercoverLift (T : Scheme.{u}) [IsAffine T]
    {P : Profinite.{u}} (a : P ≃ₜ ConnectedComponents T)
    (S : SimplicialObject (Over P)) (U : SimplicialObject T.ProEt)
    (p : ∀ n : ℕ, C((U _⦋n⦌).left, (S _⦋n⦌).left)) : Prop :=
  (∃ (M : ∀ n : ℕ, Cone (U.properFaceDiagram n))
      (μ : ∀ n : ℕ, U _⦋n⦌ ⟶ (M n).pt),
    (M 0).pt = Scheme.ProEt.mk (𝟙 T) ∧
    (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
    (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
      μ n ≫ (M n).π.app (op b) = U.map b.obj.hom.op) ∧
    (∀ n : ℕ, Presieve.singleton (μ n) ∈ Scheme.ProEt.precoverage T (M n).pt)) ∧
  (∀ n : ℕ, IsAffine (U _⦋n⦌).left ∧
    IsWContractibleRing Γ((U _⦋n⦌).left, ⊤) ∧
    (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} (U _⦋n⦌)) ∧
  (∀ (m n : SimplexCategoryᵒᵖ) (f : m ⟶ n) (x : (U.obj m).left),
    p n.unop.len ((U.map f).left x) = (S.map f).left (p m.unop.len x)) ∧
  (∀ n : ℕ, (∀ x : (U _⦋n⦌).left, IsIso ((U _⦋n⦌).hom.stalkMap x)) ∧
    (∃ H : (U _⦋n⦌).left ≃ₜ
        {z : T × (S _⦋n⦌).left | ConnectedComponents.mk z.1 = a ((S _⦋n⦌).hom z.2)},
      (∀ x, (H x).val.1 = (U _⦋n⦌).hom x) ∧ (∀ x, (H x).val.2 = p n x)) ∧
    (∃ c : ConnectedComponents (U _⦋n⦌).left ≃ₜ (S _⦋n⦌).left,
      ∀ x : (U _⦋n⦌).left, c (ConnectedComponents.mk x) = p n x) ∧
    (∃ c : closedPoints (U _⦋n⦌).left ≃ₜ (S _⦋n⦌).left,
      ∀ x : closedPoints (U _⦋n⦌).left, c x = p n x.val)) ∧
  (∀ n : ℕ,
    ∃ (e : (colimit (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
          (commonHypercoverBaseMap T a (S _⦋n⦌))) : CommAlgCat Γ(T, ⊤)) ≃ₐ[Γ(T, ⊤)]
        WContractification.PullbackProfinite Γ(T, ⊤) (S _⦋n⦌).left
          (commonHypercoverBaseMap T a (S _⦋n⦌)))
      (k : (U _⦋n⦌).left ≅ Spec (.of
        (colimit (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
          (commonHypercoverBaseMap T a (S _⦋n⦌))) : CommAlgCat Γ(T, ⊤)))),
      (∀ (Q : DiscreteQuotient (S _⦋n⦌).left) (r : Q → Γ(T, ⊤)),
        e ((colimit.ι (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
            (commonHypercoverBaseMap T a (S _⦋n⦌))) (op Q)).hom
              (fun b ↦ algebraMap Γ(T, ⊤) _ (r b))) =
          algebraMap (LocallyConstant (S _⦋n⦌).left Γ(T, ⊤))
            (WContractification.PullbackProfinite Γ(T, ⊤) (S _⦋n⦌).left
              (commonHypercoverBaseMap T a (S _⦋n⦌)))
            (LocallyConstant.comapₐ Γ(T, ⊤) ⟨Q.proj, Q.proj_continuous⟩
              ⟨r, IsLocallyConstant.of_discrete r⟩)) ∧
      k.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤)
          (colimit (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
            (commonHypercoverBaseMap T a (S _⦋n⦌))) : CommAlgCat Γ(T, ⊤)))) ≫
          T.isoSpec.inv = (U _⦋n⦌).hom ∧
      (∀ x : (U _⦋n⦌).left,
        WContractification.PullbackProfinite.projT Γ(T, ⊤) (S _⦋n⦌).left
          (commonHypercoverBaseMap T a (S _⦋n⦌))
          (Spec.map (CommRingCat.ofHom e.symm.toRingHom) (k.hom x)) = p n x))

/-- Compatible weakly contractible hypercovers from the common component space.

Source: HRS, before (4.1), Proposition 4.3(1); Bhatt--Scholze, Lemmas 2.2.8,
2.4.8 and Example 2.4.6; Stacks, Tags 0DAV and 097D.
(blueprint: lem-sfb-wstrict-common-component-hypercovers).

Proof for stage 3, following the nine steps of the node.
1. In profinite spaces over P, finite jointly surjective families form a precoverage
with pullbacks. Stonean covers give singleton basis covers; adjoining a basis arrow
preserves a cover. Apply `exists_site_finite_basis_hypercover` to the terminal object.
2. Realize each finite formal family by its finite disjoint union. It is Stonean.
Finite formal-family limits realize to ordinary limits: compatible index choices
cut out finitely many clopen pieces. Hence matching arrows become surjective.
3. The zero matching arrow is surjective. A degeneracy from degree zero supplies
surjectivity of every augmentation. If P is empty all these spaces are empty.
4. Apply `component_relative_profinite_site` for each affine base, identifying the
second component space by e. Finite limits and coverings are preserved. The
pullback-space description of `affine_component_site_projection` gives the topology,
stalks, operator action and component identifications of these relative lifts.
5. Apply `Algebra.stonean_cover_second_stage` in each degree. Its hypotheses are
w-strict locality, extremal disconnectedness, and the surjectivity from step 3.
It supplies the displayed restriction and partition colimits and w-contractibility.
6. Identify the topology of the ring model through clopen localization, the finite
product-spectrum theorem, the partition refinement diagram, the filtered-spectrum
limit theorem and the profinite partition-incidence limit theorem. This is a
homeomorphism over both factors, rather than just a point bijection.
7. Both structure maps are stalkwise isomorphisms. Apply
`Scheme.existsUnique_lift_of_stalkMap_isIso` to the homeomorphism and its inverse.
Uniqueness gives inverse scheme maps, canonically over both factors. Apply
`Scheme.proetale_wContractible_projective` to obtain weak contractibility.
8. The map (x',s) ↦ (h(x'),s) lifts uniquely to a scheme map by the same stalkwise
lifting theorem. For every simplicial operator, both composites have the same
point map over X; uniqueness gives their equality. Augmentation is included.
9. For empty P all spaces and schemes are empty and rings zero. The empty
partition is present, and its empty product is the terminal (zero) ring.
-/
theorem wstrict_common_component_hypercovers
    (X X' : Scheme.{u}) [IsAffine X] [IsAffine X']
    [IsWStrictlyLocalRing Γ(X, ⊤)] [IsWStrictlyLocalRing Γ(X', ⊤)]
    (h : X' ⟶ X) (e : ConnectedComponents X' ≃ₜ ConnectedComponents X)
    (he : ∀ x : X', e (ConnectedComponents.mk x) = ConnectedComponents.mk (h x)) :
    ∃ (S : SimplicialObject (Over (affineComponentSpace X)))
      (U : SimplicialObject X.ProEt) (V : SimplicialObject X'.ProEt)
      (p : ∀ n : ℕ, C((U _⦋n⦌).left, (S _⦋n⦌).left))
      (q : ∀ n : ℕ, C((V _⦋n⦌).left, (S _⦋n⦌).left))
      (g : ∀ n : ℕ, (V _⦋n⦌).left ⟶ (U _⦋n⦌).left),
      IsCommonProfiniteHypercover S ∧
      IsCommonComponentHypercoverLift X (Homeomorph.refl _) S U p ∧
      IsCommonComponentHypercoverLift X' e.symm S V q ∧
      (∀ n : ℕ, g n ≫ (U _⦋n⦌).hom = (V _⦋n⦌).hom ≫ h) ∧
      (∀ (n : ℕ) (x : (V _⦋n⦌).left), p n (g n x) = q n x) ∧
      (∀ (m n : SimplexCategoryᵒᵖ) (f : m ⟶ n),
        (V.map f).left ≫ g n.unop.len = g m.unop.len ≫ (U.map f).left) := by
  classical
  obtain ⟨S, hS⟩ := exists_common_stonean_hypercover (affineComponentSpace X)
  obtain ⟨U, p, hU⟩ := exists_common_component_hypercover_single_lift
    X (Homeomorph.refl _) S hS
  obtain ⟨V, q, hV⟩ := exists_common_component_hypercover_single_lift X' e.symm S hS
  change IsCommonComponentHypercoverLift X (Homeomorph.refl _) S U p at hU
  change IsCommonComponentHypercoverLift X' e.symm S V q at hV
  choose H hHt hHp using fun n ↦ (hU.2.2.2.1 n).2.1
  choose K hKt hKq using fun n ↦ (hV.2.2.2.1 n).2.1
  have hlabel (n : ℕ) (x : (V _⦋n⦌).left) :
      ConnectedComponents.mk (h ((V _⦋n⦌).hom x)) = (S _⦋n⦌).hom (q n x) := by
    have hx : ConnectedComponents.mk (K n x).val.1 =
        e.symm ((S _⦋n⦌).hom (K n x).val.2) := (K n x).property
    rw [hKt, hKq] at hx
    rw [← he, hx, e.apply_symm_apply]
  let b (n : ℕ) (x : (V _⦋n⦌).left) :
      {z : X × (S _⦋n⦌).left |
        ConnectedComponents.mk z.1 = (S _⦋n⦌).hom z.2} :=
    ⟨(h ((V _⦋n⦌).hom x), q n x), hlabel n x⟩
  have hb (n : ℕ) : Continuous (b n) :=
    ((h.continuous.comp (V _⦋n⦌).hom.continuous).prodMk (q n).continuous).subtype_mk _
  let a (n : ℕ) : (V _⦋n⦌).left.toTopCat ⟶ (U _⦋n⦌).left.toTopCat :=
    TopCat.ofHom ⟨fun x ↦ (H n).symm (b n x), (H n).symm.continuous.comp (hb n)⟩
  have hat (n : ℕ) (x : (V _⦋n⦌).left) :
      (U _⦋n⦌).hom (a n x) = h ((V _⦋n⦌).hom x) :=
    (hHt n _).symm.trans
      (congrArg (fun z ↦ z.val.1) ((H n).apply_symm_apply (b n x)))
  have hap (n : ℕ) (x : (V _⦋n⦌).left) : p n (a n x) = q n x :=
    (hHp n _).symm.trans
      (congrArg (fun z ↦ z.val.2) ((H n).apply_symm_apply (b n x)))
  have ha (n : ℕ) : a n ≫ (U _⦋n⦌).hom.base = ((V _⦋n⦌).hom ≫ h).base := by
    ext x
    exact hat n x
  have hg (n : ℕ) := Scheme.existsUnique_lift_of_stalkMap_isIso
    (U _⦋n⦌).hom (hU.2.2.2.1 n).1 ((V _⦋n⦌).hom ≫ h) (a n) (ha n)
  choose g hga hgt using fun n ↦ (hg n).exists
  have hgp (n : ℕ) (x : (V _⦋n⦌).left) : p n (g n x) = q n x := by
    have hx : g n x = a n x := ConcreteCategory.congr_hom (hga n) x
    rw [hx]
    exact hap n x
  have lift_ext (n : ℕ) {W : Scheme.{u}} (l r : W ⟶ (U _⦋n⦌).left)
      (ht : l ≫ (U _⦋n⦌).hom = r ≫ (U _⦋n⦌).hom)
      (hp : ∀ x : W, p n (l x) = p n (r x)) : l = r := by
    have hlr : l.base = r.base := by
      ext x
      apply (H n).injective
      apply Subtype.ext
      apply Prod.ext
      · rw [hHt, hHt]
        exact congrArg (fun k : W ⟶ X ↦ k x) ht
      · rw [hHp, hHp]
        exact hp x
    obtain ⟨m, hm, hu⟩ := Scheme.existsUnique_lift_of_stalkMap_isIso
      (U _⦋n⦌).hom (hU.2.2.2.1 n).1 (l ≫ (U _⦋n⦌).hom) l.base rfl
    exact (hu l ⟨rfl, rfl⟩).trans (hu r ⟨hlr.symm, ht.symm⟩).symm
  refine ⟨S, U, V, p, q, g, hS, hU, hV, hgt, hgp, ?_⟩
  intro m n f
  apply lift_ext n.unop.len
  · calc
      (V.map f).left ≫ g n.unop.len ≫ (U _⦋n.unop.len⦌).hom =
          (V.map f).left ≫ (V _⦋n.unop.len⦌).hom ≫ h := by rw [hgt]
      _ = (V _⦋m.unop.len⦌).hom ≫ h := by
        have hw : (V.map f).left ≫ (V.obj n).hom = (V.obj m).hom := (V.map f).w
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ h) hw)
      _ = g m.unop.len ≫ (U _⦋m.unop.len⦌).hom := (hgt _).symm
      _ = (g m.unop.len ≫ (U.map f).left) ≫ (U _⦋n.unop.len⦌).hom := by
        rw [Category.assoc]
        have hw : (U.map f).left ≫ (U.obj n).hom = (U.obj m).hom := (U.map f).w
        exact congrArg (fun k ↦ g m.unop.len ≫ k) hw.symm
  · intro x
    change p n.unop.len (g n.unop.len ((V.map f).left x)) =
      p n.unop.len ((U.map f).left (g m.unop.len x))
    rw [hgp, hU.2.2.1, hgp, hV.2.2.1]

end AlgebraicGeometry.ProEtale
