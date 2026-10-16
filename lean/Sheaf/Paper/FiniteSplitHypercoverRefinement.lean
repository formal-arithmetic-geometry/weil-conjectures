/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
import Sheaf.Paper.EtaleHypercoverProduct
import Sheaf.Paper.FiniteSplitHypercoverExistence
import Sheaf.Paper.FiniteSplitHypercoverReplacement
import Sheaf.Paper.EtaleHypercoverHomotopyEqualizer
import Sheaf.Paper.SemiRepresentableHypercoverEtale
import Sheaf.Paper.FiniteSplitLocalReplacementZero
import Sheaf.Paper.FiniteSplitLocalReplacementExtension
import Sheaf.Paper.FiniteSplitLocalReplacementAssembly

/-!
# Finite refinements and local lifting

Source: blueprint `lem-weil-pbc-hypercover-refinement`, order 947;
Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GJ, 01GK, 01GS.
(blueprint: lem-weil-pbc-hypercover-refinement)

Cofilteredness is stated by its three defining conditions. Covering sieves encode
restriction-stable local lifting requirements; lifts are on the finite constituent
pieces, as in the semi-representable interpretation of hypercovers.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Existence and cofilteredness modulo simplicial homotopy.
Source: blueprint order 947; Stacks Tags 0DAV, 094K, 01GI, 01GN, 01GS.
Proof: finite limits of qcqs étale objects are qcqs, by
lem-weil-pbc-qcqs-morphism-permanence. Cover each matching component by finitely many
affine opens (lem-weil-pbc-qcqs-finite-affine-open-cover), refine its covering by
finite affine étale pieces (lem-weil-pbc-etale-covering-affine-refinement), and
inductively adjoin these as nondegenerate summands, retaining all degeneracies.
Matching equations give the face identities, and epi-mono factorization gives
all remaining simplicial identities. This constructs an object in every degree.
For two objects apply this construction to their product (lem-weil-pbc-hypercover-product).
For parallel maps pull back the endpoint map of the simplicial path object.
Its matching covers follow from lem-weil-pbc-hypercover-finite-simplex-lifting
applied to the finite triangulated prisms, with the comparison
lem-weil-pbc-sr-matching-object-one-member. A finite split replacement gives a
homotopy between the two composites, hence equality in RefinementClasses.
(blueprint: lem-weil-pbc-hypercover-refinement) -/
theorem exists_and_cofiltered (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (FiniteSplitEtaleHypercover X) ∧
      (∀ U V : FiniteSplitEtaleHypercover X,
        ∃ W : FiniteSplitEtaleHypercover X, Nonempty (W.Refinement U) ∧
          Nonempty (W.Refinement V)) ∧
      (∀ (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V),
        ∃ (W : FiniteSplitEtaleHypercover X) (c : W.Refinement U),
          isRefinementHomotopic (c ≫ a) (c ≫ b)) := by
  have hypercover (U : FiniteSplitEtaleHypercover X) : IsEtaleHypercover U.simplicial := by
    intro n
    exact ⟨U.matching n, U.projection n, U.matchingMap n,
      U.projection_naturality n, U.matching_universal n,
      U.matchingMap_projection n, U.matching_cover n⟩
  refine ⟨exists_finite_split_hypercover X, ?_, ?_⟩
  · intro U V
    obtain ⟨W, ⟨c⟩⟩ := exists_finite_split_replacement (U.simplicial ⨯ V.simplicial)
      (isEtaleHypercover_prod X U.simplicial V.simplicial (hypercover U) (hypercover V))
    exact ⟨W, ⟨c ≫ prod.fst⟩, ⟨c ≫ prod.snd⟩⟩
  · intro U V a b
    obtain ⟨K, hK, c, ⟨H⟩⟩ := exists_etale_hypercover_homotopy_equalizer U V a b
    obtain ⟨W, ⟨d⟩⟩ := exists_finite_split_replacement K hK
    refine ⟨W, d ≫ c, Relation.EqvGen.rel _ _ ?_⟩
    exact ⟨by simpa only [Category.assoc] using H.precomp d⟩

private theorem finite_inf_covering
    {C : Type*} [Category* C] (J : GrothendieckTopology C) {T : C}
    {I : Type} (F : I → Sieve T) (s : Finset I) (hF : ∀ i ∈ s, F i ∈ J T) :
    s.inf F ∈ J T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [J.top_mem]
  | @insert i s hi ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)))

/-- A finite family of locally solvable requirements is solved on finite constituent
pieces after refinement. Each sieve consists of maps on which the corresponding lift
exists; its covering condition is precisely local solvability. No compatibility between
independent lifts is required. Source: blueprint order 947; Stacks Tags 01GJ, 01GK, 094K.
Proof: before fixing a nondegenerate degree, pull back every higher-degree requirement
along all degeneracies through r. There are only finitely many such requirements.
Intersect their covering families with the relative matching cover, then choose a
common finite affine refinement using lem-weil-pbc-etale-covering-base-change,
lem-weil-pbc-qcqs-finite-affine-open-cover and lem-weil-pbc-etale-covering-affine-refinement.
The new summands solve all requirements, and degenerate copies inherit the solutions
on their lower-degree sources. Continue unconstrained above r. The canonical split
cofans and the finite cofans of the nondegenerate summands supply the finite cofan
in each retained degree. For sheaf-valued lifting data these constituent solutions
glue over the disjoint union to a solution on the whole term.
(blueprint: lem-weil-pbc-hypercover-refinement) -/
theorem exists_refinement_solving_local_requirements
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : FiniteSplitEtaleHypercover X) (r k : ℕ) (degree : Fin k → Fin (r + 1))
    (R : ∀ j : Fin k, Sieve (U.simplicial.obj (op (SimplexCategory.mk (degree j).val))))
    (hR : ∀ j, R j ∈ X.smallEtaleTopology
      (U.simplicial.obj (op (SimplexCategory.mk (degree j).val)))) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      ∀ n : Fin (r + 1), ∃ (l : ℕ) (T : Fin l → X.Etale)
        (ι : ∀ i, T i ⟶ V.simplicial.obj (op (SimplexCategory.mk n.val))),
        Nonempty (IsColimit (Cofan.mk (V.simplicial.obj (op (SimplexCategory.mk n.val))) ι)) ∧
          ∀ (j : Fin k) (h : degree j = n) (i : Fin l),
            R j (ι i ≫ f.app (op (SimplexCategory.mk n.val)) ≫
              eqToHom (congrArg (fun m : Fin (r + 1) ↦
                U.simplicial.obj (op (SimplexCategory.mk m.val))) h.symm)) := by
  classical
  let D (n : ℕ) := Σ j : Fin k,
    (SimplexCategory.mk (degree j).val ⟶ SimplexCategory.mk n)
  let F (n : ℕ) (a : D n) := (R a.1).pullback (U.simplicial.map a.2.op)
  let S (n : ℕ) : Sieve (U.simplicial.obj (op (SimplexCategory.mk n))) :=
    { arrows := fun _ g ↦ ∀ a : D n, F n a g
      downward_closed := by
        intro T T' g hg f a
        exact (F n a).downward_closed (hg a) f }
  have hS (n : ℕ) : S n ∈ X.smallEtaleTopology _ := by
    have : Finite (D n) := by dsimp [D]; infer_instance
    let _ : Fintype (D n) := Fintype.ofFinite _
    apply X.smallEtaleTopology.superset_covering
      (S := Finset.univ.inf (F n))
    · intro T g hg a
      exact (Finset.inf_le (Finset.mem_univ a) :
        Finset.univ.inf (F n) ≤ F n a) g hg
    · exact finite_inf_covering X.smallEtaleTopology (F n) Finset.univ
        (fun a _ ↦ X.smallEtaleTopology.pullback_stable _ (hR a.1))
  have hstable (m l : ℕ) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
      (T : X.Etale) (g : T ⟶ U.simplicial.obj (op (SimplexCategory.mk m)))
      (hg : S m g) : S l (g ≫ U.simplicial.map θ.op) := by
    intro a
    have hh := hg ⟨a.1, a.2 ≫ θ⟩
    change R a.1 (g ≫ U.simplicial.map (a.2 ≫ θ).op) at hh
    change R a.1 ((g ≫ U.simplicial.map θ.op) ≫ U.simplicial.map a.2.op)
    simpa only [op_comp, Functor.map_comp, Category.assoc] using hh
  have hU : IsEtaleHypercover U.simplicial := by
    intro n
    exact ⟨U.matching n, U.projection n, U.matchingMap n,
      U.projection_naturality n, U.matching_universal n,
      U.matchingMap_projection n, U.matching_cover n⟩
  let L (n : ℕ) := {A : FiniteSplitReplacementStage U.simplicial n //
    StageSolves U.simplicial S A}
  obtain ⟨A₀, hA₀⟩ := exists_local_replacement_stage_zero U.simplicial hU S (hS 0)
  have hstep (n : ℕ) (A : L n) :
      ∃ B : L (n + 1), B.val.restrict n (Nat.le_succ n) = A.val := by
    obtain ⟨B, he, hB⟩ := exists_local_replacement_stage_extension
      U.simplicial hU S hS hstable n A.val A.property
    exact ⟨⟨B, hB⟩, he⟩
  choose next hnext using hstep
  let A : ∀ n, L n := Nat.rec ⟨A₀, hA₀⟩ (fun n B ↦ next n B)
  obtain ⟨V, f, hV⟩ := exists_local_replacement_of_stage_tower U.simplicial
    (fun n ↦ (A n).val) (fun n ↦ hnext n (A n)) S (fun n ↦ (A n).property)
  refine ⟨V, f, ?_⟩
  intro n
  obtain ⟨l, T, ι, hc, hι⟩ := hV n.val
  refine ⟨l, T, ι, hc, ?_⟩
  intro j h i
  subst n
  have hh := hι i ⟨j, 𝟙 _⟩
  change R j ((ι i ≫ f.app _) ≫ U.simplicial.map (𝟙 _).op) at hh
  change R j ((ι i ≫ f.app _) ≫ U.simplicial.map (𝟙 _)) at hh
  rw [U.simplicial.map_id, Category.comp_id] at hh
  simpa only [eqToHom_refl, Category.comp_id] using hh

/-- An arbitrary étale hypercover has a finite split refinement through any finite degree.
Source: blueprint order 947; Stacks Tags 01GJ, 0DAV, 094K.
Proof: construct the split skeleton inductively. In degree n the relative target is
M_n(V) ×_{M_n(K)} K_n. Its projection is a covering by
lem-weil-pbc-etale-covering-base-change. Each matching component of V is qcqs, so
lem-weil-pbc-qcqs-finite-affine-open-cover and
lem-weil-pbc-etale-covering-affine-refinement select finitely many affine pieces of
this cover, without a quasi-compactness assumption on K_n. They define the new faces
and the refinement map. Retain the inherited degeneracies and continue through r;
above r use the ordinary finite split extension. The comparison
lem-weil-pbc-sr-matching-object-one-member identifies the scheme and formal-family
matching conditions. (blueprint: lem-weil-pbc-hypercover-refinement) -/
theorem exists_truncated_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (hK : X.IsSemiRepresentableHypercover
      (K ⋙ FormalCoproduct.incl.{u} X.Etale)) (r : ℕ) :
    ∃ V : FiniteSplitEtaleHypercover X,
      Nonempty ((SimplicialObject.truncation r).obj V.simplicial ⟶
          (SimplicialObject.truncation r).obj K) := by
  have hK' : IsEtaleHypercover K :=
    AlgebraicGeometry.Scheme.semiRepresentableHypercover_isEtaleHypercover K hK
  obtain ⟨V, ⟨f⟩⟩ := exists_finite_split_replacement K hK'
  exact ⟨V, ⟨(SimplicialObject.truncation r).map f⟩⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
