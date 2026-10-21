/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.StrictQuotientScalarDirectIsomorphisms

/-! # Scalar compatibility of the strict quotient projection morphism

Source: main-20261015, sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-completed-exchange-coherence.proof.md, second paragraph,
strict coefficient supplement old Step 5; Stacks 0B56 and 0FND.
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection).

Use the published small pro-etale model, its actual completed coefficient limit and
its strict derived reductions. Index n denotes the positive exponent n+1. Direct images
are specified as right adjoints of the normalized derived inverse images. Right adjoints
with their adjunctions determine the ordinary unbounded derived operations up to unique
adjunction-preserving isomorphism. The scalar comparisons are their specified right mates,
exactly the normalization of flat-ringed-diagram-restriction. Projection is the mate of
the inverse pullback/reduction comparison, hence the adjunct of counit tensored with identity
under the diagonal direct-image identification. All equalities occur before evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme.StrictScalarBalancing

variable {A : Type (u + 1)} [CommRing A]

private theorem mate_adjunct
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (G : C₁ ⥤ C₃) (H : C₂ ⥤ C₄) (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (M : C₁) (N : C₂) (t : L₁.obj M ⟶ N) :
    adj₂.homEquiv _ _ (α.app M ≫ H.map t) =
      G.map (adj₁.homEquiv _ _ t) ≫
        (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).app N := by
  let δ := mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)
  have h := unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) M
  change G.map (adj₁.unit.app M) ≫ δ.app (L₁.obj M) =
    adj₂.unit.app (G.obj M) ≫ R₂.map (α.app M) at h
  rw [adj₂.homEquiv_unit, R₂.map_comp, ← Category.assoc, ← h, Category.assoc]
  have hd : δ.app (L₁.obj M) ≫ R₂.map (H.map t) =
      G.map (R₁.map t) ≫ δ.app N := δ.natTrans.naturality t |>.symm
  rw [hd, adj₁.homEquiv_unit, G.map_comp, Category.assoc]

/-- The strict projection transformation, defined by the actual adjunction Hom bijection.
At K its adjunct is the inverse of tau at RK followed by reduction of the ordinary counit.
Thus it is the counit-tensor projection of Stacks 0B56 under the normalized diagonal
identification, rather than a map chosen by its evaluations.
Source: completed-exchange-coherence proof, second paragraph, strict supplement Step 5;
Stacks 0B56 (blueprint: lem-weil-pbc-quotient-diagram-scalar-projection). -/
def quotientProjection {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (b : Bool) (p : PullModel f d b)
    (R : D (ring X d b) ⥤ D (ring Y d b))
    (H : TD (ring X d b) ⥤ TD (ring Y d b))
    (ordinaryAdj : p.ordinary ⊣ R) (diagramAdj : p.diagrams ⊣ H)
    (tau : p.ordinary ⋙ reduction X d b ≅ reduction Y d b ⋙ p.diagrams) :
    R ⋙ reduction Y d b ⟶ reduction X d b ⋙ H :=
  (mateEquiv ordinaryAdj diagramAdj (TwoSquare.mk _ _ _ _ tau.inv)).natTrans

/-- The ordinary direct-image scalar comparison is the right mate of a inverse.
Its normalization is the adjunct identity of flat-ringed-diagram-restriction.
Source: strict supplement Step 5, scalar-counit calculation; Stacks 0FND
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection). -/
def ordinaryScalarDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ra : D (ring X d true) ⥤ D (ring Y d true))
    (R0 : D (ring X d false) ⥤ D (ring Y d false))
    (adjA : p.completed.ordinary ⊣ Ra) (adj0 : p.constant.ordinary ⊣ R0) :
    Ra ⋙ dres (scalar Y d) ⟶ dres (scalar X d) ⋙ R0 :=
  (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ p.a.inv)).natTrans

/-- The strict-diagram direct-image scalar comparison is the right mate of p inverse.
This is the normalized d of flat-ringed-diagram-restriction, including all transitions.
Source: strict supplement Step 5, strict-diagram adjunct identity; Stacks 0FND
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection). -/
def diagramScalarDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ha : TD (ring X d true) ⥤ TD (ring Y d true))
    (H0 : TD (ring X d false) ⥤ TD (ring Y d false))
    (adjA : p.completed.diagrams ⊣ Ha) (adj0 : p.constant.diagrams ⊣ H0) :
    Ha ⋙ tdres (scalar Y d) ⟶ tdres (scalar X d) ⋙ H0 :=
  (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ p.p.inv)).natTrans

/-- Scalar restriction carries the completed-coefficient strict projection to the
constant-coefficient strict projection. The two direct scalar comparisons are invertible.
Every displayed map is a component of a natural transformation, and K ranges over the
entire unbounded ambient derived category.

Source: main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement old Step 5; Stacks 0B56 and 0FND.
(blueprint: lem-weil-pbc-quotient-diagram-scalar-projection).

Proof:
1. Completed-constant-algebra-flat-quotients gives flatness of the completed ring over
constant A. Profinite-coefficient-inverse-image identifies completed and finite rings,
preserving the quotient projections. Constant-left-module-inverse-image identifies
constant A even if A is infinite. Check scalar compatibility after every finite
projection: both adjuncts send a constant x to its residue. Joint determination by the
projections gives the scalar square. Flat-ringed-diagram-restriction, first for ordinary
modules and then for strict diagrams, gives the normalized comparisons and their
invertibility. Diagram-site-realization places them in the strict derived categories.
2. Write B for reduction. Augmented-diagram-projection-mate identifies each projection
with the adjunct of s at RK followed by B of the ordinary counit, where s is tau inverse.
Constant-tower-pushforward-normalization supplies the strict counit equation, identifying
this with counit tensored with identity under the diagonal direct-image comparison.
3. The ordinary scalar adjunct identity gives r(epsilonA) after a inverse equal to
G(chi) followed by epsilon0. This also follows directly from the right-mate formula.
4. Apply strict-quotient-scalar-balancing to M = Ra K. Its pullback equation identifies
rho after r(sA) and p inverse with G(rho) followed by s0 and B(a inverse).
Reduction-pullback-derived-tower and ringed-topoi-derived-tensor-pullback identify these
s maps: both are the termwise tensor comparison on flat-term K-flat representatives.
5. Apply naturality of rho to epsilonA, substitute the equations of steps 4 and 3,
and use naturality of s0 at chi. The result is the identity of the two adjuncts:
r(tA), corrected by p inverse and rho, equals G(B(chi) after rho) followed by t0.
6. The strict scalar adjunct identity identifies the first side with the adjunct of
the left displayed composite. Naturality of the Hom bijection identifies the other
side with the adjunct of the right displayed composite. Injectivity proves equality.
7. Counits, reassociations, balancing and right mates are natural. Thus the equality
holds naturally for every K. Every calculation takes place in the derived category of
strict towers, so no faithfulness of derived evaluation, properness, completeness or
witness hypothesis is used. -/
theorem quotientDiagramScalarProjection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : AdicCoefficientDatum A)
    (bal : Balancing d) (p : PullCompatibility f d (bal.ρ Y) (bal.ρ X))
    (Ra : D (ring X d true) ⥤ D (ring Y d true))
    (R0 : D (ring X d false) ⥤ D (ring Y d false))
    (Ha : TD (ring X d true) ⥤ TD (ring Y d true))
    (H0 : TD (ring X d false) ⥤ TD (ring Y d false))
    (ordinaryAdjA : p.completed.ordinary ⊣ Ra)
    (ordinaryAdj0 : p.constant.ordinary ⊣ R0)
    (diagramAdjA : p.completed.diagrams ⊣ Ha)
    (diagramAdj0 : p.constant.diagrams ⊣ H0) :
    IsIso (ordinaryScalarDirect f d bal p Ra R0 ordinaryAdjA ordinaryAdj0) ∧
      IsIso (diagramScalarDirect f d bal p Ha H0 diagramAdjA diagramAdj0) ∧
      ∀ K : D (ring X d true),
        (tdres (scalar Y d)).map
            ((quotientProjection f d true p.completed Ra Ha ordinaryAdjA diagramAdjA p.τ).app K) ≫
          (diagramScalarDirect f d bal p Ha H0 diagramAdjA diagramAdj0).app
            ((reduction X d true).obj K) ≫ H0.map ((bal.ρ X).hom.app K) =
        (bal.ρ Y).hom.app (Ra.obj K) ≫
          (reduction Y d false).map
            ((ordinaryScalarDirect f d bal p Ra R0 ordinaryAdjA ordinaryAdj0).app K) ≫
          (quotientProjection f d false p.constant R0 H0 ordinaryAdj0 diagramAdj0
            p.constantReassociation).app ((dres (scalar X d)).obj K) := by
  have h := strictQuotientScalarDirectIsomorphisms f d bal p Ra R0 Ha H0
    ordinaryAdjA ordinaryAdj0 diagramAdjA diagramAdj0
  refine ⟨h.1, h.2, ?_⟩
  intro K
  apply (diagramAdj0.homEquiv _ _).symm.injective
  let εa := ordinaryAdjA.counit.app K
  let ε0 := ordinaryAdj0.counit.app ((dres (scalar X d)).obj K)
  let χ := ordinaryScalarDirect f d bal p Ra R0 ordinaryAdjA ordinaryAdj0
  let πa := quotientProjection f d true p.completed Ra Ha ordinaryAdjA diagramAdjA p.τ
  let π0 := quotientProjection f d false p.constant R0 H0 ordinaryAdj0 diagramAdj0
    p.constantReassociation
  let δ := diagramScalarDirect f d bal p Ha H0 diagramAdjA diagramAdj0
  let ta := p.τ.inv.app (Ra.obj K) ≫ (reduction X d true).map εa
  let t0 := p.constantReassociation.inv.app (R0.obj ((dres (scalar X d)).obj K)) ≫
    (reduction X d false).map ε0
  have hπa : diagramAdjA.homEquiv _ _ ta = πa.app K := by
    simpa [ta, εa, πa, quotientProjection, ← ordinaryAdjA.homEquiv_symm_id K] using
      mate_adjunct ordinaryAdjA diagramAdjA _ _ p.τ.inv (Ra.obj K) K εa
  have hπ0 : diagramAdj0.homEquiv _ _ t0 =
      π0.app ((dres (scalar X d)).obj K) := by
    simpa [t0, ε0, π0, quotientProjection,
      ← ordinaryAdj0.homEquiv_symm_id ((dres (scalar X d)).obj K)] using
      mate_adjunct ordinaryAdj0 diagramAdj0 _ _ p.constantReassociation.inv
        (R0.obj ((dres (scalar X d)).obj K)) ((dres (scalar X d)).obj K) ε0
  have hχ : p.constant.ordinary.map (χ.app K) ≫ ε0 =
      p.a.inv.app (Ra.obj K) ≫ (dres (scalar X d)).map εa := by
    exact mateEquiv_counit ordinaryAdjA ordinaryAdj0
      (TwoSquare.mk _ _ _ _ p.a.inv) K
  have hτ : p.p.inv.app ((reduction Y d true).obj (Ra.obj K)) ≫
      (tdres (scalar X d)).map (p.τ.inv.app (Ra.obj K)) ≫
      (bal.ρ X).hom.app (p.completed.ordinary.obj (Ra.obj K)) =
    p.constant.diagrams.map ((bal.ρ Y).hom.app (Ra.obj K)) ≫
      p.constantReassociation.inv.app ((dres (scalar Y d)).obj (Ra.obj K)) ≫
      (reduction X d false).map (p.a.inv.app (Ra.obj K)) := by
    apply (cancel_epi (p.p.hom.app _)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    apply (cancel_epi ((tdres (scalar X d)).map (p.τ.hom.app _))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [reassoc_of% (p.equation (Ra.obj K))]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    change _ = _ ≫ (reduction X d false).map
      (𝟙 ((dres (scalar X d)).obj (p.completed.ordinary.obj (Ra.obj K))))
    rw [(reduction X d false).map_id, Category.comp_id]
  have ht : p.p.inv.app ((reduction Y d true).obj (Ra.obj K)) ≫
      (tdres (scalar X d)).map ta ≫ (bal.ρ X).hom.app K =
    p.constant.diagrams.map ((bal.ρ Y).hom.app (Ra.obj K) ≫
      (reduction Y d false).map (χ.app K)) ≫ t0 := by
    dsimp only [ta]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (bal.ρ X).hom.naturality εa
    change (tdres (scalar X d)).map ((reduction X d true).map εa) ≫
      (bal.ρ X).hom.app K = (bal.ρ X).hom.app _ ≫
        (reduction X d false).map ((dres (scalar X d)).map εa) at hn
    rw [hn]
    change _ ≫ _ ≫ (bal.ρ X).hom.app
      (p.completed.ordinary.obj (Ra.obj K)) ≫
      (reduction X d false).map ((dres (scalar X d)).map εa) = _
    rw [reassoc_of% hτ]
    simp only [← Functor.map_comp, ← hχ]
    rw [Functor.map_comp]
    have hs := p.constantReassociation.inv.naturality (χ.app K)
    change p.constant.diagrams.map ((reduction Y d false).map (χ.app K)) ≫
      p.constantReassociation.inv.app (R0.obj ((dres (scalar X d)).obj K)) =
      p.constantReassociation.inv.app ((dres (scalar Y d)).obj (Ra.obj K)) ≫
        (reduction X d false).map (p.constant.ordinary.map (χ.app K)) at hs
    dsimp only [t0]
    rw [← reassoc_of% hs]
  have hδ := mate_adjunct diagramAdjA diagramAdj0 _ _ p.p.inv
    ((reduction Y d true).obj (Ra.obj K)) ((reduction X d true).obj K) ta
  change diagramAdjA.homEquiv _ ((reduction X d true).obj K) ta = _ at hπa
  change diagramAdj0.homEquiv _
    ((reduction X d false).obj ((dres (scalar X d)).obj K)) t0 = _ at hπ0
  rw [hπa] at hδ
  change diagramAdj0.homEquiv _ _
    (p.p.inv.app _ ≫ (tdres (scalar X d)).map ta) =
    (tdres (scalar Y d)).map (πa.app K) ≫
      δ.app ((reduction X d true).obj K) at hδ
  simp only [← Category.assoc]
  change (diagramAdj0.homEquiv _ _).symm
    (((tdres (scalar Y d)).map (πa.app K) ≫ δ.app _) ≫
      H0.map ((bal.ρ X).hom.app K)) =
    (diagramAdj0.homEquiv _ _).symm
      (((bal.ρ Y).hom.app (Ra.obj K) ≫
        (reduction Y d false).map (χ.app K)) ≫
        π0.app ((dres (scalar X d)).obj K))
  rw [← hδ]
  change (diagramAdj0.homEquiv _ _).symm
    (diagramAdj0.homEquiv _ ((tdres (scalar X d)).obj
      ((reduction X d true).obj K)) _ ≫ H0.map ((bal.ρ X).hom.app K)) = _
  rw [diagramAdj0.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply, ← hπ0, diagramAdj0.homEquiv_naturality_left_symm]
  dsimp only [Functor.comp_obj]
  rw [Equiv.symm_apply_apply]
  simpa only [Category.assoc] using ht

end AlgebraicGeometry.Scheme.StrictScalarBalancing
