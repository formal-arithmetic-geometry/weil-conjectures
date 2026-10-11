/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Continuity of sections of étale sheaves of sets

Source: Stacks Project, Étale Cohomology, Tag 09YQ, degree-zero argument via Tags 0EYL,
04HR and 09YN; restriction along an étale morphism, Tag 03S2
(blueprint: lem-weil-pbc-sets-etale-section-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The section comparison for a commuting triangle `T ⟶ S ⟶ R`: first use the
inverse-image unit, then the composition isomorphism from
`etaleSetInverseImageCompositionUnits`, and finally restrict along the canonical
iterated-fibre-product isomorphism. This defines the transition maps and limit legs
in the continuity statement.

Source: Stacks Project, Étale Cohomology, Tag 09YQ, degree-zero section comparison;
Sites, Tags 03CB and 03CC
(blueprint: lem-weil-pbc-sets-etale-section-continuity). -/
noncomputable def etaleSetSectionComparison
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    ((Scheme.etaleSetPullback f).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ⟶
      ((Scheme.etaleSetPullback k).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U)) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit.app
        ((Scheme.etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ≫
    ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    (eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk)).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    ((Scheme.etaleSetPullback k).obj G).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).hom.app U).op

/-- For an étale object `V → X`, the unit followed by restriction along its diagonal
maps `F(V)` to the global sections of the inverse image on `V`. Its inverse is the
restriction identification in the last clause of continuity.

Source: Stacks Project, Étale Cohomology, Tag 03S2, inverse image along an étale morphism
is restriction (blueprint: lem-weil-pbc-sets-etale-section-continuity). -/
noncomputable def etaleSetRestrictionUnit
    {X : Scheme.{u}} (V : X.Etale) (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    F.obj.obj (op V) ⟶
      ((Scheme.etaleSetPullback V.hom).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 V.left))) :=
  letI := Etale.isContinuous_overPullback (Y := X) (Z := V.left) V.hom
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ V.hom) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      (V.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) ≫
    ((Scheme.etaleSetPullback V.hom).obj F).obj.map
      (MorphismProperty.Over.homMk
        (B := (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V)
        (pullback.diagonal V.hom) (pullback.diagonal_snd V.hom)).op

/-- Continuity for a sheaf of sets pulled back from a chosen stage `i₀`. The category
`Over (op i₀)` indexes the inverse system on the upper tail `i ≥ i₀`, so its opposite
indexes the directed system of sections. The isomorphisms `e` identify the objects of
`E` with the stated section sets; its maps are exactly the unit/composition comparisons.
Thus the functor laws give both the identity and composition laws for these maps.
The natural transformation `ν` is the canonical cocone, whose induced colimit map is
bijective. The final assertion says that the canonical unit/diagonal section map for
each étale projection is bijective, equivalently that restriction is its inverse.

Source: Stacks Project, Étale Cohomology, Theorem Tag 09YQ, degree zero for sets via
Tags 0EYL, 04HR and 09YN, and restriction along étale morphisms, Tag 03S2
(blueprint: lem-weil-pbc-sets-etale-section-continuity).

Proof:
1. First take `W₀` affine. Transitions and projections are affine by hypothesis and
   lem-weil-pbc-limit-affine-transition. Use lem-weil-pbc-affine-etale-site-colimit
   and lem-weil-pbc-affine-etale-site-topos to describe the limit affine étale site.
   Transport the inverse images and units using
   lem-weil-pbc-site-equivalence-sheaf-transport and
   lem-weil-pbc-sets-affine-etale-inverse-image-comparison. Their transition maps are
   isomorphisms with the cocycle law, so lem-weil-pbc-colimit-constant-connected-diagram
   identifies their inverse-image colimit with the inverse image at the limit.
2. Apply lem-weil-pbc-colimit-of-sites-sections to each affine descended object.
   The unit compatibility of lem-weil-pbc-sets-affine-etale-inverse-image-comparison
   and clauses (0) and (1) of lem-weil-pbc-sets-etale-inverse-image-composition-units
   identify its components with `etaleSetSectionComparison`.
3. For general `W₀`, use lem-weil-pbc-etale-qcqs-cofinal-finite-coverings to choose
   a finite affine cover and finite affine refinements of all pairwise overlaps.
   Their base changes remain affine and covering. Apply the affine result to all
   these objects. By lem-weil-pbc-pretopology-sheaf-condition, sections are the finite
   equalizer of the corresponding products of sections. Unit naturality makes all
   comparisons commute with restriction. Then
   lem-weil-pbc-filtered-colimits-commute-finite-limits gives the required bijection.
4. The unit, composition and associativity clauses of
   lem-weil-pbc-sets-etale-inverse-image-composition-units, together with fibre-product
   pasting, give the identity and composition laws, hence `E` and the cocone `ν`.
   Finally lem-weil-pbc-sets-etale-inverse-image-restriction identifies inverse image
   along each étale projection with restriction, inverse to `etaleSetRestrictionUnit`.
-/
theorem etaleSetSectionContinuity
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (_hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom] :
    ∃ (E : (Over (op i₀))ᵒᵖ ⥤ Type (u + 1))
      (e : ∀ j : Over (op i₀), E.obj (op j) ≅
        ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀)))
      (ν : E ⟶ (Functor.const (Over (op i₀))ᵒᵖ).obj
        (((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀)))),
      (∀ (j k : Over (op i₀)) (a : k ⟶ j),
        (e j).inv ≫ E.map a.op ≫ (e k).hom =
          etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp a.left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W₀) ∧
      (∀ j : Over (op i₀),
        (e j).inv ≫ ν.app (op j) =
          etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
            (c.π.app (op i₀)) (c.w j.hom) G W₀) ∧
      Function.Bijective (colimit.desc E (Cocone.mk _ ν)) ∧
      (∀ j : Over (op i₀), Function.Bijective
        (etaleSetRestrictionUnit
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀)
          ((Scheme.etaleSetPullback (D.map j.hom)).obj G))) := by
  sorry

end AlgebraicGeometry
