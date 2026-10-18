/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.AlgebraicGeometry.DescendAffine
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.LimitAffineTransition

/-!
# Pointed étale span descent with fixed target families

Source: Stacks Project, Limits, Tags 01ZM and 07RP; More on Morphisms, Tag 0GDX,
finite-stage descent paragraph (blueprint: lem-trf-fixed-family-etale-span-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical projection from a fixed family's limit pullback to its stage pullback.
It is the pullback map of the identity of the fixed model and the limit projection.
Source: Stacks Project, Tag 0GDX, fixed families in the finite-stage descent paragraph
(blueprint: lem-trf-fixed-family-etale-span-descent). -/
noncomputable def fixedFamilyLimitProjection
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (L : Cone D)
    (i₀ j : I) (hj : i₀ ≤ j) {X₀ : Scheme.{u}} (f : X₀ ⟶ D.obj (op i₀)) :
    pullback f (L.π.app (op i₀)) ⟶ pullback f (D.map (homOfLE hj).op) :=
  pullback.map f (L.π.app (op i₀)) f (D.map (homOfLE hj).op)
    (𝟙 X₀) (L.π.app (op j)) (𝟙 (D.obj (op i₀)))
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id _).trans (L.w (homOfLE hj).op).symm)

/-- A pointed affine étale span descends while its two finitely presented target models
remain fixed. The projection equations express equality with the actual base changes:
by cartesian pasting the fixed-family pullbacks are also the pullbacks of the stage
families to the limit, so these equations and the equation over the limit base determine
both arrows uniquely. All residue-field maps below are the induced canonical maps.

Source: Stacks Project, Limits, Tags 01ZM, 01ZN and 07RP; More on Morphisms, Tag 0GDX,
finite-stage descent paragraph (blueprint: lem-trf-fixed-family-etale-span-descent).

Proof:
1. Restrict to the upper tail of i₀. Compatible cones extend uniquely by taking common
   upper bounds, so the limit is unchanged. Transitions between affine schemes are affine
   (lem-weil-pbc-morphism-affine-schemes-affine); stages are qcqs
   (lem-weil-pbc-affine-scheme-qcqs), and the limit is affine
   (lem-weil-pbc-limit-affine-transition).
2. Descend the finitely presented source by thm-pd-spreading-out (01ZM, part 1).
   It is qcqs by lem-weil-pbc-qcqs-morphism-permanence.
3. Its limit base change is affine. By lem-weil-pbc-descend-affine it is affine at a
   later stage; lem-weil-pbc-affine-morphism-permanence makes the source affine, and
   lem-weil-pbc-qcqs-morphism-permanence preserves finite presentation.
4. The fixed target pullbacks are affine (lem-weil-pbc-fibre-product-affine-spectra)
   and finitely presented. Descend the two arrows by thm-pd-spreading-out (01ZM, part 2)
   and take a common upper bound. Iterated pullback comparisons preserve projections
   (def-pc-fibre-product), giving the two asserted projection equations.
5. Both descended arrows are locally finitely presented. On affine coordinate rings,
   if C = R[x]/(r) and D = R[t]/(h), choose representatives F(x) of the images of t.
   Then C = D[x]/(r,t-F(x)): substitution and the original ring map are inverse.
   Apply lem-weil-pbc-lfp-affine-opens-finite-presentation and
   def-sbc-locally-finite-presentation to each arrow.
6. Apply lem-weil-pbc-descend-etale twice (07RP) and take a common later stage.
   Étaleness persists by lem-weil-pbc-etale-scheme-base-change. Affineness and finite
   presentation persist by the same permanence statements as in steps 3 and 4.
7. Project e⁻¹(u) to define u_j. Evaluating the projection equations gives its two
   images in the fixed models; the pullback squares put all points over s_j.
8. For each of the source and two targets, compare the fibres over b and s_j by
   lem-weil-pbc-fibre-of-base-change. The map is the base change of Spec κ(b) → Spec κ(s_j),
   an isomorphism by hypothesis. Fibre projections induce residue-field isomorphisms
   (lem-weil-pbc-fibre-ring-residue-field-iso and
   lem-weil-pbc-fibre-product-affine-spectra). Commutativity identifies each canonical
   stage-to-limit residue map with the composite of these three isomorphisms.
9. Functoriality of def-weil-residue-field gives, for each stage arrow, a square whose
   vertical residue maps are the isomorphisms of step 8 and whose bottom map is the
   given elementary limit arrow. Conjugating by the vertical maps proves that both
   stage arrows induce residue-field isomorphisms. -/
theorem exists_fixedFamily_etale_span_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    (L : Cone D) (hL : IsLimit L) (b : L.pt)
    (hb : ∀ i : I, IsIso ((L.π.app (op i)).residueFieldMap b))
    (i₀ : I) (P₀ Q₀ : Scheme.{u}) [IsAffine P₀] [IsAffine Q₀]
    (fP : P₀ ⟶ D.obj (op i₀)) (fQ : Q₀ ⟶ D.obj (op i₀))
    [LocallyOfFinitePresentation fP] [LocallyOfFinitePresentation fQ]
    (U : Scheme.{u}) [IsAffine U] (fU : U ⟶ L.pt)
    [LocallyOfFinitePresentation fU] (u : U) (hu : fU u = b)
    (a : U ⟶ pullback fP (L.π.app (op i₀)))
    (c : U ⟶ pullback fQ (L.π.app (op i₀))) [Etale a] [Etale c]
    (ha : a ≫ pullback.snd fP (L.π.app (op i₀)) = fU)
    (hc : c ≫ pullback.snd fQ (L.π.app (op i₀)) = fU)
    (haκ : IsIso (a.residueFieldMap u)) (hcκ : IsIso (c.residueFieldMap u)) :
    ∃ (j : I) (hj : i₀ ≤ j) (Uj : Scheme.{u}) (fUj : Uj ⟶ D.obj (op j)),
      IsAffine Uj ∧ LocallyOfFinitePresentation fUj ∧
      ∃ (aj : Uj ⟶ pullback fP (D.map (homOfLE hj).op))
        (cj : Uj ⟶ pullback fQ (D.map (homOfLE hj).op)),
        Etale aj ∧ Etale cj ∧
        aj ≫ pullback.snd fP (D.map (homOfLE hj).op) = fUj ∧
        cj ≫ pullback.snd fQ (D.map (homOfLE hj).op) = fUj ∧
        ∃ e : pullback fUj (L.π.app (op j)) ≅ U,
          e.hom ≫ fU = pullback.snd fUj (L.π.app (op j)) ∧
          e.hom ≫ a ≫ fixedFamilyLimitProjection D L i₀ j hj fP =
            pullback.fst fUj (L.π.app (op j)) ≫ aj ∧
          e.hom ≫ c ≫ fixedFamilyLimitProjection D L i₀ j hj fQ =
            pullback.fst fUj (L.π.app (op j)) ≫ cj ∧
          aj ((e.inv ≫ pullback.fst fUj (L.π.app (op j))) u) =
            fixedFamilyLimitProjection D L i₀ j hj fP (a u) ∧
          cj ((e.inv ≫ pullback.fst fUj (L.π.app (op j))) u) =
            fixedFamilyLimitProjection D L i₀ j hj fQ (c u) ∧
          IsIso ((fixedFamilyLimitProjection D L i₀ j hj fP).residueFieldMap (a u)) ∧
          IsIso ((fixedFamilyLimitProjection D L i₀ j hj fQ).residueFieldMap (c u)) ∧
          IsIso ((e.inv ≫ pullback.fst fUj (L.π.app (op j))).residueFieldMap u) ∧
          IsIso (aj.residueFieldMap ((e.inv ≫ pullback.fst fUj (L.π.app (op j))) u)) ∧
          IsIso (cj.residueFieldMap ((e.inv ≫ pullback.fst fUj (L.π.app (op j))) u)) := by
  sorry

end AlgebraicGeometry
