/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleAffineChartDescent
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField

/-!
# Eventual pointed étaleness of a supplied finite-stage span

Source: Stacks Project, More on Morphisms, Tag 0GDX, finite-stage span and residue-field
paragraphs; Limits, Tag 07RP; Schemes, Tag 01JT.
(blueprint: lem-trf-finite-stage-span-pointed-etale-refinement).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical projection from the limit pullback to a specified stage pullback.
Its components are the identity on the supplied model and the cone projection to that stage.

Source: Stacks Project, More on Morphisms, Tag 0GDX, finite-stage span paragraph;
the fibre-product universal property
(blueprint: lem-trf-finite-stage-span-pointed-etale-refinement).
-/
noncomputable def Scheme.finiteStageSpanProjection
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (r j : I) (hj : r ≤ j) (T : Over (D.obj (op r))) :
    pullback T.hom (c.π.app (op r)) ⟶ pullback T.hom (D.map (homOfLE hj).op) :=
  pullback.map T.hom (c.π.app (op r)) T.hom (D.map (homOfLE hj).op)
    (𝟙 T.left) (c.π.app (op j)) (𝟙 (D.obj (op r)))
    (by simp) (by simp)

/-- A supplied affine finitely presented span becomes pointed elementary étale on a tail.
The three models are quantified through list membership solely to spell out the same
finite-presentation hypotheses and conclusions for V, P and Q. The two point equalities
identify the targets of the final two canonical residue maps with the displayed projected
points, so no arbitrary identifications of fields enter the statement.

Source: Stacks Project, More on Morphisms, Tag 0GDX, finite-stage span and residue-field
paragraphs; Limits, Tag 07RP; Schemes, Tag 01JT.
(blueprint: lem-trf-finite-stage-span-pointed-etale-refinement).

Proof:
1. Fibre products of affine schemes are affine (lem-weil-pbc-fibre-product-affine-spectra).
   Finite presentation persists by lem-weil-pbc-qcqs-morphism-permanence. The two supplied
   arrows are locally of finite presentation by lem-a1-map-over-base-finite-presentation,
   since the target structure maps are locally of finite type.
2. Transition morphisms between affine schemes are affine by pqf-lem-affine-local-target.
   Apply lem-weil-pbc-etale-affine-chart-descent to each arrow, using the whole affine
   source, target and base as charts. A common upper bound of the resulting indices gives
   étaleness of both arrows at every later stage.
3. Pullback associativity identifies each limit model with its stage model pulled back
   along the corresponding cone projection (def-pc-fibre-product). At a point over b,
   put K = κ(p_j(b)), L = κ(b) and E = κ(t_j). The assumed canonical isomorphism K → L
   identifies E ⊗[K] L with E, by a ⊗ c ↦ a λ⁻¹(c), inverse a ↦ a ⊗ 1. This tensor
   ring is a field, so its map to κ(t) has zero kernel. Apply
   lem-weil-pbc-fibre-product-point-residue-field and its compatibility with the first
   tensor inclusion: the actual projection residue map E → κ(t) is an isomorphism.
   Do this for z and its two images to obtain the three canonical residue comparisons.
4. The defining projection identities of the actual pullback arrows give both point
   equalities. Functoriality of def-weil-residue-field gives commuting residue squares.
   The two stage-arrow residue maps are composites of the three projection isomorphisms,
   the assumed limit-arrow isomorphisms, and their inverses, hence are isomorphisms. -/
theorem exists_finiteStage_span_pointed_etale_refinement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (r : I) (b : c.pt)
    (hres : ∀ (i : I), r ≤ i → IsIso ((c.π.app (op i)).residueFieldMap b))
    (V P Q : Over (D.obj (op r)))
    (hmodels : ∀ T ∈ [V, P, Q], IsAffine T.left ∧
      LocallyOfFinitePresentation T.hom ∧ QuasiCompact T.hom ∧ QuasiSeparated T.hom)
    (α : V ⟶ P) (β : V ⟶ Q)
    (z : ((Over.pullback (c.π.app (op r))).obj V).left)
    (hz : pullback.snd V.hom (c.π.app (op r)) z = b)
    (hα : Etale ((Over.pullback (c.π.app (op r))).map α).left)
    (hβ : Etale ((Over.pullback (c.π.app (op r))).map β).left)
    (hαres : IsIso (((Over.pullback (c.π.app (op r))).map α).left.residueFieldMap z))
    (hβres : IsIso (((Over.pullback (c.π.app (op r))).map β).left.residueFieldMap z)) :
    ∃ (k : I) (_ : r ≤ k), ∀ (j : I) (_ : k ≤ j) (hj : r ≤ j),
      (∀ T ∈ [V, P, Q],
        IsAffine ((Over.pullback (D.map (homOfLE hj).op)).obj T).left ∧
        LocallyOfFinitePresentation ((Over.pullback (D.map (homOfLE hj).op)).obj T).hom ∧
        QuasiCompact ((Over.pullback (D.map (homOfLE hj).op)).obj T).hom ∧
        QuasiSeparated ((Over.pullback (D.map (homOfLE hj).op)).obj T).hom) ∧
      Etale ((Over.pullback (D.map (homOfLE hj).op)).map α).left ∧
      Etale ((Over.pullback (D.map (homOfLE hj).op)).map β).left ∧
      ((Over.pullback (D.map (homOfLE hj).op)).map α).left
          (Scheme.finiteStageSpanProjection D c r j hj V z) =
        Scheme.finiteStageSpanProjection D c r j hj P
          (((Over.pullback (c.π.app (op r))).map α).left z) ∧
      ((Over.pullback (D.map (homOfLE hj).op)).map β).left
          (Scheme.finiteStageSpanProjection D c r j hj V z) =
        Scheme.finiteStageSpanProjection D c r j hj Q
          (((Over.pullback (c.π.app (op r))).map β).left z) ∧
      IsIso ((Scheme.finiteStageSpanProjection D c r j hj V).residueFieldMap z) ∧
      IsIso ((Scheme.finiteStageSpanProjection D c r j hj P).residueFieldMap
        (((Over.pullback (c.π.app (op r))).map α).left z)) ∧
      IsIso ((Scheme.finiteStageSpanProjection D c r j hj Q).residueFieldMap
        (((Over.pullback (c.π.app (op r))).map β).left z)) ∧
      IsIso (((Over.pullback (D.map (homOfLE hj).op)).map α).left.residueFieldMap
        (Scheme.finiteStageSpanProjection D c r j hj V z)) ∧
      IsIso (((Over.pullback (D.map (homOfLE hj).op)).map β).left.residueFieldMap
        (Scheme.finiteStageSpanProjection D c r j hj V z)) := by
  sorry

end AlgebraicGeometry
