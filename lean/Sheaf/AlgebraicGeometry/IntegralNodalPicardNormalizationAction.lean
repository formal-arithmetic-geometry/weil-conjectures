/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.FinitePinchingInvertiblePatching
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Picard-trivial automorphisms and normalized nodal branches

Source: Deligne--Mumford, Lemma 1.15, printed p.85; Stacks Project, curves.tex,
Tag 0C1M (lemma-glue-points)
(blueprint: lem-sfb-integral-nodal-picard-normalization-action).

The gluing homomorphisms are specified by their fibre identifications, rather than by
choosing arbitrary elements in the kernel of pullback. Degree-zero groups are the existing
subsets `Scheme.Hom.picZero` (degree `χ(L) - χ(𝒪)`, blueprint def-sc-pic0) of the existing
Picard group, taken on the normalization; homomorphisms into them are homomorphisms into
Pic with the stated degree-zero image condition.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- A node with an ordering of its two normalized branches, represented by rational points.
Source: Deligne--Mumford, Lemma 1.15, p.85
(blueprint: lem-sfb-integral-nodal-picard-normalization-action). -/
structure NodalOrderedBranch (k : Type u) [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] where
  node : Spec (.of k) ⟶ Y
  overProof : node ≫ f = 𝟙 _
  singular : ∀ s : Spec (.of k), node s ∉ f.smoothLocus
  minus : Spec (.of k) ⟶ Y.normalization
  plus : Spec (.of k) ⟶ Y.normalization
  minus_map : minus ≫ Y.fromNormalization = node
  plus_map : plus ≫ Y.fromNormalization = node
  distinct : minus ≠ plus

/-- Restrict a normalized trivialization to a branch, transporting its source to the
line fibre at the node by the canonical composition and equality comparisons.
Source: Stacks Project, curves.tex, Tag 0C1J (example-glue-points)
(blueprint: lem-sfb-integral-nodal-picard-normalization-action). -/
noncomputable def nodalFibreTrivialization {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsIntegral Y] (M : Y.Modules)
    (e : (Scheme.Modules.pullback Y.fromNormalization).obj M ≅
      SheafOfModules.unit Y.normalization.ringCatSheaf)
    (p : Spec (.of k) ⟶ Y.normalization) (q : Spec (.of k) ⟶ Y)
    (hp : p ≫ Y.fromNormalization = q) :
    (Scheme.Modules.pullback q).obj M ≅ SheafOfModules.unit (Spec (.of k)).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr hp).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp p Y.fromNormalization).app M).symm ≪≫
    (Scheme.Modules.pullback p).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso p

/-- The scalar for one ordered node is `z`, for its reverse `z⁻¹`, and for every other
node it is `1`. Source: Deligne--Mumford, Lemma 1.15, p.85; Stacks Tag 0C1M
(blueprint: lem-sfb-integral-nodal-picard-normalization-action). -/
noncomputable def nodalBranchScalar {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] {f : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation f]
    (r s : NodalOrderedBranch k f) (z : kˣ) : kˣ := by
  classical
  exact if s.minus = r.minus ∧ s.plus = r.plus then z
    else if s.minus = r.plus ∧ s.plus = r.minus then z⁻¹ else 1

/-- The class obtained by gluing the trivial normalized line with the prescribed scalar
at the ordered node and scalar one at all other nodes. A single normalized trivialization
must satisfy all branch equations simultaneously. The equation says that the plus fibre
coordinate is the prescribed scalar times the minus fibre coordinate.
Source: Stacks Project, curves.tex, Tags 0C1J and 0C1M; Deligne--Mumford, p.85
(blueprint: lem-sfb-integral-nodal-picard-normalization-action). -/
def IsNodalScalarGluing {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    {f : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation f]
    (r : NodalOrderedBranch k f) (z : kˣ) (L : Y.Pic) : Prop :=
  ∃ e : (Scheme.Modules.pullback Y.fromNormalization).obj
      ((fromSkeleton Y.Modules).obj L.val) ≅
        SheafOfModules.unit Y.normalization.ringCatSheaf,
    ∀ s : NodalOrderedBranch k f,
      (nodalFibreTrivialization _ e s.plus s.node s.plus_map).hom =
        (nodalFibreTrivialization _ e s.minus s.node s.minus_map).hom ≫
          Scheme.Modules.smulHom (X := Spec (.of k))
            (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)
            ((Scheme.ΓSpecIso (.of k)).inv.hom (↑(nodalBranchScalar r s z) : k))

/-- Normalization, scalar gluing and the action of Picard-trivial automorphisms of an
integral projective nodal curve. The lift is unique among all scheme endomorphisms
of the normalization commuting with it. Its pullback fixes ordinary degree-zero classes and every
point above the singular locus when the original pullback fixes normalized-degree-zero
classes. The permutation formula uses inverse images, since pullback is contravariant.

Source: Deligne--Mumford, proof of Lemma 1.15, printed p.85; Stacks Project, Tag 0C1M
(blueprint: lem-sfb-integral-nodal-picard-normalization-action).

Proof plan:
1. Projectivity gives properness (lem-kun-projective-implies-proper). Apply
lem-sfb-nodal-completed-normalization-model: normalization is finite, with two rational
branches over each node and isomorphic away from the finite singular set. Integral closure
in the function field is integral, hence connected, so the normalization is one smooth
projective connected curve (def-sc-normalization).
2. An automorphism carries integral closures in the function field to integral closures;
these affine maps glue. Any lift has this same function-field map, proving uniqueness.
3. At a node the completed additive difference sequence has kernel the pairs of power
series with equal constant term. Descend exactness by faithful flatness of completion
(lem-weil-pbc-local-completion-faithfully-flat, lem-weil-pbc-flat-tensor-exact,
lem-sc-faithfully-flat-tensor-zero). The conductor fibre consists of the two reduced points.
4. The affine rings form the conductor fibre product; the map to branch residues is
surjective by the Chinese remainder theorem. Apply lem-sfb-finite-pinching-invertible-patching:
lines are normalized lines with one fibre identification at each node, with tensor product
multiplying these identifications.
5. Choose identifications of the one-dimensional branch fibres of any normalized line.
It descends, and a degree-zero line descends to a normalized-degree-zero class.
6. Gluing trivial lines gives a homomorphism from the product of copies of k*. Its kernel
is trivial: every global unit on the proper connected normalization is a single scalar
(lem-sc-global-functions), so an isomorphism cannot change any gluing parameter.
7. Reversal inverts the coordinate. A root z of T^3-T-1 satisfies z(z^2-1)=1 in every
characteristic (def-weil-algebraic-closure). Evaluation at this z distinguishes both
orderings and all different nodes, by the injectivity of the product homomorphism.
8. Pullback places z at the inverse-image ordered pair; the canonical trivialization and
pinching full faithfulness give precisely the displayed formula. If pullback is the
identity, distinctness forces every ordered pair, hence each branch point, to be fixed.
9. Isomorphisms preserve degree (def-pc-degree-line-bundle). Surjectivity and commutation
of the normalization square transfer Picard-triviality to the normalization. Empty node
sets give empty gluing data, with all branch assertions vacuous.
-/
theorem integral_nodal_picard_normalization_action
    (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of k)) [IsHProjective f] [LocallyOfFinitePresentation f]
    (hnodal : HasNodalGeometricFibres f) :
    Smooth (Y.fromNormalization ≫ f) ∧ IsHProjective (Y.fromNormalization ≫ f) ∧
    ConnectedSpace Y.normalization ∧ topologicalKrullDim Y.normalization = 1 ∧
    (∀ M : Y.normalization.Pic,
      M ∈ (Y.fromNormalization ≫ f).picZero →
      ∃ L : Y.Pic, Scheme.Pic.map Y.fromNormalization L ∈ (Y.fromNormalization ≫ f).picZero ∧
        Scheme.Pic.map Y.fromNormalization L = M) ∧
    (∀ (q : Spec (.of k) ⟶ Y), q ≫ f = 𝟙 _ →
      (∀ s : Spec (.of k), q s ∉ f.smoothLocus) →
      ∃ r : NodalOrderedBranch k f, r.node = q ∧
        ∀ p : Spec (.of k) ⟶ Y.normalization,
          p ≫ Y.fromNormalization = q → p = r.minus ∨ p = r.plus) ∧
    ∃ j : NodalOrderedBranch k f → (kˣ →* Y.Pic),
      (∀ (r : NodalOrderedBranch k f) (z : kˣ),
        IsNodalScalarGluing r z (j r z) ∧
        Scheme.Pic.map Y.fromNormalization (j r z) ∈ (Y.fromNormalization ≫ f).picZero) ∧
      (∀ r : NodalOrderedBranch k f, Function.Injective (j r)) ∧
      Function.Injective j ∧
      ∀ (b : Y ≅ Y), b.hom ≫ f = f →
        ∃ β : Y.normalization ≅ Y.normalization,
          β.hom ≫ Y.fromNormalization = Y.fromNormalization ≫ b.hom ∧
          (∀ γ : Y.normalization ⟶ Y.normalization,
            γ ≫ Y.fromNormalization = Y.fromNormalization ≫ b.hom → γ = β.hom) ∧
          (∀ r : NodalOrderedBranch k f, ∃ s : NodalOrderedBranch k f,
            s.node = r.node ≫ b.inv ∧ s.minus = r.minus ≫ β.inv ∧
            s.plus = r.plus ≫ β.inv ∧
            ∀ z : kˣ, Scheme.Pic.map b.hom (j r z) = j s z) ∧
          (∀ L : Y.Pic,
            Scheme.Pic.map Y.fromNormalization (Scheme.Pic.map b.hom L) ∈
                (Y.fromNormalization ≫ f).picZero ↔
            Scheme.Pic.map Y.fromNormalization L ∈ (Y.fromNormalization ≫ f).picZero) ∧
          (∀ M : Y.normalization.Pic,
            Scheme.Pic.map β.hom M ∈ (Y.fromNormalization ≫ f).picZero ↔
            M ∈ (Y.fromNormalization ≫ f).picZero) ∧
          ((∀ L : Y.Pic, Scheme.Pic.map Y.fromNormalization L ∈ (Y.fromNormalization ≫ f).picZero →
              Scheme.Pic.map b.hom L = L) →
            (∀ M : Y.normalization.Pic,
              M ∈ (Y.fromNormalization ≫ f).picZero →
                Scheme.Pic.map β.hom M = M) ∧
            ∀ p : Y.normalization, Y.fromNormalization p ∉ f.smoothLocus → β.hom p = p) := by
  sorry

end AlgebraicGeometry
