/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.ZetaSeries
import WeilConjectures.AlgebraicGeometry.ComplementaryPureSubcurveBoundaryFinite
import WeilConjectures.AlgebraicGeometry.FiniteReducedDiscreteResidueFields
import WeilConjectures.AlgebraicGeometry.SplitNodeCompletionTransport
import WeilConjectures.AlgebraicGeometry.SplitNodalSubcurveLocalDichotomy
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.PointCount
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Reduced closed subcurves of a split nodal curve

Source: Stacks Project, `curves.tex`, Tag 0E38 (1), (2)(a)--(c), specialized to
split nodes in the sense of Tags 0C4D and 0CBU
(blueprint: lem-trf-stacks-nodal-closed-subcurve).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem residue_separable_of_closed_immersion
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Y ⟶ X) [IsClosedImmersion i] (y : Y)
    (hfin : (f.residueFieldAlgebraMap (i y)).Finite)
    (hsep : @Algebra.IsSeparable k (X.residueField (i y)) _ _
      (f.residueFieldAlgebraMap (i y)).toAlgebra) :
    ((i ≫ f).residueFieldAlgebraMap y).Finite ∧
      @Algebra.IsSeparable k (Y.residueField y) _ _
        ((i ≫ f).residueFieldAlgebraMap y).toAlgebra := by
  have := i.isIso_residueFieldMap y
  let := (f.residueFieldAlgebraMap (i y)).toAlgebra
  let := ((i ≫ f).residueFieldAlgebraMap y).toAlgebra
  let e : X.residueField (i y) ≃ₐ[k] Y.residueField y :=
    { (asIso (i.residueFieldMap y)).commRingCatIsoToRingEquiv with
      commutes' a := by
        change _ = (i ≫ f).residueFieldAlgebraMap y a
        rw [Scheme.Hom.residueFieldAlgebraMap_comp]
        rfl }
  have := hsep
  refine ⟨?_, AlgEquiv.Algebra.isSeparable e⟩
  rw [Scheme.Hom.residueFieldAlgebraMap_comp]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (i.residueFieldMap y)).2).comp hfin

private theorem stalk_scalar_compatibility
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Y ⟶ X) (y : Y) (a : k) :
    (i.stalkMap y).hom
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm (i y)).hom a) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫
        Y.presheaf.Γgerm y).hom a) := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.Γgerm (i y) ≫ i.stalkMap y).hom a = _
  simp only [TopCat.Presheaf.Γgerm]
  rw [i.germ_stalkMap ⊤ y (by trivial)]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rfl

/-- A reduced closed pure subcurve of a split nodal curve is again split nodal.
Its intersection with the scheme-theoretic complementary closure is a finite disjoint
union of spectra of finite separable extensions of the ground field, consists of ambient
nonsmooth nodes, and lies in the smooth locus of the subcurve.

The complementary closure is the canonical scheme-theoretic image of the complementary
open immersion. The intersection is the scheme pullback of its inclusion and `i`.
Every completion isomorphism below respects the original `k`-structure: the displayed
scalar identity is exactly the condition of being a `k`-algebra isomorphism. The disjoint
union isomorphism likewise commutes with the maps to `Spec k` on every summand.

Source: Stacks Project, `curves.tex`, Tag 0E38 (1), (2)(a)--(c), with the split
completed-local-ring convention of Tags 0C4D and 0CBU
(blueprint: lem-trf-stacks-nodal-closed-subcurve).

Proof: The boundary-finiteness theorem gives a finite discrete intersection with closed
ambient image points. The local dichotomy separates stalk-isomorphism points from boundary
branch points. At a nonsmooth point of Y the smooth-branch alternative is impossible, so the
stalk and residue-field isomorphisms transport the ambient nodal presentation; the transport
lemma retains its k-scalar identity. At a boundary point the stalk-isomorphism alternative
is excluded by the pullback condition. The branch alternative gives smoothness on Y and
field stalks on the intersection, while the ambient hypothesis gives its nonsmooth nodal
presentation. Field stalks make the intersection reduced. Finally the canonical residue
maps identify this finite discrete reduced scheme with the coproduct of its residue-field
spectra, whose embeddings are finite separable and commute with the maps to Spec k.
-/
theorem stacks_nodal_closed_subcurve
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (hnodal : ∀ x : X, IsClosed ({x} : Set X) →
      (¬ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) →
      (f.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (X.residueField x) _ _
        (f.residueFieldAlgebraMap x).toAlgebra ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) (X.residueField x) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (X.residueField x)) *
              MvPowerSeries.X 1}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (f.residueFieldAlgebraMap x a)))
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1) :
    (∀ y : Y, IsClosed ({y} : Set Y) →
      (¬ ∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) →
      ((i ≫ f).residueFieldAlgebraMap y).Finite ∧
      @Algebra.IsSeparable k (Y.residueField y) _ _
        ((i ≫ f).residueFieldAlgebraMap y).toAlgebra ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y) ≃+*
          (MvPowerSeries (Fin 2) (Y.residueField y) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (Y.residueField y)) *
              MvPowerSeries.X 1}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y)
            (((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫
              Y.presheaf.Γgerm y).hom a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C ((i ≫ f).residueFieldAlgebraMap y a))) ∧
    (∃ (n : ℕ) (K : Fin n → Type u) (_ : ∀ a, Field (K a)) (ι : ∀ a, k →+* K a),
      (∀ a, (ι a).Finite ∧ @Algebra.IsSeparable k (K a) _ _ (ι a).toAlgebra) ∧
      ∃ e : (∐ fun a : Fin n => Spec (.of (K a))) ≅
          pullback (C := Scheme.{u}) i
            (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
        ∀ a : Fin n,
          Sigma.ι (fun b : Fin n => Spec (.of (K b))) a ≫ e.hom ≫
            pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι ≫ i ≫ f =
          Spec.map (CommRingCat.ofHom (ι a))) ∧
    (∀ t : pullback (C := Scheme.{u}) i
        (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
      ¬(∃ U : X.Opens,
        i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t) ∈ U ∧
          Smooth (U.ι ≫ f)) ∧
      (∃ e : AdicCompletion
          (IsLocalRing.maximalIdeal (X.presheaf.stalk
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))))
          (X.presheaf.stalk
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))) ≃+*
          (MvPowerSeries (Fin 2) (X.residueField
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (X.residueField
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t)))) *
                MvPowerSeries.X 1}),
        ∀ a : k,
          e (AdicCompletion.of
            (IsLocalRing.maximalIdeal (X.presheaf.stalk
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))))
            (X.presheaf.stalk
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t)))
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))).hom
                a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (f.residueFieldAlgebraMap
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t)) a))) ∧
      ∃ U : Y.Opens,
        pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t ∈ U ∧
          Smooth (U.ι ≫ i ≫ f)) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let j := (Scheme.openComplementOfIsClosedImmersion i).ι.imageι
  let T := pullback (C := Scheme.{u}) i j
  let b : T ⟶ X := pullback.fst i j ≫ i
  obtain ⟨hfin, hdisc, hclosed⟩ := complementary_pure_subcurve_boundary_finite hX i hY
  have : Finite T := hfin
  have : DiscreteTopology T := hdisc
  have hlocal (y : Y) (hy : IsClosed ({y} : Set Y)) :
      (∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)) ∨
      ((f.residueFieldAlgebraMap (i y)).Finite ∧
        @Algebra.IsSeparable k (X.residueField (i y)) _ _
          (f.residueFieldAlgebraMap (i y)).toAlgebra ∧
        Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (i y)))
          (X.presheaf.stalk (i y)) ≃+*
          (MvPowerSeries (Fin 2) (X.residueField (i y)) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2)
              (X.residueField (i y))) * MvPowerSeries.X 1}))) := by
    by_cases hsm : ∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)
    · exact Or.inl hsm
    · have hx : IsClosed ({i y} : Set X) := by
        simpa using i.isClosedEmbedding.isClosedMap _ hy
      obtain ⟨hf, hs, e, _⟩ := hnodal (i y) hx hsm
      exact Or.inr ⟨hf, hs, ⟨e⟩⟩
  have hboundary (t : T) :
      (¬ ∃ U : X.Opens, b t ∈ U ∧ Smooth (U.ι ≫ f)) ∧
      (∃ U : Y.Opens, pullback.fst i j t ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) ∧
      IsField (T.presheaf.stalk t) := by
    let y := pullback.fst i j t
    have hy : IsClosed ({y} : Set Y) := by
      have h := (hclosed t).preimage i.continuous
      have heq : i ⁻¹' {i y} = {y} := by
        ext z
        exact i.isClosedEmbedding.injective.eq_iff
      rwa [heq] at h
    rcases split_nodal_subcurve_local_dichotomy f hX i hY y hy (hlocal y hy) with
      ⟨_, _, hnot⟩ | ⟨hns, hs, hfield⟩
    · exact False.elim (hnot ⟨pullback.snd i j t, by
        have h := congrArg (fun a : T ⟶ X ↦ a t) (pullback.condition (f := i) (g := j))
        exact h.symm⟩)
    · exact ⟨hns, hs, hfield t rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro y hy hns
    rcases split_nodal_subcurve_local_dichotomy f hX i hY y hy (hlocal y hy) with
      ⟨hiso, hsm, _⟩ | ⟨_, hsm, _⟩
    · have hnX : ¬ ∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f) :=
        fun h ↦ hns (hsm h)
      have hx : IsClosed ({i y} : Set X) := by
        simpa using i.isClosedEmbedding.isClosedMap _ hy
      obtain ⟨hf, hs, e, he⟩ := hnodal (i y) hx hnX
      obtain ⟨hfy, hsy⟩ := residue_separable_of_closed_immersion f i y hf hs
      have := i.isIso_residueFieldMap y
      let eA := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
      let eF := (asIso (i.residueFieldMap y)).commRingCatIsoToRingEquiv
      refine ⟨hfy, hsy, ?_⟩
      apply split_node_completion_transport
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm (i y)).hom)
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫ Y.presheaf.Γgerm y).hom)
        (f.residueFieldAlgebraMap (i y)) ((i ≫ f).residueFieldAlgebraMap y) eA eF
        (stalk_scalar_compatibility f i y) ?_ e he
      intro a
      rw [Scheme.Hom.residueFieldAlgebraMap_comp]
      rfl
    · exact False.elim (hns hsm)
  · have hfield (t : T) : IsField (T.presheaf.stalk t) := (hboundary t).2.2
    have hred (t : T) : _root_.IsReduced (T.presheaf.stalk t) := by
      let := (hfield t).toField
      infer_instance
    have : IsReduced T := isReduced_of_isReduced_stalk T
    exact finite_reduced_discrete_residue_fields T (b ≫ f) (fun t ↦ by
      have hnode := hnodal (b t) (hclosed t) (hboundary t).1
      exact residue_separable_of_closed_immersion f b t hnode.1 hnode.2.1)
  · intro t
    exact ⟨(hboundary t).1,
      (hnodal (b t) (hclosed t) (hboundary t).1).2.2, (hboundary t).2.1⟩

end AlgebraicGeometry
