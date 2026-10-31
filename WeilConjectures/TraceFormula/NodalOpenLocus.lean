/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.FirstFittingSingularSubscheme
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.UnramifiedLocusBaseChange
import WeilConjectures.TraceFormula.SyntomicLocusBaseChange
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.TraceFormula.NodalCandidateGeometricCriterion

/-! # The nodal open locus in a flat family

Source: Stacks Project, `curves.tex`, Tag 0DSC, lemma-locus-where-nodal
(blueprint: lem-trf-nodal-open-locus).

## Main definitions and statements

* `IsOrdinaryNode`: a closed point with completed local ring `Ω[[u,v]]/(uv)`.
* `IsSmoothOrOrdinaryNode`: the pointwise disjunction on a geometric fibre.
* `HasOnlySmoothOrNodalGeometricFibres`: this condition on every geometric fibre.
* `nodalOpenLocus`: existence, largestness, base change, and geometric-fibre description.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An ordinary node over `Ω` is a closed point with the specified completed local ring.
The coefficient field is algebraically closed whenever this predicate is used below.
Source: Stacks Project, `curves.tex`, definition-nodal and Tag 0DSC
(blueprint: lem-trf-nodal-open-locus). -/
def IsOrdinaryNode (Ω : Type u) [Field Ω] (X : Scheme.{u}) (x : X) : Prop :=
  x ∈ closedPoints X ∧ Nonempty
    (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+*
      (MvPowerSeries (Fin 2) Ω ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
          (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))

/-- A point of a geometric fibre is smooth or an ordinary node.
Source: Stacks Project, `curves.tex`, Tag 0DSC (blueprint: lem-trf-nodal-open-locus). -/
def IsSmoothOrOrdinaryNode {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation f] (x : X) : Prop :=
  x ∈ (f.smoothLocus : Set X) ∨ IsOrdinaryNode Ω X x

/-- Every geometric fibre of `f` consists of smooth points and ordinary nodes.
Geometric tests use the scheme universe, as for Mathlib's geometric morphism properties;
no test-field universe smaller than the scheme universe is introduced.
Source: Stacks Project, `curves.tex`, Tag 0DSC (blueprint: lem-trf-nodal-open-locus). -/
def HasOnlySmoothOrNodalGeometricFibres {X T : Scheme.{u}} (f : X ⟶ T)
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
    ∀ x : (pullback (C := Scheme.{u}) f g),
      IsSmoothOrOrdinaryNode (pullback.snd f g) x

private theorem ordinaryNode_openImmersion
    {Ω : Type u} [Field Ω] {C D : Scheme.{u}} [JacobsonSpace C]
    (e : D ⟶ C) [IsOpenImmersion e] (y : D) :
    IsOrdinaryNode Ω D y ↔ IsOrdinaryNode Ω C (e y) := by
  have hc : y ∈ closedPoints D ↔ e y ∈ closedPoints C := by
    exact (Set.ext_iff.mp e.isOpenEmbedding.preimage_closedPoints y).symm
  let r := (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv
  obtain ⟨E, _⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
    (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) r
    (IsLocalRing.map_ringEquiv_maximalIdeal r).symm
  exact and_congr hc ⟨fun ⟨q⟩ => ⟨E.trans q⟩, fun ⟨q⟩ => ⟨E.symm.trans q⟩⟩

private theorem smoothOrNode_openImmersion
    {Ω : Type u} [Field Ω] {C D : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation f]
    (e : D ⟶ C) [IsOpenImmersion e] (y : D) :
    IsSmoothOrOrdinaryNode (e ≫ f) y ↔ IsSmoothOrOrdinaryNode f (e y) := by
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace f
  have hs : y ∈ (e ≫ f).smoothLocus ↔ e y ∈ f.smoothLocus := by
    rw [← e.preimage_smoothLocus_eq f]
    rfl
  exact or_congr hs (ordinaryNode_openImmersion e y)

private theorem open_fibre_good_iff
    {Y T : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFinitePresentation p] (U : Y.Opens) :
    HasOnlySmoothOrNodalGeometricFibres (U.ι ≫ p) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
        ∀ x : pullback (C := Scheme.{u}) p g, pullback.fst p g x ∈ U →
          IsSmoothOrOrdinaryNode (pullback.snd p g) x := by
  constructor
  · intro h Ω _ _ g x hx
    let q := pullbackRightPullbackFstIso p g U.ι
    let e := q.inv ≫ pullback.snd U.ι (pullback.fst p g)
    have he : e ≫ pullback.snd p g = pullback.snd (U.ι ≫ p) g := by
      simp [e, q]
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := U.ι) (g := pullback.fst p g) (⟨pullback.fst p g x, hx⟩ : U) x rfl
    have hi := smoothOrNode_openImmersion (pullback.snd p g) e (q.hom z)
    simp only [he] at hi
    have hx' : e (q.hom z) = x := by
      change (q.hom ≫ q.inv ≫ pullback.snd U.ι (pullback.fst p g)) z = x
      simpa only [Iso.hom_inv_id_assoc] using hz
    rw [hx'] at hi
    exact hi.mp (h Ω g (q.hom z))
  · intro h Ω _ _ g z
    let q := pullbackRightPullbackFstIso p g U.ι
    let e := q.inv ≫ pullback.snd U.ι (pullback.fst p g)
    have he : e ≫ pullback.snd p g = pullback.snd (U.ι ≫ p) g := by
      simp [e, q]
    have hy : pullback.fst p g (e z) ∈ U := by
      have hf : e ≫ pullback.fst p g = pullback.fst (U.ι ≫ p) g ≫ U.ι := by
        simp [e, q, ← pullback.condition]
      rw [← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply]
      exact (pullback.fst (U.ι ≫ p) g z).property
    have hi := smoothOrNode_openImmersion (pullback.snd p g) e z
    simp only [he] at hi
    exact hi.mpr (h Ω g (e z) hy)

private theorem points_detected_by_geometric_pullbacks
    {Y T : Scheme.{u}} (p : Y ⟶ T) (P : Y → Prop)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
      ∀ x : pullback (C := Scheme.{u}) p g, P (pullback.fst p g x)) :
    ∀ y : Y, P y := by
  intro y
  let Ω := AlgebraicClosure (Y.residueField y)
  let a : Spec (.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y
  let z : Spec (.of Ω) ⟶ pullback p (a ≫ p) :=
    pullback.lift a (𝟙 _) (by simp)
  have hy : pullback.fst p (a ≫ p) (z default) = y := by
    change (z ≫ pullback.fst p (a ≫ p)) default = y
    simp only [z, pullback.lift_fst]
    exact Scheme.fromSpecResidueField_apply y _
  simpa only [hy] using h Ω (a ≫ p) (z default)

private theorem greatest_of_geometric_membership
    {Y T : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFinitePresentation p] (U : Y.Opens)
    (hm : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
      ∀ x : pullback (C := Scheme.{u}) p g,
        pullback.fst p g x ∈ U ↔ IsSmoothOrOrdinaryNode (pullback.snd p g) x) :
    HasOnlySmoothOrNodalGeometricFibres (U.ι ≫ p) ∧
      ∀ V : Y.Opens, HasOnlySmoothOrNodalGeometricFibres (V.ι ≫ p) → V ≤ U := by
  refine ⟨(open_fibre_good_iff p U).mpr (fun Ω _ _ g x hx => (hm Ω g x).mp hx), ?_⟩
  intro V hV
  apply points_detected_by_geometric_pullbacks p (fun y => y ∈ V → y ∈ U)
  intro Ω _ _ g x hx
  exact (hm Ω g x).mpr ((open_fibre_good_iff p V).mp hV Ω g x hx)

private theorem geometric_membership_baseChange
    {Y T T' : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFinitePresentation p]
    (U : Y.Opens)
    (hm : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
      ∀ x : pullback (C := Scheme.{u}) p g,
        pullback.fst p g x ∈ U ↔ IsSmoothOrOrdinaryNode (pullback.snd p g) x)
    (g : T' ⟶ T) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (h : Spec (.of Ω) ⟶ T'),
      ∀ x : pullback (C := Scheme.{u}) (pullback.snd p g) h,
        pullback.fst (pullback.snd p g) h x ∈ pullback.fst p g ⁻¹ᵁ U ↔
          IsSmoothOrOrdinaryNode (pullback.snd (pullback.snd p g) h) x := by
  intro Ω _ _ h x
  let q := pullbackLeftPullbackSndIso p g h
  have hi := smoothOrNode_openImmersion (pullback.snd p (h ≫ g)) q.hom x
  have hq : q.hom ≫ pullback.snd p (h ≫ g) =
      pullback.snd (pullback.snd p g) h := by simp [q]
  simp only [hq] at hi
  have hm' := hm Ω (h ≫ g) (q.hom x)
  have hf : pullback.fst p (h ≫ g) (q.hom x) =
      pullback.fst p g (pullback.fst (pullback.snd p g) h x) := by
    change (q.hom ≫ pullback.fst p (h ≫ g)) x = _
    simp [q]
  rw [hf] at hm'
  exact hm'.trans hi.symm

private theorem fibre_all_mem_iff_geometric
    {Y T : Scheme.{u}} (p : Y ⟶ T) (U : Y.Opens) (t : T)
    (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω] :
    (∀ x : pullback (C := Scheme.{u}) p (T.fromSpecResidueField t),
      pullback.fst p (T.fromSpecResidueField t) x ∈ U) ↔
    (∀ x : pullback (C := Scheme.{u}) p
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t),
      pullback.fst p
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t) x ∈ U) := by
  let k := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω))
  let q := pullbackLeftPullbackSndIso p (T.fromSpecResidueField t) k
  constructor
  · intro H x
    have hx := H (pullback.fst (pullback.snd p (T.fromSpecResidueField t)) k (q.inv x))
    change (q.inv ≫ pullback.fst _ _ ≫ pullback.fst _ _) x ∈ U at hx
    simpa only [q, pullbackLeftPullbackSndIso_inv_fst] using hx
  · intro H x
    obtain ⟨z, hz⟩ := (pullback.fst
      (pullback.snd p (T.fromSpecResidueField t)) k).surjective x
    have hx := H (q.hom z)
    change (q.hom ≫ pullback.fst _ _) z ∈ U at hx
    simpa only [q, pullbackLeftPullbackSndIso_hom_fst, Scheme.Hom.comp_apply, hz] using hx

private theorem isOpen_nodalCandidateSet
    {Y T : Scheme.{u}} (p : Y ⟶ T) [Flat p] [LocallyOfFinitePresentation p] :
    IsOpen ((Scheme.firstFittingSingularSubscheme p) ''
      (((Scheme.firstFittingSingularSubscheme p) ⁻¹' p.fiberCompleteIntersectionLocus ∩
        unramifiedLocus (Scheme.firstFittingSingularSubscheme p ≫ p))ᶜ))ᶜ := by
  obtain ⟨V, hV, _⟩ := (syntomic_locus_base_change p).2
    (inferInstance : Flat p) (inferInstance : LocallyOfFinitePresentation p)
  have hv : IsOpen p.fiberCompleteIntersectionLocus := hV ▸ V.2
  have hw := (hv.preimage (Scheme.firstFittingSingularSubscheme p).continuous).inter
    (unramifiedLocus_baseChange (Scheme.firstFittingSingularSubscheme p ≫ p)).1
  exact ((Scheme.firstFittingSingularSubscheme p).isClosedEmbedding.isClosedMap _
    hw.isClosed_compl).isOpen_compl

private noncomputable def nodalCandidate
    {Y T : Scheme.{u}} (p : Y ⟶ T) [Flat p] [LocallyOfFinitePresentation p] : Y.Opens :=
  ⟨_, isOpen_nodalCandidateSet p⟩

/-- The largest nodal open of a flat, locally finitely presented family with pure
one-dimensional nonempty geometric fibres, compatible with arbitrary base change.

Source: Stacks Project, `curves.tex`, Tag 0DSC, lemma-locus-where-nodal
(blueprint: lem-trf-nodal-open-locus).

Proof: Let Z be the first-Fitting singular closed subscheme, V the fibrewise
complete-intersection locus, and W the unramified locus of Z over the base.
Construct U as the complement of the image of Z \ (V ∩ W). The syntomic-locus
and unramified-locus theorems make V and W open; the closed immersion Z → Y
sends the complementary closed subset to a closed subset, so U is open.
The pointwise geometric criterion identifies its inverse image on every
geometric fibre with the smooth points and ordinary nodes.

Open immersions preserve the predicate: smooth loci pull back, closed points
are preserved between open subschemes of a Jacobson scheme, and stalk
isomorphisms induce maximal-ideal-adic completion isomorphisms. Associativity
of pullbacks therefore shows that U has the required fibres. Any other good
open is contained in U after every geometric pullback; a point lifts through
the algebraic closure of its residue field, so this containment holds on Y.
The same argument, using the iterated-pullback isomorphism, proves largestness
of the inverse image after arbitrary base change. Finally the projection from
a geometric fibre to the residue-field fibre is surjective, so the entire
ordinary fibre lies in U exactly when every nonsmooth geometric point is nodal.
-/
theorem nodalOpenLocus
    (Y T : Scheme.{u}) (p : Y ⟶ T) [Flat p]
    [LocallyOfFinitePresentation p]
    (hgeom : ∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
      [IsAlgClosure (T.residueField t) Ω],
      Nonempty (pullback (C := Scheme.{u}) p
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t)) →
      (pullback p (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
        T.fromSpecResidueField t)).IsPureDimension 1) :
    ∃ U : Y.Opens,
      HasOnlySmoothOrNodalGeometricFibres (U.ι ≫ p) ∧
      (∀ V : Y.Opens,
        HasOnlySmoothOrNodalGeometricFibres (V.ι ≫ p) → V ≤ U) ∧
      (∀ (T' : Scheme.{u}) (g : T' ⟶ T),
        HasOnlySmoothOrNodalGeometricFibres
            ((pullback.fst p g ⁻¹ᵁ U).ι ≫ pullback.snd p g) ∧
        (∀ V : (pullback p g).Opens,
          HasOnlySmoothOrNodalGeometricFibres (V.ι ≫ pullback.snd p g) →
            V ≤ pullback.fst p g ⁻¹ᵁ U)) ∧
      (∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
        [IsAlgClosure (T.residueField t) Ω],
        ∀ x : (pullback (C := Scheme.{u}) p
          (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
            T.fromSpecResidueField t)),
          pullback.fst p
              (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                T.fromSpecResidueField t) x ∈ U ↔
            IsSmoothOrOrdinaryNode
              (pullback.snd p
                (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                  T.fromSpecResidueField t)) x) ∧
      (∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
        [IsAlgClosure (T.residueField t) Ω],
        ((∀ x : (pullback (C := Scheme.{u}) p (T.fromSpecResidueField t)),
            pullback.fst p (T.fromSpecResidueField t) x ∈ U) ↔
          (∀ x : (pullback (C := Scheme.{u}) p
              (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                T.fromSpecResidueField t)),
            x ∉ (pullback.snd p
                (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                  T.fromSpecResidueField t)).smoothLocus →
              IsOrdinaryNode Ω
                (pullback p
                  (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
                    T.fromSpecResidueField t)) x))) := by
  classical
  let U := nodalCandidate p
  have hm : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T),
      ∀ x : pullback (C := Scheme.{u}) p g,
        pullback.fst p g x ∈ U ↔ IsSmoothOrOrdinaryNode (pullback.snd p g) x := by
    intro Ω _ _ g x
    exact nodalCandidate_geometric_criterion Y T p hgeom Ω g x
  obtain ⟨hU, hmax⟩ := greatest_of_geometric_membership p U hm
  refine ⟨U, hU, hmax, ?_, ?_, ?_⟩
  · intro T' g
    exact greatest_of_geometric_membership (pullback.snd p g)
      (pullback.fst p g ⁻¹ᵁ U) (geometric_membership_baseChange p U hm g)
  · intro t Ω _ _ _
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (T.residueField t)
    exact hm Ω _
  · intro t Ω _ _ _
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (T.residueField t)
    refine (fibre_all_mem_iff_geometric p U t Ω).trans ?_
    constructor
    · intro H x hsing
      exact ((hm Ω _ x).mp (H x)).resolve_left hsing
    · intro H x
      apply (hm Ω _ x).mpr
      by_cases hx : x ∈ (pullback.snd p
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t)).smoothLocus
      · exact Or.inl hx
      · exact Or.inr (H x hx)

end AlgebraicGeometry
