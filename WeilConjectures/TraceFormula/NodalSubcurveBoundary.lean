/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.TraceFormula.ReducedSchemeImage
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.ComplementaryPureSubcurveComponents
import WeilConjectures.AlgebraicGeometry.StacksNodalClosedSubcurve
import WeilConjectures.RingTheory.NodalCoefficientStraightening
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Reduced nodal subcurves and their boundary

Source: Stacks Project, `curves.tex`, Tag 0E38 (blueprint: lem-trf-nodal-subcurve-boundary).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closed subscheme supported on the closure of the complement of a
closed immersion.  Source: Stacks Project, `curves.tex`, Tag 0E38
(blueprint: lem-trf-nodal-subcurve-boundary). -/
noncomputable def reducedComplement {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.mk
      (closure (Set.range (Scheme.openComplementOfIsClosedImmersion i).ι))
      isClosed_closure)).subscheme

/-- The canonical inclusion of the reduced complement into the ambient scheme.
Source: Stacks Project, `curves.tex`, Tag 0E38 (blueprint: lem-trf-nodal-subcurve-boundary). -/
noncomputable def reducedComplementι {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : reducedComplement i ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.mk
      (closure (Set.range (Scheme.openComplementOfIsClosedImmersion i).ι))
      isClosed_closure)).subschemeι

/-- The canonical inclusion of the scheme-theoretic boundary.  The fibre product
of two closed immersions is locally the quotient by the sum of their ideals.
Source: Stacks Project, Tag 0E38 (blueprint: lem-trf-nodal-subcurve-boundary). -/
noncomputable def reducedBoundaryι {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] :
    pullback (C := Scheme.{u}) i (reducedComplementι i) ⟶ X :=
  pullback.fst i (reducedComplementι i) ≫ i

private theorem reduced_closed_iso_of_range_eq {A B X : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ X) [IsClosedImmersion a] [IsClosedImmersion b]
    [IsReduced A] [IsReduced B] (hr : Set.range a = Set.range b) :
    ∃ e : A ≅ B, e.hom ≫ b = a := by
  have hk : a.ker = b.ker := by
    rw [a.ker_eq_vanishingIdeal, b.ker_eq_vanishingIdeal]
    congr 1
    exact congrArg TopologicalSpace.Closeds.closure hr
  have : IsIso (IsClosedImmersion.lift b a hk.ge) :=
    IsClosedImmersion.isIso_lift b a hk.symm
  exact ⟨asIso (IsClosedImmersion.lift b a hk.ge), IsClosedImmersion.lift_fac _ _ _⟩

private theorem complement_image_range {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsReduced X] :
    IsReduced (Scheme.openComplementOfIsClosedImmersion i).ι.image ∧
      Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι =
        closure ((Set.range i)ᶜ) := by
  have h := schemeTheoreticImage_reduced _ _
    (Scheme.openComplementOfIsClosedImmersion i).ι
  refine ⟨h.2.1, h.2.2.2.1.trans ?_⟩
  rw [Scheme.Opens.range_ι]
  rfl

private noncomputable def nodalModelCongr
    {K L : Type u} [Field K] [Field L] (e : K ≃+* L) :
    (MvPowerSeries (Fin 2) K ⧸ Ideal.span
      {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * MvPowerSeries.X 1}) ≃+*
    (MvPowerSeries (Fin 2) L ⧸ Ideal.span
      {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) L) * MvPowerSeries.X 1}) := by
  let E : MvPowerSeries (Fin 2) K ≃+* MvPowerSeries (Fin 2) L :=
    RingEquiv.ofRingHom (MvPowerSeries.map e.toRingHom) (MvPowerSeries.map e.symm.toRingHom)
      (by ext a d; simp) (by ext a d; simp)
  exact Ideal.quotientEquiv _ _ E (by
    rw [Ideal.map_span, Set.image_singleton]
    simp [E, MvPowerSeries.map_X])

private theorem completion_congr {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  obtain ⟨E, _⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) e
    (IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective).symm
  exact ⟨E⟩

private theorem smooth_iff_neighbourhood {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) :
    (f.stalkMap x).hom.FormallySmooth ↔
      ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  constructor
  · intro h
    have hs : Smooth (f.smoothLocus.ι ≫ f) := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff,
        ← Scheme.Hom.preimage_smoothLocus_eq]
      simp
    exact ⟨f.smoothLocus, h, hs⟩
  · rintro ⟨U, hx, hU⟩
    have := hU
    have h := (U.ι ≫ f).smoothLocus_eq_top
    have hx' : (⟨x, hx⟩ : U) ∈ (U.ι ≫ f).smoothLocus := by rw [h]; trivial
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hx'

private theorem closed_residue_bijective
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : x ∈ closedPoints X) :
    Function.Bijective (f.residueFieldAlgebraMap x) := by
  have heq : CommRingCat.ofHom (f.residueFieldAlgebraMap x) =
      (residueFieldIsoBase f x hx).inv := by
    apply Spec.map_injective
    rw [Scheme.Hom.specMap_residueFieldAlgebraMap, SpecMap_residueFieldIsoBase_inv]
  change Function.Bijective (CommRingCat.ofHom (f.residueFieldAlgebraMap x)).hom
  rw [heq]
  exact (residueFieldIsoBase f x hx).commRingCatIsoToRingEquiv.symm.bijective

private theorem scalar_nodal_completion {k R : Type u} [Field k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (β : k →+* R)
    (hβ : Function.Surjective ((IsLocalRing.residue R).comp β))
    (E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span
        {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        (MvPowerSeries (Fin 2) k ⧸ Ideal.span
          {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
      ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal R) R (β a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C a) := by
  let S := MvPowerSeries (Fin 2) k
  let I : Ideal S := Ideal.span {(MvPowerSeries.X 0 : S) * MvPowerSeries.X 1}
  let T := S ⧸ I
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let α : k →+* T := E.toRingHom.comp ((algebraMap R A).comp β)
  have : Nontrivial T := E.injective.nontrivial
  have : IsLocalRing T := IsLocalRing.of_surjective' E.toRingHom E.surjective
  have hmS : IsLocalRing.maximalIdeal S =
      Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → S)) := by
    rw [← (MvPowerSeries.quotient_first_variables k 2 2 le_rfl).2.2.2.2.1]
    ext v
    change (¬ IsUnit (v : MvPowerSeries (Fin 2) k)) ↔
      MvPowerSeries.constantCoeff v = 0
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  have hmT : IsLocalRing.maximalIdeal T =
      (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → S))).map
        (Ideal.Quotient.mk I) := by
    rw [← hmS]
    exact (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).symm
  obtain ⟨d, hd⟩ := MvPowerSeries.nodal_coefficient_straightening k α (by
    intro z
    obtain ⟨r, hr⟩ := (AdicCompletion.residueField_map_bijective R).2
      (IsLocalRing.residue A (E.symm z))
    obtain ⟨a, ha⟩ := hβ r
    refine ⟨a, ?_⟩
    rw [← hmT]
    have hmem : E.symm z - algebraMap R A (β a) ∈ IsLocalRing.maximalIdeal A := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, ← IsLocalRing.ResidueField.map_residue]
      change IsLocalRing.residue A (E.symm z) -
        IsLocalRing.ResidueField.map (algebraMap R A)
          (((IsLocalRing.residue R).comp β) a) = 0
      rw [ha, hr, sub_self]
    have hmap := Ideal.mem_map_of_mem E.toRingHom hmem
    rw [IsLocalRing.map_maximalIdeal_of_surjective E.toRingHom E.surjective] at hmap
    change E (E.symm z - algebraMap R A (β a)) ∈ IsLocalRing.maximalIdeal T at hmap
    change z - E ((algebraMap R A) (β a)) ∈ IsLocalRing.maximalIdeal T
    simpa only [map_sub, E.apply_symm_apply] using hmap)
  exact ⟨E.trans d, hd⟩

private theorem residue_scalar_germ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    (IsLocalRing.residue (X.presheaf.stalk x)).comp
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom) =
      f.residueFieldAlgebraMap x := by
  have h : CommRingCat.ofHom (algebraMap (CommRingCat.of k)
      (f.base x).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv ≫ f.residueFieldMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc, Scheme.residue_residueFieldMap,
      Scheme.Hom.germ_stalkMap_assoc]
    rfl
  exact congrArg CommRingCat.Hom.hom h.symm

/-- A reduced pure one-dimensional subcurve of a nodal neighbourhood is nodal;
its scheme-theoretic boundary is a finite disjoint union of rational points,
which are nodes of the ambient scheme and smooth on both subcurves.
Source: Stacks Project, `curves.tex`, Tag 0E38, (1), (2)(a)--(c)
(blueprint: lem-trf-nodal-subcurve-boundary).

Proof plan:
1. A field is Noetherian. By lem-weil-pbc-finite-type-over-noetherian, X is
   Noetherian. Its open N is Noetherian and quasi-compact by
   lem-weil-pbc-noetherian-open-subscheme-noetherian. Reducedness restricts
   to N, and finitely many restricted finite-type charts make N finite type.
   Y is still reduced, closed and pure of dimension one in N. If N is empty,
   Y and the boundary are empty and all assertions are vacuous.
2. Apply lem-sbc-equidimensional-open-local-dimension to X, its full open,
   and n = 1. Then lem-sbc-constant-local-dimension-components on the open N
   gives pure dimension one for N.
3. Put W equal to the reduced closure of N minus Y in N.
   By lem-trf-complementary-pure-subcurve-components, W is pure of dimension
   one, possibly empty, and its reduced complementary closure is Y.
   Both complementary opens are reduced, so lem-trf-reduced-scheme-image
   identifies their scheme-theoretic closures with W and Y.
4. The immersion of X minus Y into X is quasi-compact because X is Noetherian,
   and quasi-separated because it is an immersion. Its reduced image is Z by
   lem-trf-reduced-scheme-image. Apply lemma-nagata-scheme-image-restrict-open
   to identify W with Z restricted to N. Since Y lies in N, the intersections
   Y cap W and Y cap Z agree, including their sum-of-ideals scheme structure.
5. Apply lem-trf-stacks-nodal-closed-subcurve to N and Y. The previous steps
   supply every ambient hypothesis. The base is algebraically closed, so
   lem-weil-pbc-closed-point-residue-field-base identifies closed residue fields
   with k. Tag 0E38 gives nodality of Y, a finite separable boundary, ambient
   nodes, and smoothness on Y. The local rings of N and X agree.
6. Every finite extension of an algebraically closed field is the base field:
   each minimal polynomial splits and is irreducible, hence linear. Therefore
   the boundary is a finite disjoint union of copies of Spec k, including the
   empty union.
7. If W is empty, the boundary is empty. Otherwise apply
   lem-trf-stacks-nodal-closed-subcurve to N and W, whose complementary closure
   is Y by step 3. Its smoothness conclusion gives smoothness of W along the
   boundary. Since W is the restriction of Z to N, Z is smooth there too.
-/
theorem nodal_subcurve_boundary
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X] (hpureX : X.IsPureDimension 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hpureY : Y.IsPureDimension 1) (N : X.Opens)
    (hN : ∀ y : Y, i y ∈ N)
    (hnodal : ∀ (x : X), x ∈ N → x ∈ closedPoints X →
      ¬(f.stalkMap x).hom.FormallySmooth →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))) :
    (∀ (x : Y), x ∈ closedPoints Y →
      ¬((i ≫ f).stalkMap x).hom.FormallySmooth →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
          (Y.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))) ∧
    (∃ n : ℕ, Nonempty
      (pullback (C := Scheme.{u}) i (reducedComplementι i) ≅
        ∐ fun _ : Fin n => Spec (.of k))) ∧
    (∀ t : pullback (C := Scheme.{u}) i (reducedComplementι i),
      reducedBoundaryι i t ∈ closedPoints X ∧
      ¬(f.stalkMap (reducedBoundaryι i t)).hom.FormallySmooth ∧
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (reducedBoundaryι i t)))
          (X.presheaf.stalk (reducedBoundaryι i t)) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))) ∧
    (∀ t : pullback (C := Scheme.{u}) i (reducedComplementι i),
      ((i ≫ f).stalkMap ((pullback.fst i (reducedComplementι i)) t)).hom.FormallySmooth ∧
      ((reducedComplementι i ≫ f).stalkMap
        ((pullback.snd i (reducedComplementι i)) t)).hom.FormallySmooth) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace N :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian N.toScheme := ⟨⟩
  have : QuasiCompact N.ι := inferInstance
  let g := N.ι ≫ f
  let j : Y ⟶ N := IsOpenImmersion.lift N.ι i (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    simpa using hN y)
  have hj : j ≫ N.ι = i := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j ≫ N.ι) := hj.symm ▸ inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j N.ι
  have hdimN : N.toScheme.IsPureDimension 1 := by
    apply topologicalKrullDim_component_eq_of_constant_local_dimension N 1
    intro x hx
    apply topologicalKrullDimAt_eq_of_equidimensional_open f ⊤ 1 _ x (by simp)
    intro C hC
    let e : (⊤ : X.Opens).toScheme ≃ₜ X := Homeomorph.Set.univ X
    have hC' : e '' C ∈ irreducibleComponents X :=
      image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
        e.isOpenMap (fun _ ↦
          (Set.subsingleton_singleton.preimage e.injective).isPreirreducible) e.surjective hC
    exact ((e.image C).isHomeomorph.topologicalKrullDim_eq _).trans
      (hpureX _ hC')
  have hnodN : ∀ x : N.toScheme, IsClosed ({x} : Set N.toScheme) →
      (¬ ∃ U : N.toScheme.Opens, x ∈ U ∧ Smooth (U.ι ≫ g)) →
      (g.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (N.toScheme.residueField x) _ _
        (g.residueFieldAlgebraMap x).toAlgebra ∧
      Nonempty (AdicCompletion
        (IsLocalRing.maximalIdeal (N.toScheme.presheaf.stalk x))
        (N.toScheme.presheaf.stalk x) ≃+*
        (MvPowerSeries (Fin 2) (N.toScheme.residueField x) ⧸
          Ideal.span {(MvPowerSeries.X 0 :
            MvPowerSeries (Fin 2) (N.toScheme.residueField x)) * MvPowerSeries.X 1})) := by
    intro x hx hs
    have hxX : x.val ∈ closedPoints X := by
      have h := N.ι.isOpenEmbedding.preimage_closedPoints
      exact h.ge hx
    have hnot : ¬(f.stalkMap x.val).hom.FormallySmooth := by
      intro h
      apply hs
      apply (smooth_iff_neighbourhood g x).mp
      change x ∈ g.smoothLocus
      rw [← Scheme.Hom.preimage_smoothLocus_eq]
      exact h
    obtain ⟨E⟩ := hnodal x.val x.property hxX hnot
    obtain ⟨c⟩ := completion_congr (N.stalkIso x).commRingCatIsoToRingEquiv
    let r := (residueFieldIsoBase g x hx).commRingCatIsoToRingEquiv.symm
    have hb := closed_residue_bijective g x hx
    let := (g.residueFieldAlgebraMap x).toAlgebra
    have hf : (g.residueFieldAlgebraMap x).Finite := RingHom.Finite.of_surjective _ hb.2
    have : Module.Finite k (N.toScheme.residueField x) := hf
    refine ⟨hf, inferInstance, ⟨c.trans (E.trans (nodalModelCongr r))⟩⟩
  have hnodN' : ∀ x : N.toScheme, IsClosed ({x} : Set N.toScheme) →
      (¬ ∃ U : N.toScheme.Opens, x ∈ U ∧ Smooth (U.ι ≫ g)) →
      (g.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (N.toScheme.residueField x) _ _
        (g.residueFieldAlgebraMap x).toAlgebra ∧
      ∃ e : AdicCompletion
          (IsLocalRing.maximalIdeal (N.toScheme.presheaf.stalk x))
          (N.toScheme.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) (N.toScheme.residueField x) ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (N.toScheme.residueField x)) *
              MvPowerSeries.X 1}),
        ∀ a : k, e (AdicCompletion.of
          (IsLocalRing.maximalIdeal (N.toScheme.presheaf.stalk x))
          (N.toScheme.presheaf.stalk x)
          (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
            N.toScheme.presheaf.Γgerm x).hom a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (g.residueFieldAlgebraMap x a)) := by
    intro x hx hs
    obtain ⟨hf, hsep, E⟩ := hnodN x hx hs
    obtain ⟨E⟩ := E
    have hb := closed_residue_bijective g x hx
    let r := RingEquiv.ofBijective (g.residueFieldAlgebraMap x) hb
    obtain ⟨e, he⟩ := scalar_nodal_completion
      (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ N.toScheme.presheaf.Γgerm x).hom)
      (by rw [residue_scalar_germ]; exact hb.2)
      (E.trans (nodalModelCongr r.symm))
    refine ⟨hf, hsep, e.trans (nodalModelCongr r), fun a ↦ ?_⟩
    change nodalModelCongr r (e _) = _
    rw [he]
    simp [nodalModelCongr, MvPowerSeries.map_C, r]
  have hsub := stacks_nodal_closed_subcurve g hdimN hnodN' j hpureY
  let Z := reducedComplement i
  let z : Z ⟶ X := reducedComplementι i
  have : IsClosedImmersion z := by
    dsimp [z, Z, reducedComplementι, reducedComplement]
    infer_instance
  have : IsReduced Z := by
    dsimp [Z, reducedComplement]
    infer_instance
  let W := z ⁻¹ᵁ N
  let w : W.toScheme ⟶ N := z ∣_ N
  have hzr : Set.range z = closure ((Set.range i)ᶜ) := by
    dsimp [z, Z, reducedComplementι, reducedComplement]
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change closure (Set.range (Scheme.openComplementOfIsClosedImmersion i).ι) = _
    congr 1
    exact Scheme.Opens.range_ι _
  have hwr : Set.range w = closure ((Set.range j)ᶜ) := by
    have hr : Set.range w = N.ι ⁻¹' Set.range z := by
      dsimp only [w]
      rw [← (isPullback_morphismRestrict z N).isoPullback_hom_fst,
        Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        (show Set.range (isPullback_morphismRestrict z N).isoPullback.hom = Set.univ from
          (isPullback_morphismRestrict z N).isoPullback.hom.homeomorph.surjective.range_eq),
        Set.image_univ, Scheme.Pullback.range_fst]
    rw [hr, hzr,
      N.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage N.ι.continuous]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range]
    constructor
    · intro hx h
      obtain ⟨y, hy⟩ := h
      apply hx
      exact ⟨y, by rw [← hj, Scheme.Hom.comp_apply, hy]⟩
    · intro hx h
      obtain ⟨y, hy⟩ := h
      apply hx
      exact ⟨y, N.ι.isOpenEmbedding.injective (by
        rw [← Scheme.Hom.comp_apply, hj, hy])⟩
  let V := Scheme.openComplementOfIsClosedImmersion j
  let c : V.ι.image ⟶ N := V.ι.imageι
  have : IsReduced V.ι.image := (complement_image_range j).1
  obtain ⟨e, he⟩ := reduced_closed_iso_of_range_eq c w
    ((complement_image_range j).2.trans hwr.symm)
  have hcomp := complementary_pure_subcurve_components hdimN j hpureY w hwr
  obtain ⟨I, hI, hjr, hwr', hpureW, eY, heY⟩ := hcomp
  have hother := stacks_nodal_closed_subcurve g hdimN hnodN' w hpureW
  let V' := Scheme.openComplementOfIsClosedImmersion w
  let c' : V'.ι.image ⟶ N := V'.ι.imageι
  have : IsReduced V'.ι.image := (complement_image_range w).1
  have hc'r : Set.range c' = Set.range j := by
    rw [(complement_image_range w).2]
    have h := congrArg (fun a : Y ⟶ N.toScheme ↦ Set.range a) heY
    have hrange : Set.range (eY.hom ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure ((Set.range w)ᶜ))).subschemeι) =
        Set.range (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure ((Set.range w)ᶜ))).subschemeι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        (show Set.range eY.hom = Set.univ from eY.hom.homeomorph.surjective.range_eq),
        Set.image_univ]
    rw [hrange, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
    exact h
  obtain ⟨e', he'⟩ := reduced_closed_iso_of_range_eq c' j hc'r
  have hpb : IsPullback (pullback.fst j c)
      (pullback.snd j c ≫ e.hom ≫ W.ι) i z := by
    have hp : IsPullback (pullback.fst j c) (pullback.snd j c ≫ e.hom) j w := by
      exact (IsPullback.of_hasPullback j c).of_iso
        (Iso.refl _) (Iso.refl _) e (Iso.refl _)
        (by simp) (by simp) (by simp) (by simpa using he.symm)
    simpa only [hj, Category.assoc] using
      hp.paste_vert (isPullback_morphismRestrict z N)
  let b := hpb.isoPullback
  have hbY : b.inv ≫ pullback.fst j c = pullback.fst i z := hpb.isoPullback_inv_fst
  have hbZ : b.inv ≫ pullback.snd j c ≫ e.hom ≫ W.ι = pullback.snd i z :=
    hpb.isoPullback_inv_snd
  have hjg : j ≫ g = i ≫ f := by
    dsimp [g]
    rw [← Category.assoc, hj]
  let q : pullback j c ⟶ pullback w c' :=
    pullback.lift (pullback.snd j c ≫ e.hom) (pullback.fst j c ≫ e'.inv) (by
      rw [Category.assoc, he, Category.assoc,
        show e'.inv ≫ c' = j from (by rw [← he', Iso.inv_hom_id_assoc])]
      exact (pullback.condition (f := j) (g := c)).symm)
  rcases hsub with ⟨hYnode, ⟨n, K, hK, ι, hι, a, ha⟩, hboundary⟩
  let (v : Fin n) : Field (K v) := hK v
  have hKbij (v : Fin n) : Function.Bijective (ι v) := by
    let := (ι v).toAlgebra
    have : Module.Finite k (K v) := (hι v).1
    exact IsAlgClosed.ringHom_bijective_of_isIntegral (ι v)
      (by rw [← RingHom.algebraMap_toAlgebra (ι v)]; exact Algebra.IsIntegral.isIntegral)
  let aK (v : Fin n) : Spec (.of (K v)) ≅ Spec (.of k) :=
    (Scheme.Spec.mapIso (RingEquiv.ofBijective (ι v) (hKbij v)).toCommRingCatIso.op)
  let haTop : (Σ v : Fin n, ↥(Spec (.of (K v)))) ≃ₜ
      ↥(∐ fun v : Fin n ↦ Spec (.of (K v))) :=
    TopCat.homeoOfIso
      ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
        (PreservesCoproduct.iso Scheme.forgetToTop (fun v : Fin n ↦ Spec (.of (K v)))).symm)
  have haPoints : T1Space ↥(∐ fun v : Fin n ↦ Spec (.of (K v))) := haTop.t1Space
  have hT1 : T1Space ↥(pullback j c) := a.hom.homeomorph.t1Space
  have : T1Space ↥(pullback i z) := b.hom.homeomorph.t1Space
  refine ⟨?_, ⟨n, ⟨b.symm ≪≫ a.symm ≪≫ Sigma.mapIso aK⟩⟩, ?_, ?_⟩
  · intro y hy hs
    have hs' : ¬ ∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ j ≫ g) := by
      simpa only [hjg] using (smooth_iff_neighbourhood (i ≫ f) y).not.mp hs
    obtain ⟨_, _, E, _⟩ := hYnode y hy hs'
    exact ⟨E.trans (nodalModelCongr
      (residueFieldIsoBase (i ≫ f) y hy).commRingCatIsoToRingEquiv)⟩
  · intro t
    let s := b.inv t
    let x := j (pullback.fst j c s)
    have hx : N.ι x = reducedBoundaryι i t := by
      change ((pullback.fst j c ≫ j) ≫ N.ι) (b.inv t) = _
      rw [Category.assoc, hj, ← Scheme.Hom.comp_apply, ← Category.assoc, hbY]
      rfl
    have hclosed : reducedBoundaryι i t ∈ closedPoints X := by
      have : IsClosedImmersion (pullback.fst i z ≫ i) := inferInstance
      have ht : IsClosed ({t} : Set ↥(pullback (C := Scheme.{u}) i z)) := isClosed_singleton
      change IsClosed ({(pullback.fst i z ≫ i) t} : Set X)
      simpa only [Set.image_singleton] using
        (pullback.fst i z ≫ i).isClosedEmbedding.isClosedMap _ ht
    have hs := hboundary s
    have hns : ¬(f.stalkMap (N.ι x)).hom.FormallySmooth := by
      intro h
      apply hs.1
      apply (smooth_iff_neighbourhood g x).mp
      change x ∈ g.smoothLocus
      rw [← Scheme.Hom.preimage_smoothLocus_eq]
      exact h
    obtain ⟨E, _⟩ := hs.2.1
    obtain ⟨d⟩ := completion_congr (N.stalkIso x).commRingCatIsoToRingEquiv
    have hn : Nonempty (AdicCompletion
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (N.ι x)))
        (X.presheaf.stalk (N.ι x)) ≃+*
        (MvPowerSeries (Fin 2) k ⧸ Ideal.span
          {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})) :=
      ⟨d.symm.trans (E.trans (nodalModelCongr
        (residueFieldIsoBase g x (by
          have h := N.ι.isOpenEmbedding.preimage_closedPoints
          apply h.le
          change N.ι x ∈ closedPoints X
          rw [hx]
          exact hclosed)).commRingCatIsoToRingEquiv))⟩
    exact ⟨hclosed, hx ▸ hns, hx ▸ hn⟩
  · intro t
    let s := b.inv t
    have hY := (hboundary s).2.2
    have hY' : ((j ≫ g).stalkMap (pullback.fst j c s)).hom.FormallySmooth :=
      (smooth_iff_neighbourhood (j ≫ g) _).mpr (by simpa using hY)
    have hW := (hother.2.2 (q s)).2.2
    have hW' : ((w ≫ g).stalkMap (e.hom (pullback.snd j c s))).hom.FormallySmooth := by
      apply (smooth_iff_neighbourhood (w ≫ g) _).mpr
      have hq : q ≫ pullback.fst w c' = pullback.snd j c ≫ e.hom :=
        pullback.lift_fst _ _ _
      have hp := congrArg (fun a : pullback j c ⟶ W.toScheme ↦ a s) hq
      simp only [Scheme.Hom.comp_apply] at hp
      rw [hp] at hW
      simpa only [Category.assoc] using hW
    have hz : w ≫ g = W.ι ≫ (z ≫ f) := by
      dsimp [g, w]
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hjg] at hY'
    have hyPoint : pullback.fst j c s = pullback.fst i z t := by
      exact congrArg (fun a : pullback i z ⟶ Y ↦ a t) hbY
    have hzPoint : W.ι (e.hom (pullback.snd j c s)) = pullback.snd i z t := by
      exact congrArg (fun a : pullback i z ⟶ Z ↦ a t) hbZ
    refine ⟨hyPoint ▸ hY', ?_⟩
    change ((z ≫ f).stalkMap _).hom.FormallySmooth
    rw [hz] at hW'
    have hmem : e.hom (pullback.snd j c s) ∈ (W.ι ≫ (z ≫ f)).smoothLocus := hW'
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at hmem
    exact hzPoint ▸ hmem

end AlgebraicGeometry
