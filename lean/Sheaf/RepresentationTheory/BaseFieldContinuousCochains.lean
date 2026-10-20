/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q61
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RepresentationTheory.DiscreteIntegerInvariantsInfrastructure
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsEffaceable
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.Algebra.Group.Subgroup.Finite
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Continuous cochains compute Galois cohomology

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-base-field-cd,
sk-lem-base-field-cd-cochains, clauses (1)--(3), and its proof; Stacks Project,
Tags 04JP, 04JR, 010T and 00DB (blueprint: det-base-field-cd-cochains).

Locally constant functions are exactly continuous functions into the discrete coefficient
group. An equivalent abelian category `A` permits any presentation of the category of
discrete integer representations. Coordinate equations specify all maps uniquely.
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- The invariants functor in an equivalent presentation of discrete integer modules.
This is the restriction of `Rep.invariantsFunctor`, followed by the underlying additive
group functor, with no choice of an invariant subgroup.
Source: Stacks Project, Tag 04JR (blueprint: det-base-field-cd-cochains). -/
noncomputable abbrev baseFieldIntegerInvariants
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G) :=
  E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat

/-- Right derived invariants, using Mathlib's injective-resolution definition.
Source: Stacks Project, Tag 04JR (blueprint: det-base-field-cd-cochains). -/
noncomputable abbrev baseFieldDerivedInvariants
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A] [Abelian A] [EnoughInjectives A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(baseFieldIntegerInvariants G A E).Additive] (n : ℕ) :
    A ⥤ AddCommGrpCat.{max u s} :=
  (baseFieldIntegerInvariants G A E).rightDerived n

/-- The natural coordinates and the inhomogeneous differential of continuous cochains.
`Fin.contractNth` multiplies adjacent entries, with its final face deleting the last entry.
For `n = 0` the formula is exactly `g • m - m`.
Source: blueprint cochains statement, displayed differential
(blueprint: det-base-field-cd-cochains). -/
def HasBaseFieldCochainCoordinates
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V) : Prop :=
  (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
    e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g)) ∧
  (∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
    e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
      (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
        ∑ k : Fin (n + 1),
          (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g))

/-- Continuous cochain cohomology is a universal delta-functor, naturally identified with
derived invariants by mutually inverse morphisms of delta-functors.

Source: blueprint cochains statement (1), and Stacks Project, Tag 010T
(blueprint: det-base-field-cd-cochains).

Proof: The category is the category of discrete integer representations via `E`.
The integer-invariants infrastructure gives enough injectives and left exact invariants;
invariants are additive since coefficient maps restrict additively. The locally constant
cochain effaceability theorem supplies `C`, its coordinates, and its cohomological
delta-functor with degree zero naturally equal to invariants. The coordinate formula is
the displayed differential, including degree zero. Positive cohomology is effaced by the
orbit embedding into the discrete coinduced module: evaluation at one proves monicity,
and insertion of one contracts the homogeneous complex in positive degrees. By Tag 010T
this delta-functor is universal. The right derived functors of the left exact invariant
functor are universal too. Extend the degree-zero identification in both directions.
Uniqueness in universality makes the composites the identity in every degree, so the
comparison is natural and commutes with connecting maps. -/
theorem exists_baseFieldContinuousCochains_universal
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    ∃ (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
      (e : ∀ (M : A) (n : ℕ),
        (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V),
      HasBaseFieldCochainCoordinates G A E C e ∧
      ∃ (hI : EnoughInjectives A) (hV : (baseFieldIntegerInvariants G A E).Additive)
        (T R : CohomologicalDeltaFunctor A AddCommGrpCat.{max u s}),
        T.F = (fun n ↦ C ⋙ HomologicalComplex.homologyFunctor
          AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n) ∧
        T.IsUniversal ∧ Nonempty (T.F 0 ≅ baseFieldIntegerInvariants G A E) ∧
        R.F = (fun n ↦ @baseFieldDerivedInvariants G _ _ _ A _ _ hI E hV n) ∧
        ∃ (α : CohomologicalDeltaFunctor.Hom T R) (β : CohomologicalDeltaFunctor.Hom R T),
          (∀ n : ℕ, α.app n ≫ β.app n = 𝟙 (T.F n)) ∧
          (∀ n : ℕ, β.app n ≫ α.app n = 𝟙 (R.F n)) := by
  classical
  obtain ⟨hI, hVlim⟩ := discreteInteger_invariants_infrastructure G A E
  let : EnoughInjectives A := hI
  let : PreservesFiniteLimits (baseFieldIntegerInvariants G A E) := hVlim
  let : (baseFieldIntegerInvariants G A E).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨C, e, hm, hd, T, hTF, ⟨hTzero⟩, heff⟩ :=
    exists_locallyConstantCochains_effaceable G A E
  have hT : T.IsUniversal := effaceable_deltaFunctor_isUniversal T heff
  obtain ⟨R, hRF, hR, ⟨hRzero⟩⟩ :=
    (baseFieldIntegerInvariants G A E).exists_universal_rightDerived_deltaFunctor
  have hRzero' : R.F 0 ≅ baseFieldIntegerInvariants G A E := by
    rw [hRF]
    exact hRzero
  let z : T.F 0 ≅ R.F 0 := hTzero ≪≫ hRzero'.symm
  obtain ⟨α, hα, _⟩ := hT R z.hom
  obtain ⟨β, hβ, _⟩ := hR T z.inv
  let idT : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ 𝟙 (T.F n), by intros; simp⟩
  let idR : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ 𝟙 (R.F n), by intros; simp⟩
  let αβ : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ α.app n ≫ β.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [α.naturality S hS n]
      simp only [Category.assoc]
      rw [β.naturality S hS n]⟩
  let βα : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ β.app n ≫ α.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [β.naturality S hS n]
      simp only [Category.assoc]
      rw [α.naturality S hS n]⟩
  have hαβ : αβ = idT := (hT T (𝟙 (T.F 0))).unique
    (by change α.app 0 ≫ β.app 0 = _; rw [hα, hβ]; exact z.hom_inv_id) rfl
  have hβα : βα = idR := (hR R (𝟙 (R.F 0))).unique
    (by change β.app 0 ≫ α.app 0 = _; rw [hβ, hα]; exact z.inv_hom_id) rfl
  refine ⟨C, e, ⟨hm, hd⟩, hI, inferInstance, T, R, hTF, hT, ⟨hTzero⟩,
    hRF, α, β, ?_, ?_⟩
  · intro n
    exact congrArg (fun f : CohomologicalDeltaFunctor.Hom T T ↦ f.app n) hαβ
  · intro n
    exact congrArg (fun f : CohomologicalDeltaFunctor.Hom R R ↦ f.app n) hβα

private noncomputable def ab_isColimit_of_union
    {I : Type t} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {F : I ⥤ AddCommGrpCat.{s}} (c : Cocone F)
    (hinj : ∀ i, Function.Injective (c.ι.app i))
    (hsurj : ∀ x : c.pt, ∃ i y, c.ι.app i y = x) : IsColimit c := by
  classical
  let idx (x : c.pt) := (hsurj x).choose
  let rep (x : c.pt) : F.obj (idx x) := (hsurj x).choose_spec.choose
  have hrep (x : c.pt) : c.ι.app (idx x) (rep x) = x :=
    (hsurj x).choose_spec.choose_spec
  have leg (s : Cocone F) {i j : I} (h : i ≤ j) (x : F.obj i) :
      s.ι.app j (F.map (homOfLE h) x) = s.ι.app i x :=
    ConcreteCategory.congr_hom (s.w (homOfLE h)) x
  let d (s : Cocone F) (x : c.pt) := s.ι.app (idx x) (rep x)
  have fac (s : Cocone F) (i : I) (x : F.obj i) : d s (c.ι.app i x) = s.ι.app i x := by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i (idx (c.ι.app i x))
    have he : F.map (homOfLE hjk) (rep (c.ι.app i x)) = F.map (homOfLE hik) x := by
      apply hinj k
      rw [leg c hjk, leg c hik, hrep]
    dsimp [d]
    exact (leg s hjk _).symm.trans ((congrArg (s.ι.app k) he).trans (leg s hik x))
  let desc (s : Cocone F) : c.pt ⟶ s.pt := AddCommGrpCat.ofHom
    { toFun := d s
      map_zero' := by
        let i : I := Classical.arbitrary I
        have h := fac s i 0
        change d s 0 = 0
        have hz : c.ι.app i 0 = 0 := (c.ι.app i).hom.map_zero
        rw [hz] at h
        exact h.trans (s.ι.app i).hom.map_zero
      map_add' := by
        intro x y
        obtain ⟨k, hxk, hyk⟩ := exists_ge_ge (idx x) (idx y)
        let a := F.map (homOfLE hxk) (rep x)
        let b := F.map (homOfLE hyk) (rep y)
        have ha : c.ι.app k a = x := (leg c hxk _).trans (hrep x)
        have hb : c.ι.app k b = y := (leg c hyk _).trans (hrep y)
        rw [← ha, ← hb]
        change d s ((c.ι.app k).hom a + (c.ι.app k).hom b) = _
        rw [← map_add, fac]
        change (s.ι.app k).hom (a + b) = _
        rw [map_add, fac, fac] }
  refine ⟨desc, ?_, ?_⟩
  · intro s i
    ext x
    exact fac s i x
  · intro s m hm
    ext x
    obtain ⟨i, y, rfl⟩ := hsurj x
    exact (ConcreteCategory.congr_hom (hm i) y).trans (fac s i y).symm

private noncomputable def cochain_homology_isColimit
    {I : Type t} [SmallCategory I] [IsFiltered I]
    {K : I ⥤ CochainComplex AddCommGrpCat.{s} ℕ} (c : Cocone K)
    (hc : ∀ n, IsColimit ((HomologicalComplex.eval _ _ n).mapCocone c)) (n : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor _ _ n).mapCocone c) := by
  let L := AddCommGrpCat.uliftFunctor.{t, s}
  let H := ShortComplex.homologyFunctor AddCommGrpCat.{s}
  let S := HomologicalComplex.shortComplexFunctor AddCommGrpCat.{s} (ComplexShape.up ℕ) n
  have hS : IsColimit (S.mapCocone c) :=
    ShortComplex.isColimitOfIsColimitπ _ (hc _) (hc _) (hc _)
  have hSL : IsColimit (L.mapShortComplex.mapCocone (S.mapCocone c)) :=
    ShortComplex.isColimitOfIsColimitπ _
      (isColimitOfPreserves L (hc _)) (isColimitOfPreserves L (hc _))
      (isColimitOfPreserves L (hc _))
  have : PreservesColimit (K ⋙ S) L.mapShortComplex :=
    preservesColimit_of_preserves_colimit_cocone hS hSL
  letI : HasFilteredColimitsOfSize.{t, t} AddCommGrpCat.{max t s} :=
    hasFilteredColimitsOfSize_shrink
  letI : AB5OfSize.{t, t} AddCommGrpCat.{max t s} :=
    AB5OfSize_of_univLE.{t, t, max t s, max t s} _
  have : PreservesColimit (K ⋙ S) (L.mapShortComplex ⋙
      ShortComplex.homologyFunctor AddCommGrpCat.{max t s}) := inferInstance
  have : PreservesColimit (K ⋙ S) (H ⋙ L) :=
    preservesColimit_of_natIso _ (ShortComplex.homologyFunctorIso L)
  have : PreservesColimit (K ⋙ S) H :=
    preservesColimit_of_reflects_of_preserves H L
  have hH := isColimitOfPreserves H hS
  exact IsColimit.mapCoconeEquiv
    (HomologicalComplex.homologyFunctorIso AddCommGrpCat.{s} (ComplexShape.up ℕ) n).symm hH

/-- Directed unions of discrete coefficient modules are preserved by continuous cochain
cohomology. The injective cocone legs identify each stage with a stable subgroup; their
joint surjectivity says exactly that the union is the vertex. `IsColimit` states the
canonical comparison is an isomorphism, without choosing a colimit object.

Source: blueprint cochains statement (2), proof (2), and Stacks Project, Tag 00DB
(blueprint: det-base-field-cd-cochains).

Proof: A locally constant cochain on compact `G^n` has finite image. Nonemptiness and
directedness put this finite set in one coefficient stage, so the cochain complex at the
union is the degreewise colimit of the stage complexes. The differential preserves every
stable subgroup. Filtered colimits of abelian groups are exact (Tag 00DB). Apply exactness
to the sequences from cycles to terms to boundaries, and from boundaries to cycles to
cohomology. The resulting cycle and boundary identifications show that the canonical
cohomology cocone is a colimit. Transport through the natural derived-invariant comparison
of clause (1) to obtain the assertion for Galois cohomology, including degree zero. -/
theorem baseFieldContinuousCochains_directedUnion
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hC : HasBaseFieldCochainCoordinates G A E C e)
    (I : Type t) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ A) (c : Cocone D)
    (hinj : ∀ i : I, Function.Injective (E.functor.map (c.ι.app i)).hom.hom)
    (hunion : ∀ m : (E.functor.obj c.pt).obj.V,
      ∃ (i : I) (x : (E.functor.obj (D.obj i)).obj.V),
        (E.functor.map (c.ι.app i)).hom.hom x = m)
    (n : ℕ) :
    Nonempty (IsColimit ((C ⋙ HomologicalComplex.homologyFunctor
      AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n).mapCocone c)) := by
  classical
  let V (i : I) := (E.functor.obj (D.obj i)).obj.V
  let f (i : I) := (E.functor.map (c.ι.app i)).hom.hom
  have trans (i j : I) (hij : i ≤ j) (x : V i) :
      f j ((E.functor.map (D.map (homOfLE hij))).hom.hom x) = f i x := by
    have h := congrArg (fun k ↦ (E.functor.map k).hom.hom x) (c.w (homOfLE hij))
    rw [Functor.map_comp] at h
    exact h
  have stage (s : Set (E.functor.obj c.pt).obj.V) (hs : s.Finite) :
      ∃ i : I, ∀ m ∈ s, ∃ a : V i, f i a = m := by
    induction s, hs using Set.Finite.induction_on with
    | empty => exact ⟨Classical.arbitrary I, by simp⟩
    | @insert m s hm hs ih =>
      obtain ⟨i, a, ha⟩ := hunion m
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, ?_⟩
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨(E.functor.map (D.map (homOfLE hik))).hom.hom a,
          (trans i k hik a).trans ha⟩
      · obtain ⟨b, hb⟩ := hj z hz
        exact ⟨(E.functor.map (D.map (homOfLE hjk))).hom.hom b,
          (trans j k hjk b).trans hb⟩
  have surj (q : ℕ) (x : (C.obj c.pt).X q) :
      ∃ (i : I) (y : (C.obj (D.obj i)).X q), ((C.map (c.ι.app i)).f q) y = x := by
    obtain ⟨i, hi⟩ := stage _ (e c.pt q x).range_finite
    have hv (g : Fin q → G) : ∃ a : V i, f i a = e c.pt q x g :=
      hi _ ⟨g, rfl⟩
    let a (g : Fin q → G) : V i := (hv g).choose
    have ha (g : Fin q → G) : f i (a g) = e c.pt q x g := (hv g).choose_spec
    let y : LocallyConstant (Fin q → G) (V i) :=
      LocallyConstant.desc a (e c.pt q x) (funext ha) (hinj i)
    refine ⟨i, (e (D.obj i) q).symm y, ?_⟩
    apply (e c.pt q).injective
    ext g
    calc
      e c.pt q (((C.map (c.ι.app i)).f q) ((e (D.obj i) q).symm y)) g =
          f i ((e (D.obj i) q) ((e (D.obj i) q).symm y) g) := hC.1 _ _ _ q _ g
      _ = e c.pt q x g := by
        rw [AddEquiv.apply_symm_apply]
        exact ha g
  have inj (i : I) (q : ℕ) : Function.Injective ((C.map (c.ι.app i)).f q) := by
    intro x y hxy
    apply (e (D.obj i) q).injective
    ext g
    apply hinj i
    exact (hC.1 _ _ (c.ι.app i) q x g).symm.trans
      ((congrArg (fun z ↦ e c.pt q z g) hxy).trans (hC.1 _ _ (c.ι.app i) q y g))
  exact ⟨cochain_homology_isColimit (C.mapCocone c)
    (fun q ↦ ab_isColimit_of_union _ (fun i ↦ inj i q) (surj q)) n⟩

/-- Open normal subgroups acting trivially on the entire coefficient module.
The subtype order is inclusion; its order dual is the inflation index category.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
abbrev baseFieldTrivialOpenNormals
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :=
  {N : OpenNormalSubgroup G // ∀ (g : G), g ∈ N → ∀ m : M.obj.V, M.obj.ρ g m = m}

/-- The finite-quotient diagram for the inverse-limit hypothesis, with its actual quotient
projections. Its index order is inclusion, so an arrow `N ≤ N'` induces `G/N → G/N'`.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
def baseFieldQuotientDiagram
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    baseFieldTrivialOpenNormals G M ⥤ Type u where
  obj N := G ⧸ N.val.toSubgroup
  map {N N'} f := TypeCat.ofHom (fun x ↦
    QuotientGroup.map N.val.toSubgroup N'.val.toSubgroup
      (MonoidHom.id G) (fun _ hx ↦ (leOfHom f) hx) x)
  map_id N := by
    ext x
    refine Quotient.inductionOn x ?_
    intro g
    rfl
  map_comp f g := by
    ext x
    refine Quotient.inductionOn x ?_
    intro h
    rfl

/-- The canonical quotient cone with vertex `G`, without any chosen limit comparison.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
def baseFieldQuotientCone
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    Cone (baseFieldQuotientDiagram G M) where
  pt := G
  π :=
    { app := fun N ↦ TypeCat.ofHom (QuotientGroup.mk' N.val.toSubgroup)
      naturality := by intros; ext x; rfl }

/-- The inverse-limit hypothesis is Mathlib's universal property for the canonical quotient
cone. For compact Hausdorff `G` and its finite discrete quotients, its underlying limit
bijection is also a topological group isomorphism, by the compact-to-Hausdorff criterion.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
def IsBaseFieldQuotientLimit
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) : Prop :=
  Nonempty (IsLimit (baseFieldQuotientCone G M))

private theorem lc_factors
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Type s) (n : ℕ) (f : LocallyConstant (Fin n → G) V) :
    ∃ N : OpenNormalSubgroup G, ∀ g h : Fin n → G,
      (∀ i, QuotientGroup.mk' N.toSubgroup (g i) =
        QuotientGroup.mk' N.toSubgroup (h i)) → f g = f h := by
  classical
  cases n with
  | zero =>
    refine ⟨⟨⊤, (show (⊤ : Subgroup G).Normal from inferInstance)⟩, ?_⟩
    exact fun g h _ ↦ congrArg f (Subsingleton.elim g h)
  | succ n =>
    let : TopologicalSpace V := ⊥
    let : DiscreteTopology V := ⟨rfl⟩
    obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
      (ProfiniteGrp.of (Fin (n + 1) → G)) V f f.continuous
    let H (i : Fin (n + 1)) : OpenNormalSubgroup G :=
      { toOpenSubgroup := U.toOpenSubgroup.comap (MonoidHom.mulSingle (fun _ : Fin (n + 1) ↦ G) i)
          (continuous_mulSingle i)
        isNormal' := U.isNormal'.comap (MonoidHom.mulSingle (fun _ : Fin (n + 1) ↦ G) i) }
    let N : OpenNormalSubgroup G := Finset.univ.inf' Finset.univ_nonempty H
    refine ⟨N, ?_⟩
    intro g h hh
    have ha (i : Fin (n + 1)) : (g i)⁻¹ * h i ∈ N := by
      exact QuotientGroup.eq.mp (hh i)
    have hsingle (i : Fin (n + 1)) : Pi.mulSingle i ((g i)⁻¹ * h i) ∈ U := by
      exact (Finset.inf'_le H (Finset.mem_univ i) : N ≤ H i) (ha i)
    have hmem : (fun i ↦ (g i)⁻¹ * h i) ∈ U :=
      Subgroup.pi_mem_of_mulSingle_mem _ hsingle
    have he := hU g (fun i ↦ (g i)⁻¹ * h i) hmem
    have hp : g * (fun i ↦ (g i)⁻¹ * h i) = h := by
      ext i
      simp only [Pi.mul_apply, mul_inv_cancel_left]
    rw [hp] at he
    exact he.symm

section QuotientComplex
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type s} [AddCommGroup V] [Module ℤ V]
  (K : CochainComplex AddCommGrpCat.{max u s} ℕ)
  (e : ∀ n, K.X n ≃+ LocallyConstant (Fin n → G) V)

private def qSub (N : OpenNormalSubgroup G) (n : ℕ) : AddSubgroup (K.X n) where
  carrier x := ∀ g h : Fin n → G,
    (∀ i, QuotientGroup.mk' N.toSubgroup (g i) =
      QuotientGroup.mk' N.toSubgroup (h i)) → e n x g = e n x h
  zero_mem' := by
    intro g h hh
    rw [(e n).map_zero]
    rfl
  add_mem' := by
    intro x y hx hy g h hh
    simp only [map_add, LocallyConstant.add_apply]
    rw [hx g h hh, hy g h hh]
  neg_mem' := by
    intro x hx g h hh
    simp only [map_neg, LocallyConstant.neg_apply]
    rw [hx g h hh]

private noncomputable def qCoordinates (N : OpenNormalSubgroup G) (n : ℕ) :
    qSub K e N n ≃+ LocallyConstant (Fin n → G ⧸ N.toSubgroup) V := by
  classical
  let sec : G ⧸ N.toSubgroup → G := Function.surjInv (QuotientGroup.mk'_surjective _)
  have hsec (g : G ⧸ N.toSubgroup) : QuotientGroup.mk' N.toSubgroup (sec g) = g :=
    Function.surjInv_eq _ g
  let p : C(Fin n → G, Fin n → G ⧸ N.toSubgroup) :=
    ⟨fun g i ↦ QuotientGroup.mk' N.toSubgroup (g i),
      continuous_pi (fun i ↦ QuotientGroup.continuous_mk.comp (continuous_apply i))⟩
  refine
    { toFun := fun x ↦ ⟨fun g ↦ e n x.val (fun i ↦ sec (g i)),
        IsLocallyConstant.of_discrete _⟩
      invFun := fun f ↦ ⟨(e n).symm (f.comap p), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro g h hh
    rw [AddEquiv.apply_symm_apply]
    exact congrArg f (funext hh)
  · intro x
    apply Subtype.ext
    apply (e n).injective
    ext g
    rw [AddEquiv.apply_symm_apply]
    exact x.property _ _ (fun i ↦ hsec _)
  · intro f
    ext g
    change e n ((e n).symm (f.comap p)) (fun i ↦ sec (g i)) = f g
    rw [AddEquiv.apply_symm_apply]
    change f (fun i ↦ QuotientGroup.mk' N.toSubgroup (sec (g i))) = f g
    congr 1
    exact funext (fun i ↦ hsec _)
  · intro x y
    ext g
    exact congrArg (fun f : LocallyConstant (Fin n → G) V ↦
      f (fun i ↦ sec (g i))) ((e n).map_add x.val y.val)

variable (ρ : Representation ℤ G V)
  (hd : ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
    e (n + 1) (K.d n (n + 1) x) g =
      ρ (g 0) (e n x (fun k ↦ g k.succ)) +
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
          e n x (Fin.contractNth k (· * ·) g))
  (N : OpenNormalSubgroup G) (hN : ∀ a : G, a ∈ N → ∀ v : V, ρ a v = v)

omit [IsTopologicalGroup G] in
include ρ hd hN in
private theorem qSub_d (n : ℕ) (x : qSub K e N n) :
    K.d n (n + 1) x.val ∈ qSub K e N (n + 1) := by
  intro g h hh
  rw [hd, hd]
  have he : e n x.val (fun k ↦ g k.succ) = e n x.val (fun k ↦ h k.succ) :=
    x.property _ _ (fun i ↦ hh i.succ)
  congr 1
  · rw [he]
    obtain ⟨a, ha, hga⟩ := (QuotientGroup.mk'_eq_mk' N.toSubgroup).mp (hh 0)
    rw [← hga, map_mul, Module.End.mul_apply, hN a ha]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply x.property
    intro i
    have hc (a : Fin (n + 1) → G) :=
      Fin.comp_contractNth (· * ·) (· * ·) (QuotientGroup.mk' N.toSubgroup).map_mul k a
    have hg := congrFun (hc g) i
    have hh' := congrFun (hc h) i
    dsimp only [Function.comp_apply] at hg hh'
    rw [hg, hh']
    congr 1
    exact funext hh

omit [IsTopologicalGroup G] in
include ρ hd hN in
private theorem qSub_d_all (i j : ℕ) (x : qSub K e N i) :
    K.d i j x.val ∈ qSub K e N j := by
  by_cases hij : i + 1 = j
  · subst j
    exact qSub_d K e ρ hd N hN i x
  · have hz : K.d i j = 0 := K.shape i j hij
    rw [hz]
    exact (qSub K e N j).zero_mem

private def qComplex : CochainComplex AddCommGrpCat.{max u s} ℕ where
  X n := AddCommGrpCat.of (qSub K e N n)
  d i j := AddCommGrpCat.ofHom
    { toFun x := ⟨K.d i j x.val, qSub_d_all K e ρ hd N hN i j x⟩
      map_zero' := Subtype.ext (K.d i j).hom.map_zero
      map_add' x y := Subtype.ext ((K.d i j).hom.map_add x.val y.val) }
  shape i j hij := by
    ext x
    change K.d i j x.val = 0
    rw [K.shape i j hij]
    rfl
  d_comp_d' i j k hij hjk := by
    ext x
    exact ConcreteCategory.congr_hom (K.d_comp_d i j k) x.val

private def qInclusion : qComplex K e ρ hd N hN ⟶ K where
  f i := AddCommGrpCat.ofHom (qSub K e N i).subtype
  comm' i j hij := by ext x; rfl

omit [Module ℤ V] in
private theorem qCoordinates_pull (n : ℕ) (x : qSub K e N n) (g : Fin n → G) :
    qCoordinates K e N n x (fun i ↦ QuotientGroup.mk' N.toSubgroup (g i)) = e n x.val g := by
  change e n x.val (fun i ↦ Function.surjInv (QuotientGroup.mk'_surjective _)
    (QuotientGroup.mk' N.toSubgroup (g i))) = e n x.val g
  exact x.property _ _ (fun i ↦ Function.surjInv_eq _ _)

omit [IsTopologicalGroup G] [Module ℤ V] in
private theorem qSub_mono {N N' : OpenNormalSubgroup G} (hNN : N' ≤ N) (n : ℕ) :
    qSub K e N n ≤ qSub K e N' n := by
  intro x hx g h hh
  apply hx
  intro i
  exact QuotientGroup.eq.mpr (hNN (QuotientGroup.eq.mp (hh i)))

private def qMap {N N' : OpenNormalSubgroup G}
    (hN : ∀ a : G, a ∈ N → ∀ v : V, ρ a v = v)
    (hN' : ∀ a : G, a ∈ N' → ∀ v : V, ρ a v = v) (hNN : N' ≤ N) :
    qComplex K e ρ hd N hN ⟶ qComplex K e ρ hd N' hN' where
  f n := AddCommGrpCat.ofHom
    { toFun x := ⟨x.val, qSub_mono K e hNN n x.property⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  comm' _ _ _ := by ext x; rfl

private abbrev qIndex :=
  {N : OpenNormalSubgroup G // ∀ a : G, a ∈ N → ∀ v : V, ρ a v = v}

private def qDiagram : (qIndex ρ)ᵒᵈ ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ where
  obj N := qComplex K e ρ hd N.val N.property
  map {N N'} f := qMap K e ρ hd N.property N'.property (leOfHom f)
  map_id _ := by ext n x; rfl
  map_comp _ _ := by ext n x; rfl

private def qCocone : Cocone (qDiagram K e ρ hd) where
  pt := K
  ι :=
    { app N := qInclusion K e ρ hd N.val N.property
      naturality _ _ f := by ext n x; rfl }

end QuotientComplex

private theorem trivialNormals_nonempty
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (hlim : IsBaseFieldQuotientLimit G M) : Nonempty (baseFieldTrivialOpenNormals G M) := by
  classical
  by_contra h
  have : IsEmpty (baseFieldTrivialOpenNormals G M) := not_nonempty_iff.mp h
  obtain ⟨hL⟩ := hlim
  have he : (𝟙 G : (G : Type u) ⟶ G) = TypeCat.ofHom (fun _ : G ↦ (1 : G)) :=
    hL.hom_ext (fun j ↦ isEmptyElim j)
  have hG (g : G) : g = 1 := by
    simpa using ConcreteCategory.congr_hom he g
  apply h
  refine ⟨⟨⟨⊤, (show (⊤ : Subgroup G).Normal from inferInstance)⟩, ?_⟩⟩
  intro g hg m
  rw [hG g, map_one]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the quotient-invariant subcomplex coordinates and their dependent integer-module
-- instances needs a larger heartbeat budget; single-file checking remains below 60 seconds.
/-- Finite-quotient inflation realizes both the continuous complex and its cohomology as
colimits. The coordinate equations specify quotient differentials, all transition maps,
and the cocone legs by their pullbacks to tuples in `G`; quotient surjectivity makes these
specifications unique. In particular these are canonical inflation maps.

Source: blueprint cochains statement (3), opening compactness paragraph and proof (3);
Stacks Project, Tag 00DB (blueprint: det-base-field-cd-cochains).

Proof: The inverse-limit hypothesis implies that the subgroup family is nonempty: an
empty inverse limit is trivial, and the whole group then acts trivially. Fix a member N0.
Compactness and the open-normal neighborhood basis show that every cochain factors through
some finite quotient G/K: cover by finitely many constant boxes and intersect their open
normal subgroups. Replace K by K intersect N0. This subgroup acts trivially on M, so the
displayed quotient differential pulls back to the differential on G. Intersections make
the index nonempty directed under reverse inclusion. Inflation is injective since quotient
maps are surjective. Representatives agreeing on G agree at their common intersection.
Thus the specified inflation cocone is a colimit of complexes, degree by degree. Exactness
of filtered colimits identifies its cycles and boundaries, hence gives the cohomology
colimit cocone. Clause (1) identifies these cohomology groups with derived invariants for
G and each finite quotient, with inflation as their canonical comparison. Degree zero
uses the singleton G^0 and zero incoming boundaries. -/
theorem baseFieldContinuousCochains_finiteQuotients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hC : HasBaseFieldCochainCoordinates G A E C e)
    (M : A) (hlim : IsBaseFieldQuotientLimit G (E.functor.obj M)) :
    ∃ (D : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ ⥤
        CochainComplex AddCommGrpCat.{max u s} ℕ)
      (eN : ∀ (N : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ) (n : ℕ),
        (D.obj N).X n ≃+
          LocallyConstant (Fin n → G ⧸ N.val.toSubgroup) (E.functor.obj M).obj.V)
      (ι : D ⟶ (Functor.const _).obj (C.obj M)),
      (∀ (N : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ)
        (n : ℕ) (x : (D.obj N).X n) (g : Fin (n + 1) → G),
        eN N (n + 1) (((D.obj N).d n (n + 1)) x)
            (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k)) =
          (E.functor.obj M).obj.ρ (g 0)
              (eN N n x (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k.succ))) +
            ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
              eN N n x (fun j ↦ QuotientGroup.mk' N.val.toSubgroup
                (Fin.contractNth k (· * ·) g j))) ∧
      (∀ (N N' : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ)
        (f : N ⟶ N') (n : ℕ) (x : (D.obj N).X n) (g : Fin n → G),
        eN N' n (((D.map f).f n) x) (fun k ↦ QuotientGroup.mk' N'.val.toSubgroup (g k)) =
          eN N n x (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k))) ∧
      (∀ (N : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ)
        (n : ℕ) (x : (D.obj N).X n) (g : Fin n → G),
        e M n (((ι.app N).f n) x) g =
          eN N n x (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k))) ∧
      Nonempty (IsColimit (Cocone.mk (C.obj M) ι)) ∧
      (∀ n : ℕ, Nonempty (IsColimit
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u s}
          (ComplexShape.up ℕ) n).mapCocone (Cocone.mk (C.obj M) ι)))) := by
  classical
  let K := C.obj M
  let V := (E.functor.obj M).obj.V
  let ec := e M
  let : Module ℤ V := (E.functor.obj M).obj.hV2
  let ρ : Representation ℤ G V := (E.functor.obj M).obj.ρ
  have hd := hC.2 M
  let J := (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ
  have : Nonempty J := trivialNormals_nonempty G (E.functor.obj M) hlim
  have : IsDirected J (· ≤ ·) :=
    ⟨fun a b ↦ ⟨⟨a.val ⊓ b.val, fun g hg m ↦ a.property g hg.1 m⟩,
      (show a.val ⊓ b.val ≤ a.val from inf_le_left),
      (show a.val ⊓ b.val ≤ b.val from inf_le_right)⟩⟩
  let D : J ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ := qDiagram K ec ρ hd
  let c : Cocone D := qCocone K ec ρ hd
  have hc (n : ℕ) :
      IsColimit ((HomologicalComplex.eval AddCommGrpCat.{max u s}
        (ComplexShape.up ℕ) n).mapCocone c) := by
    apply ab_isColimit_of_union
    · intro N x y hxy
      exact Subtype.ext hxy
    · intro x
      obtain ⟨N, hN⟩ := lc_factors G V n (ec n x)
      let N₀ : baseFieldTrivialOpenNormals G (E.functor.obj M) :=
        (trivialNormals_nonempty G (E.functor.obj M) hlim).some
      let N' : J := ⟨N ⊓ N₀.val, fun g hg m ↦ N₀.property g hg.2 m⟩
      have hx : x ∈ qSub K ec N'.val n := by
        intro g h hh
        apply hN g h
        intro i
        exact QuotientGroup.eq.mpr ((QuotientGroup.eq.mp (hh i)).1)
      exact ⟨N', ⟨x, hx⟩, rfl⟩
  refine ⟨D, (fun N n ↦ qCoordinates K ec N.val n), c.ι, ?_, ?_, ?_, ?_, ?_⟩
  · intro N n x g
    dsimp only
    erw [qCoordinates_pull]
    change ec (n + 1) (K.d n (n + 1) x.val) g = _
    rw [hd]
    congr 1
    · erw [qCoordinates_pull]
    · apply Finset.sum_congr rfl
      intro k hk
      erw [qCoordinates_pull]
  · intro N N' f n x g
    dsimp only
    erw [qCoordinates_pull, qCoordinates_pull]
    rfl
  · intro N n x g
    exact (qCoordinates_pull K ec N.val n x g).symm
  · exact ⟨HomologicalComplex.isColimitOfEval D c hc⟩
  · intro n
    exact ⟨cochain_homology_isColimit c hc n⟩


end Rep
