module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.TraceFormula.LocalDimensionFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyPrincipalSupportDimensionOne
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.GabberGlobalSNCAlteration
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!+# Regular alteration preserving a Cartier subboundary

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Theorem 2.1,
printed p. 149, and VIII, Remark 4.2.2(i), printed pp. 118--119;
Stacks Project, Tag 0AG0, lemma-regular-local-UFD
(blueprint: lem-sfb-alteration-cartier-subboundary).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartier_ne_bot {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I.IsInvertible) : I ≠ ⊥ := by
  intro h
  obtain ⟨U, hx, f, hf, hgen⟩ := hI (genericPoint X)
  have : Nonempty U.1 := ⟨⟨genericPoint X, hx⟩⟩
  rw [h, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hgen
  have hf0 : f = 0 := Ideal.span_singleton_eq_bot.mp hgen.symm
  exact nonZeroDivisors.ne_zero hf hf0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartier_comap_of_dominant {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    {I : Y.IdealSheafData} (hI : I.IsInvertible) : (I.comap f).IsInvertible := by
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  apply (hI.isLocallyPrincipal.comap f).isInvertible
  intro h
  have hle := Scheme.IdealSheafData.le_ker_of_comap_eq_bot f h
  rw [f.ker_eq_bot, le_bot_iff] at hle
  exact cartier_ne_bot hI hle

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartier_generic_not_mem {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I.IsInvertible) : genericPoint X ∉ I.support := by
  intro h
  have htop : I.support = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact ((genericPoint_spec X).specializes trivial).mem_closed I.support.isClosed h
  exact cartier_ne_bot hI (Scheme.IdealSheafData.support_eq_top_iff.mp htop)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem eq_generic_of_dim_zero {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 0) : x = genericPoint X := by
  have hz : Order.coheight x = 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hx
    exact_mod_cast hx
  have hm := Order.coheight_eq_zero.mp hz
  have h : x ≤ genericPoint X := (genericPoint_spec X).specializes trivial
  exact ((genericPoint_spec X).specializes trivial).antisymm (hm h) |>.eq.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartier_support_subfamily
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (hJ : J.IsInvertible)
    (n : ℕ) (C : Fin n → X.IdealSheafData)
    (hC : ∀ i, IsIntegral (C i).subscheme)
    (hdim : ∀ i, ∀ z : (C i).subscheme,
      ringKrullDim (X.presheaf.stalk ((C i).subschemeι z)) =
        ringKrullDim ((C i).subscheme.presheaf.stalk z) + 1)
    (hsub : J.support ≤ ⨆ i, (C i).support) :
    ∃ A : Finset (Fin n), J.support = ⨆ i ∈ A, (C i).support := by
  classical
  let A := Finset.univ.filter (fun i ↦ (C i).support ≤ J.support)
  refine ⟨A, le_antisymm ?_ ?_⟩
  · intro x hx
    have hpos : (0 : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x) := by
      have hn : x ≠ genericPoint X := fun h ↦ cartier_generic_not_mem hJ (h ▸ hx)
      have hzero : ringKrullDim (X.presheaf.stalk x) ≠ 0 :=
        fun h ↦ hn (eq_generic_of_dim_zero x h)
      exact lt_of_le_of_ne ringKrullDim_nonneg_of_nontrivial hzero.symm
    obtain ⟨y, hyx, hyJ, hydim⟩ :=
      Scheme.exists_dimension_one_generalization_in_locallyPrincipal_support
        J hJ.isLocallyPrincipal x hx hpos
    let Z : TopologicalSpace.Closeds X :=
      ⟨⋃ i, ((C i).support : Set X), isClosed_iUnion_of_finite (fun i ↦ (C i).support.isClosed)⟩
    have hle : (⨆ i, (C i).support) ≤ Z :=
      iSup_le fun i ↦ Set.subset_iUnion (fun i ↦ ((C i).support : Set X)) i
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp (hle (hsub hyJ))
    obtain ⟨z, hz⟩ := (C i).range_subschemeι ▸ hyi
    have := hC i
    have hzdim : ringKrullDim ((C i).subscheme.presheaf.stalk z) = 0 := by
      have he := hdim i z
      rw [hz, hydim] at he
      exact ENat.WithBot.add_one_cancel.mp (by simpa using he.symm)
    have hzgen := eq_generic_of_dim_zero z hzdim
    have hiJ : (C i).support ≤ J.support := by
      have hη : (C i).subschemeι (genericPoint (C i).subscheme) ∈ J.support := by
        rw [← hzgen, hz]
        exact hyJ
      intro w hw
      have hw' : w ∈ Set.range (C i).subschemeι := by
        rw [(C i).range_subschemeι]
        exact hw
      obtain ⟨v, rfl⟩ := hw'
      exact (((genericPoint_spec (C i).subscheme).specializes trivial).map
        (C i).subschemeι.continuous).mem_closed J.support.isClosed hη
    have hxi : x ∈ (C i).support :=
      hyx.mem_closed (C i).support.isClosed hyi
    have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiJ⟩
    have hle₁ : (C i).support ≤ ⨆ (_ : i ∈ A), (C i).support :=
      le_iSup (fun _ : i ∈ A ↦ (C i).support) hiA
    have hle₂ : (⨆ (_ : i ∈ A), (C i).support) ≤ ⨆ j ∈ A, (C j).support :=
      le_iSup (fun j ↦ ⨆ (_ : j ∈ A), (C j).support) i
    exact hle₂ (hle₁ hxi)
  · exact iSup_le fun i ↦ iSup_le fun hi ↦ (Finset.mem_filter.mp hi).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem regular_of_open {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (hX : IsRegularScheme X) : IsRegularScheme Y := by
  have : IsLocallyNoetherian X := hX.1
  have : IsRegular X := hX.2
  exact ⟨isLocallyNoetherian_of_isOpenImmersion f, ⟨fun y ↦
    IsRegularLocalRing.of_ringEquiv
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem snc_comap_clopen {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (hf : IsClosed (Set.range f))
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossingsBoundary D) :
    IsStrictNormalCrossingsBoundary (D.comap f) := by
  classical
  obtain ⟨hDI, hDrad, n, C, hCinj, hCreg, hCsupp, hCint⟩ := hD
  have hwhole (i : Fin n) :
      (∃ y : Y, f y ∈ (C i).support) →
      ((C i).support : Set X) ⊆ Set.range f := by
    intro hi
    have : IsIntegral (C i).subscheme := (hCreg i).1
    have hirr : IsIrreducible ((C i).support : Set X) := by
      rw [← (C i).range_subschemeι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (C i).subschemeι.continuous.continuousOn
    obtain ⟨y, hy⟩ := hi
    exact hirr.2.isPreconnected.subset_isClopen
      ⟨hf, f.isOpenEmbedding.isOpen_range⟩ ⟨f y, hy, Set.mem_range_self y⟩
  let T := {i : Fin n // ∃ y : Y, f y ∈ (C i).support}
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let g : Fin (Fintype.card T) ↪ Fin n :=
    ⟨fun j ↦ (e j).1, Subtype.val_injective.comp e.injective⟩
  let C' := fun j ↦ (C (g j)).comap f
  have hsub (j) : ((C (g j)).support : Set X) ⊆ Set.range f :=
    hwhole _ (e j).2
  have hreg (I : X.IdealSheafData) (hI : IsRegularScheme I.subscheme) :
      IsRegularScheme (I.comap f).subscheme := by
    let q := (I.comapIso f).hom ≫ CategoryTheory.Limits.pullback.snd f I.subschemeι
    have : IsOpenImmersion q := inferInstance
    exact regular_of_open q hI
  refine ⟨hDI.comap_of_isOpenImmersion f, ?_, Fintype.card T, C', ?_, ?_, ?_, ?_⟩
  · apply Scheme.IdealSheafData.ext
    funext V
    simp only [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ← Ideal.comap_radical]
    have he := congrArg (fun I : X.IdealSheafData ↦ I.ideal
      ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩) hDrad
    exact congrArg (fun I ↦ Ideal.comap (f.appIso V.1).inv.hom I) he
  · intro j k hjk
    change (C' j).support = (C' k).support at hjk
    apply g.injective
    apply hCinj
    apply SetLike.coe_injective
    ext x
    have hj := hsub j
    have hk := hsub k
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hj hx
      have hy : y ∈ (C' j).support := by
        change y ∈ ((C (g j)).comap f).support
        rw [Scheme.IdealSheafData.support_comap]
        exact hx
      rw [hjk] at hy
      change y ∈ ((C (g k)).comap f).support at hy
      rw [Scheme.IdealSheafData.support_comap] at hy
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hk hx
      have hy : y ∈ (C' k).support := by
        change y ∈ ((C (g k)).comap f).support
        rw [Scheme.IdealSheafData.support_comap]
        exact hx
      rw [← hjk] at hy
      change y ∈ ((C (g j)).comap f).support at hy
      rw [Scheme.IdealSheafData.support_comap] at hy
      exact hy
  · intro j
    have : IsIntegral (C (g j)).subscheme := (hCreg _).1
    have hn : Nonempty (C' j).subscheme := by
      obtain ⟨y, hy⟩ := (e j).2
      have hy' : y ∈ (C' j).support := by
        change y ∈ ((C (g j)).comap f).support
        rw [Scheme.IdealSheafData.support_comap]
        exact hy
      have hyr : y ∈ Set.range (C' j).subschemeι := by
        rw [(C' j).range_subschemeι]; exact hy'
      obtain ⟨z, _⟩ := hyr
      exact ⟨z⟩
    let q := ((C (g j)).comapIso f).hom ≫
      CategoryTheory.Limits.pullback.snd f (C (g j)).subschemeι
    have : IsOpenImmersion q := inferInstance
    exact ⟨isIntegral_of_isOpenImmersion q, hreg _ (hCreg _).2⟩
  · have hcoe {Z : Type u} [TopologicalSpace Z] {m : ℕ}
        (F : Fin m → TopologicalSpace.Closeds Z) :
        ((⨆ i, F i : TopologicalSpace.Closeds Z) : Set Z) = ⋃ i, (F i : Set Z) := by
      rw [← Finset.sup_univ_eq_iSup, TopologicalSpace.Closeds.coe_finset_sup]
      simp
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.coe_support_comap, hCsupp, hcoe, hcoe]
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hy⟩
      let t : T := ⟨i, y, hy⟩
      refine ⟨e.symm t, ?_⟩
      change y ∈ ((C (g (e.symm t))).comap f).support
      rw [Scheme.IdealSheafData.support_comap]
      change f y ∈ (C (g (e.symm t))).support
      have hg : g (e.symm t) = i := by
        change (e (e.symm t)).1 = i
        rw [e.apply_symm_apply]
      rwa [hg]
    · rintro ⟨j, hy⟩
      refine ⟨g j, ?_⟩
      change y ∈ ((C (g j)).comap f).support at hy
      rwa [Scheme.IdealSheafData.support_comap] at hy
  · intro s
    let I := ⨆ i ∈ s.image g, C i
    have he : I.comap f = ⨆ j ∈ s, C' j := by
      dsimp [I, C']
      rw [Finset.iSup_finset_image]
      simp_rw [(Scheme.IdealSheafData.map_gc f).l_iSup]
    rw [← he]
    intro z
    let q := (I.comapIso f).hom ≫ CategoryTheory.Limits.pullback.snd f I.subschemeι
    have : IsOpenImmersion q := inferInstance
    have hc := hCint (s.image g) (q z)
    refine ⟨hreg I hc.1, ?_⟩
    have hw : f ((I.comap f).subschemeι z) = I.subschemeι (q z) := by
      have h := (I.isPullback_comap f).w
      exact congr($(h) z)
    have hdX :=
      (asIso (f.stalkMap ((I.comap f).subschemeι z))).commRingCatIsoToRingEquiv.ringKrullDim
    have hdI := (asIso (q.stalkMap z)).commRingCatIsoToRingEquiv.ringKrullDim
    rw [← hdX, hw, hc.2, hdI, Finset.card_image_of_injective _ g.injective]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two effective Cartier ideals with nested supports admit a regular integral alteration
on which the larger support is an SNC boundary and the smaller is a union of its components.
The witnesses `n` and `C` expose the component family from the existing SNC predicate;
their intersection conditions are exactly those in that predicate. The structure morphism
of `Y` is `a ≫ b`, so `a` is a morphism over the original field. The finite field extension
uses the canonical generic-stalk algebra, without any separability requirement.

Source: ILO, Expose X, Theorem 2.1, p. 149; VIII, Remark 4.2.2(i), pp. 118--119;
Stacks Project, Tag 0AG0 (blueprint: lem-sfb-alteration-cartier-subboundary).

Proof:
1. The Cartier support misses the generic point, so it has empty interior. Choose
   a prime different from the characteristic and apply the existing global Gabber
   alteration to this support.
2. Its source is Noetherian and regular. The normal decomposition gives clopen
   integral components. Choose a nonempty component Y. The alteration's generic-point
   clause makes its restriction proper and dominant, with finite generic residue
   extension. The generic-stalk/residue-field degree comparison gives finiteness of
   the canonical function-field algebra. Composition gives the structure-map conditions.
3. Restrict the SNC ideal to Y and discard components missing Y. An integral component
   meeting the clopen Y lies wholly in Y. Pullback preserves its integral and regular
   structure, and support injectivity. Open restriction preserves radicality and the
   Cartier condition. Pullback commutes with the finite sums defining intersections;
   the open-immersion stalk isomorphisms preserve their dimensions and regularity.
4. Dominance between integral schemes is schematic dominance. Each pulled-back ideal
   is locally principal and nonzero, hence Cartier. The support-comap and radical
   equations identify the larger support with the SNC boundary.
5. For any point in the smaller support, the existing locally-principal dimension-one
   detection theorem supplies a generalization in that support with stalk dimension one.
   It belongs to a boundary component. The SNC singleton-intersection dimension formula
   makes its stalk on that component dimension zero, hence it is the component's generic
   point. Closedness puts the whole component in the smaller support and specialization
   puts the original point on that component.
6. Select the finite set of components contained in the smaller support. The preceding
   pointwise argument proves the union equality; taking complements proves the last
   two clauses. Empty supports, unit ideals and equal supports are included, and no
   step requires separability of the generic field extension. -/
theorem exists_alteration_cartier_subboundary
    (k : Type u) [Field k] (B : Scheme.{u}) [IsIntegral B]
    (b : B ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (I J : B.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hJI : J.support ≤ I.support) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ B) (_ : IsIntegral Y) (_ : IsDominant a),
      IsRegularScheme Y ∧ IsSeparated (a ≫ b) ∧
      LocallyOfFiniteType (a ≫ b) ∧ QuasiCompact (a ≫ b) ∧ IsProper a ∧
      (@algebraMap B.functionField Y.functionField _ _
        a.dominantFunctionFieldAlgebra).Finite ∧
      ∃ (D : Y.IdealSheafData) (n : ℕ) (C : Fin n → Y.IdealSheafData)
        (Aout : Finset (Fin n)),
        IsStrictNormalCrossingsBoundary D ∧
        Function.Injective (fun i ↦ (C i).support) ∧
        (∀ i, IsIntegral (C i).subscheme ∧ IsRegularScheme (C i).subscheme) ∧
        D.support = ⨆ i, (C i).support ∧
        (∀ s : Finset (Fin n), ∀ z : (⨆ i ∈ s, C i).subscheme,
          IsRegularScheme ((⨆ i ∈ s, C i).subscheme) ∧
          ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ s, C i).subschemeι z)) =
            ringKrullDim ((⨆ i ∈ s, C i).subscheme.presheaf.stalk z) + (s.card : ℕ)) ∧
        (I.comap a).IsInvertible ∧ (J.comap a).IsInvertible ∧
        (I.comap a).support = D.support ∧
        (J.comap a).support = ⨆ i ∈ Aout, (C i).support ∧
        a ⁻¹' (I.support : Set B)ᶜ = (D.support : Set Y)ᶜ ∧
        a ⁻¹' (J.support : Set B)ᶜ =
          ((⨆ i ∈ Aout, (C i).support : TopologicalSpace.Closeds Y) : Set Y)ᶜ := by
  classical
  have hnd : interior (I.support : Set B) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hη := ((genericPoint_spec B).mem_open_set_iff isOpen_interior).mpr
      ⟨x, Set.mem_univ x, hx⟩
    exact cartier_generic_not_mem hI (interior_subset hη)
  obtain ⟨ℓ, hℓ, hchar⟩ : ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ℓ ≠ ringChar k := by
    by_cases h : 2 = ringChar k
    · exact ⟨3, by decide, by omega⟩
    · exact ⟨2, by decide, h⟩
  obtain ⟨K, hK, i, hi, _, P, p, a₀, hp, _, ha₀, _, hsurj, hcomm, hgen,
    D₀, hD₀, _, hsnc, hP, _⟩ :=
    exists_gabber_global_snc_alteration k ℓ hℓ hchar B b
      I.support I.support.isClosed hnd
  have : IsProper a₀ := ha₀
  have : LocallyOfFiniteType (a₀ ≫ b) := inferInstance
  have : QuasiCompact (a₀ ≫ b) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (a₀ ≫ b)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (a₀ ≫ b)
  have : IsNoetherian P := {}
  have : IsRegular P := hP.2
  obtain ⟨m, U, hUrange, hUclosed, hUdisj, hUcover, hUint, _⟩ :=
    (regular_normal_and_normal_decomposition P).2.1 inferInstance
      (fun x ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk x⟩)
  obtain ⟨x, hx⟩ := hsurj.1 (genericPoint B)
  have hxU : x ∈ ⨆ j, U j := by rw [hUcover]; trivial
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  let Y := (U j).toScheme
  let a := (U j).ι ≫ a₀
  have : IsIntegral Y := (hUint j).1
  have hcl : IsClosed (Set.range (U j).ι) := by
    rw [Scheme.Opens.range_ι]
    exact hUclosed j
  have : IsClosedImmersion (U j).ι := .of_isOpenImmersion _ hcl
  have : IsProper a := inferInstance
  have hYreg : IsRegular Y := ⟨fun y ↦
    IsRegularLocalRing.of_ringEquiv
      (asIso ((U j).ι.stalkMap y)).commRingCatIsoToRingEquiv⟩
  have hY : IsRegularScheme Y :=
    ⟨LocallyOfFiniteType.isLocallyNoetherian (a ≫ b), hYreg⟩
  have hη : IsGenericPoint ((U j).ι (genericPoint Y)) (U j : Set P) := by
    have h := (genericPoint_spec Y).image (U j).ι.continuous
    rw [Set.image_univ] at h
    change IsGenericPoint _ (closure (Set.range (U j).ι)) at h
    rwa [Scheme.Opens.range_ι, (hUclosed j).closure_eq] at h
  have hηB : a (genericPoint Y) = genericPoint B := by
    have hcomp : (U j : Set P) ∈ irreducibleComponents P :=
      hUrange ▸ Set.mem_range_self j
    obtain ⟨⟨T, hT, hηT⟩, _, _⟩ := hgen _ hcomp _ hη
    have hT' : T = Set.univ := by simpa only [irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using hT
    apply ((genericPoint_spec B).eq _).symm
    change IsGenericPoint (a₀ ((U j).ι (genericPoint Y))) Set.univ
    simpa only [hT'] using hηT
  have hdom : IsDominant a := by
    constructor
    have hηrange : genericPoint B ∈ Set.range a := ⟨genericPoint Y, hηB⟩
    apply dense_iff_closure_eq.mpr
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← genericPoint_closure B]
    exact closure_mono (Set.singleton_subset_iff.mpr hηrange)
  have hfinite : (@algebraMap B.functionField Y.functionField _ _
      a.dominantFunctionFieldAlgebra).Finite := by
    have hcomp : (U j : Set P) ∈ irreducibleComponents P :=
      hUrange ▸ Set.mem_range_self j
    have hf₀ := (hgen _ hcomp _ hη).2.1
    have hf : (a.residueFieldMap (genericPoint Y)).hom.Finite := by
      dsimp [a]
      rw [Scheme.residueFieldMap_comp, CommRingCat.hom_comp]
      exact (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso _).2).comp hf₀
    let := a.dominantFunctionFieldAlgebra
    let := (a.residueFieldMap (genericPoint Y)).hom.toAlgebra
    have : Module.Finite (B.residueField (a (genericPoint Y)))
        (Y.residueField (genericPoint Y)) := hf
    have he := a.finrank_stalk_eq_finrank_residueField
      (genericPoint Y) (genericPoint B) hηB
      (Field.toIsField B.functionField) (Field.toIsField Y.functionField)
    have hp : 0 < Module.finrank B.functionField Y.functionField := by
      rw [show Module.finrank B.functionField Y.functionField =
        Module.finrank (B.residueField (a (genericPoint Y)))
          (Y.residueField (genericPoint Y)) from he]
      exact Module.finrank_pos
    exact Module.finite_of_finrank_pos hp
  have : IsLocallyNoetherian Y := hY.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (a ≫ b)
  have : IsNoetherian Y := {}
  let D := D₀.comap (U j).ι
  have hD : IsStrictNormalCrossingsBoundary D :=
    snc_comap_clopen (U j).ι hcl D₀ hsnc
  obtain ⟨n, C, hCinj, hCreg, hCsupp, hCint⟩ := hD.2.2
  have hIsupp : (I.comap a).support = D.support := by
    apply SetLike.coe_injective
    simp only [D, a, Scheme.IdealSheafData.coe_support_comap, hD₀,
      Scheme.IdealSheafData.support_radical, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Set.preimage_preimage]
    rfl
  have hI' := cartier_comap_of_dominant a hI
  have hJ' := cartier_comap_of_dominant a hJ
  have hJsub : (J.comap a).support ≤ ⨆ i, (C i).support := by
    rw [← hCsupp, ← hIsupp, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap]
    exact fun x hx ↦ hJI hx
  obtain ⟨Aout, hAout⟩ := cartier_support_subfamily (J.comap a) hJ' n C
    (fun i ↦ (hCreg i).1) (fun i z ↦ by
      have he : (⨆ j ∈ ({i} : Finset (Fin n)), C j) = C i := by simp
      have hh := hCint {i}
      rw [he] at hh
      simpa using (hh z).2) hJsub
  refine ⟨Y, a, inferInstance, hdom, hY, inferInstance, inferInstance, inferInstance,
    inferInstance, hfinite, D, n, C, Aout, hD, hCinj, hCreg, hCsupp, hCint,
    hI', hJ', hIsupp, hAout, ?_, ?_⟩
  · rw [← hIsupp, Scheme.IdealSheafData.coe_support_comap]
    rfl
  · rw [← hAout, Scheme.IdealSheafData.coe_support_comap]
    rfl

end AlgebraicGeometry
