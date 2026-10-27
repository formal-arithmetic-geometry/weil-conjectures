module

public import Sheaf.Paper.EmbeddedEllLattice
public import Sheaf.Paper.IntegralScalarConstructibleImage
public import Sheaf.Paper.ContinuousIntegralLocalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.LatticePairRestriction
import Sheaf.Paper.LatticeScalarExtensionFractions
import Sheaf.Paper.FullEmbeddedLatticeRationalization
import Sheaf.Paper.ContinuousIntegralRegularTelescope
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Condensed and continuous presentations of embedded lattices

Source: HRS Example 3.1; Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(6);
blueprint latest, stratified-lattice-scheme proof (1).
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits Opposite
open scoped ChangeOfRings CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.EmbeddedLatticeComparison

attribute [local instance] latticeWeakSheafifyOver latticeWEqualsOver

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- The fixed continuous realization of the rational internal module.
Source: HRS Example 3.1, using the published canonical encoding.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev continuousModule (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) :=
  (CondensedRing.continuousFieldModuleEquivalenceUniverse ell E X).functor.obj L

/-- The integral-to-rational continuous coefficient inclusion.
Source: Bhatt--Scholze 6.8.1; the existing continuous coefficient map.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev inclusion (X : Scheme.{u}) :=
  latticeCoefficientSheafMap X (Padic.coefficientExtensionIntegers ell E).subtype
    continuous_subtype_val

/-- Integral module underlying the rational module on a slice.
Source: Bhatt--Scholze 6.8.4(6), restriction along the integral inclusion.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev ambient {X : Scheme.{u}}
    (L : SheafOfModules.{u + 1} (latticeModuleRing X E)) (U : X.ProEt) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (latticeScalarMap (inclusion ell E X) U))).obj (L.over U)

/-- The actual locally free subsheaves with full ell-localization.
The underlying abelian sheaves of the canonical encoding are unchanged, so these are
also the embedded internal lattices, with their transported integral action.
Source: Bhatt--Scholze 6.8.3 and 6.8.4(6).
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev Lattices {X : Scheme.{u}}
    (L : SheafOfModules.{u + 1} (latticeModuleRing X E)) (U : X.ProEt) :=
  SheafOfModules.EmbeddedEllLattice ell (ambient ell E L U)

/-- Restrict scalar extension back to the integral ring.
Source: Stacks 03EK, sheafified tensor scalar extension.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev localizedTensor (X : Scheme.{u}) (U : X.ProEt)
    (M : SheafOfModules.{u + 1}
      ((latticeModuleRing X (Padic.coefficientExtensionIntegers ell E)).over U)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (latticeScalarMap (inclusion ell E X) U))).obj
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (latticeScalarMap (inclusion ell E X) U) M)

/-- A local pure tensor, followed by the actual sheafification unit.
Source: Stacks 03EK; Bhatt--Scholze 6.8.2.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev tensorSection (X : Scheme.{u}) (U : X.ProEt)
    (M : SheafOfModules.{u + 1}
      ((latticeModuleRing X (Padic.coefficientExtensionIntegers ell E)).over U))
    (T : (Over U)ᵒᵖ) (s : (latticeCoefficientSheaf X E).obj.obj (op T.unop.left))
    (m : M.val.obj T) :=
  (latticeTensorUnit (inclusion ell E X) U M).app T
    (s ⊗ₜ[(latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers ell E)).obj.obj
      (op T.unop.left), (((inclusion ell E X).hom.app (op T.unop.left)).hom)] m)

/-- The continuous coefficient inclusion, viewed on underlying abelian sheaves.
Source: HRS Example 3.1, functoriality in the coefficient ring.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev continuousInclusion (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map (inclusion ell E X)

/-- The pulled-back integral inclusion is the inverse image of postcomposition by A ↪ E.
Source: HRS Example 3.1, functoriality in the coefficient ring.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison). -/
abbrev internalInclusion (X : Scheme.{u}) :=
  (upperStarFromPoint X).map
    (Profinite.continuousMapRingObjMapOfUniverse
      (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val)

private theorem integral_mem_iff (x : E) :
    x ∈ Padic.coefficientExtensionIntegers ell E ↔ ‖x‖ ≤ 1 := by
  have hm := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := ℚ_[ell]) (L := E))).choose_spec.choose_spec.1 x
  change x ∈ Padic.coefficientExtensionIntegers ell E ↔ _ at hm
  rw [hm]
  change spectralNorm ℚ_[ell] E x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[ell]]

omit [FiniteDimensional ℚ_[ell] E] in
private theorem ell_ne_zero : (ell : E) ≠ 0 := by
  have h : (ell : ℚ_[ell]) ≠ 0 := by exact_mod_cast (Fact.out : ell.Prime).ne_zero
  simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ell] E).injective.ne h

private theorem compact_denominator (S : Type u) [TopologicalSpace S] [CompactSpace S]
    (f : C(S, E)) : ∃ (n : ℕ) (a : C(S, Padic.coefficientExtensionIntegers ell E)),
      ∀ x, f x = (a x : E) / (ell : E) ^ n := by
  have hnorm : ‖(ell : E)‖ < 1 := by
    have h : ‖(ell : E)‖ = ‖(ell : ℚ_[ell])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (ell : ℚ_[ell]))
    rw [h]
    exact Padic.norm_p_lt_one
  have hb : 0 < ‖f‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hb) hnorm
  have hmem (x : S) : f x * (ell : E) ^ n ∈ Padic.coefficientExtensionIntegers ell E := by
    rw [integral_mem_iff, norm_mul, norm_pow]
    calc
      ‖f x‖ * ‖(ell : E)‖ ^ n ≤ (‖f‖ + 1) * ‖(ell : E)‖ ^ n :=
        mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x |>.trans (by linarith))
          (by positivity)
      _ ≤ (‖f‖ + 1) * (‖f‖ + 1)⁻¹ := (mul_lt_mul_of_pos_left hn hb).le
      _ = 1 := mul_inv_cancel₀ hb.ne'
  refine ⟨n, ⟨fun x ↦ ⟨f x * (ell : E) ^ n, hmem x⟩,
    (f.continuous.mul continuous_const).subtype_mk _⟩, ?_⟩
  intro x
  exact (mul_div_cancel_right₀ (f x) (pow_ne_zero n (ell_ne_zero ell E))).symm

private abbrev coefficientPresheaf (R : Type u) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab

private def coefficientLeg (n : ℕ) :
    coefficientPresheaf (Padic.coefficientExtensionIntegers ell E) ⟶
      coefficientPresheaf E where
  app S := AddCommGrpCat.ofHom
    { toFun x := ULift.up
        (⟨fun s ↦ (x.down s : E) / (ell : E) ^ n,
          (continuous_subtype_val.comp x.down.continuous).div_const _⟩ : C(S.unop, E))
      map_zero' := by apply ULift.ext; ext; simp
      map_add' x y := by
        apply ULift.ext
        ext s
        change ((x.down s : E) + (y.down s : E)) / (ell : E) ^ n = _
        exact add_div _ _ _ }
  naturality _ _ _ := rfl

private def coefficientCocone : Cocone (CondensedRing.integralLocalizationSequence ell
    (coefficientPresheaf (Padic.coefficientExtensionIntegers ell E))) where
  pt := coefficientPresheaf E
  «ι» := NatTrans.ofSequence (coefficientLeg ell E) (by
    intro n
    simp only [CondensedRing.integralLocalizationSequence,
      Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    ext S x
    change ULift.{u + 1} C(S.unop, Padic.coefficientExtensionIntegers ell E) at x
    apply ULift.ext
    ext s
    change ((ell • x.down s : Padic.coefficientExtensionIntegers ell E) : E) /
      (ell : E) ^ (n + 1) = (x.down s : E) / (ell : E) ^ n
    change (Padic.coefficientExtensionIntegers ell E).subtype (ell • x.down s) /
      (ell : E) ^ (n + 1) = (x.down s : E) / (ell : E) ^ n
    rw [map_nsmul, nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ell E]
    rfl)

private def coefficientCoconeIsColimit : IsColimit (coefficientCocone ell E) := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨n, a, ha⟩ := compact_denominator ell E S.unop x.down
    refine ⟨n, ULift.up a, ?_⟩
    apply ULift.ext
    exact ContinuousMap.ext ha
  · intro n x y h
    have hxy : x = y := by
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      have h' := congrArg (fun f : ULift.{u + 1} C(S.unop, E) ↦ f.down s) h
      change (x.down s : E) / (ell : E) ^ n = (y.down s : E) / (ell : E) ^ n at h'
      exact (div_left_inj' (pow_ne_zero n (ell_ne_zero ell E))).mp h'
    subst y
    exact ⟨n, 𝟙 n, rfl⟩

private def pointCoefficientIso (R : Type u) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] :
    (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (coefficientPresheaf R) ≅ Profinite.continuousMapRingObjOfUniverse R :=
  Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse R)

private abbrev coefficientFunctor (X : Scheme.{u}) :=
  presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

private def schemeCoefficientIso (X : Scheme.{u})
    (R : Type u) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    (coefficientFunctor X).obj (coefficientPresheaf R) ≅
      condensedRingObj (Profinite.continuousCoefficientRingObj R) X :=
  (upperStarFromPoint X).mapIso (pointCoefficientIso R)

private theorem coefficientSquare (X : Scheme.{u}) :
    internalInclusion ell E X ≫ ContinuousRingUniverse.comparison X E =
      ContinuousRingUniverse.comparison X (Padic.coefficientExtensionIntegers ell E) ≫
        continuousInclusion ell E X := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  unfold internalInclusion ContinuousRingUniverse.comparison upperStarFromPoint
  erw [adj.homEquiv_naturality_left]
  rw [adj.homEquiv_naturality_right]
  dsimp only [adj]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

private theorem coefficientTelescope (X : Scheme.{u}) :
    ∃ c : Cocone (CondensedRing.integralLocalizationSequence ell
        (condensedRingObj (Profinite.continuousCoefficientRingObj
          (Padic.coefficientExtensionIntegers ell E)) X)),
      Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ condensedRingObj (Profinite.continuousCoefficientRingObj E) X,
        c.ι.app 0 ≫ e.hom = internalInclusion ell E X := by
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  let F := coefficientFunctor X
  have : F.Additive := by
    exact rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  apply CondensedRing.transportRegularTelescope ell F (coefficientCocone ell E)
    (isColimitOfPreserves F (coefficientCoconeIsColimit ell E))
    (schemeCoefficientIso X (Padic.coefficientExtensionIntegers ell E))
    (schemeCoefficientIso X E) (𝟭 _) (internalInclusion ell E X)
  have hzero : (coefficientCocone ell E).ι.app 0 =
      Functor.whiskerRight
        (Profinite.continuousMapRingPresheafMapOfUniverse
          (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val)
        (forget₂ RingCat Ab) := by
    ext S x
    apply ULift.ext
    ext t
    change (x.down t : E) / (ell : E) ^ 0 = (x.down t : E)
    simp
  change F.map ((coefficientCocone ell E).ι.app 0) ≫ _ = _
  rw [hzero]
  change (upperStarFromPoint X).map
      ((presheafToSheaf _ Ab).map _) ≫
        (upperStarFromPoint X).map (pointCoefficientIso E).hom =
      (upperStarFromPoint X).map
        (pointCoefficientIso (Padic.coefficientExtensionIntegers ell E)).hom ≫
      (upperStarFromPoint X).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Profinite.continuousMapRingObjMapOfUniverse, Sheaf.sheafCompose_map_eq]
  simp only [pointCoefficientIso, Iso.hom_inv_id_assoc]
  rfl

section Images

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  (U : X.ProEt)

private def pairImageSubmodule (P : IntegralLatticePair a L U) :
    ((SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj (L.over U)).val.Submodule where
  obj T := LinearMap.range ((pairEmbedding a L U P).val.app T).hom
  map {T T'} f := by
    rintro x ⟨m, rfl⟩
    refine ⟨P.module.val.map f m, ?_⟩
    exact PresheafOfModules.naturality_apply (pairEmbedding a L U P).val f m

private def pairImagePresheafIso
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P : IntegralLatticePair a L U) :
    P.module.val ≅ (pairImageSubmodule a L U P).toPresheafOfModules :=
  PresheafOfModules.isoMk (fun T ↦
    (LinearEquiv.ofInjective ((pairEmbedding a L U P).val.app T).hom
      (P.embedding_injective a L U ha T)).toModuleIso) (by
    intro T T' f
    ext m
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply (pairEmbedding a L U P).val f m)

private theorem pairImage_isSheaf
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P : IntegralLatticePair a L U) :
    Presheaf.IsSheaf ((Scheme.ProEt.topology X).over U)
      (pairImageSubmodule a L U P).toPresheafOfModules.presheaf := by
  let e := (PresheafOfModules.toPresheaf _).mapIso (pairImagePresheafIso a L U ha P)
  exact (Presheaf.isSheaf_of_iso_iff e).mp P.module.isSheaf

private def pairImageIso
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P : IntegralLatticePair a L U) :
    P.module ≅ ⟨(pairImageSubmodule a L U P).toPresheafOfModules,
      pairImage_isSheaf a L U ha P⟩ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (pairImagePresheafIso a L U ha P)

private theorem pairImage_locallyFree
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (P : IntegralLatticePair a L U) :
    (⟨(pairImageSubmodule a L U P).toPresheafOfModules,
      pairImage_isSheaf a L U ha P⟩ : SheafOfModules _).IsFiniteLocallyFree := by
  have := P.locallyFree
  exact SheafOfModules.IsFiniteLocallyFree.of_iso (pairImageIso a L U ha P)

private theorem pairImage_range (P : IntegralLatticePair a L U) (T : (Over U)ᵒᵖ) :
    Set.range (fun m : (pairImageSubmodule a L U P).obj T ↦ m.val) = P.image T := by
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact m.property
  · rintro ⟨m, hm⟩
    exact ⟨⟨x, ⟨m, hm⟩⟩, rfl⟩

end Images

private theorem inclusion_injective (X : Scheme.{u}) (U : X.ProEt) :
    ∀ T, Function.Injective
      (((latticeScalarMap (inclusion ell E X) U).hom.app T).hom) := by
  intro T f g h
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun s : ULift.{u + 1} C(T.unop.left.left, E) ↦ s.down x) h

private theorem pairImage_full (X : Scheme.{u})
    (L : SheafOfModules.{u + 1} (latticeModuleRing X E)) (U : X.ProEt)
    (P : IntegralLatticePair (inclusion ell E X) L U) :
    ∀ (T : Over U) (x : (ambient ell E L U).val.obj (op T)),
      ∃ s : Sieve T, s ∈ ((Scheme.ProEt.topology X).over U) T ∧
        ∀ (V : Over U) (f : V ⟶ T), s f →
          ∃ n : ℕ, ell ^ n • (ambient ell E L U).val.map f.op x ∈
            (pairImageSubmodule (inclusion ell E X) L U P).obj (op V) := by
  intro T x
  obtain ⟨s, hs, hx⟩ := (lattice_scalar_extension_fractions ell E X U P.module).2
    T (P.rationalization.inv.val.app (op T) x)
  refine ⟨s, hs, ?_⟩
  intro V f hf
  obtain ⟨n, m, hm⟩ := hx V f hf
  refine ⟨n, m, ?_⟩
  have h := congrArg (P.rationalization.hom.val.app (op V)) hm
  rw [map_nsmul] at h
  have hn := PresheafOfModules.naturality_apply P.rationalization.inv.val f.op x
  change _ = _ at hn
  rw [← hn] at h
  have hi := congrArg (fun k ↦ k.val.app (op V)
    ((L.over U).val.map f.op x)) P.rationalization.inv_hom_id
  change P.rationalization.hom.val.app (op V)
    (P.rationalization.inv.val.app (op V) ((L.over U).val.map f.op x)) = _ at hi
  erw [hi] at h
  exact h.symm

private def imageLattice (X : Scheme.{u})
    (L : SheafOfModules.{u + 1} (latticeModuleRing X E)) (U : X.ProEt)
    (P : IntegralLatticePair (inclusion ell E X) L U) : Lattices ell E L U where
  submodule := pairImageSubmodule (inclusion ell E X) L U P
  isSheaf := pairImage_isSheaf (inclusion ell E X) L U (inclusion_injective ell E X U) P
  locallyFree := pairImage_locallyFree (inclusion ell E X) L U
    (inclusion_injective ell E X U) P
  full := pairImage_full ell E X L U P

private theorem embedded_ext {X : Scheme.{u}}
    {L : SheafOfModules.{u + 1} (latticeModuleRing X E)} {U : X.ProEt}
    {N N' : Lattices ell E L U}
    (h : N.submodule = N'.submodule) : N = N' := by
  cases N
  cases N'
  cases h
  rfl


/-- Condensed and continuous coefficients identify the integral inclusion, fractions,
embedded lattices and rationalized pairs, with every restriction and matrix label.

Source: blueprint latest, stratified-lattice-scheme proof (1); HRS Example 3.1;
Bhatt--Scholze 6.8.2 and 6.8.4(6); Stacks 03EK.
(blueprint: lem-sfb-embedded-lattice-coefficient-comparison).

Proof:
1. Apply lem-sfb-continuous-ring-universe-realization to A and E. Precomposition
with the test projection commutes with the inclusion, giving the coefficient square.
2. det-prop-sfb-qlbar-colimit-x-invert-ell identifies A[1/ell] with E. This is a
sheaf localization: there need not be one denominator on a non-quasi-compact object.
3. def-weil-pbc-internal-abelian-sheaf-module-equivalence identifies internal modules
and sectionwise modules with unchanged abelian sheaves and restrictions. Its action
on a tensor is multiplication; balanced bilinear maps identify scalar extensions.
4. For every M, form the fraction telescope. Its comparison to sheafified E tensor M
sends m/ell^n to ell^(-n) tensor m. The fraction relation makes this well-defined:
multiply by a sufficiently large invertible power of ell. The inverse sends
(a/ell^n) tensor m to am/ell^n, is balanced, and respects restrictions. Check inverse
identities on local pure tensors and fractions; sheafification glues the maps.
5. On a finite-free cover, m ↦ alpha(1 tensor m) is coordinatewise A ↪ E, hence
injective. Unique local lifts glue, so its image is a finite locally free subsheaf.
Step 4 identifies its localization with L. Conversely, for a full embedded N, the
map E tensor N → L sends s tensor n to sn, and is an isomorphism by localization.
6. The integral isomorphism from a pair to its image intertwines rationalizations.
lem-weil-pbc-lattice-pair-image-classification identifies equality of images with
exactly the stated equivalence relation. Thus the surjection with this kernel
induces the bijection on isomorphism classes; the image formula pins its inverse.
7. lem-weil-pbc-lattice-pair-restriction identifies restricted images objectwise.
All coefficient, fraction and tensor maps commute with restrictions, hence so does F.
8. In a rational frame the specified pair has image g A^r. Multiplication by g and
its inverse identify it with A^r and its localization with E^r. The displayed image
formula is the normalization for every rank, including zero. -/
theorem embedded_lattice_coefficient_comparison (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (_hL : (continuousModule ell E X L).IsFiniteLocallyFree) :
    IsIso (ContinuousRingUniverse.comparison X (Padic.coefficientExtensionIntegers ell E)) ∧
    IsIso (ContinuousRingUniverse.comparison X E) ∧
    internalInclusion ell E X ≫ ContinuousRingUniverse.comparison X E =
      ContinuousRingUniverse.comparison X (Padic.coefficientExtensionIntegers ell E) ≫
        continuousInclusion ell E X ∧
    (∃ c : Cocone (CondensedRing.integralLocalizationSequence ell
        (condensedRingObj (Profinite.continuousCoefficientRingObj
          (Padic.coefficientExtensionIntegers ell E)) X)),
      Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ condensedRingObj (Profinite.continuousCoefficientRingObj E) X,
        ∀ (n : ℕ) (T : X.ProEtᵒᵖ)
          (a : (condensedRingObj (Profinite.continuousCoefficientRingObj
            (Padic.coefficientExtensionIntegers ell E)) X).obj.obj T),
          (ContinuousRingUniverse.comparison X E).hom.app T
            (e.hom.hom.app T ((c.ι.app n).hom.app T a)) =
              latticeConstantCoefficient X E T.unop ((ell : E) ^ n)⁻¹ *
                (show (latticeCoefficientSheaf X E).obj.obj T from
                  (continuousInclusion ell E X).hom.app T
                    ((ContinuousRingUniverse.comparison X
                      (Padic.coefficientExtensionIntegers ell E)).hom.app T a))) ∧
    (∀ (U : X.ProEt) (M : SheafOfModules.{u + 1}
        ((latticeModuleRing X (Padic.coefficientExtensionIntegers ell E)).over U)),
      ∃ c : Cocone (CondensedRing.integralLocalizationSequence ell M), Nonempty (IsColimit c) ∧
        ∃ e : c.pt ≅ localizedTensor ell E X U M,
          (∀ (n : ℕ) (T : (Over U)ᵒᵖ) (m : M.val.obj T),
            e.hom.val.app T ((c.ι.app n).val.app T m) =
              tensorSection ell E X U M T
                (latticeConstantCoefficient X E T.unop.left ((ell : E) ^ n)⁻¹) m) ∧
          (∀ (n : ℕ) (T : (Over U)ᵒᵖ)
            (a : (latticeCoefficientSheaf X
              (Padic.coefficientExtensionIntegers ell E)).obj.obj (op T.unop.left))
            (m : M.val.obj T),
            e.inv.val.app T (tensorSection ell E X U M T
              ((inclusion ell E X).hom.app (op T.unop.left) a *
                latticeConstantCoefficient X E T.unop.left ((ell : E) ^ n)⁻¹) m) =
                  (c.ι.app n).val.app T (a • m))) ∧
    ∃ F : ∀ U : X.ProEt,
        IntegralLatticePair (inclusion ell E X) (continuousModule ell E X L) U →
          Lattices ell E (continuousModule ell E X L) U,
      (∀ U, Function.Surjective (F U)) ∧
      (∀ (U : X.ProEt)
        (P Q : IntegralLatticePair (inclusion ell E X) (continuousModule ell E X L) U),
          F U P = F U Q ↔ P.Equivalent Q) ∧
      (∀ (U : X.ProEt)
        (P : IntegralLatticePair (inclusion ell E X) (continuousModule ell E X L) U)
        (T : (Over U)ᵒᵖ),
          Set.range (fun m : (F U P).submodule.obj T ↦ m.val) = P.image T) ∧
      (∀ (U V : X.ProEt) (f : V ⟶ U)
        (P : IntegralLatticePair (inclusion ell E X) (continuousModule ell E X L) U)
        (T : (Over V)ᵒᵖ),
          Set.range (fun m :
            (F V (P.restrict (inclusion ell E X) f)).submodule.obj T ↦ m.val) =
            Set.range (fun m : (F U P).submodule.obj ((Over.map f).op.obj T) ↦ m.val)) ∧
      (∀ (U : X.ProEt) (r : ℕ)
        (t : (continuousModule ell E X L).over U ≅ latticeFreeSheaf X E U r)
        (g : Matrix.GeneralLinearGroup (Fin r) E),
        ∃ P : IntegralLatticePair (inclusion ell E X) (continuousModule ell E X L) U,
          ∀ T : (Over U)ᵒᵖ,
            Set.range (fun m : (F U P).submodule.obj T ↦ t.hom.val.app T m.val) =
              matrixLatticeImage X E (Padic.coefficientExtensionIntegers ell E) U r g T)  := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ell]
  have square := coefficientSquare ell E X
  refine ⟨ContinuousRingUniverse.comparison_isIso X _,
    ContinuousRingUniverse.comparison_isIso X _, square, ?_, ?_, ?_⟩
  · obtain ⟨c, hc, e, hz⟩ := coefficientTelescope ell E X
    refine ⟨c, hc, e, ?_⟩
    intro n
    induction n with
    | zero =>
      intro T a
      have h := congrArg (fun f ↦ f.hom.app T a) hz
      have hs := congrArg (fun f ↦ f.hom.app T a) square
      change (ContinuousRingUniverse.comparison X E).hom.app T
        (e.hom.hom.app T ((c.ι.app 0).hom.app T a)) = _
      rw [show e.hom.hom.app T ((c.ι.app 0).hom.app T a) =
        (internalInclusion ell E X).hom.app T a from h]
      change (ContinuousRingUniverse.comparison X E).hom.app T
        ((internalInclusion ell E X).hom.app T a) =
        (continuousInclusion ell E X).hom.app T
          ((ContinuousRingUniverse.comparison X
            (Padic.coefficientExtensionIntegers ell E)).hom.app T a) at hs
      rw [pow_zero, inv_one]
      change _ = (1 : (latticeCoefficientSheaf X E).obj.obj T) * _
      rw [one_mul]
      exact hs
    | succ n ih =>
      intro T a
      have hw := c.w (homOfLE (Nat.le_succ n))
      simp only [CondensedRing.integralLocalizationSequence,
        Functor.ofSequence_map_homOfLE_succ] at hw
      have hstep := congrArg (fun f ↦ f.hom.app T a) hw
      change (c.ι.app (n + 1)).hom.app T (ell • a) = (c.ι.app n).hom.app T a at hstep
      have hn := congrArg ((ContinuousRingUniverse.comparison X E).hom.app T)
        (congrArg (e.hom.hom.app T) hstep)
      rw [map_nsmul, map_nsmul, map_nsmul, ih] at hn
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      have hn' := congrArg (fun f : ULift.{u + 1} C(T.unop.left, E) ↦ f.down x) hn
      let q : ULift.{u + 1} C(T.unop.left, E) :=
        (ContinuousRingUniverse.comparison X E).hom.app T
          (e.hom.hom.app T ((c.ι.app (n + 1)).hom.app T a))
      let b : ULift.{u + 1} C(T.unop.left, E) :=
        (continuousInclusion ell E X).hom.app T
          ((ContinuousRingUniverse.comparison X
            (Padic.coefficientExtensionIntegers ell E)).hom.app T a)
      change (ell • q).down x =
        ((ULift.up (ContinuousMap.const T.unop.left ((ell : E) ^ n)⁻¹) :
          ULift.{u + 1} C(T.unop.left, E)) * b).down x at hn'
      change ell • q.down x = ((ell : E) ^ n)⁻¹ * b.down x at hn'
      rw [nsmul_eq_mul] at hn'
      change (ell : E) * _ = ((ell : E) ^ n)⁻¹ * _ at hn'
      change q.down x = ((ell : E) ^ (n + 1))⁻¹ * b.down x
      apply (mul_left_cancel₀ (ell_ne_zero ell E))
      rw [hn']
      field_simp [ell_ne_zero ell E]
      ring
  · intro U M
    exact (lattice_scalar_extension_fractions ell E X U M).1
  · let F := imageLattice ell E X (continuousModule ell E X L)
    refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
    · intro U N
      obtain ⟨α, hα⟩ := full_embedded_lattice_rationalization ell E X
        (continuousModule ell E X L) U N
      let P : IntegralLatticePair (inclusion ell E X) (continuousModule ell E X L) U :=
        { module := ⟨N.submodule.toPresheafOfModules, N.isSheaf⟩
          locallyFree := N.locallyFree
          rationalization := α }
      refine ⟨P, embedded_ext ell E ?_⟩
      apply PresheafOfModules.Submodule.ext
      intro T
      apply Submodule.ext
      intro x
      constructor
      · rintro ⟨m, hm⟩
        have h := hα T m
        change (pairEmbedding (inclusion ell E X) (continuousModule ell E X L) U P).val.app
          T m = m.val at h
        rw [h] at hm
        exact hm ▸ m.property
      · intro hx
        refine ⟨⟨x, hx⟩, ?_⟩
        exact hα T ⟨x, hx⟩
    · intro U P Q
      rw [IntegralLatticePair.equivalent_iff_image_eq (inclusion ell E X) _ U
        (inclusion_injective ell E X U) P Q]
      constructor
      · intro h T
        have hh := congrArg (fun N : Lattices ell E (continuousModule ell E X L) U ↦
          Set.range (fun m : N.submodule.obj T ↦ m.val)) h
        exact (pairImage_range (inclusion ell E X) _ U P T).symm.trans
          (hh.trans (pairImage_range (inclusion ell E X) _ U Q T))
      · intro h
        apply embedded_ext ell E
        apply PresheafOfModules.Submodule.ext
        intro T
        apply Submodule.ext
        intro x
        exact Set.ext_iff.mp (h T) x
    · intro U P T
      exact pairImage_range (inclusion ell E X) _ U P T
    · intro U V f P T
      rw [show Set.range (fun m : (F V (P.restrict (inclusion ell E X) f)).submodule.obj T ↦
          m.val) = (P.restrict (inclusion ell E X) f).image T from
            pairImage_range (inclusion ell E X) _ V _ T,
        IntegralLatticePair.restrict_image]
      exact (pairImage_range (inclusion ell E X) _ U P ((Over.map f).op.obj T)).symm
    · intro U r t g
      obtain ⟨P, hP⟩ := exists_matrixIntegralLatticePair X E
        (Padic.coefficientExtensionIntegers ell E) U r (continuousModule ell E X L) t g
      refine ⟨P, ?_⟩
      intro T
      have hrange : Set.range (fun m : (F U P).submodule.obj T ↦
          t.hom.val.app T m.val) = Set.image (t.hom.val.app T) (P.image T) := by
        ext x
        constructor
        · rintro ⟨m, rfl⟩
          exact ⟨m.val, m.property, rfl⟩
        · rintro ⟨y, ⟨m, hm⟩, rfl⟩
          exact ⟨⟨y, ⟨m, hm⟩⟩, rfl⟩
      rw [hrange]
      exact hP T

end AlgebraicGeometry.ProEtale.EmbeddedLatticeComparison
