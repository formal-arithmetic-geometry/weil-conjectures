/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLocalReductionLowerBound
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre

/-! # Uniform reduction criterion for a principal regular ideal

Source: the uniform triangulation supplement, local-model bounds and compatible
origin descent (blueprint: lem-pbc-principal-uniform-reduction-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

private theorem principalLocalReduction_isGE
    {T X : Scheme.{u}} (g : X ⟶ T)
    {A : Type (u + 1)} [CommRing A] [IsDomain A]
    (d : AdicCoefficientDatum A) (π : A) (hI : d.ideal = Ideal.span {π})
    (hπ : π ≠ 0)
    (L : CochainComplex (pbcModules X
      ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] (n : ℕ) :
    (adicTowerLocalReduction d g L n).IsGE (a - 1) := by
  obtain ⟨p, hz, hs, hp⟩ := completed_principal_resolution T d π hI hπ n
  obtain ⟨f', hz', hs'⟩ := normalized_pullback_sequence g
    (pbcAdicProjection T d n) _ p hp hz hs
  exact lower_bound_of_coefficient_sequence X _ f' _
    (fun V ↦ by
      change (((adicTowerInverseImage g).map (pbcAdicProjection T d n)).hom.app V)
        (1 : ((adicTowerInverseImage g).obj (pbcAdicCompletion T d)).obj.obj V) = 1
      exact map_one _) hz' hs' (DerivedCategory.Q.obj L) a

/-- For a nonzero principal ideal in a domain, uniform local reduction models with
compatible etale origins are equivalent to one intrinsic constructible cohomology interval.
Source: blueprint constructible-complete triangulation supplement, steps 2, 6 and 7;
Stacks Tags 093M and 06YU for the local coefficient-resolution argument
(blueprint: lem-pbc-principal-uniform-reduction-criterion).

Proof: the regular principal quotient has a two-term free resolution. Exact constants,
flat completed coefficients, and exact inverse image give the same resolution on each
local chart. Its reduction triangle bounds a model in [a,b] in [a-1,b]. Stratum-cover
zero detection descends these bounds. Finite-lisse local cohomology descends to
constructible global cohomology, and exact restriction to constant coefficients
preserves both bounds and homology. Conversely apply normalized constructible local
effectivity to the canonical reduction tower with its common interval. Realize its
level origins through the exact coefficient equivalence. Bounded-below etale comparison
lifts adjacent normalization isomorphisms uniquely; its faithfulness verifies their
compatibility equations. The canonical tower supplies the uniform local models and
the lifted normalizations supply the witnessed tower. Empty schemes, zero models,
and the first positive quotient satisfy the same argument. -/
theorem pbcPrincipalUniformReductionCriterion
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] [IsDomain A]
    (d : AdicCoefficientDatum A) (π : A) (hI : d.ideal = Ideal.span {π})
    (hπ : π ≠ 0) (K : PbcCompletedDerived T d) :
    (PbcHasUniformConstructibleReductions T d K ∧
      PbcHasCompatibleEtaleOrigins T d K) ↔ PbcUniformReductionProfile T d K := by
  constructor
  · rintro ⟨⟨M, e, ⟨a, b, hab, S, hS⟩, he⟩, _⟩
    choose W hW hL using hS
    have hcov := fun i ↦ cover_of_sieve (S.domain i) (W i) (hW i)
    choose I U f hU hf using hcov
    let V (i : Fin S.n) : Cover.{u + 1} proetalePrecoverage (S.domain i) :=
      { I₀ := I i, X := fun j ↦ (U i j).left, f := fun j ↦ (U i j).hom, mem₀ := hU i }
    have hmodels (i : Fin S.n) (j : (V i).I₀) :
        Nonempty (AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :=
      hL i (U i j) (f i j) (hf i j)
    let L (i : Fin S.n) (j : (V i).I₀) := Classical.choice (hmodels i j)
    have hb := uniform_model_bounds T d M a b S V L (by
      intro i j n
      have : (L i j).complex.IsStrictlyGE a :=
        (CochainComplex.isStrictlyGE_iff _ _).2
          (fun q hq ↦ (L i j).bounded q (Or.inl hq))
      exact principalLocalReduction_isGE _ d π hI hπ _ a n)
    have hc := uniform_constructible T d M a b S V L
    have ha (n : ℕ) : (M.level n).IsGE (a - 1) :=
      (DerivedCategory.isGE_iff _ _).2 (fun q hq ↦ hb n q (Or.inl hq))
    have hz (n : ℕ) : (M.level n).IsLE b :=
      (DerivedCategory.isLE_iff _ _).2 (fun q hq ↦ hb n q (Or.inr hq))
    refine ⟨a - 1, b, fun n ↦ ?_⟩
    let R := pbcRestrict (pbcLevelConstantComparison T d n).hom
    have hge := ha n
    have hle := hz n
    have hgeK := DerivedCategory.TStructure.t.isGE_of_iso (e n) (a - 1)
    have hleK := DerivedCategory.TStructure.t.isLE_of_iso (e n) b
    have eH (q : ℤ) := R.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso (e n)) ≪≫
      (R.mapDerivedCategoryHomologyFunctorIso q).app ((pbcCompletedReduction T d n).obj K)
    refine ⟨R.isGE_mapDerivedCategory_obj _ (a - 1),
      R.isLE_mapDerivedCategory_obj _ b, fun q ↦ ?_⟩
    apply (CoefficientSerre.coefficient_constructible_iff T (PbcQuotient d n) _).mpr
    exact isConstructible_of_iso
      ((CoefficientSerre.proEtaleModuleRestriction T (PbcQuotient d n)).mapIso (eH q))
      ((CoefficientSerre.coefficient_constructible_iff T (PbcQuotient d n) _).mp (hc n q))
  · intro hK
    let M := pbcReductionAdicTower T d K
    have hlevels := (uniformProfile_localEffectivity T d K hK).1
    have levels (n : ℕ) := levelOrigin_realization T d M n (hlevels n)
    choose V hV W e using levels
    let W' (n : ℕ) := (W n).some
    let e' (n : ℕ) := (e n).some
    let δ (n : ℕ) := (pbcFunctionReduction T d n).symm.app (V (n + 1)) ≪≫
      (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
        (e' (n + 1)) ≪≫ M.normalization (n + 1) n (Nat.le_succ n) ≪≫ (e' n).symm
    let θ (n : ℕ) := (pbcDerivedFunctionRealization T d n).preimageIso (δ n)
    obtain ⟨β, hβ⟩ := compatibleEtaleNormalizations T d V hV W' θ
    let P : PbcWitnessedTower T d :=
      { K := V, boundedBelow := hV, origin := W', theta := θ,
        beta := β, compatibility := hβ }
    refine ⟨uniformProfile_uniformReductions T d K hK, P, e', fun n ↦ ?_⟩
    change (pbcDerivedFunctionRealization T d n).map (θ n).hom ≫ (e' n).hom = _
    change (pbcDerivedFunctionRealization T d n).map
      ((pbcDerivedFunctionRealization T d n).preimage (δ n).hom) ≫ (e' n).hom = _
    rw [Functor.map_preimage]
    dsimp only [δ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

end AlgebraicGeometry.Scheme
