/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Proper.Geometric.ProperGeometricFibreCohomologicalBound
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.FlatModelGeneration
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Proper.ProperBoundedConstructible
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricStalkTensorConstantSingle
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# Compact-support Tor windows over finite or algebraically closed fields

Source: Stacks Project, Tag 0E8I, lemma-j-shriek-and-tensor; Tags 03DJ, 06YQ and 08G1;
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts paragraph
(blueprint: lem-sp-etale-compact-support-tor-window).

This is the corrected field domain of the ordinary small-etale compactification
calculation: the base field is finite or algebraically closed and its characteristic
is different from the coefficient prime. Characteristic zero is included.
The bound depends only on the proper morphism and precedes all coefficient choices.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Extension by zero preserves the bounded flat constructible model, and proper
pushforward gives a uniform compact-support Tor window over the corrected field domain.

Source: Stacks Project, Tag 0E8I, lemma-j-shriek-and-tensor; literature/blueprint/latest/
blueprint/part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/
sec-change-of-finite-coefficients/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md,
Charts paragraph (blueprint: lem-sp-etale-compact-support-tor-window).

Proof:
1. Finite type over k makes V quasi-compact. The uniform geometric-fibre dimension
   and torsion cohomology bound supplies e depending only on r. The colimit torsion
   characterization identifies its hypothesis with local torsion, F.IsTorsion.
   Degrees above 2e are positive, so the natural-degree bound gives the integer bound.
2. Exact extension by zero induces mapDerivedCategory. Its localization comparison,
   followed by the given Q(P) isomorphism to K, identifies Q(j_!P) with Dj_!K.
   Additivity preserves every zero term, so support remains in [a,b].
3. On the open, j_!P restricts to P; on the closed complement it restricts to zero.
   Geometric stalks detect flatness, hence every extended term is flat. Symmetry
   identifies exactness of right tensor with the two-sided flatness predicate.
4. Finite type over the field makes W locally Noetherian, so j is quasi-compact.
   Constructible extension by zero and the finite-value constructibility comparison
   give constructible terms. Exact functors commute with homology; transport the
   constructible cohomology and bounded cohomology interval of K to Dj_!K.
5. The extended complex has flat terms and support in [a,b]. The bounded-flat
   criterion makes it K-flat and gives Tor amplitude [a,b]. Transport this through
   the localization comparison to obtain the asserted Tor amplitude of Dj_!K.
6. Since ell is prime and char(k) differs from ell, ell and its powers are units
   on all the k-schemes, also in characteristic zero. A sheaf killed by a power
   of ell is locally torsion, so Step 1 supplies the fibre bound d=2e. Apply the
   proper finite-Tor theorem (det-ctf-finite-proper-tor) with this bound to Dj_!K.
   Its proof uses the preceding prime/unit calculation, proper base change and
   the proper projection formula; it does not need positive characteristic.
   This gives bounded constructibility and Tor amplitude [a,b+2e] for Rr_*Dj_!K.
   The composite is exactly the unbounded compactification functor of
   def-amb-etale-compact-support, without a bounded-below replacement. -/
theorem exists_etaleCompactSupport_torWindow_of_finite_or_isAlgClosed
    (k : Type u) [Field k] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
    {W V : Scheme.{u}} [W.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (r : W ⟶ V) [r.IsOver (Spec (.of k))] [IsProper r] :
    ∃ e : ℕ,
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
        (F : Sheaf (pullback r v).smallEtaleTopology AddCommGrpCat.{u + 1}),
        F.IsTorsion →
        ∀ i : ℤ, (2 * (e : ℤ)) < i →
          Subsingleton ((cohomology AddCommGrpCat.{u + 1} (pullback r v) i).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
      ∀ (U : Scheme.{u}) [U.Over (Spec (.of k))]
        [IsSeparated (U ↘ Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
        (j : U ⟶ W) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
        (R : Type (u + 1)) [CommRing R] [Finite R],
        (∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : R) = 0) →
        ∀ (a b : ℤ), a ≤ b → ∀ (K : DerivedCategoryModule R U),
          DerivedCategory.isBoundedConstructible R U K →
          DerivedCategory.hasTorAmplitudeIn R U a b K →
          ∀ (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ),
            Nonempty (_root_.DerivedCategory.Q.obj P ≅ K) →
            (∀ q : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (P.X q))) →
            (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) →
            (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) →
            Nonempty
              (_root_.DerivedCategory.Q.obj
                (((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapHomologicalComplex
                  (.up ℤ)).obj P) ≅
                ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory).obj K) ∧
            (∀ q : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight
              ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj (P.X q)))) ∧
            (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
              ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj (P.X q))) ∧
            (∀ q : ℤ, q < a ∨ b < q → IsZero
              ((((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapHomologicalComplex
                (.up ℤ)).obj P).X q)) ∧
            (HomologicalComplex.quasiIso
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) (.up ℤ)).kFlat
                (((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapHomologicalComplex
                  (.up ℤ)).obj P) ∧
            DerivedCategory.isBoundedConstructible R W
              (((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory).obj K) ∧
            DerivedCategory.hasTorAmplitudeIn R W a b
              (((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory).obj K) ∧
            DerivedCategory.isBoundedConstructible R V
              ((rightDerivedLowerStar (ModuleCat.{u + 1} R) r).obj
                (((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory).obj K)) ∧
            DerivedCategory.hasTorAmplitudeIn R V a (b + 2 * (e : ℤ))
              ((rightDerivedLowerStar (ModuleCat.{u + 1} R) r).obj
                (((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory).obj
                  K)) := by
  classical
  have : CompactSpace V :=
    QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of k))
  obtain ⟨e, _, he⟩ :=
    exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound r
  have hbound : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
      (F : Sheaf (pullback r v).smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsTorsion → ∀ i : ℤ, 2 * (e : ℤ) < i →
        Subsingleton ((cohomology AddCommGrpCat.{u + 1} (pullback r v) i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
    intro Ω _ _ v F hF i hi
    have hn : i = (i.toNat : ℤ) := by omega
    rw [hn]
    exact AddCommGrpCat.isZero_iff_subsingleton.mp
      (he Ω v F ((Scheme.isTorsionAbelianSheaf_characterizations F).1.mpr hF)
        i.toNat (by omega))
  refine ⟨e, hbound, ?_⟩
  intro U _ _ _ _ j _ _ R _ _ hR a b hab K hK _ P hPK hflat hcons hzero
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  let E : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ :=
    (J.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨ePK⟩ := hPK
  let eEK : _root_.DerivedCategory.Q.obj E ≅ J.mapDerivedCategory.obj K :=
    (J.mapDerivedCategoryFactors.app P).symm ≪≫ J.mapDerivedCategory.mapIso ePK
  have hflatP (q : ℤ) : ObjectProperty.flat (P.X q) := by
    refine ⟨?_, hflat q⟩
    exact (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X q)).symm (hflat q)
  have hflatE (q : ℤ) : ObjectProperty.flat (E.X q) :=
    flat_openImmersionLowerShriek_obj j (hflatP q)
  have hzeroE (q : ℤ) (hq : q < a ∨ b < q) : IsZero (E.X q) :=
    J.map_isZero (hzero q hq)
  have : E.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff E a).2
    (fun q hq ↦ hzeroE q (.inl hq))
  have : E.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff E b).2
    (fun q hq ↦ hzeroE q (.inr hq))
  have htor : DerivedCategory.hasTorAmplitudeIn R W a b (J.mapDerivedCategory.obj K) := by
    rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn]
    exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eEK
      (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat E a b hflatE)
  have : IsLocallyNoetherian W :=
    LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of k))
  have hJcons (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
      (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
      Scheme.IsConstructibleEtaleModuleSheaf (J.obj F) := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact j F)
  have hbc : DerivedCategory.isBoundedConstructible R W (J.mapDerivedCategory.obj K) := by
    refine ⟨fun q ↦ ?_, ?_⟩
    · let hsource : Scheme.IsConstructibleSheaf
          (FA := fun M N : ModuleCat.{u + 1} R ↦ M →ₗ[R] N)
          (CA := fun M : ModuleCat.{u + 1} R ↦ M)
          (J.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
          (hJcons _ (hK.1 q))
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
        (Scheme.IsConstructibleSheaf.of_iso
          (FA := fun M N : ModuleCat.{u + 1} R ↦ M →ₗ[R] N)
          (CA := fun M : ModuleCat.{u + 1} R ↦ M)
          (F := J.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
          (by exact (J.mapDerivedCategoryHomologyFunctorIso q).app K))
    · obtain ⟨c, d, hcd, hcdK⟩ := hK.2
      exact ⟨c, d, hcd, fun q hq ↦ (J.map_isZero (hcdK q hq)).of_iso
        ((J.mapDerivedCategoryHomologyFunctorIso q).symm.app K)⟩
  have hd : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
      (F : Sheaf (pullback r v).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (pullback r v).Etale) (s : F.obj.obj (Opposite.op T)),
        ∃ n : ℕ, (ℓ ^ n) • s = 0) →
      ∀ i : ℤ, ((2 * e : ℕ) : ℤ) < i →
        IsZero ((cohomology AddCommGrpCat.{u + 1} (pullback r v) i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
    intro Ω _ _ v F hF i hi
    have hFt : F.IsTorsion := Sheaf.IsTorsion.of_forall_isAddTorsion fun T s ↦ by
      obtain ⟨n, hn⟩ := hF T.unop s
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨ℓ ^ n, pow_pos hℓ.pos n, hn⟩
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr
      (hbound Ω v F hFt i (by simpa using hi))
  have hproper := isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper_current
    ℓ hℓ k hk hchar r R hR (2 * e) hd a b hab (J.mapDerivedCategory.obj K) hbc htor
  refine ⟨⟨eEK⟩, fun q ↦ (hflatE q).2, fun q ↦ hJcons _ (hcons q),
    hzeroE, CochainComplex.kFlat_of_bounded_of_flat E a b hflatE, hbc, htor,
    hproper.1, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hproper.2


end AlgebraicGeometry.Etale
