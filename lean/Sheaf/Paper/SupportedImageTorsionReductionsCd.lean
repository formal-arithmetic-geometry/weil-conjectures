/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
import Sheaf.Paper.SupportedImageFirstReductionCd
import Sheaf.Paper.PrincipalTensorScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.ClassicalInternalModuleSections
import Sheaf.Paper.SupportedFiniteImageClassicalOrigin
import Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit

/-! # Torsion bounds for actual supported images and their integral reductions

Source: Hemo--Richarz--Scholbach, Section 8, (8.1), proof of Lemma 8.6;
Bhatt--Scholze Corollary 5.1.6; Stacks Tag 099W for classical inputs only.
The general integral reduction assertion is the agent obligation recorded as WANTED.
Its first-power case is isolated in SupportedImageFirstReductionCd; coefficient
triangles propagate that case to every positive power in this module.
(blueprint: lem-sfb-supported-image-torsion-reductions-cd).

Paths in a finite qcqs open-closed tree encode support chains. Every chain over the
affine root can be completed to such a tree by adding complementary leaf siblings.
A root path encodes the empty chain. The integral level indexed by n is pi^(n+1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem torsion_cd_proAffineEtale
    {X U : Scheme.{u}} (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (v : U ⟶ X) (hv : proAffineEtale v) :
    U.HasTorsionEtaleCohomologicalDimensionLE d := by
  obtain ⟨I, _, _, D, t, s, hs, hst⟩ := hv
  have hA (i : I) : IsAffine (D.obj i) := (hst i).1.2.1
  let (i : I) : IsAffine (D.obj i) := hA i
  let (i : I) : Etale (t.app i) := (hst i).1.1
  let {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f) := inferInstance
  exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit D
    (Cone.mk U s) hs d (fun i ↦ hcd (D.obj i) (t.app i))

/-- The finite-coefficient clause, independent of the unresolved integral comparison route.
Source: HRS Section 8, Lemma 8.6, discrete torsion paragraph; Stacks Tags 099V and 0F0R.
(blueprint: lem-sfb-supported-finite-image-cd).

Proof: the supported image has a classical torsion antecedent G on U. The affine
pro-etale presentation and the affine-limit torsion bound give cd_tor(U) <= d.
Module/abelian evaluation and classical comparison identify the requested derived
sections with etale derived sections of G. The dimension assumption kills their
cohomology in degree q>d; this degree is positive, so it is a natural degree covered
by the definition of torsion cohomological dimension. Transport zero along the iso.
-/
theorem supported_finite_image_cohomology_vanishes
    (X : Scheme.{u}) (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    {S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (U : Scheme.{u}) (v : U ⟶ X) (hv : proAffineEtale v)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) S)) (f : L ⟶ M)
    (hL : HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) S L)
    (hM : HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) S M)
    (q : ℤ) (hq : (d : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((condensedModuleSections (FiniteDiscreteOrdinary.coefficient A) U).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) v).obj
            ((p.extension (FiniteDiscreteOrdinary.coefficient A)).obj (image f)))))) := by
  obtain ⟨G, hG, ⟨eG⟩⟩ := supported_finite_image_classical_origin A tree p L M f hL hM v
  obtain ⟨e⟩ := classical_internal_module_sections (FiniteDiscreteOrdinary.coefficient A) U
    ((CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) v).obj
      ((p.extension (FiniteDiscreteOrdinary.coefficient A)).obj (image f))) G eG
  have hd := torsion_cd_proAffineEtale d hcd v hv
  have hq0 : 0 ≤ q := by omega
  have hdq : d < q.toNat := by omega
  have : Subsingleton ((Etale.cohomology Ab.{u + 1} U q.toNat).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) := hd G hG q.toNat hdq
  have hz : IsZero ((Etale.cohomology Ab.{u + 1} U q.toNat).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance
  have heq : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
  rw [heq] at hz
  exact hz.of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} q).mapIso e)


/-- Exact coefficient triangles propagate a fixed cohomology-degree bound from
reduction modulo pi to reduction modulo every positive power of pi. This applies
to arbitrary complexes, without a completeness or flatness assumption. -/
private theorem integral_reduction_cohomology_of_first
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (U : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules ℓ E U)) (q : ℤ)
    (hfirst : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((condensedModuleSections (DerivedNakayama.integerRing ℓ E) U).rightDerivedFunctor.obj
        ((AdicCompletion.restrict ℓ E U 0).obj
          ((AdicCompletion.derivedReduction ℓ E U 0).obj K))))) (n : ℕ) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((condensedModuleSections (DerivedNakayama.integerRing ℓ E) U).rightDerivedFunctor.obj
        ((AdicCompletion.restrict ℓ E U n).obj
          ((AdicCompletion.derivedReduction ℓ E U n).obj K)))) := by
  obtain ⟨e, _⟩ := PrincipalNormalization.principal_tensor_scalar_extension ℓ E U
  obtain ⟨d, hd, r, hr, i, t, hi, ht, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution ℓ E
  let H := (condensedModuleSections (DerivedNakayama.integerRing ℓ E) U).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor Ab.{u + 1} q
  have h₀ : IsZero (H.obj ((DerivedNakayama.reductionFunctor ℓ E U 1).obj K)) :=
    hfirst.of_iso (H.mapIso ((e 0).app K))
  have hlevels (m : ℕ) :
      IsZero (H.obj ((DerivedNakayama.reductionFunctor ℓ E U (m + 1)).obj K)) := by
    induction m with
    | zero => exact h₀
    | succ m hm =>
      obtain ⟨δ, hT⟩ := (hres U (m + 1) (by omega)).2.2 1 (by omega) (by omega) K
      exact (H.map_distinguished_exact _ hT).isZero_of_both_zeros
        (h₀.eq_of_src _ _) (hm.eq_of_tgt _ _)
  exact (hlevels n).of_iso (H.mapIso ((e n).app K).symm)

/-- Both vanishing assertions use the actual abelian image of an arbitrary map.
Source: Hemo--Richarz--Scholbach, Section 8, proof of Lemma 8.6, torsion paragraph;
the integral reduction assertion is the agent obligation with exact reference WANTED.
(blueprint: lem-sfb-supported-image-torsion-reductions-cd).

Proof status:

1. The finite assertion is reduced in the separate theorem
   `supported_finite_image_cohomology_vanishes` to classical origin and derived
   evaluation comparison. Its affine-limit dimension step and the assembly are proved.
   The supporting statements are `supported_finite_image_classical_origin` and
   `classical_internal_module_sections`. They concern degree-zero finite coefficients
   and scalar forgetting, respectively; neither repeats the integral assertion.
2. The previous integral proof uses `supported_image_koszul_comparison_nonpositive`
   on S. That lemma now requires `[CompactSpace S] [IsLocallyNoetherian S]`. This
   theorem has no Noetherianity hypothesis. The unrestricted local lemma was refuted
   in coord/reports/Q09/lem-sfb-supported-image-koszul-comparison-nonpositive.md.
   Consequently the previous step 5, and its ensuing two-row spectral sequence,
   do not prove this integral assertion. In particular, applying classical comparison
   directly to the actual integral image or its reductions would be unjustified.
3. The original global statement is retained for re-review. No counterexample to
   its global vanishing conclusion is claimed. HRS Lemma 8.6 treats the hearts of
   constructible complexes under its geometric hypotheses; it does not assert the
   unrestricted local prerequisite used by the earlier proof.
4. The current proof isolates only the first-power global estimate in
   `supported_image_first_reduction_cohomology_vanishes`. The canonical tensor/scalar
   comparison and coefficient triangles prove the passage from that case to every
   higher power by induction, using exactness of degree-q derived sections. This
   replaces the invalid unrestricted local comparison application; the remaining
   first-power assertion carries the inherited dispute and has not been proved.
5. The finite argument includes empty support paths, empty schemes, the zero ring,
   zero images and d=0. No new nonzero hypothesis or geometric hypothesis is added.
-/
-- STATEMENT-DISPUTED: the first-power integral bound still requires re-review.
-- The current proof uses its named obligation and coefficient-power induction;
-- it does not apply the refuted unrestricted local comparison assertion.
-- No counterexample to global integral vanishing is claimed.
theorem supported_image_torsion_reductions_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (_hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    {S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (U : Scheme.{u}) (v : U ⟶ X) (_hv : proAffineEtale v) :
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [DiscreteTopology A] [Finite A],
      (∃ a : ℕ, ∀ x : A, (ℓ ^ a) • x = 0) →
      ∀ (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) S))
        (f : L ⟶ M),
        HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) S L →
        HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) S M →
        ∀ q : ℤ, (d : ℤ) < q →
          IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
            ((condensedModuleSections
              (FiniteDiscreteOrdinary.coefficient A) U).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) v).obj
                  ((p.extension (FiniteDiscreteOrdinary.coefficient A)).obj (image f))))))) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
        (L M : AdicCompletion.Modules ℓ E S) (f : L ⟶ M),
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S L →
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S M →
      ∀ (n : ℕ) (q : ℤ), (d : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((condensedModuleSections (DerivedNakayama.integerRing ℓ E) U).rightDerivedFunctor.obj
            ((AdicCompletion.restrict ℓ E U n).obj
              ((AdicCompletion.derivedReduction ℓ E U n).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  ((CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E) v).obj
                    ((p.extension (DerivedNakayama.integerRing ℓ E)).obj (image f))))))))) := by
  constructor
  · intro A _ _ _ _ _ _ L M f hL hM q hq
    exact supported_finite_image_cohomology_vanishes X d _hcd tree p U v _hv A L M f hL hM q hq
  · intro E _ _ _ L M f hL hM n q hq
    apply integral_reduction_cohomology_of_first ℓ E U _ q ?_ n
    exact supported_image_first_reduction_cohomology_vanishes
      ℓ X d _hcd tree p U v _hv E L M f hL hM q hq

end AlgebraicGeometry.ProEtale
