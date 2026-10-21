/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.CompactProjectionExchange

import Sheaf.AlgebraicGeometry.VectorIntegrationMate
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-!
# Vector-bundle purity before smooth orientation

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-amb-vector-bundle-purity`; expanded statement and nine-step proof in its DAG node
(blueprint: thm-amb-vector-bundle-purity).

The compactification, coefficient, trace, tensor projection map and adjunction are the
published constructions. The inverse projection is specified by its inverse, rather than
by an arbitrary isomorphism. The site comparison is used only on the bounded coefficient;
the purity assertion quantifies over every object of the ordinary unbounded category.

## Main definitions and statement

- `vectorBundlePurityCompactification`, `vectorBundlePurityLower`: the existing supports.
- `vectorBundlePurityAdjunction`: the existing ordinary ambient adjunction.
- `vectorBundlePurityTwistedPullback`, `vectorBundlePurityProjectionMap`: the actual arrows.
- `VectorBundlePurityAtModulus`: the normalization, bounded realization and purity clauses.
- `vectorBundlePurity`: finite Tate descent and purity with the prescribed coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance high] SymmetricCategory.toBraidedCategory

namespace AlgebraicGeometry.Etale

/-- The same chosen compactification as in vectorIntegrationSource. Its existence follows
from the already recorded bundle geometry and Nagata; it is not a hypothesis on the bundle.
Source: blueprint vector-bundle purity, proof step 2
(blueprint: thm-amb-vector-bundle-purity). -/
def vectorBundlePurityCompactification (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    Compactification (VectorBundleZeroSection.π S d M) :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).2.1
  HasCompactification.compactification (VectorBundleZeroSection.π S d M)

/-- The recorded ordinary unbounded compact-support functor for the bundle, computed with
exactly the compactification used by its named integration map.
Source: blueprint vector-bundle purity, displayed integration counit
(blueprint: thm-amb-vector-bundle-purity). -/
def vectorBundlePurityLower (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (vectorBundlePurityCompactification S d M)

/-- The canonical ordinary compact-support adjunction, on the whole derived categories.
This reuses rightDerivedUpperShriek and its specified adjunction, with finite coefficients.
Source: blueprint vector-bundle purity, proof steps 2 and 4
(blueprint: thm-amb-vector-bundle-purity). -/
def vectorBundlePurityAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).2.1
  rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d M)

/-- The object pi^*K(d)[2d], with the prescribed ordered tensor of shifted finite Tate
lines used by the integration definition. Pullback is the recorded exact inverse image.
Source: blueprint vector-bundle purity, displayed source of gamma
(blueprint: thm-amb-vector-bundle-purity). -/
def vectorBundlePurityTwistedPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :=
  ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).obj
    ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d M)).obj K)).obj
      (vectorIntegrationCoefficient A N hA S d M)

/-- The actual compactified tensor projection map, with K first. The middle map is
proper projection followed by the inverse open-extension tensor comparison. Both outer
maps are the canonical signed tensor symmetries, as in the recorded proper formula.
Source: Stacks Tag 0GL1 and Tag 0GL5; blueprint vector-bundle purity, proof step 4
(blueprint: thm-amb-vector-bundle-purity). -/
def vectorBundlePurityProjectionMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (vectorIntegrationSource A N hA S d M) ⟶
      (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M K) :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).2.1
  compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
    (vectorIntegrationCoefficient A N hA S d M)

/-- The clauses at one annihilating, invertible modulus. The local normalization refers
to the unique already defined integration map. A D+ representative is required only for
its coefficient. For every such representative the unique pro-etale realization is fixed
by the actual proper/open site comparison and the image of that same trace. Thus it is
not an unrelated pro-etale map or an unbounded site-comparison assertion.
The inverse projection p is characterized by p.inv = the specified projection map;
there is no new assumption on K, and its adjunct is the actual integration mate.
Source: blueprint vector-bundle purity, statement and proof steps 3--4
(blueprint: thm-amb-vector-bundle-purity). -/
def VectorBundlePurityAtModulus (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] : Prop :=
  VectorIntegrationNormalization N hN A hA S hS d M
      (vectorBundleIntegration N hN A hA S hS d M) ∧
  DerivedCategory.TStructure.t.bounded (vectorIntegrationCoefficient A N hA S d M) ∧
  (∃ C : DerivedCategory.Plus
      (Sheaf (VectorBundleZeroSection.scheme S d M).smallEtaleTopology (ModuleCat.{u + 1} A)),
    Nonempty (DerivedCategory.Plus.ι.obj C ≅ vectorIntegrationCoefficient A N hA S d M)) ∧
  (∀ (C : DerivedCategory.Plus
      (Sheaf (VectorBundleZeroSection.scheme S d M).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a : DerivedCategory.Plus.ι.obj C ≅ vectorIntegrationCoefficient A N hA S d M),
    ∃! t :
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (vectorBundlePurityCompactification S d M)).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
            (VectorBundleZeroSection.scheme S d M)).mapDerivedCategory.obj
              (vectorIntegrationCoefficient A N hA S d M)) ⟶
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj
          (ordinaryFiniteUnit A S),
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (vectorBundlePurityCompactification S d M)).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
            (VectorBundleZeroSection.scheme S d M)).mapDerivedCategory.map a.hom) ≫ t =
        (ProEtale.compactSupportSiteComparison A
          (vectorBundlePurityCompactification S d M)).hom.app C ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
          ((vectorBundlePurityLower A S d M).map a.hom ≫
            vectorBundleIntegration N hN A hA S hS d M)) ∧
  (∀ K : DerivedCategoryModule A S,
    ∃ p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M K) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (vectorIntegrationSource A N hA S d M),
      p.inv = vectorBundlePurityProjectionMap A N hA S d M K ∧
      IsIso ((vectorBundlePurityAdjunction A S d M).homEquiv _ K
        (p.hom ≫ ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
          (vectorBundleIntegration N hN A hA S hS d M) ≫
            (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom)))

/-- Positive-level finiteness, reused through the existing sheaf-universe lift.
Source: finite-coefficient notation and def-weil-l-adic-coefficient-extension, clause 4
(blueprint: thm-amb-vector-bundle-purity). -/
instance vectorBundlePurityFiniteCoefficient (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]
    (n : ℕ) : Finite (Scheme.finiteTateCoefficient ell F n) :=
  letI := Padic.finite_coefficientExtensionRing ell F (n + 1) (Nat.le_add_left 1 n)
  inferInstance

/-- Invertibility of a positive power is transported along the canonical natural-number
cast equality. This supplies a consequence of ell invertible, not an extra hypothesis.
Source: blueprint vector-bundle purity, proof step 1
(blueprint: thm-amb-vector-bundle-purity). -/
theorem vectorBundlePurityInvertiblePower (ell : ℕ) (S : Scheme.{u})
    (hS : IsUnit (ell : Γ(S, ⊤))) (r : ℕ) :
    IsUnit ((ell ^ (r + 1) : ℕ) : Γ(S, ⊤)) :=
  by
    simpa only [Nat.cast_pow] using hS.pow (r + 1)

private theorem existsUnique_postcompose {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : X ⟶ Z) : ∃! t : Y ⟶ Z, a.hom ≫ t = b := by
  refine ⟨a.inv ≫ b, by simp, ?_⟩
  intro t ht
  apply (cancel_epi a.hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ht

private theorem baseCoefficient_bounded (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    _root_.DerivedCategory.TStructure.t.bounded (affineLinearBaseCoefficient A N hA S d) := by
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateTwist S N A hA 1) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line S N hN
      (fun x ↦ by
        simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom) A hA 1).2.2.1
  have ht := _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat
  have hshift := DerivedCategory.torAmplitudeIn.shift ht (2 : ℤ)
  induction d with
  | zero =>
    change _root_.DerivedCategory.TStructure.t.bounded (ordinaryFiniteUnit A S)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  | succ d ih =>
    exact bounded_derivedTensor_of_finiteTorAmplitude (ModuleCat.{u + 1} A) S ih
      ⟨_, _, hshift⟩

private theorem coefficient_annihilator (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]
    (n : ℕ) : ((ell ^ (n + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0 := by
  let O := Padic.coefficientExtensionIntegers ell F
  let m := Padic.coefficientExtensionMaximalIdeal ell F
  have hs := (Padic.extension_integers_dvr ell F
    (Padic.coefficientExtensionAbsoluteValue ell F)
    (spectralNorm_extends (K := Padic ell) (L := F))).choose_spec.choose_spec
  have hm : (ell : O) ∈ m := by
    apply (hs.2.1 (ell : O)).2
    have he := spectralNorm_extends (K := Padic ell) (L := F) (ell : Padic ell)
    change spectralNorm (Padic ell) F (ell : F) < 1
    simpa only [map_natCast] using he.trans_lt (Padic.norm_p_lt_one (p := ell))
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer ell F} : Set O) = m := by
    exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply ULift.down_injective
  change ((ell ^ (n + 1) : ℕ) : Padic.coefficientExtensionRing ell F (n + 1)) = 0
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell F (n + 1))),
    Ideal.Quotient.eq_zero_iff_mem]
  change ((ell ^ (n + 1) : ℕ) : O) ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer ell F} : Set O) ^ (n + 1)
  rw [hg, Nat.cast_pow]
  exact Ideal.pow_mem_pow hm (n + 1)

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true
private theorem purityAtModulus (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundlePurityAtModulus N hN A hA S hS d M := by
  dsimp only [VectorBundlePurityAtModulus]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (existsUnique_vectorIntegrationGluing _ _ _ _ _ _ _ _).2.exists.choose_spec.2
  · apply (_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _
        (VectorBundleZeroSection.π S d M)).app _).symm
    exact Functor.bounded_mapDerivedCategory_obj _
      (baseCoefficient_bounded _ _ (hN) _ S
        (hS) d)
  · let B := vectorIntegrationCoefficient _ _ (hA) S d M
    have hb : _root_.DerivedCategory.TStructure.t.bounded B := by
      apply (_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory _
          (VectorBundleZeroSection.π S d M)).app _).symm
      exact Functor.bounded_mapDerivedCategory_obj _
        (baseCoefficient_bounded _ _ (hN) _ S
          (hS) d)
    exact ⟨⟨B, hb.1⟩, ⟨Iso.refl _⟩⟩
  · intro C a
    let P := ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (A))
      (vectorBundlePurityCompactification S d M)
    let Q := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (A))
      (VectorBundleZeroSection.scheme S d M)).mapDerivedCategory
    exact existsUnique_postcompose (P.mapIso (Q.mapIso a))
      ((ProEtale.compactSupportSiteComparison _
        (vectorBundlePurityCompactification S d M)).hom.app C ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (A)) S).mapDerivedCategory.map
          ((vectorBundlePurityLower _ S d M).map a.hom ≫
            vectorBundleIntegration _ (hN) _ _ S
              (hS) d M))
  · intro K
    let : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    let : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    have hp : IsIso (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
        (vectorIntegrationCoefficient A N hA S d M)) := by
      have := isIso_projectionMap_of_finite A (VectorBundleZeroSection.π S d M)
      have hcomponent : IsIso (((projectionMap (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.π S d M)).app
            (vectorIntegrationCoefficient A N hA S d M)).app K) := inferInstance
      unfold compactProjectionMapCoeffFirst
      refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' hcomponent ?_)
      · exact (((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).app K).app
          (vectorIntegrationSource A N hA S d M)).isIso_hom
      · exact Functor.map_isIso _
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A)
            (VectorBundleZeroSection.scheme S d M)).app
              (vectorIntegrationCoefficient A N hA S d M)).app
                ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d M)).obj K)).hom
    have hq : IsIso (vectorBundlePurityProjectionMap A N hA S d M K) := hp
    refine ⟨(asIso (vectorBundlePurityProjectionMap A (N)
      (hA) S d M K)).symm, rfl, ?_⟩
    simp only [Iso.symm_hom, asIso_inv]
    dsimp only [vectorBundlePurityAdjunction, vectorBundlePurityTwistedPullback]
    exact vectorIntegrationMate_isIso (N) (hN) A
      (hA) S (hS) d M K

/-- Vector-bundle purity for the actual integration mate on ordinary unbounded
etale derived categories. The positive level is indexed by its predecessor n.
Finite Tate descent is specified on all S-schemes, all nonnegative powers,
every annihilating positive ell-power, and its normalized exponent transitions.
The annihilator needed by the displayed coefficient is a conclusion, not an assumption.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an, order 1973;
the current DAG statement and proof (blueprint: thm-amb-vector-bundle-purity).

Proof:
1. Since $ellin(varpi_F)$, we have $ell^nA=0$; take $m=ell^n$. Apply [lem-amb-finite-tate-site-
   descent] to every $S$-scheme $T$. It identifies the finite-level pro-etale twist with the
   inverse image of $mu_{m,T}^{mathrm{et}}otimes_{mathbf Z/m}A_T$, canonically independently of
   $m$ and compatibly with tensor powers and pullbacks. These are exactly the coefficient
   identifications in the statement; no freeness of $A$ over $mathbf Z/m$ is used.
   Uses: lem-amb-finite-tate-site-descent.
2. Apply [lem-amb-vector-projective-completion] to $E/S$. It gives the compactification
   $Exrightarrow{j}overline Exrightarrow{r}S$, with $overline
   E=operatorname{Proj}_Soperatorname{Sym}(mathcal O_Soplusmathcal E)$, and verifies
   Noetherianity, finite type and separatedness, including rank zero. Thus [thm-amb-etale-
   exceptional-adjoint] supplies the actual ambient right adjoint $pi^times$ for the compact-
   support functor used below.
   Uses: lem-amb-vector-projective-completion, thm-amb-etale-exceptional-adjoint.
3. Put $B_pi=Rpi_!A_E(d)[2d]$ in the ordinary etale category. The construction in [def-amb-
   vector-integration] identifies $B_pi$ with $mathcal H^0(B_pi)[0]$ and specifies $t_pi$
   uniquely by its restrictions to trivializing opens. Each restriction is the actual affine-
   space trace, an isomorphism by [lem-amb-affine-space-top-trace]. Hence the sheaf map $mathcal
   H^0(t_pi)$ is an isomorphism by [lem-weil-pbc-etale-cover-detects-iso], applied to the
   underlying abelian sheaves. Both complexes have only degree-zero cohomology, so [lem-weil-
   pbc-unbounded-derived-iso-cohomology] gives that $t_pi$ is an isomorphism.
   For the pro-etale realization, the input $A_E(d)[2d]$ is bounded below. Apply [lem-amb-
   compact-support-site-comparison-open] to Step 2's compactification and this input. Its
   specified comparison commutes with open restriction; Step 1 identifies the coefficients. On
   every trivializing open the pulled-back trace is the same prescribed normalized affine trace.
   Maps between degree-zero objects are sheaf maps by [lem-weil-pbc-derived-single-fully-
   faithful]; the sheaf axiom therefore identifies their global gluings. This identifies the
   actual named trace on this bounded coefficient input, without asserting an unbounded pro-
   etale comparison.
   Uses: def-amb-vector-integration, lem-amb-affine-space-top-trace, lem-weil-pbc-etale-cover-
     detects-iso, lem-weil-pbc-unbounded-derived-iso-cohomology, lem-amb-compact-support-site-
     comparison-open, lem-weil-pbc-derived-single-fully-faithful.
4. We spell out the extension-by-zero tensor calculation on the ordinary etale site. For the
   open immersion $j:Ehookrightarrowoverline E$ of Step 2, $E$ is an object of $overline
   E_{mathrm{et}}$ and the slice site is $E_{mathrm{et}}$. This $j$ is quasi-compact: its
   intersection with any affine open of the Noetherian target is a Noetherian open subscheme,
   hence quasi-compact [lem-weil-pbc-noetherian-open-subscheme-noetherian]. It is therefore
   finite type [lem-weil-pbc-qc-open-immersion-finite-type], as required for the extension
   adjunction used below. The tensor calculation itself applies to any open immersion. For
   sheaves the natural tensor identity is [lem-weil-pbc-ringed-slice-extension-tensor], applied
   to the constant ring $A_X$. Choose a K-flat resolution $P$ with flat terms of $Min
   D(X_{mathrm{et}},A)$. By [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and [prop-weil-
   pbc-inverse-image-modules-exact], $j^*P$ is a K-flat resolution of $j^*M$. Apply the sheaf
   identity in every total-tensor degree; direct sums commute with $j_!$ because it is a left
   adjoint [lem-amb-etale-adjoint-locality]. Exactness [lem-weil-pbc-extension-by-zero-exact]
   allows this equality to descend through quasi-isomorphisms. It gives $Motimes_A^L Dj_!Lcong
   Dj_!(j^*Motimes_A^LL)$, naturally in arbitrary unbounded $M,L$. Now [thm-amb-etale-
   exceptional-adjoint] gives $pi^times$ for Step 2's compactification. Apply [lem-amb-proper-
   coproducts-projection] to $r$, $K$, and $Dj_!A_E(d)[2d]$; the tensor identity just proved
   changes its target to $Rpi_!(pi^*K(d)[2d])$. Invert this projection map and follow by
   $1otimes t_pi$, with the actual $t_pi$ identified in Step 3 and prescribed by [def-amb-
   vector-integration]. This constructs a global morphism $c_{pi,K}$ and its adjoint
   $gamma_{pi,K}$.
   Uses: lem-weil-pbc-ringed-slice-extension-tensor, lem-weil-pbc-ringed-topoi-derived-tensor-
     pullback, prop-weil-pbc-inverse-image-modules-exact, lem-amb-etale-adjoint-locality, lem-
     weil-pbc-extension-by-zero-exact, thm-amb-etale-exceptional-adjoint, lem-amb-proper-
     coproducts-projection, def-amb-vector-integration, lem-weil-pbc-noetherian-open-subscheme-
     noetherian, lem-weil-pbc-qc-open-immersion-finite-type.
5. For the affine line $p:mathbf A^1_Tto T$, put $q:mathbf P^1_Tto T$ and let $a:mathbf
   A^1_Thookrightarrowmathbf P^1_T$. The normalized whole-derived-category adjunction $Rq_*dashv
   q^*(1)[2]$ of [lem-asd-ordinary-finite-p1-adjunction] has counit $epsilon_{q,L}=(1_Lotimes
   t_q)pi_q^{-1}$. Compose it with $Da_!dashv a^*$ from [lem-amb-etale-adjoint-locality]. Since
   $Rp_!=Rq_*Da_!$ by [def-amb-etale-compact-support], this constructs $Rp_!dashv p^*(1)[2]$.
   Its counit is $epsilon_{q,L}circ Rq_*(Da_!a^*q^*L(1)[2]to q^*L(1)[2])$. Step 4's tensor
   identification turns the map inside $Rq_*$ into $1_{q^*L}otimes(Da_!a^*A_{mathbf
   P^1_T}(1)[2]to A_{mathbf P^1_T}(1)[2])$. Naturality of the canonical proper projection map
   therefore rewrites this counit as $(1_Lotimes t_p)pi_p^{-1}$, where $t_p$ is its value at
   $L=A_T$. The current statement of [lem-amb-affine-space-top-trace] specifies its rank-one
   adjunction to be exactly this composite of open extension with [lem-asd-ordinary-
   finite-p1-adjunction], so its trace is this actual counit at $A_T$. Step 1 identifies this
   coefficient twist with the finite-level twist of the original integration definition. The
   twist restriction and the identification of $a^*q^*L(1)[2]$ with $p^*L(1)[2]$ use [lem-asd-
   etale-finite-twist-pullback].
   Uses: lem-asd-ordinary-finite-p1-adjunction, lem-amb-etale-adjoint-locality, def-amb-etale-
     compact-support, lem-amb-affine-space-top-trace, lem-asd-etale-finite-twist-pullback.
6. Induct on $e$, with $p_0=1_T$ and identity counit. Step 5 gives the affine-line adjunction
   and its integration counit. Write $p_{e+1}=p_eh$ with $h:mathbf A^1_{mathbf A^e_T}tomathbf
   A^e_T$. The comparison of [lem-amb-unbounded-compact-support-comparisons] identifies
   $Rp_{e+1,!}$ with $Rp_{e!}Rh_!$. Compose the adjunctions using [def-weil-pbc-composite-
   adjunction]. The right adjoint becomes $h^*(1)[2]p_e^*(e)[2e]=p_{e+1}^*(e+1)[2e+2]$ by [lem-
   asd-etale-finite-twist-pullback]. Its counit at $L$ is $epsilon_{p_e,L}circ
   Rp_{e!}(epsilon_{h,p_e^*L(e)[2e]})$.
   Substitute the two integration-counit formulas. The composition identity in [lem-amb-shriek-
   tensor-composition] combines their projection maps, including the proper/open interchange.
   The resulting counit is $(1_Lotimes t_{p_{e+1}})mathrm{PF}_{p_{e+1},L}^{-1}$. To identify its
   trace, evaluate the ordered composite counit at $A_T$: this is the definition in [lem-amb-
   affine-space-top-trace]. Each intermediate coefficient value is a shifted Tate sheaf by that
   node's trace isomorphism and Step 4's projection formula, hence bounded below. The bounded-
   below agreement in [lem-amb-unbounded-compact-support-comparisons] identifies precisely the
   two composition maps on these values. Thus this is the specified actual trace.
   The adjunct of this counit under any chosen right adjoint is an isomorphism: the two
   adjunction Hom bijections give mutually inverse comparisons by applying each to the other's
   counit. Therefore the normalized affine-space comparison is invertible for every unbounded
   $L$.
   Uses: lem-amb-unbounded-compact-support-comparisons, def-weil-pbc-composite-adjunction, lem-
     asd-etale-finite-twist-pullback, lem-amb-shriek-tensor-composition, lem-amb-affine-space-top-
     trace.
7. Choose an affine Zariski cover $u:Uhookrightarrow S$ trivializing $mathcal E$, and put
   $v:E_Uhookrightarrow E$, $pi_U:E_Uto U$. The opens $U$ and $E_U$ are Noetherian by [lem-weil-
   pbc-noetherian-open-subscheme-noetherian]. Applying the same statement to their intersections
   with affine opens of their targets shows that $u,v$ are quasi-compact; hence they are of
   finite type by [lem-weil-pbc-qc-open-immersion-finite-type]. An open immersion is locally an
   identity map, so is etale; its diagonal is an isomorphism, hence it is separated. For
   arbitrary $Min D(E_U,A)$, the composition isomorphisms of [lem-amb-unbounded-compact-support-
   comparisons], the equality $pi v=upi_U$, and the normalization [lem-asd-etale-compact-
   support-normalization] for $u,v$ give $$Rpi_!Dv_!Mcong R(pi v)_!M=R(upi_U)_!Mcong
   Du_!Rpi_{U!}M.$$ Apply the exact etale-extension adjunctions of [lem-amb-etale-adjoint-
   locality], the global adjunction, and the adjunction for $pi_U$ from [thm-amb-etale-
   exceptional-adjoint]. Their Hom bijections give, naturally in $M$,
   $$operatorname{Hom}_{E_U}(M,v^*pi^times K)congoperatorname{Hom}_{S}(Rpi_!Dv_!M,K)congoperator
   name{Hom}_{U}(Rpi_{U!}M,u^*K)congoperatorname{Hom}_{E_U}(M,pi_U^times u^*K).$$ Take the
   images of the two identity maps to obtain inverse maps between the represented objects;
   naturality makes both composites identities. This supplies the canonical isomorphism
   $beta_K:v^*pi^times Kcongpi_U^times u^*K$. In particular we have derived base restriction
   using both extension adjunctions and compact-support composition; we have not applied the
   domain-only locality lemma as if it asserted base restriction.
   Uses: lem-amb-unbounded-compact-support-comparisons, lem-asd-etale-compact-support-
     normalization, lem-amb-etale-adjoint-locality, thm-amb-etale-exceptional-adjoint, lem-weil-
     pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-qc-open-immersion-finite-type.
8. Use the canonical exchange $C:u^*Rpi_!xrightarrow{sim}Rpi_{U!}v^*$ of [lem-amb-unbounded-
   compact-support-comparisons]. The twist pullback formulas of [lem-asd-etale-finite-twist-
   pullback] identify $v^*(pi^*K(d)[2d])$ with $pi_U^*(u^*K)(d)[2d]$. By [def-amb-vector-
   integration] and Step 3, $u^*t_pi=t_{pi_U}$ under this coefficient exchange. Apply [lem-amb-
   shriek-projection-open-restriction] to $f=pi$, $M=A_E(d)[2d]$ and $K$. It identifies the
   actual projection maps and their inverses after restriction. Consequently the restricted
   integration counit $u^*c_{pi,K}$ is $c_{pi_U,u^*K}$ under $C$.
   The Hom chain of Step 7 uses the extension/composition comparison
   $delta:Rpi_!Dv_!xrightarrow{sim}Du_!Rpi_{U!}$. By [lem-amb-shriek-open-exchange-adjoint], its
   pairing with the evaluation counits has adjunct exactly $C^{-1}$. Thus taking adjuncts of the
   preceding equality uses the same exchange as that Hom chain and yields $$beta_Kcirc
   v^*gamma_{pi,K}=gamma_{pi_U,u^*K}.$$ Indeed both sides transpose to the same restricted
   integration counit through these adjunction bijections. On the chosen trivialization
   $E_U=mathbf A^d_U$, Step 6 proves the right side invertible. Step 7 makes $beta_K$ an
   isomorphism, so $v^*gamma_{pi,K}$ is an isomorphism on each such open.
   Uses: lem-amb-unbounded-compact-support-comparisons, lem-asd-etale-finite-twist-pullback, def-
     amb-vector-integration, lem-amb-shriek-projection-open-restriction, lem-amb-shriek-open-
     exchange-adjoint.
9. For every integer $n$, exact inverse image [prop-weil-pbc-inverse-image-modules-exact]
   commutes with $ker d/operatorname{im}d$, so it identifies $v^*mathcal H^n(gamma_{pi,K})$ with
   $mathcal H^n(v^*gamma_{pi,K})$. By Step 8 this is an isomorphism on each member $E_U$ of an
   open cover of $E$. Every geometric point of $E$ lies in one of these opens; its stalk is the
   same stalk computed there. Thus [lemma-weil-pbc-geometric-stalk-conservative] makes every
   $mathcal H^n(gamma_{pi,K})$ an isomorphism. The unbounded cohomology criterion [lem-weil-pbc-
   unbounded-derived-iso-cohomology], applied to the abelian category of etale $A$-module
   sheaves, now proves that $gamma_{pi,K}$ itself is an isomorphism. No gluing or equality
   detection for arbitrary derived morphisms is asserted: the global mate was constructed in
   Step 4, its local equality was proved by adjunction in Step 8, and only its isomorphy is
   detected locally.
   Uses: prop-weil-pbc-inverse-image-modules-exact, lemma-weil-pbc-geometric-stalk-conservative,
     lem-weil-pbc-unbounded-derived-iso-cohomology.
-/
theorem vectorBundlePurity (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]
    (n : ℕ) (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (ell : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    (∃ b : ∀ (T : Scheme.{u}) (_f : T ⟶ S) (r : ℕ)
        (hA : ((ell ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0) (k : ℕ),
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient ell F n)) T).obj
            (Scheme.finiteEtaleTateTwist T (ell ^ (r + 1)) _ hA k) ≅
              Scheme.finiteTateProSheaf ell F n T k,
      (∀ (T : Scheme.{u}) (f : T ⟶ S) (r : ℕ)
        (hA : ((ell ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0) (k : ℕ),
        Scheme.IsFiniteTateSiteComparison ell F n T r hA k (b T f r hA k)) ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S) (r r' : ℕ) (_h : r ≤ r')
        (hA : ((ell ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0)
        (hA' : ((ell ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0) (k : ℕ),
        ∃! t : Scheme.finiteEtaleTateTwist T (ell ^ (r' + 1)) _ hA' k ≅
            Scheme.finiteEtaleTateTwist T (ell ^ (r + 1)) _ hA k,
          Scheme.IsFiniteTateEtaleTransition ell F n T r r' hA hA' k t ∧
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient ell F n)) T).mapIso t ≪≫
              b T f r hA k = b T f r' hA' k) ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S) (r : ℕ)
        (hA : ((ell ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0) (k : ℕ)
        (G : Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient ell F n)))
        (a : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient ell F n)) T).obj G ≅
            Scheme.finiteTateProSheaf ell F n T k),
        ∃! h : Scheme.finiteEtaleTateTwist T (ell ^ (r + 1)) _ hA k ≅ G,
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient ell F n)) T).mapIso h ≪≫ a =
              b T f r hA k)) ∧
    ∃ hA : ((ell ^ (n + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0,
      VectorBundlePurityAtModulus (ell ^ (n + 1))
        (Nat.pow_pos (Fact.out : ell.Prime).pos) (Scheme.finiteTateCoefficient ell F n) hA
        S (vectorBundlePurityInvertiblePower ell S hS n) d M := by
  constructor
  · obtain ⟨b, hb, hpb, ht, hu⟩ := Scheme.finite_tate_site_descent ell F n
    have hi (T : Scheme.{u}) (f : T ⟶ S) : IsUnit (ell : Γ(T, ⊤)) := by
      simpa only [map_natCast] using hS.map f.appTop.hom
    refine ⟨fun T f r hA k ↦ b T (hi T f) r hA k, ?_, ?_, ?_⟩
    · intro T f r hA k
      exact hb T (hi T f) r hA k
    · intro T f r r' h hA hA' k
      exact ht T (hi T f) r r' h hA hA' k
    · intro T f r hA k G a
      exact hu T (hi T f) r hA k G a
  · refine ⟨coefficient_annihilator ell F n, ?_⟩
    exact purityAtModulus (ell ^ (n + 1)) (Nat.pow_pos (Fact.out : ell.Prime).pos)
      _ (coefficient_annihilator ell F n) S (vectorBundlePurityInvertiblePower ell S hS n) d M


end AlgebraicGeometry.Etale
