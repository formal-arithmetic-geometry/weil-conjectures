/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

public import Mathlib.RingTheory.Kaehler.Basic

public import Mathlib.AlgebraicGeometry.Properties

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Mathlib.AlgebraicGeometry.Scheme

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.AdjoinRoot
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility

/-! # Cyclic root covers and their logarithmic differential blocks

Source: Popa, Kodaira dimension of algebraic varieties, Proposition 1.6.5,
Theorem 1.6.6 and Lemma 1.6.7, printed pages 24--27; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms)

The existence statement retains all the local normalizations. In particular the cover
is characterized by its root-algebra charts, the logarithmic module by its generators
and relations, and the cohomology comparisons by their canonical edge maps.
Finite sums are bilimit bicones; their cohomology is written as a finite product.

## Main definitions

* `CyclicRootCoverEigenformsData`: root charts, logarithmic presentation, eigensheaves,
  differential connections and canonically normalized cohomology comparisons.

## Main statements

* `cyclic_root_cover_eigenforms`: existence of the entire specified package.
The derivations and connections are maps of underlying abelian sheaves with explicit
base-field linearity, rather than morphisms of structure-sheaf modules.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The tensor power of a local section, with the same tensor convention as `tensorPow`.
Source: Popa Proposition 1.6.5 (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
noncomputable def cyclicRootSectionPower {Y : Scheme.{u}} {M : Y.Modules} {U : Y.Opens}
    (e : Γ(M, U)) : (a : ℕ) → Γ(M.tensorPow a, U)
  | 0 => unitSectionsEquiv U 1
  | a + 1 => tmulSection e (cyclicRootSectionPower e a)

/-- The inverse tensor powers in the root algebra, using the recorded internal-Hom dual.
Source: Popa Proposition 1.6.5 (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
noncomputable abbrev cyclicRootNegativePower {Y : Scheme.{u}} (L : Y.Modules) (a : ℕ) :=
  (Scheme.Modules.dual L).tensorPow a

/-- The positive characters, with their actual exponents in `Fin m`.
Source: Popa Proposition 1.6.5 (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
abbrev CyclicRootPositiveIndex (m : ℕ) := {a : Fin m // a.val ≠ 0}

/-- Character zero of the degree-m root cover.
Source: Popa Proposition 1.6.5 (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
abbrev cyclicRootZeroIndex (m : ℕ) (hm : 2 ≤ m) : Fin m :=
  ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hm⟩

/-- The invariant differential summand and all positive logarithmic summands.
Source: Popa Proposition 1.6.5 (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
noncomputable abbrev cyclicRootDifferentialSummand {F : Type u} [Field F]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of F)) (L log : Y.Modules) (m : ℕ) :
    Option (CyclicRootPositiveIndex m) → Y.Modules
  | none => p.relativeDifferentials
  | some a => log ⊗ cyclicRootNegativePower L a.val.val

/-- The ordinary pullback of relative one-forms into the direct image, fixed by `d`.
Source: Popa Proposition 1.6.5 (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
noncomputable def cyclicRootPullDifferentials {F : Type u} [Field F]
    {Y W : Scheme.{u}} (p : Y ⟶ Spec (.of F)) (f : W ⟶ Y) :
    p.relativeDifferentials ⟶ (pushforward f).obj (f ≫ p).relativeDifferentials :=
  (p.relativeDifferentialsHomEquiv _).symm (p.pushforwardDerivation f)

/-- The existing underlying-abelian cohomology, with the module coefficient visible.
Source: Stacks Tag 03FD (blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
noncomputable abbrev cyclicRootH {Y : Scheme.{u}} (M : Y.Modules) (q : ℕ) :=
  Sheaf.H ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) q

/-- The canonical finite-morphism edge map through the module/abelian comparison.
Source: Stacks Tags 01F7 and 03FD; Popa proof of Theorem 1.6.6.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
noncomputable def cyclicRootCohomologyEdge {Y W : Scheme.{u}} (f : W ⟶ Y)
    (M : W.Modules) (q : ℕ) : ((pushforward f).obj M).H q →+ M.H q :=
  (moduleCohomologyExtResolutionEquiv W M q).toAddMonoidHom.comp
    ((moduleCohomologyEdgeMap f M q).hom.comp
      (moduleCohomologyExtResolutionEquiv Y ((pushforward f).obj M) q).symm.toAddMonoidHom)

/-- Geometry and the structure-sheaf sum of the specified root cover.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootCoverGeometry
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m) where
  W : Scheme.{u}
  f : W ⟶ Y
  finiteLocallyFree : f.IsFiniteLocallyFreeOfDegree m
  affinePreimage : ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)
  smoothDimension : SmoothOfRelativeDimension n (f ≫ p)
  projective : IsProjective (f ≫ p)
  /-- The finite direct sum defining the root algebra, compared with its actual algebra. -/
  functions : Bicone (fun a : Fin m ↦ cyclicRootNegativePower L a.val)
  functionsBilimit : functions.IsBilimit
  functionsIso : functions.pt ≅ (pushforward f).obj (𝟙_ W.Modules)

/-- Generators, relation and residue of logarithmic one-forms.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootLogarithmicForms
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m) where
  /-- The logarithmic module has the local presentation Ω ⊕ O / (du,-u). -/
  log : Y.Modules
  regular : p.relativeDifferentials ⟶ log
  regularMono : Mono regular
  logGenerator : ∀ (U : Y.affineOpens) (v : Γ(Y, U.1)),
    s.zeroLocus.ideal U = Ideal.span {v} → Γ(log, U.1)
  logGenerated : ∀ (U : Y.affineOpens) (v : Γ(Y, U.1))
    (hv : s.zeroLocus.ideal U = Ideal.span {v}) (x : Γ(log, U.1)),
    ∃ (α : Γ(p.relativeDifferentials, U.1)) (b : Γ(Y, U.1)),
      x = regular.app U.1 α + b • logGenerator U v hv
  logRelations : ∀ (U : Y.affineOpens) (v : Γ(Y, U.1))
    (hv : s.zeroLocus.ideal U = Ideal.span {v})
    (α : Γ(p.relativeDifferentials, U.1)) (b : Γ(Y, U.1)),
    regular.app U.1 α + b • logGenerator U v hv = 0 ↔
      ∃ c : Γ(Y, U.1), b = c * v ∧ α = -(c • p.sectionsD U.1 v)
  emptyDivisor : s.zeroLocus.support = ⊥ → IsIso regular
  residue : log ⟶ (pushforward s.zeroLocus.subschemeι).obj
    (𝟙_ s.zeroLocus.subscheme.Modules)
  residueFormula : ∀ (U : Y.affineOpens) (v : Γ(Y, U.1))
    (hv : s.zeroLocus.ideal U = Ideal.span {v})
    (α : Γ(p.relativeDifferentials, U.1)) (b : Γ(Y, U.1)),
    residue.app U.1 (regular.app U.1 α + b • logGenerator U v hv) =
      unitSectionsEquiv (s.zeroLocus.subschemeι ⁻¹ᵁ U.1) (s.zeroLocus.subschemeι.app U.1 b)

/-- The differential eigensheaf sum, including its invariant normalization.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootFormDecomposition
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m)
    (cover : CyclicRootCoverGeometry F Y p L n m hm s)
    (logarithmic : CyclicRootLogarithmicForms F Y p L n m hm s) where
  forms : Bicone (cyclicRootDifferentialSummand p L logarithmic.log m)
  formsBilimit : forms.IsBilimit
  formsIso : forms.pt ≅ (pushforward cover.f).obj (cover.f ≫ p).relativeDifferentials
  invariantForms : forms.ι none ≫ formsIso.hom = cyclicRootPullDifferentials p cover.f

/-- The local root-algebra and logarithmic differential normalizations.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootChartComparisons
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m)
    (cover : CyclicRootCoverGeometry F Y p L n m hm s)
    (logarithmic : CyclicRootLogarithmicForms F Y p L n m hm s)
    (decomposition : CyclicRootFormDecomposition F Y p L n m hm s cover logarithmic) where
  /-- Each root chart is the specified monic quotient, compatibly with every summand. -/
  rootChart : ∀ (U : Y.affineOpens) (e : Γ(L, U.1)) (_he : IsFreeGenerator e)
    (v : Γ(Scheme.Modules.dual L, U.1)) (_hv : IsFreeGenerator v)
    (_hev : (dualEvaluation L).app U.1 (tmulSection e v) = unitSectionsEquiv U.1 1)
    (b : Γ(Y, U.1))
    (_hs : s.app U.1 (unitSectionsEquiv U.1 1) = b • cyclicRootSectionPower e m),
    ∃ θ : AdjoinRoot ((Polynomial.X : Polynomial Γ(Y, U.1)) ^ m - Polynomial.C b) ≃+*
        Γ(cover.W, cover.f ⁻¹ᵁ U.1),
      (∀ c : Γ(Y, U.1), θ (AdjoinRoot.of _ c) = cover.f.app U.1 c) ∧
      (∀ a : Fin m,
        (cover.functions.ι a ≫ cover.functionsIso.hom).app U.1 (cyclicRootSectionPower v a.val) =
          unitSectionsEquiv (cover.f ⁻¹ᵁ U.1) ((θ (AdjoinRoot.root _)) ^ a.val)) ∧
      ∀ (hb : s.zeroLocus.ideal U = Ideal.span {b}) (a : CyclicRootPositiveIndex m),
        (∀ α : Γ(p.relativeDifferentials, U.1),
          (decomposition.forms.ι (some a) ≫ decomposition.formsIso.hom).app U.1
              (tmulSection (logarithmic.regular.app U.1 α) (cyclicRootSectionPower v a.val.val)) =
            (θ (AdjoinRoot.root _)) ^ a.val.val •
              @id Γ((cover.f ≫ p).relativeDifferentials, cover.f ⁻¹ᵁ U.1)
                ((cyclicRootPullDifferentials p cover.f).app U.1 α)) ∧
        (decomposition.forms.ι (some a) ≫ decomposition.formsIso.hom).app U.1
            (tmulSection (logarithmic.logGenerator U b hb) (cyclicRootSectionPower v a.val.val)) =
          ((m : Γ(cover.W, cover.f ⁻¹ᵁ U.1)) * (θ (AdjoinRoot.root _)) ^ (a.val.val - 1)) •
            (cover.f ≫ p).sectionsD (cover.f ⁻¹ᵁ U.1) (θ (AdjoinRoot.root _))

/-- The root-of-unity actions, specified on all their character summands.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootCharacters
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m)
    (cover : CyclicRootCoverGeometry F Y p L n m hm s)
    (logarithmic : CyclicRootLogarithmicForms F Y p L n m hm s)
    (decomposition : CyclicRootFormDecomposition F Y p L n m hm s cover logarithmic) where
  functionAction : rootsOfUnity m F →* Aut ((pushforward cover.f).obj (𝟙_ cover.W.Modules))
  formAction : rootsOfUnity m F →*
    Aut ((pushforward cover.f).obj (cover.f ≫ p).relativeDifferentials)
  functionCharacters : ∀ (ζ : rootsOfUnity m F) (a : Fin m) (U : Y.Opens)
    (x : Γ(cyclicRootNegativePower L a.val, U)),
    ((functionAction ζ).hom.app U)
        ((cover.functions.ι a ≫ cover.functionsIso.hom).app U x) =
      p.specStructureMap U (((ζ.val : Fˣ) : F) ^ a.val) •
        (cover.functions.ι a ≫ cover.functionsIso.hom).app U x
  formCharacters : ∀ (ζ : rootsOfUnity m F) (a : CyclicRootPositiveIndex m) (U : Y.Opens)
    (x : Γ(logarithmic.log ⊗ cyclicRootNegativePower L a.val.val, U)),
    ((formAction ζ).hom.app U)
        ((decomposition.forms.ι (some a) ≫ decomposition.formsIso.hom).app U x) =
      p.specStructureMap U (((ζ.val : Fˣ) : F) ^ a.val.val) •
        (decomposition.forms.ι (some a) ≫ decomposition.formsIso.hom).app U x
  invariantCharacter : ∀ ζ : rootsOfUnity m F,
    decomposition.forms.ι none ≫ decomposition.formsIso.hom ≫ (formAction ζ).hom =
      decomposition.forms.ι none ≫ decomposition.formsIso.hom

/-- The actual universal differentials and their F-linear connection blocks.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootDifferentialBlocks
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m)
    (cover : CyclicRootCoverGeometry F Y p L n m hm s)
    (logarithmic : CyclicRootLogarithmicForms F Y p L n m hm s)
    (decomposition : CyclicRootFormDecomposition F Y p L n m hm s cover logarithmic) where
  /-- Universal derivations, specified on sections, in underlying abelian sheaves. -/
  dY : (SheafOfModules.toSheaf Y.ringCatSheaf).obj (𝟙_ Y.Modules) ⟶
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj p.relativeDifferentials
  dYFormula : ∀ (U : Y.Opens) (b : Γ(Y, U)),
    dY.hom.app (op U) (unitSectionsEquiv U b) = p.sectionsD U b
  dW : (SheafOfModules.toSheaf cover.W.ringCatSheaf).obj (𝟙_ cover.W.Modules) ⟶
    (SheafOfModules.toSheaf cover.W.ringCatSheaf).obj (cover.f ≫ p).relativeDifferentials
  dWFormula : ∀ (U : cover.W.Opens) (b : Γ(cover.W, U)),
    dW.hom.app (op U) (unitSectionsEquiv U b) = (cover.f ≫ p).sectionsD U b
  connection : ∀ a : CyclicRootPositiveIndex m,
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj (cyclicRootNegativePower L a.val.val) ⟶
      (SheafOfModules.toSheaf Y.ringCatSheaf).obj
        (logarithmic.log ⊗ cyclicRootNegativePower L a.val.val)
  connectionLinear : ∀ (a : CyclicRootPositiveIndex m) (U : Y.Opens) (c : F)
    (x : Γ(cyclicRootNegativePower L a.val.val, U)),
    (connection a).hom.app (op U) (p.specStructureMap U c • x) =
      p.specStructureMap U c •
        @id Γ(logarithmic.log ⊗ cyclicRootNegativePower L a.val.val, U)
          ((connection a).hom.app (op U) x)
  connectionFormula : ∀ (U : Y.affineOpens) (e : Γ(L, U.1)) (_he : IsFreeGenerator e)
    (v : Γ(Scheme.Modules.dual L, U.1)) (_hv : IsFreeGenerator v)
    (_hev : (dualEvaluation L).app U.1 (tmulSection e v) = unitSectionsEquiv U.1 1)
    (b : Γ(Y, U.1))
    (_hs : s.app U.1 (unitSectionsEquiv U.1 1) = b • cyclicRootSectionPower e m)
    (hb : s.zeroLocus.ideal U = Ideal.span {b})
    (a : CyclicRootPositiveIndex m) (c : Γ(Y, U.1)),
    (connection a).hom.app (op U.1) (c • cyclicRootSectionPower v a.val.val) =
      tmulSection
        (logarithmic.regular.app U.1 (p.sectionsD U.1 c) +
          (p.specStructureMap U.1 ((a.val.val : F) / (m : F)) * c) •
            logarithmic.logGenerator U b hb)
        (cyclicRootSectionPower v a.val.val)
  differentialBlock : ∀ (a : CyclicRootPositiveIndex m) (U : Y.Opens)
    (x : Γ(cyclicRootNegativePower L a.val.val, U)),
    dW.hom.app (op (cover.f ⁻¹ᵁ U))
        ((cover.functions.ι a.val ≫ cover.functionsIso.hom).app U x) =
      (decomposition.forms.ι (some a) ≫ decomposition.formsIso.hom).app U
        ((connection a).hom.app (op U) x)
  differentialInvariantBlock : ∀ (U : Y.Opens) (b : Γ(Y, U)),
    dW.hom.app (op (cover.f ⁻¹ᵁ U)) (unitSectionsEquiv (cover.f ⁻¹ᵁ U) (cover.f.app U b)) =
      (decomposition.forms.ι none ≫ decomposition.formsIso.hom).app U (p.sectionsD U b)

/-- Canonical finite-morphism cohomology comparisons and differential blocks.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
def CyclicRootCohomologyBlocks
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m)
    (cover : CyclicRootCoverGeometry F Y p L n m hm s)
    (logarithmic : CyclicRootLogarithmicForms F Y p L n m hm s)
    (decomposition : CyclicRootFormDecomposition F Y p L n m hm s cover logarithmic)
    (differentials : CyclicRootDifferentialBlocks F Y p L n m hm s cover logarithmic
      decomposition) : Prop :=
  ∃ (cf : ∀ q : ℕ, cyclicRootH (𝟙_ cover.W.Modules) q →
      (cyclicRootH (𝟙_ Y.Modules) q ×
        ((a : CyclicRootPositiveIndex m) →
          cyclicRootH (cyclicRootNegativePower L a.val.val) q)))
    (cw : ∀ q : ℕ, cyclicRootH (cover.f ≫ p).relativeDifferentials q →
      (cyclicRootH p.relativeDifferentials q ×
        ((a : CyclicRootPositiveIndex m) →
          cyclicRootH (logarithmic.log ⊗ cyclicRootNegativePower L a.val.val) q)))
    (i₀ : 𝟙_ Y.Modules ⟶ (pushforward cover.f).obj (𝟙_ cover.W.Modules)),
    i₀ = cover.functions.ι (cyclicRootZeroIndex m hm) ≫ cover.functionsIso.hom ∧
    (∀ q : ℕ, Function.Bijective (cf q)) ∧
    (∀ q : ℕ, Function.Bijective (cw q)) ∧
    (∀ (q : ℕ) (x y : cyclicRootH (𝟙_ cover.W.Modules) q),
      cf q (x + y) = cf q x + cf q y) ∧
    (∀ (q : ℕ) (x y : cyclicRootH (cover.f ≫ p).relativeDifferentials q),
      cw q (x + y) = cw q x + cw q y) ∧
    (∀ (q : ℕ) (x : cyclicRootH (𝟙_ Y.Modules) q ×
      ((a : CyclicRootPositiveIndex m) →
        cyclicRootH (cyclicRootNegativePower L a.val.val) q)),
      cf q
        (cyclicRootCohomologyEdge cover.f (𝟙_ cover.W.Modules) q
          (Scheme.Modules.H.map (M := 𝟙_ Y.Modules)
            (N := (pushforward cover.f).obj (𝟙_ cover.W.Modules)) i₀ q x.1) +
        ∑ a : CyclicRootPositiveIndex m,
          cyclicRootCohomologyEdge cover.f (𝟙_ cover.W.Modules) q
            (Scheme.Modules.H.map (M := cyclicRootNegativePower L a.val.val)
              (N := (pushforward cover.f).obj (𝟙_ cover.W.Modules))
              (cover.functions.ι a.val ≫ cover.functionsIso.hom) q (x.2 a))) = x) ∧
    (∀ (q : ℕ) (x : cyclicRootH p.relativeDifferentials q ×
      ((a : CyclicRootPositiveIndex m) →
        cyclicRootH (logarithmic.log ⊗ cyclicRootNegativePower L a.val.val) q)),
      cw q
        (cyclicRootCohomologyEdge cover.f (cover.f ≫ p).relativeDifferentials q
          (Scheme.Modules.H.map (M := p.relativeDifferentials)
            (N := (pushforward cover.f).obj (cover.f ≫ p).relativeDifferentials)
            (cyclicRootPullDifferentials p cover.f) q x.1) +
        ∑ a : CyclicRootPositiveIndex m,
          cyclicRootCohomologyEdge cover.f (cover.f ≫ p).relativeDifferentials q
            (Scheme.Modules.H.map
              (M := logarithmic.log ⊗ cyclicRootNegativePower L a.val.val)
              (N := (pushforward cover.f).obj (cover.f ≫ p).relativeDifferentials)
              (decomposition.forms.ι (some a) ≫ decomposition.formsIso.hom) q (x.2 a))) = x) ∧
    (∀ (q : ℕ) (x : cyclicRootH (𝟙_ cover.W.Modules) q)
      (a : CyclicRootPositiveIndex m),
      (cw q (Sheaf.H.map differentials.dW q x)).2 a =
        Sheaf.H.map (differentials.connection a) q ((cf q x).2 a)) ∧
    (∀ (q : ℕ) (x : cyclicRootH (𝟙_ cover.W.Modules) q),
      (cw q (Sheaf.H.map differentials.dW q x)).1 =
        Sheaf.H.map differentials.dY q ((cf q x).1))

/-- All clauses of the cyclic root-cover theorem, with their local normalizations.
Source: Popa Proposition 1.6.5, Theorem 1.6.6 and Lemma 1.6.7; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms). -/
structure CyclicRootCoverEigenformsData
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F))
    (L : Y.Modules) (n m : ℕ) (hm : 2 ≤ m) (s : 𝟙_ Y.Modules ⟶ L.tensorPow m) where
  cover : CyclicRootCoverGeometry F Y p L n m hm s
  logarithmic : CyclicRootLogarithmicForms F Y p L n m hm s
  decomposition : CyclicRootFormDecomposition F Y p L n m hm s cover logarithmic
  charts : CyclicRootChartComparisons F Y p L n m hm s cover logarithmic decomposition
  characters : CyclicRootCharacters F Y p L n m hm s cover logarithmic decomposition
  differentials : CyclicRootDifferentialBlocks F Y p L n m hm s cover logarithmic decomposition
  cohomology : CyclicRootCohomologyBlocks F Y p L n m hm s cover logarithmic decomposition
    differentials

/-- The cyclic root cover, logarithmic eigensheaves, residue and cohomological blocks.
Source: Popa Proposition 1.6.5 and proof, proof of Theorem 1.6.6 and Lemma 1.6.7,
printed pages 24--27; Stacks Tag 0FMW.
(blueprint: lem-sfb-cyclic-root-cover-eigenforms)

Proof:
1. Nonvanishing on the integral base makes the local coefficients nonzerodivisors.
   Frame changes glue A[t]/(t^m-u), with basis 1,t,...,t^(m-1), into the root cover.
   Uses `lem-pc-zero-scheme-properties`.
2. The monic power basis gives finite local freeness of degree m and affine preimages.
   Uses `lem-weil-pbc-affine-morphism-relative-spec`,
   `lem-weil-pbc-monic-quotient-free` and `pqf-def-coherent`.
3. The universal property gives Ω_B = (B⊗Ω_A ⊕ B dt)/(du-m t^(m-1)dt).
4. Smoothness of the zero divisor makes du part of a local basis along the divisor.
   Uses `lem-pur-conormal-sequence-smooth-immersion` and
   `lem-sc-smooth-omega-finite-locally-free`.
5. At branch points eliminate du; away from the divisor eliminate dt. The
   hypersurface criterion proves smoothness, and the differential ranks give dimension n.
   Uses `sbc-lem-affine-space-smooth`, `lem-sbc-smooth-relative-dimension-permanence`,
   `lem-zl-hypersurface-nonzero-relative-differential` and
   `lem-weil-pbc-smooth-over-field-dimension-differentials`.
6. Finite-over-projective gives projectivity. Constant local dimension gives pure
   dimension without any connectedness assumption on W.
   Uses `lem-fin-finite-over-projective`, `lem-weil-pbc-finite-type-over-noetherian`
   and `lem-sbc-constant-local-dimension-components`.
7. Locally Ω(log D) is generated by Ω and du/u with relation u(du/u)=du.
   Residue takes the logarithmic coefficient modulo u and is invariant under frame changes.
8. Multiplication t↦ζt has eigensummands L^(-a), by the monic power basis.
   Uses `lem-sc-primitive-root`.
9. The positive differential inclusion sends α⊗e^(-a) to t^a f*α;
   t^a du/u = m t^(a-1)dt gives the logarithmic eigensummands.
10. Leibniz gives d(bt^a)=t^a(db+(a/m)b du/u). The dg terms cancel on overlaps.
11. Choose a finite affine-intersection cover. Affine vanishing, open-restriction
   comparison and module/abelian comparison make all these sheaves Cech-acyclic.
   Uses `lem-pc-projective-proper`, `lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-separated-affine-open-intersection`, `lem-pc-affine-morphism-hi`,
   `lem-pc-affine-vanishing`, `lem-pc-open-restriction-module-cohomology`,
   `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` and
   `lem-sc-ringed-space-module-sheaves-enough-injectives`.
12. The section complexes of f_*G and G on the inverse-image cover coincide.
   The normalized Cech edge, additive naturality, site change and forgetting
   give precisely the stated canonical comparisons and every differential block, using
   `lem-weil-pbc-acyclic-cech-edge-compatibility`. -/
theorem cyclic_root_cover_eigenforms
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (.of F)) (n : ℕ)
    [SmoothOfRelativeDimension n p] [IsProjective p] [GeometricallyIntegral p]
    (L : Y.Modules) [L.IsInvertible] (m : ℕ) (hm : 2 ≤ m)
    (s : 𝟙_ Y.Modules ⟶ L.tensorPow m) (hs : s ≠ 0)
    (hD : Smooth (s.zeroLocus.subschemeι ≫ p)) :
    Nonempty (CyclicRootCoverEigenformsData F Y p L n m hm s) := by
  sorry

end AlgebraicGeometry
