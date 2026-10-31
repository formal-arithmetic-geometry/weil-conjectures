/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CharacterIntegralTrace
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnitTrivialization
public import WeilConjectures.AlgebraicGeometry.VectorBundleThom
public import WeilConjectures.AlgebraicGeometry.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses

import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.IntegralModels
import WeilConjectures.AlgebraicGeometry.VectorIntegrationPresentationIso
import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.CompactSupportFiniteTorsion
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.VectorTraceScalarDescent
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization

/-! # The compactly supported character integral of a linear form

Source: latest blueprint, sec-fourier-transform/sk-lem-wft-character-integral,
lem-fd-character-integral and its proof (blueprint: lem-fd-character-integral).
We use coordinate-tower compactification coordinates for affine space. The
Artin--Schreier sheaf is the recorded degree-q character-projector image sheaf.
Root evaluation uses the comparison dependency and the distinguished root zero.
The zero-form trace is the signed actual coordinate-tower trace, followed by
actual derived coefficient sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CharacterIntegral
open DiagonalCoefficients RationalP1 ArtinSchreierTrace ArtinSchreierUnit

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))

/-- Root containment in the finite-extension branch; the algebraic-closure branch
has all roots already. Source: blueprint rational coefficient preamble
(blueprint: lem-fd-character-integral). -/
def HasRoots (p : ℕ) : Prop :=
  match c with
  | some E => ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
      ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1
  | none => True

/-- The linear function with coefficients a in the existing ordered affine-space
coordinates. In rank zero the sum is empty and is zero.
Source: blueprint λ:A^r→A^1 linear (blueprint: lem-fd-character-integral). -/
def linearFunction (Ω : Type u) [Field Ω] (r : ℕ) (a : Fin r → Ω) :
    Γ(affineTraceTower (Spec (.of Ω)) r, ⊤) :=
  ∑ i : Fin r, (affineTraceProjection (Spec (.of Ω)) r).appTop
    ((Scheme.ΓSpecIso (.of Ω)).inv.hom (a i)) *
      affineTraceCoordinate (Spec (.of Ω)) r i

/-- Pull back the existing degree-q projector sheaf along the linear function and
then the specified finite-field structure map. Source: blueprint λ^*Lψ
(blueprint: lem-fd-character-integral). -/
def linearSheaf (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (ψ : AddChar k (MonObj.Γ (coefficient ℓ c).X)) (r : ℕ) (a : Fin r → Ω) :
    Modules ℓ c (affineTraceTower (Spec (.of Ω)) r) :=
  letI : (affineTraceTower (Spec (.of Ω)) r).Over (Spec (.of k)) :=
    ⟨affineTraceProjection (Spec (.of Ω)) r ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩
  condensedArtinSchreierSheafOf (coefficient ℓ c).X k _ ψ (linearFunction Ω r a)

/-- The existing signed Tate coefficient line, transported through the recorded
internal/sectionwise module equivalence; no root basis is chosen.
Source: blueprint Λ(-r) and sk-def-sp-tate-twist
(blueprint: lem-fd-character-integral). -/
def signedLine (T : Scheme.{u}) (n : ℤ) : Modules ℓ c T :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient ℓ c).X T)).inverse.obj
      (spSignedTwist T (condensedRingObj (coefficient ℓ c).X T) (line ℓ c T) n)

/-- Actual derived coefficient sections after the ordered compactification word.
This is RΓc, with values in modules over the global coefficient ring Λ(*).
Source: blueprint compact cohomology convention and finite-to-condensed comparison
(blueprint: lem-fd-character-integral). -/
def compactSections (Ω : Type u) [Field Ω] (r : ℕ) :
    DerivedCategory (Modules ℓ c (affineTraceTower (Spec (.of Ω)) r)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ (coefficient ℓ c).X)) :=
  compact ℓ c (Spec (.of Ω)) r ⋙
    (CondensedRing.condensedRingCoefficientSections (coefficient ℓ c).X
      (Spec (.of Ω))).rightDerivedFunctor

/-- The zero-form comparison: pull the root-zero unit trivialization through the
ordered twisted pullback, apply compact support, then the signed vector trace.
Source: blueprint last paragraph; sign fixed in its current DAG clarification
(blueprint: lem-fd-character-integral). -/
def zeroTrace (Ω : Type u) [Field Ω] (r : ℕ)
    (d : TraceData ℓ c (Spec (.of Ω)))
    {M : Modules ℓ c (Spec (.of Ω))}
    (ε : M ⟶ Mod.regular (condensedRingObj (coefficient ℓ c).X (Spec (.of Ω)))) :=
  (CondensedRing.condensedRingCoefficientSections (coefficient ℓ c).X
    (Spec (.of Ω))).rightDerivedFunctor.map
      ((compact ℓ c (Spec (.of Ω)) r).map
          ((twistedPull ℓ c (Spec (.of Ω)) r).map
            ((DerivedCategory.singleFunctor _ 0).map ε)) ≫
        trace ℓ c (Spec (.of Ω)) d r)

/-- A nontrivial additive character has zero affine character integral for a
nonzero linear form. For the zero form, its integral is Λ(-r)[-2r], and the
isomorphism is the root-zero trivialization followed by (-1)^r times the
projective-line-normalized coordinate integration.

Source: latest blueprint lem-fd-character-integral and its twelve-step DAG proof
(blueprint: lem-fd-character-integral).

Proof:
1. By the character classification, write ψ(z)=Ψ(Tr(az)) with a nonzero. Character
values and their inverses are integral, so the degree-q projector has integral
and all finite quotient models, each lisse of rank one and Tor amplitude zero.
2. Over Spec Ω apply the normalized finite affine top trace. Translation of A1
preserves this integration by vector-integration presentation invariance. Since
integration is invertible, translation acts trivially on its compact cohomology.
3. The prime Artin--Schreier cover has total space A1. Finite direct image is
exact and compact-support composition identifies its direct image cohomology
with that of A1, equivariantly for all deck translations.
4. The sum of a nontrivial prime character is zero in the coefficient field,
hence also in its integer subring and every quotient. The character projector
therefore acts as zero on compact cohomology. Its split image has zero cohomology.
This argument does not cancel a possibly nonunit element in a quotient ring.
5. Compare the degree-q projector with the prime projector along the trace
polynomial. A nonzero scalar change of the line coordinate gives line vanishing.
6. Compactify the affine factor by projective space. Open tensor compatibility,
the proper projection formula and finite-torsion base change give the required
Kunneth isomorphism over the arbitrary algebraically closed field Ω.
7. For a nonzero coefficient vector, use λ and the other r-1 coordinates as an
invertible coordinate change. Its inverse solves for the chosen nonzero
coefficient. The Kunneth calculation and line vanishing prove the nonzero case.
8. For λ=0 evaluate the eigenfunction at root zero. Its values are ψ(b)v(0),
so evaluation is precisely the normalized coefficient-unit isomorphism. The
finite top trace then gives the zero case, including the identity in rank zero.
9. Open-extension and proper-direct-image etale/pro-etale comparisons, followed
by the ordinary/internal module equivalence, identify these finite calculations
with the actual native projector images and compactification functors.
10. Constructible finite-Tor compact support is derived complete integrally. Its
canonical scalar comparisons identify the whole reduction tower. Derived inverse
limit gives vanishing in the nonzero case and the compatible integration in the
zero case. Scalar descent includes the nonflat finite quotient maps.
11. Rationalize and extend to the finite-subextension-valued algebraic closure.
Projector splittings and compact support commute with these scalar comparisons.
A finite set of character values descends to a finite coefficient field. Exact
sections at the algebraically closed point give the displayed derived complexes.
12. Multiply the ordered trace by (-1)^r. This is invertible at every stage and
is the prescribed vector-bundle trace. The retained completed projective
references fix its normalization. Finite arbitrary-base-change compatibility
extends it to Ω, without assuming Ω algebraic over the initial finite field.
-/
theorem characterIntegral (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (k Ω : Type u) [Field k] [Fintype k] [CharP k p] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] (hroots : HasRoots ℓ c p)
    (ψ : AddChar k (MonObj.Γ (coefficient ℓ c).X)) (hψ : ψ ≠ 1) (r : ℕ) :
    letI : (Spec (.of Ω)).Over (Spec (.of k)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩
    let M := condensedArtinSchreierSheafOf (coefficient ℓ c).X k (Spec (.of Ω)) ψ 0
    Nonempty (TraceData ℓ c (Spec (.of Ω))) ∧
    (∀ a : Fin r → Ω, a ≠ 0 →
      IsZero ((compactSections ℓ c Ω r).obj
        ((DerivedCategory.singleFunctor _ 0).obj (linearSheaf ℓ c k Ω ψ r a)))) ∧
    Nonempty ((compactSections ℓ c Ω r).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar (coefficient ℓ c).X
          (affineTraceProjection (Spec (.of Ω)) r)).obj M)) ≅
      (CondensedRing.condensedRingCoefficientSections (coefficient ℓ c).X
        (Spec (.of Ω))).rightDerivedFunctor.obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (signedLine ℓ c (Spec (.of Ω)) (-(r : ℤ)))) ⟦-2 * (r : ℤ)⟧)) ∧
    ∃ (s : Over.mk (AffineSpace.homOfVector ((Spec (.of Ω)) ↘ Spec (.of k))
          (fun _ : PUnit ↦ (0 : Γ(Spec (.of Ω), ⊤)))) ⟶ universalCover k)
      (ε : M ≅ Mod.regular (condensedRingObj (coefficient ℓ c).X (Spec (.of Ω)))),
      s.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = 0 ∧
      ε.hom = condensedEvaluation (coefficient ℓ c).X
        (AffineSpace.homOfVector ((Spec (.of Ω)) ↘ Spec (.of k))
          (fun _ : PUnit ↦ (0 : Γ(Spec (.of Ω), ⊤)))) s
        (image.ι (condensedArtinSchreierProjector (coefficient ℓ c).X k ψ)) ∧
      ∀ d : TraceData ℓ c (Spec (.of Ω)), IsIso (zeroTrace ℓ c Ω r d ε.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CharacterIntegral
