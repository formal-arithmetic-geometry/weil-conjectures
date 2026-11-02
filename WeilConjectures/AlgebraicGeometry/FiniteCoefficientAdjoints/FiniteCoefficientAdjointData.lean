/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedEtaleOriginWitnesses
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Compactification.NagataCompactification

/-! # Ordinary finite-coefficient exceptional adjunctions

Source: current blueprint sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, supplemented by the ordinary closed-support
argument of DAG lem-pur-finite-coefficient-adjoint-comparisons, proof steps 9--12;
Stacks Tags 09XP, 06YS and 0B65
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).

The interfaces below bundle the clauses of this node. Coefficients are actual quotients
of the recorded integer rings. All categories are ordinary derived categories. The
adjunction's counit and the projection comparison are normalized by their specified
site-comparison constructions. No smoothness or coefficient-cocycle hypothesis occurs.

The interfaces below are relocated unchanged to permit proof lemmas to import them.
(blueprint: def-pur-finite-coefficient-adjoint-data).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option linter.all false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- Index a finite coefficient stage by a finite extension of the fixed coefficient field
and a positive exponent of its fixed uniformizer. Source: current blueprint
sk-lem-sp-field-extension-towers (blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
structure Stage (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] where
  field : Type (u + 1)
  [fieldStructure : Field field]
  [algebraStructure : Algebra (Padic l) field]
  [finiteStructure : FiniteDimensional (Padic l) field]
  inclusion : E →ₐ[Padic l] field
  exponent : ℕ+

attribute [instance] Stage.fieldStructure Stage.algebraStructure Stage.finiteStructure

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The integer ring of a stage is the existing valuation-ring construction.
Source: blueprint coefficient setting
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev Stage.integers (s : Stage l E) := Padic.coefficientExtensionIntegers l s.field

/-- The element is the image of the *base* uniformizer, including at ramified stages.
Source: blueprint sk-lem-sp-field-extension-towers
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def Stage.parameter (s : Stage l E) : s.integers :=
  strictEtaleIntegerMap l s.inclusion (Padic.coefficientExtensionUniformizer l E)

/-- The actual quotient ideal, with no replacement by the upper field's exponent n.
Source: blueprint sk-lem-sp-field-extension-towers
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def Stage.ideal (s : Stage l E) : Ideal s.integers :=
  Ideal.span ({s.parameter} : Set s.integers) ^ (s.exponent : ℕ)

/-- The finite coefficient ring O_F/t^n O_F. Source: blueprint field-extension towers
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev Stage.ring (s : Stage l E) := s.integers ⧸ s.ideal

/-- The base-field stages are exactly the original coefficient quotients A_n.
Source: blueprint coefficient setting
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def baseStage (n : ℕ+) : Stage l E where
  field := E
  inclusion := AlgHom.id (Padic l) E
  exponent := n

/-- Positive stages are finite, including ramified base-uniformizer stages.
Source: blueprint field-extension towers; node proof steps 1 and 15
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: uniqueness of the extended absolute value identifies the integer rings with
unit balls. The image of t is nonzero of absolute value less than one. The upper DVR
writes it as a unit times v^e, e positive. Its nth power ideal is (v)^(en), whose
quotient is finite by lem-weil-valued-dvr-finite-quotients. -/
@[instance] theorem stageFinite (s : Stage l E) : Finite s.ring := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  rcases hE with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrE, hgenE, _⟩
  have hπE : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
    exact ((hrE.choose_spec.2.2 _).mp hgenE.choose_spec).1
  have hparam : s.parameter ≠ 0 := by
    intro hz
    apply hπE
    apply Subtype.ext
    apply s.inclusion.injective
    change s.inclusion (Padic.coefficientExtensionUniformizer l E : E) = s.inclusion 0
    exact (congrArg Subtype.val hz).trans (map_zero s.inclusion).symm
  rcases hF with ⟨_, _, _, _, _, _, _, hDVR, _, _, _, hfinite, _, hgenF, _⟩
  have : IsDiscreteValuationRing s.integers := hDVR
  have hπF : Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} :
      Set s.integers) = Padic.coefficientExtensionMaximalIdeal l s.field :=
    hgenF.choose_spec
  have hmax := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec.2.2.2.2.1
  have hirr : Irreducible (Padic.coefficientExtensionUniformizer l s.field) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [hπF]
    exact (IsLocalRing.eq_maximalIdeal hmax).symm
  have hideal : s.ideal ≠ ⊥ := by
    rw [Stage.ideal, Ideal.span_singleton_pow]
    exact mt Ideal.span_singleton_eq_bot.mp (pow_ne_zero _ hparam)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hideal hirr
  have : Finite (s.integers ⧸ Ideal.span
      ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers)) := by
    rw [hπF]
    exact hfinite
  change Finite (s.integers ⧸ s.ideal)
  rw [hn, ← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) n

/-- A coefficient arrow retains its actual field embedding and exponent inequality.
These are exactly composites of a quotient and a finite-free extension.
Source: blueprint field-extension towers
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
structure Arrow (s t : Stage l E) where
  embedding : s.field →ₐ[Padic l] t.field
  over_base : embedding.comp s.inclusion = t.inclusion
  level : (t.exponent : ℕ) ≤ (s.exponent : ℕ)

/-- The integer map sends the source quotient ideal into the target ideal.
Source: node proof step 1, blueprint field-extension towers
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: equality of the embeddings on E sends the source parameter to the target
parameter. Functoriality of principal ideals and powers sends (t^m) into (t^n)
when n <= m. This is also valid for equal levels and identity embeddings. -/
theorem Arrow.ideal_le {s t : Stage l E} (a : Arrow s t) :
    s.ideal ≤ t.ideal.comap (strictEtaleIntegerMap l a.embedding) := by
  have hparam : strictEtaleIntegerMap l a.embedding s.parameter = t.parameter := by
    apply Subtype.ext
    change a.embedding (s.inclusion _) = t.inclusion _
    exact DFunLike.congr_fun a.over_base _
  apply Ideal.map_le_iff_le_comap.mp
  simp only [Stage.ideal, Ideal.map_pow, Ideal.map_span, Set.image_singleton, hparam]
  exact Ideal.pow_le_pow_right a.level

/-- The canonical coefficient homomorphism is induced on the actual quotient rings.
Source: blueprint field-extension towers
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def Arrow.ringMap {s t : Stage l E} (a : Arrow s t) : s.ring →+* t.ring :=
  Ideal.quotientMap t.ideal (strictEtaleIntegerMap l a.embedding) a.ideal_le

/-- Finite-free means actual finite and free modules for the quotient algebra map.
Source: blueprint coefficient extensions
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def Arrow.IsFiniteFree {s t : Stage l E} (a : Arrow s t) : Prop :=
  letI := a.ringMap.toAlgebra
  Module.Finite s.ring t.ring ∧ Module.Free s.ring t.ring

/-- Ordinary pro-etale derived category in the fixed-module presentation.
Source: blueprint finite coefficient categories
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The existing bounded constructible finite-Tor property, retaining etale origin.
Source: blueprint finite coefficient categories
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev ctf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T

/-- Derived coefficient tensor, fixed by adjunction to actual scalar restriction.
Source: Stacks 06YY (blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev tensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ

/-- The exact derived site inverse image.
Source: blueprint site comparison
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev nu (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The ordinary right derived site restriction.
Source: blueprint site comparison
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev rnu (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Compact support for the specified compactification, rather than a fresh choice.
Source: blueprint finite operations
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev lower (A : Type (u + 1)) [CommRing A] (c : Compactification f) :=
  ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The etale adjoint-existence instance for precisely the specified compactification.
Source: thm-amb-etale-exceptional-adjoint
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: the proper morphism c.g is finite type over the Noetherian target, so its
source is locally Noetherian and quasi-compact. Apply the recorded etale adjoint
existence theorem to this same compactification and these finite coefficients. -/
theorem etaleLeftAdjoint (A : Type (u + 1)) [CommRing A] [Finite A]
    [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsLeftAdjoint := by
  exact Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c

/-- The etale exceptional functor for the same compactification, fixed by its adjunction.
Source: thm-amb-etale-exceptional-adjoint
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def etaleUpper (A : Type (u + 1)) [CommRing A] [Finite A]
    [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) :=
  letI := etaleLeftAdjoint A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- The etale adjunction includes its fixed unit and counit.
Source: thm-amb-etale-exceptional-adjoint
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def etaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ etaleUpper A c :=
  letI := etaleLeftAdjoint A c
  Adjunction.ofIsLeftAdjoint _

/-- G_A = nu_X^* f_A^times Rnu_Y,* in ordinary derived categories.
Source: blueprint finite operations
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def upper (A : Type (u + 1)) [CommRing A] [Finite A]
    [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) : D A Y ⥤ D A X :=
  rnu A Y ⋙ etaleUpper A c ⋙ nu A X

/-- The restriction of a functor preserving the existing ctf property.
Source: blueprint finite coefficient categories
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def restrict {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {T U : Scheme.{u}} (F : D A T ⥤ D B U)
    (h : ∀ K, ctf A T K → ctf B U (F.obj K)) :=
  (ctf B U).lift ((ctf A T).ι ⋙ F) (fun K ↦ h K.obj K.property)

/-- Bundle exactly the finite pro-etale adjunction, normalized by the geometric counit.
The field `etaleBound` supplies the bound needed to evaluate the specified comparison;
it is a conclusion, never a hypothesis of the item.
Source: blueprint finite operations; node proof steps 5--7
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
structure AdjointDatum (A : Type (u + 1)) [CommRing A] [Finite A]
    [IsNoetherian X] [IsNoetherian Y] (c : Compactification f) where
  lower_preserves : ∀ K, ctf A X K → ctf A Y ((lower A c).obj K)
  upper_preserves : ∀ K, ctf A Y K → ctf A X ((upper A c).obj K)
  adjunction : restrict (lower A c) lower_preserves ⊣ restrict (upper A c) upper_preserves
  etaleBound : ∀ K, ctf A Y K → DerivedCategory.TStructure.t.plus
    ((etaleUpper A c).obj ((rnu A Y).obj K))
  counit_normalization : ∀ (K : (ctf A Y).FullSubcategory),
    (adjunction.counit.app K).hom =
      (ProEtale.compactSupportSiteComparison A c).hom.app
          ⟨(etaleUpper A c).obj ((rnu A Y).obj K.obj), etaleBound K.obj K.property⟩ ≫
        (nu A Y).map ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj)) ≫
        (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K.obj

variable {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C] [IsNoetherian X] [IsNoetherian Y]

/-- The actual unit component, viewed in the ambient ordinary derived category.
Source: blueprint finite adjunction
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev AdjointDatum.unit {c : Compactification f} (d : AdjointDatum A c)
    (K : (ctf A X).FullSubcategory) := (d.adjunction.unit.app K).hom

/-- The actual counit component in the ambient ordinary derived category.
Source: blueprint finite adjunction
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
abbrev AdjointDatum.counit {c : Compactification f} (d : AdjointDatum A c)
    (K : (ctf A Y).FullSubcategory) := (d.adjunction.counit.app K).hom

/-- The canonical pro-etale projection arrow at a retained origin witness: transport the
existing etale projection mate along the specified site and coefficient comparisons.
Source: blueprint coefficient compatibility; node proof steps 4 and 7
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def projectionAtWitness (φ : A →+* B) (c : Compactification f)
    (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩)
    (hB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj w.complex.obj)) :
    (tensor φ Y).obj ((lower A c).obj K.obj) ⟶
      (lower B c).obj ((tensor φ X).obj K.obj) :=
  (tensor φ Y).map ((lower A c).map w.iso.inv) ≫
    (tensor φ Y).map ((ProEtale.compactSupportSiteComparison A c).hom.app w.complex) ≫
    (ProEtale.pbcComparisonReduction Y φ).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        w.complex.obj) ≫
    (nu B Y).map (Etale.ExceptionalCoefficients.compactSupportMap φ c w.complex.obj) ≫
    (ProEtale.compactSupportSiteComparison B c).inv.app
      ⟨(Etale.scalarExtension φ X).obj w.complex.obj, hB⟩ ≫
    (lower B c).map ((ProEtale.pbcComparisonReduction X φ).inv.app w.complex.obj) ≫
    (lower B c).map ((tensor φ X).map w.iso.hom)

/-- The projection and its invertible right-adjoint mate, with the exact unit and counit
identities. The projection's witness equation fixes the canonical map, not just its type.
Source: blueprint coefficient compatibility; node proof steps 7--14
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
structure Change (φ : A →+* B) (c : Compactification f)
    (dA : AdjointDatum A c) (dB : AdjointDatum B c) where
  tensor_preserves_X : ∀ K, ctf A X K → ctf B X ((tensor φ X).obj K)
  tensor_preserves_Y : ∀ K, ctf A Y K → ctf B Y ((tensor φ Y).obj K)
  projection : (ctf A X).ι ⋙ lower A c ⋙ tensor φ Y ≅
    (ctf A X).ι ⋙ tensor φ X ⋙ lower B c
  mate : (ctf A Y).ι ⋙ upper A c ⋙ tensor φ X ≅
    (ctf A Y).ι ⋙ tensor φ Y ⋙ upper B c
  etale_tensor_bound : ∀ (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
    DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj w.complex.obj)
  projection_normalization : ∀ (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
    projection.hom.app K = projectionAtWitness φ c K w (etale_tensor_bound K w)
  counit_equation : ∀ (K : (ctf A Y).FullSubcategory),
    (lower B c).map (mate.hom.app K) ≫
        dB.counit ⟨(tensor φ Y).obj K.obj, tensor_preserves_Y K.obj K.property⟩ =
      projection.inv.app ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩ ≫
        (tensor φ Y).map (dA.counit K)
  unit_equation : ∀ (K : (ctf A X).FullSubcategory),
    (tensor φ X).map (dA.unit K) ≫
        mate.hom.app ⟨(lower A c).obj K.obj, dA.lower_preserves K.obj K.property⟩ ≫
        (upper B c).map (projection.hom.app K) =
      dB.unit ⟨(tensor φ X).obj K.obj, tensor_preserves_X K.obj K.property⟩

/-- The canonical refinement comparison evaluated on a retained witness, transported
from the ordinary etale proper/open comparison.
Source: blueprint compact-support coherence; node proof steps 7 and 12
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def refinementAtWitness [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩) :
    (lower A c).obj K.obj ⟶ (lower A d).obj K.obj :=
  (lower A c).map w.iso.inv ≫
    (ProEtale.compactSupportSiteComparison A c).hom.app w.complex ≫
    (nu A Y).map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).inv.app w.complex ≫
        DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app
            w.complex) ≫
        (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) d).hom.app w.complex) ≫
    (ProEtale.compactSupportSiteComparison A d).inv.app w.complex ≫
    (lower A d).map w.iso.hom

/-- The specified compactification-refinement isomorphism and its counit-preserving
right-adjoint conjugate. Source: blueprint compact-support coherence
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
structure RefinementDatum [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (dc : AdjointDatum A c) (dd : AdjointDatum A d) where
  lowerIso : (ctf A X).ι ⋙ lower A c ≅ (ctf A X).ι ⋙ lower A d
  upperIso : (ctf A Y).ι ⋙ upper A d ≅ (ctf A Y).ι ⋙ upper A c
  lower_normalization : ∀ (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩),
    lowerIso.hom.app K = refinementAtWitness r K w
  upper_normalization : ∀ (K : (ctf A Y).FullSubcategory),
    (lower A c).map (upperIso.hom.app K) ≫ dc.counit K =
      lowerIso.hom.app ⟨(upper A d).obj K.obj, dd.upper_preserves K.obj K.property⟩ ≫
        dd.counit K

/-- Quotient coefficient maps preserve identities, with equality of the actual ring maps.
Source: blueprint coefficient towers; node proof step 14
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: the integer restriction of the identity field embedding is the identity ring
map, since both have the same inclusion in the field. The quotient map is then the
identity on every quotient generator; surjectivity of the quotient map gives equality. -/
theorem Arrow.ringMap_id {s : Stage l E} (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field) : a.ringMap = RingHom.id s.ring := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk s.ideal (strictEtaleIntegerMap l a.embedding x) =
    Ideal.Quotient.mk s.ideal x
  congr 1
  apply Subtype.ext
  change a.embedding (x : s.field) = (x : s.field)
  rw [h]
  rfl

/-- Quotient coefficient maps preserve composition, including mixed coefficient changes.
Source: blueprint coefficient towers; node proof step 14
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: the restrictions of the composite field embedding and the composite integer
maps agree after the injective inclusion of the target integer ring into its field.
Evaluate the two quotient maps on each quotient generator, using quotientMap_mk and
that equality. Quotient generators are surjective, giving equality of ring homomorphisms. -/
theorem Arrow.ringMap_comp {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding) :
    ab.ringMap = b.ringMap.comp a.ringMap := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk v.ideal (strictEtaleIntegerMap l ab.embedding x) =
    Ideal.Quotient.mk v.ideal
      (strictEtaleIntegerMap l b.embedding (strictEtaleIntegerMap l a.embedding x))
  congr 1
  apply Subtype.ext
  change ab.embedding (x : s.field) = b.embedding (a.embedding (x : s.field))
  rw [h]
  rfl

/-- The finite exceptional coefficient system. Every coherence below is a componentwise
identity for specified natural transformations, hence equivalently an equality of those
natural transformations by extensionality. The quantification over field embeddings and
levels includes quotient, finite-free, and mixed diagrams.
Source: current blueprint coefficient compatibility and field-extension towers;
node proof steps 12--14
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
structure System (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] where
  datum : ∀ (s : Stage l E) (c : Compactification f), AdjointDatum s.ring c
  change : ∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
    Change a.ringMap c (datum s c) (datum t c)
  origin_X : ∀ (s : Stage l E) (K : (ctf s.ring X).FullSubcategory),
    Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩
  origin_Y : ∀ (s : Stage l E) (K : (ctf s.ring Y).FullSubcategory),
    Scheme.FixedEtaleOriginWitness Y s.ring ⟨K.obj, K.property.plus⟩
  projection_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
    (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
    (tensor b.ringMap Y).map ((change a c).projection.hom.app K) ≫
        (change b c).projection.hom.app
          ⟨(tensor a.ringMap X).obj K.obj,
            (change a c).tensor_preserves_X K.obj K.property⟩ ≫
        (lower v.ring c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
            a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
            ((lower s.ring c).obj K.obj) ≫
        (change ab c).projection.hom.app K
  mate_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
    (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
    (tensor b.ringMap X).map ((change a c).mate.hom.app K) ≫
        (change b c).mate.hom.app
          ⟨(tensor a.ringMap Y).obj K.obj,
            (change a c).tensor_preserves_Y K.obj K.property⟩ ≫
        (upper v.ring c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
            a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
            ((upper s.ring c).obj K.obj) ≫
        (change ab c).mate.hom.app K
  projection_id : ∀ (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field)
    (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
    (change a c).projection.hom.app K ≫
        (lower s.ring c).map ((ProEtale.normalizedOriginScalarUnit
          (Scheme.ProEt.topology X) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
        a.ringMap (Arrow.ringMap_id a h)).hom.app ((lower s.ring c).obj K.obj)
  mate_id : ∀ (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field)
    (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
    (change a c).mate.hom.app K ≫
        (upper s.ring c).map ((ProEtale.normalizedOriginScalarUnit
          (Scheme.ProEt.topology Y) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        a.ringMap (Arrow.ringMap_id a h)).hom.app ((upper s.ring c).obj K.obj)
  refinement : ∀ (s : Stage l E) {c d : Compactification f} (r : c.Refinement d),
    RefinementDatum r (datum s c) (datum s d)
  projection_refinement : ∀ {s t : Stage l E} (a : Arrow s t)
    {c d : Compactification f} (r : c.Refinement d) (K : (ctf s.ring X).FullSubcategory),
    (tensor a.ringMap Y).map ((refinement s r).lowerIso.hom.app K) ≫
        (change a d).projection.hom.app K =
      (change a c).projection.hom.app K ≫
        (refinement t r).lowerIso.hom.app
          ⟨(tensor a.ringMap X).obj K.obj, (change a c).tensor_preserves_X K.obj K.property⟩
  mate_refinement : ∀ {s t : Stage l E} (a : Arrow s t)
    {c d : Compactification f} (r : c.Refinement d) (K : (ctf s.ring Y).FullSubcategory),
    (tensor a.ringMap X).map ((refinement s r).upperIso.hom.app K) ≫
        (change a c).mate.hom.app K =
      (change a d).mate.hom.app K ≫
        (refinement t r).upperIso.hom.app
          ⟨(tensor a.ringMap Y).obj K.obj, (change a c).tensor_preserves_Y K.obj K.property⟩

/-- The Noetherian instance follows from finite type over the arbitrary field, with no
perfectness or algebraic-closure hypothesis. Source: node proof step 1
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: Spec k is Noetherian. Local finite type over a locally Noetherian scheme
gives local Noetherianity, and quasi-compactness over Spec k gives quasi-compactness.
These two facts are the two fields of IsNoetherian T. -/
theorem finiteTypeNoetherian (k : Type u) [Field k] (T : Scheme.{u})
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] : IsNoetherian T := by
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  exact ⟨⟩

/-- A k-morphism between the schemes in the statement has the morphism properties
used by compact support, without additional hypotheses on that morphism.
Source: node proof step 1 (blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
Proof: rewrite f followed by the target structure morphism as the source structure
morphism using IsOver. Separatedness and local finite type descend from this composite.
The source is quasi-compact and the target is quasi-separated, so f is quasi-compact. -/
theorem finiteTypeMorphismProperties (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f := by
  have hcomp : f ≫ (Y ↘ Spec (.of k)) = (X ↘ Spec (.of k)) := by
    simp
  have : IsSeparated (f ≫ (Y ↘ Spec (.of k))) := by rw [hcomp]; infer_instance
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) := by
    rw [hcomp]
    infer_instance
  have : IsNoetherian X := finiteTypeNoetherian k X
  have : IsNoetherian Y := finiteTypeNoetherian k Y
  exact ⟨IsSeparated.of_comp f (Y ↘ Spec (.of k)),
    locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k)), inferInstance⟩

/-- The system over separated finite-type k-schemes, installing only the Noetherian
instances implied by those hypotheses. Source: blueprint finite operations
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons). -/
def FiniteTypeSystem (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :=
  letI := finiteTypeNoetherian k X
  letI := finiteTypeNoetherian k Y
  letI := (finiteTypeMorphismProperties k f).1
  letI := (finiteTypeMorphismProperties k f).2.1
  letI := (finiteTypeMorphismProperties k f).2.2
  System l E f

/-- Ramification and cofinality for the actual base-uniformizer stage.
Source: the coefficient setting and field-extension tower in the current blueprint;
DVR expansion, node lem-weil-l-adic-extension-integers-dvr.
(blueprint: lem-pur-stage-ramification-cofinality).
Proof: the base uniformizer is nonzero and nonunit after the embedding. Expand it
in the upper DVR as a unit times a power of its chosen uniformizer. Nonunitness
makes the exponent positive. Taking powers identifies the principal ideals.
The positive exponent makes its multiples cofinal among natural numbers. -/
theorem stage_ramification (s : Stage l E) :
    ∃ (e : ℕ+) (z : s.integersˣ),
      s.parameter = (z : s.integers) *
        Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
      (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
        Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
      ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ) := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have : IsLocalRing s.integers := hF.2.2.2.1
  have : IsDiscreteValuationRing s.integers := hF.2.2.2.2.2.2.2.1
  have hgenE := hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenF : Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} :
      Set s.integers) = Padic.coefficientExtensionMaximalIdeal l s.field :=
    hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmaxF : (Padic.coefficientExtensionMaximalIdeal l s.field).IsMaximal :=
    hF.2.2.2.2.1
  have hπ : Irreducible (Padic.coefficientExtensionUniformizer l s.field) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [hgenF]
    exact (IsLocalRing.eq_maximalIdeal hmaxF).symm
  have hval : Padic.coefficientExtensionAbsoluteValue l s.field
      (s.parameter : s.field) = Padic.coefficientExtensionAbsoluteValue l E
        (Padic.coefficientExtensionUniformizer l E : E) := by
    change spectralNorm (Padic l) s.field (s.inclusion _) = spectralNorm (Padic l) E _
    unfold spectralNorm
    rw [minpoly.algHom_eq s.inclusion s.inclusion.injective]
    rfl
  have hlt : Padic.coefficientExtensionAbsoluteValue l s.field
      (s.parameter : s.field) < 1 := by
    rw [hval]
    exact (hE.2.1 _).mp (hgenE ▸ Ideal.mem_span_singleton_self _)
  have hzero : s.parameter ≠ 0 := by
    intro hz
    have hπE : Padic.coefficientExtensionUniformizer l E ≠ 0 :=
      ((hE.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.2.2 _).mp hgenE).1
    apply hπE
    apply Subtype.ext
    apply s.inclusion.injective
    exact (congrArg Subtype.val hz).trans (map_zero s.inclusion).symm
  obtain ⟨e, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hzero hπ
  have he : 0 < e := by
    by_contra he
    have he0 : e = 0 := Nat.eq_zero_of_not_pos he
    have hu : IsUnit s.parameter := by
      rw [hz, he0, pow_zero, mul_one]
      exact z.isUnit
    exact (ne_of_lt hlt) ((hF.2.2.1 _).mp hu)
  refine ⟨⟨e, he⟩, z, hz, ?_, ?_⟩
  · intro n
    rw [Ideal.span_singleton_pow, hz, mul_pow]
    change Ideal.span ({↑z ^ n *
      (Padic.coefficientExtensionUniformizer l s.field ^ e) ^ n} : Set s.integers) = _
    rw [Ideal.span_singleton_mul_left_unit (z.isUnit.pow n)]
    simp only [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow, pow_mul]
    rfl
  · intro r
    refine ⟨⟨r + 1, Nat.succ_pos _⟩, ?_⟩
    exact (Nat.le_succ r).trans (by simpa using Nat.mul_le_mul_right (r + 1) he)

/-- Same-level arrows are finite free over the actual quotient coefficient rings.
Source: the field-extension tower in the current blueprint, and integral closure
of a complete discretely valued field in a finite extension.
(blueprint: lem-pur-stage-same-level-finite-free).
Proof: put the upper field over the lower field using the recorded embedding.
Its integer ring is the integral closure of the lower integer ring, hence finite.
It is torsion-free as a subring of a field; a finite torsion-free module over the
lower DVR is free. Base change by the principal-power quotient is therefore
finite free. Compatibility of the embedding with the base parameter identifies
the base-changed ideal with the upper stage ideal. Transport through the standard
tensor/quotient equivalence to obtain the claimed quotient module. -/
theorem stage_finiteFree {s t : Stage l E} (a : Arrow s t)
    (h : s.exponent = t.exponent) : a.IsFiniteFree := by
  classical
  let R := s.integers
  let S := t.integers
  let φ : R →+* S := strictEtaleIntegerMap l a.embedding
  let : Algebra s.field t.field := a.embedding.toRingHom.toAlgebra
  let : Algebra R t.field := (a.embedding.toRingHom.comp R.subtype).toAlgebra
  let : Algebra R S := φ.toAlgebra
  have : IsScalarTower R s.field t.field := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S t.field := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Padic l) s.field t.field :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (a.embedding.commutes x).symm
  have : FiniteDimensional s.field t.field :=
    Module.Finite.of_restrictScalars_finite (Padic l) s.field t.field
  have hs := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have : IsFractionRing R s.field := hs.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing R := hs.2.2.2.2.2.2.2.2.1
  have : CharZero s.field :=
    charZero_of_injective_algebraMap (algebraMap (Padic l) s.field).injective
  have : IsIntegralClosure S R t.field := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change x ∈ integralClosure R t.field ↔ ∃ y : S, (y : t.field) = x
    rw [← Padic.padic_integers_integralClosure l s.field t.field a.embedding x]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : Module.Finite R S := IsIntegralClosure.finite R s.field t.field S
  have : Module.IsTorsionFree R t.field := by
    apply Module.isTorsionFree_iff_smul_eq_zero.mpr
    intro r x hx
    change (a.embedding r) * x = 0 at hx
    rcases mul_eq_zero.mp hx with hr | hx
    · left
      apply Subtype.ext
      exact a.embedding.injective (hr.trans (map_zero a.embedding).symm)
    · exact Or.inr hx
  have : Module.Free R S := IsIntegralClosure.module_free R s.field t.field S
  have hparam : φ s.parameter = t.parameter := by
    apply Subtype.ext
    exact DFunLike.congr_fun a.over_base _
  have hJ : s.ideal.map (algebraMap R S) = t.ideal := by
    change s.ideal.map φ = t.ideal
    simp only [Stage.ideal, Ideal.map_pow, Ideal.map_span, Set.image_singleton, h]
    rw [hparam]
  let : Algebra s.ring t.ring := a.ringMap.toAlgebra
  let e : (S ⧸ s.ideal.map (algebraMap R S)) ≃ₗ[s.ring] t.ring :=
    (Ideal.quotEquivOfEq hJ).toAddEquiv.toLinearEquiv (by
      intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl)
  let e' := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S s.ideal).symm.toLinearEquiv
    |>.trans e
  exact ⟨Module.Finite.equiv e', Module.Free.of_equiv e'⟩

end AlgebraicGeometry.FiniteCoefficientAdjoints
