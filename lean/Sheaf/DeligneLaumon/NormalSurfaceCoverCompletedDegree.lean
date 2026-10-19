/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.JapaneseDomain
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.CompletionRegularLocal
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import Sheaf.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.IntegralExtensionDimension
import WeilConjectures.RingTheory.NagataDomainN2
import Sheaf.RingTheory.RegularRingNormal

/-!
# Normalization covers of regular surfaces and completed degrees

Source: Stacks Project, Resolution of Surfaces, Tag 0BGN, intermediate-field paragraph;
Algebra, Tags 035S and 07N9; More on Algebra, Tags 07NY and 0C23
(blueprint: lem-per-normal-surface-cover-completed-degree).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Normalization in a finite function-field extension preserves excellent normal surfaces,
and each completed local degree is bounded by the generic degree. It also gives the induced
proper model over a finite normal intermediate algebra.

Source: Stacks Project, Tag 0BGN, intermediate-field paragraph; Tags 035S, 07N9, 07NY, 0C23
(blueprint: lem-per-normal-surface-cover-completed-degree).

The universally quantified rings R and S below are the two stalks, transported by specified
ring equivalences. The levelwise formula characterizes the canonical completion map uniquely.
The fraction-ring algebra is required to extend that map, so the degree is its actual degree.

Proof plan:
1. On a nonempty affine open V=\operatorname{Spec}A of Y, the function field is
F=\operatorname{Frac}(A) by [lem-sc-integral-function-field-affine-fraction]. Put B=\overline
A^{\,K}. By [lem-exc-quasi-excellent-nagata], A is Nagata; [lem-weil-pbc-nagata-domain-n2] and
[def-weil-pbc-japanese-domain] give that B is a finite A-module. By
[lem-weil-pbc-integral-closure-finite-extension-normal], B is a normal domain with fraction field K.
The affine descriptions of [def-fin-normalization-extension] identify \pi^{-1}V with
\operatorname{Spec}B. Thus \pi is finite by [def-weil-finite-integral-morphism], and it is
surjective by [lem-weil-pbc-integral-injective-lying-over], since A\subseteq B is integral.
2. The affine pieces \operatorname{Spec}B have common generic point with residue field K (the
inclusions into K agree on overlaps), so their glued scheme X is integral and has function field K.
Their local rings are normal domains by [lem-weil-pbc-localization-normal-domain]. Each B is
Noetherian by [lem-weil-pbc-finite-algebra-noetherian] and excellent by
[lem-exc-finite-type-localization-excellent]: a finite list of A-module generators also generates B
as an A-algebra. A finite affine cover of Y gives a finite such cover of X, hence X is Noetherian.
To compute dimension on each piece, [lem-weil-pbc-integral-extension-dimension] gives \dim B\leq\dim
A. Conversely lift the bottom prime of any finite chain in A by
[lem-weil-pbc-integral-injective-lying-over] and lift successive inclusions by [pqf-lem-going-up].
Distinct contractions force distinct lifted primes, so \dim B\geq\dim A. Applying
[lem-pc-dimension-affine-open-cover] to these two covers gives \dim X=\dim Y=2.
3. Fix a closed x as in the statement. Since \pi is a closed map by
[lem-weil-pbc-finite-closed-map-finite-fibres], y=\pi(x) is closed. Choose the affine
V=\operatorname{Spec}A above containing y, write \pi^{-1}V=\operatorname{Spec}B, and let \mathfrak q
and \mathfrak p=\mathfrak q\cap A represent x and y. By
[lem-weil-pbc-affine-open-stalk-localization], R=A_{\mathfrak p} and S=B_{\mathfrak q}. By
[lem-weil-pbc-integral-incomparability], contracting a length-two prime chain ending at \mathfrak q
gives a strict length-two chain ending at \mathfrak p. Thus 2=\dim S\leq\dim R\leq\dim Y=2. The ring
R is regular by the hypothesis on Y, while S is normal by Step 2. No finiteness of R\to S is
asserted.
4. The rings R,S are excellent by [lem-exc-finite-type-localization-excellent] and Noetherian by
[lem-weil-pbc-localization-noetherian]. Their completions are Noetherian by
[lem-weil-pbc-adic-completion-noetherian], local with the extended maximal ideals by
[lem-weil-pbc-local-completion-local-ring], and complete by
[lem-weil-pbc-module-completion-complete] applied with module the ring itself (the maximal ideals
are finitely generated). By [lem-weil-pbc-completion-dimension] their dimensions are two. By
[lem-weil-pbc-completion-regular-local], \widehat R is regular; it is a domain by
[lem-sc-regular-local-domain]. For S, excellence supplies the G-ring condition
[def-exc-excellent-ring], so [lem-weil-pbc-g-ring-completion-regular] makes S\to\widehat S flat with
geometrically regular Noetherian fibres. Those fibres are regular by taking the identity field
extension in [def-weil-pbc-g-ring], hence normal by [lem-weil-pbc-regular-ring-normal]. Apply
[lem-weil-pbc-flat-normal-fibres-noetherian-normal] to deduce that \widehat S is normal. A local
normal ring is a normal domain by [def-weil-pbc-normal-ring] applied at its maximal ideal.
5. Apply [lem-weil-pbc-completion-finite-extension] to the finite map A\subseteq B at \mathfrak p.
It gives the canonical \widehat R-algebra isomorphism
E:=\widehat R\otimes_A B\simeq\prod_{\mathfrak q'\mid\mathfrak p}\widehat{B_{\mathfrak q'}}.
In particular \widehat S is the factor indexed by \mathfrak q. If b_1,\ldots,b_t generate B over A,
the elements 1\otimes b_j generate E over \widehat R; their projections generate \widehat S. Thus
the canonical completion map \widehat R\to\widehat S is finite. Its identification as the map
induced by R\to S is part of the cited statement.
6. Choose an F-basis v_1,\ldots,v_d of K. Express the finitely many generators b_j of B in this
basis. A common nonzero denominator a\in A for their coordinates defines an injective A-linear map
u:B\to A^d, sending b to a times its coordinate vector: coordinates of every A-linear combination of
the b_j lie in a^{-1}A^d, and zero coordinates imply b=0. This is just finite linear algebra and
clearing the finitely many displayed denominators; it does not assume B free.
7. By [lem-weil-pbc-local-completion-faithfully-flat], R\to\widehat R is faithfully flat, hence
flat. Localize the injection u of Step 6 at \mathfrak p using
[lem-weil-pbc-localization-module-exact]. Tensor it over R with the flat module \widehat R;
[lem-trf-flat-tensor-preserves-injection] gives an injection E\hookrightarrow\widehat R^d. In the
product of Step 5, insertion in the \mathfrak q coordinate is an injective \widehat R-linear map
\widehat S\hookrightarrow E. Consequently \widehat S is torsion free over the domain \widehat R. If
a nonzero r\in\widehat R mapped to zero in \widehat S, it would annihilate 1\in\widehat S,
contradicting torsion freeness and the fact that \widehat S is a nonzero domain. The completion map
is therefore injective.
8. Put Q=\operatorname{Frac}(\widehat R). Localizing the injection \widehat S\hookrightarrow\widehat
R^d of Step 7 using [lem-weil-pbc-localization-module-exact] gives an injection H:=(\widehat
R\setminus\{0\})^{-1}\widehat S\hookrightarrow Q^d. Since \widehat R\to\widehat S is injective and
\widehat S is a domain, H is a nonzero domain; it has Q-dimension at most d (a linearly independent
family maps to one in Q^d). By [lem-weil-pbc-finite-dimensional-domain-is-field], H is a field. It
contains \widehat S and is contained in \operatorname{Frac}(\widehat S), so every quotient of two
elements of \widehat S already lies in H. Thus H=\operatorname{Frac}(\widehat S) and
[\operatorname{Frac}(\widehat S):Q]\leq d, with the field map induced by the completion map as
required.
9. For the final assertion let f:Y\to\operatorname{Spec}C be the given proper morphism. On each
nonempty affine V=\operatorname{Spec}A\subseteq Y, the map C\to A\subseteq F is the prescribed
inclusion, by [lem-sc-integral-function-field-affine-fraction] and the generic-point hypothesis.
Every z\in D\subseteq K is integral over C because D is finite over C; equivalently it satisfies a
monic polynomial over C (the finite-implies-integral clause of
[lem-weil-pbc-finite-algebra-is-integral]). The same polynomial has coefficients in A, so
z\in\overline A^{\,K}=B. These inclusions D\to B commute with restrictions, all being inclusions in
K. Using the affine normalization description [def-fin-normalization-extension], they therefore glue
to h:X\to\operatorname{Spec}D over \operatorname{Spec}C. At the generic point the induced map is
D\subseteq K, hence its extension to fraction fields is the identity on K.
10. The composite X\xrightarrow{\pi}Y\xrightarrow{f}\operatorname{Spec}C is proper: \pi is finite by
Step 1, hence proper by [lem-weil-pbc-finite-proper], and [lem-weil-pbc-proper-composition] applies
to \pi,f. The morphism \operatorname{Spec}D\to\operatorname{Spec}C is finite, hence separated by
[lem-weil-pbc-finite-closed-map-finite-fibres]. Apply [lemma-nagata-proper-to-separated-target] to
the triangle X\xrightarrow{h}\operatorname{Spec}D\to\operatorname{Spec}C constructed in Step 9. It
proves h proper, completing the last assertion.
-/
theorem normal_surface_cover_completed_degree
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hRegular : IsRegularScheme Y)
    (hExcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hDim : topologicalKrullDim Y = 2)
    (K : Type u) [Field K] [Algebra Y.functionField K]
    [FiniteDimensional Y.functionField K] :
    IsIntegral (Y.normalizationIn K) ∧
    (∀ x : Y.normalizationIn K,
      IsDomain ((Y.normalizationIn K).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Y.normalizationIn K).presheaf.stalk x)) ∧
    (∀ U : (Y.normalizationIn K).affineOpens,
      IsExcellent Γ(Y.normalizationIn K, U)) ∧
    IsNoetherian (Y.normalizationIn K) ∧
    topologicalKrullDim (Y.normalizationIn K) = 2 ∧
    (∃ e : Spec (.of K) ≅ Spec (Y.normalizationIn K).functionField,
      e.hom ≫ (Y.normalizationIn K).fromSpecFunctionField =
        (Y.fromSpecOfAlgebraFunctionField K).toNormalization) ∧
    IsFinite (Y.fromNormalizationIn K) ∧ Surjective (Y.fromNormalizationIn K) ∧
    (∀ x : Y.normalizationIn K, IsClosed ({x} : Set (Y.normalizationIn K)) →
      ringKrullDim ((Y.normalizationIn K).presheaf.stalk x) = 2 →
      IsClosed ({Y.fromNormalizationIn K x} : Set Y) ∧
      ringKrullDim (Y.presheaf.stalk (Y.fromNormalizationIn K x)) = 2 ∧
      ∀ (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
        (eR : R ≃+* Y.presheaf.stalk (Y.fromNormalizationIn K x))
        (eS : S ≃+* (Y.normalizationIn K).presheaf.stalk x),
      ∃ (hR : IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))
        (hS : IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))
        (hRD : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal R) R))
        (hSD : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S)),
        IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
        IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
        IsAdicComplete
          (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R))
          (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∧
        IsAdicComplete
          (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S))
          (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
        ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal S) S) = 2 ∧
        ∃ φ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+*
            AdicCompletion (IsLocalRing.maximalIdeal S) S,
          (∀ (n : ℕ) (a : AdicCompletion (IsLocalRing.maximalIdeal R) R) (r : R),
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n a =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n) r →
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n (φ a) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S) ^ n)
                (eS.symm ((Y.fromNormalizationIn K).stalkMap x (eR r)))) ∧
          φ.Finite ∧ Function.Injective φ ∧
          ∃ a : Algebra (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))
              (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)),
            (algebraMap
                (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))
                (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comp
              (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal R) R)
                (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))) =
              (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal S) S)
                (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comp φ ∧
            Module.Finite
              (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))
              (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) ∧
            Module.finrank
              (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))
              (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) ≤
                Module.finrank Y.functionField K) ∧
    (∀ (C D : Type u) [CommRing C] [CommRing D] [IsDomain C] [IsDomain D]
      [IsNoetherianRing C] [IsNoetherianRing D] [IsIntegrallyClosed C]
      [IsIntegrallyClosed D] [Algebra C D] [Module.Finite C D]
      [Algebra C Y.functionField] [IsFractionRing C Y.functionField]
      [Algebra D K] [IsFractionRing D K] [Algebra C K]
      [IsScalarTower C D K] [IsScalarTower C Y.functionField K]
      (f : Y ⟶ Spec (.of C)) [IsProper f],
      Y.fromSpecFunctionField ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap C Y.functionField)) →
      ∃ h : Y.normalizationIn K ⟶ Spec (.of D),
        IsProper h ∧
        h ≫ Spec.map (CommRingCat.ofHom (algebraMap C D)) = Y.fromNormalizationIn K ≫ f ∧
        (Y.fromSpecOfAlgebraFunctionField K).toNormalization ≫ h =
          Spec.map (CommRingCat.ofHom (algebraMap D K))) := by
  sorry

end AlgebraicGeometry
