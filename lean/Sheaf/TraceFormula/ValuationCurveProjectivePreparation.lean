/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.TraceFormula.ValuationHorizontalCurveModels
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.Compactification.NagataSketchClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import Sheaf.TraceFormula.ReducedFibreModification
import Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite

/-! # Normal projective preparation and locality for valuation curves

Source: Temkin, Stable modification of relative curves, Lemma 4.4.1, Lemma 4.2.1,
and the local reduction in Proposition 4.4.6
(blueprint: lem-trf-valuation-curve-projective-preparation).

The proposition-valued definitions below spell out the clauses of the statement.
Normalization uses Mathlib's actual relative integral-closure construction in the generic
fibre. Because that fibre is normal, this is the normalization in the product of component
function fields, including for reducible and empty curves. No normalization is chosen from
an existence assertion. The qcqs proofs needed to form it are conclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Temkin

/-- Normalization, its curve properties, and its universal factorization for normal
modification sources. Source: Temkin, Lemma 4.4.1(i) and Proposition 4.3.1
(blueprint: lem-trf-valuation-curve-projective-preparation). -/
def ValuationNormalizationPreparation (B : HorizontalValuationBase.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ B.T), RelativeCurve p →
    Smooth (pullback.snd p B.genericMap) →
    ∃ (_ : QuasiCompact (pullback.fst p B.genericMap))
      (_ : QuasiSeparated (pullback.fst p B.genericMap)),
      IsFinite (pullback.fst p B.genericMap).fromNormalization ∧
      EtaModification B.genericMap (pullback.fst p B.genericMap).fromNormalization p ∧
      (∀ z : (pullback.fst p B.genericMap).normalization,
        IsDomain ((pullback.fst p B.genericMap).normalization.presheaf.stalk z) ∧
        IsIntegrallyClosed ((pullback.fst p B.genericMap).normalization.presheaf.stalk z)) ∧
      RelativeCurve ((pullback.fst p B.genericMap).fromNormalization ≫ p) ∧
      GeometricallyReduced ((pullback.fst p B.genericMap).fromNormalization ≫ p) ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ X), EtaModification B.genericMap g p →
        (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) →
        ∃! a : Y ⟶ (pullback.fst p B.genericMap).normalization,
          a ≫ (pullback.fst p B.genericMap).fromNormalization = g

/-- Normal affine curves admit normal projective compactifications with reduced geometric
fibres. Projectivity is the recorded finite-projective-space convention.
Source: Temkin, Lemma 4.4.1(ii)
(blueprint: lem-trf-valuation-curve-projective-preparation). -/
def ValuationProjectivePreparation (B : HorizontalValuationBase.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ B.T), RelativeCurve p →
    Smooth (pullback.snd p B.genericMap) → IsAffine X →
    (∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∃ (C : Scheme.{u}) (c : C ⟶ B.T) (j : X ⟶ C),
      IsOpenImmersion j ∧ j ≫ c = p ∧ IsProjective c ∧ RelativeCurve c ∧
      GeometricallyReduced c ∧
      (∀ z : C, IsDomain (C.presheaf.stalk z) ∧ IsIntegrallyClosed (C.presheaf.stalk z))

/-- The finite modification locus, localization at a closed modification point, connected
normal affine preparation, identity extension, and restriction of intermediate diagrams.
The reduced closed immersion `l` fixes the scheme structure used for quasi-finiteness.
The locus is characterized by the failure of invertibility on every neighbourhood.
Source: Temkin, Lemma 4.2.1 and Proposition 4.4.6, local reduction
(blueprint: lem-trf-valuation-curve-projective-preparation). -/
def ValuationLocalPreparation (B : HorizontalValuationBase.{u}) : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ B.T) (f : Y ⟶ X),
    RelativeCurve p → RelativeCurve (f ≫ p) →
    Smooth (pullback.snd p B.genericMap) →
    Smooth (pullback.snd (f ≫ p) B.genericMap) →
    (∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) →
    (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) →
    EtaModification B.genericMap f p →
    ∃ (L : Scheme.{u}) (l : L ⟶ X), IsClosedImmersion l ∧ IsReduced L ∧
      Set.range l = {x | ∀ U : X.Opens, x ∈ U → ¬ IsIso (f ∣_ U)} ∧
      (Set.range l).Finite ∧ LocallyOfFiniteType (l ≫ p) ∧ QuasiCompact (l ≫ p) ∧
      (∀ t : B.T, Finite ((l ≫ p).fiber t)) ∧
      ∀ x : X, x ∈ Set.range l → IsClosed ({x} : Set X) →
        IsOpenImmersion
          (Spec.map (CommRingCat.ofHom
            (algebraMap B.V (Localization.AtPrime (p x).asIdeal)))) ∧
        ∃ (U : X.Opens) (_hx : x ∈ U)
          (v : U.toScheme ⟶ Spec (.of (Localization.AtPrime (p x).asIdeal)))
          (ηs : Spec (.of B.K) ⟶ Spec (.of (Localization.AtPrime (p x).asIdeal))),
          v ≫ Spec.map (CommRingCat.ofHom
            (algebraMap B.V (Localization.AtPrime (p x).asIdeal))) = U.ι ≫ p ∧
          ηs ≫ Spec.map (CommRingCat.ofHom
            (algebraMap B.V (Localization.AtPrime (p x).asIdeal))) = B.genericMap ∧
          IsAffine U.toScheme ∧ ConnectedSpace U.toScheme ∧ RelativeCurve v ∧
          (∀ z : U.toScheme, z.1 ∈ Set.range l →
            IsClosed ({z} : Set U.toScheme) → z.1 = x) ∧
          ∃ (C D : Scheme.{u})
            (c : C ⟶ Spec (.of (Localization.AtPrime (p x).asIdeal)))
            (j : U.toScheme ⟶ C) (g : D ⟶ C) (i : pullback f U.ι ⟶ D),
            IsOpenImmersion j ∧ j ≫ c = v ∧ IsProjective c ∧ RelativeCurve c ∧
            GeometricallyReduced c ∧
            (∀ z : C, IsDomain (C.presheaf.stalk z) ∧
              IsIntegrallyClosed (C.presheaf.stalk z)) ∧
            IsPullback i (pullback.snd f U.ι) g j ∧ IsOpenImmersion i ∧
            EtaModification ηs g c ∧ RelativeCurve (g ≫ c) ∧ IsProper (g ≫ c) ∧
            GeometricallyReduced (g ≫ c) ∧
            (∀ z : D, IsDomain (D.presheaf.stalk z) ∧
              IsIntegrallyClosed (D.presheaf.stalk z)) ∧
            (∀ O : C.Opens, Disjoint (O : Set C) (j '' (U.ι ⁻¹' Set.range l)) →
              IsIso (g ∣_ O)) ∧
            ∀ (Z : Scheme.{u}) (h : D ⟶ Z) (k : Z ⟶ C), h ≫ k = g →
              (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
                IsIntegrallyClosed (Z.presheaf.stalk z)) →
              EtaModification ηs h (k ≫ c) →
              EtaModification ηs k c →
              RelativeCurve (pullback.snd k j ≫ v) ∧
              (∀ z : pullback (C := Scheme) k j,
                IsDomain ((pullback k j).presheaf.stalk z) ∧
                IsIntegrallyClosed ((pullback k j).presheaf.stalk z)) ∧
              EtaModification ηs (pullback.snd k j) v ∧
              EtaModification ηs (pullback.snd h (pullback.fst k j))
                (pullback.fst k j ≫ k ≫ c)

/-- Compatible intermediate diagrams glue with the identity away from the prescribed
closed support. The cartesian square and equality involving `hU` fix the prescribed
identification on the overlap, rather than merely preserving the old isomorphism locus.
Source: Temkin, locality following Lemma 4.2.1 and Proposition 4.4.6, local reduction
(blueprint: lem-trf-valuation-curve-projective-preparation). -/
def ValuationGluingPreparation (B : HorizontalValuationBase.{u}) : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ B.T) (f : Y ⟶ X),
    RelativeCurve p → RelativeCurve (f ≫ p) →
    Smooth (pullback.snd p B.genericMap) →
    Smooth (pullback.snd (f ≫ p) B.genericMap) →
    (∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) →
    (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) →
    EtaModification B.genericMap f p →
    ∀ (U : X.Opens) (x : X) (W : Set X) (hW : IsClosed W),
      IsAffine U.toScheme → ConnectedSpace U.toScheme → IsClosed ({x} : Set X) →
      (∀ O : X.Opens, x ∈ O → ¬ IsIso (f ∣_ O)) →
      (∀ z : U.toScheme, (∀ O : X.Opens, z.1 ∈ O → ¬ IsIso (f ∣_ O)) →
        IsClosed ({z} : Set U.toScheme) → z.1 = x) →
      x ∈ W → W ⊆ U →
      QuasiCompact (Scheme.Opens.ι (⟨Wᶜ, hW.isOpen_compl⟩ : X.Opens)) →
      QuasiCompact (U.ι ⁻¹ᵁ (⟨Wᶜ, hW.isOpen_compl⟩ : X.Opens)).ι →
      ∀ (ZU : Scheme.{u}) (hU : pullback f U.ι ⟶ ZU) (kU : ZU ⟶ U.toScheme),
        hU ≫ kU = pullback.snd f U.ι →
        RelativeCurve (kU ≫ U.ι ≫ p) →
        (∀ z : ZU, IsDomain (ZU.presheaf.stalk z) ∧ IsIntegrallyClosed (ZU.presheaf.stalk z)) →
        EtaModification B.genericMap hU (kU ≫ U.ι ≫ p) →
        EtaModification B.genericMap kU (U.ι ≫ p) →
        IsIso (hU ∣_ (kU ⁻¹ᵁ (U.ι ⁻¹ᵁ (⟨Wᶜ, hW.isOpen_compl⟩ : X.Opens)))) →
        ∃ (Z : Scheme.{u}) (h : Y ⟶ Z) (k : Z ⟶ X) (j : ZU ⟶ Z),
          h ≫ k = f ∧ RelativeCurve (k ≫ p) ∧
          (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)) ∧
          EtaModification B.genericMap h (k ≫ p) ∧ EtaModification B.genericMap k p ∧
          IsPullback j kU k U.ι ∧ pullback.fst f U.ι ≫ h = hU ≫ j ∧
          IsIso (h ∣_ (k ⁻¹ᵁ (⟨Wᶜ, hW.isOpen_compl⟩ : X.Opens))) ∧
          (W ⊆ {z | z ⤳ x} →
            ∀ O : X.Opens, Disjoint (O : Set X) {z | z ⤳ x} →
              IsIso (h ∣_ (k ⁻¹ᵁ O)))

/-- Generic étale markings are carried by their actual flat schematic closures.
Uniqueness, restriction and the proper maps between compatible closures include the
markings in normalization, compactification, intermediate diagrams and compatible gluing.
Source: Temkin, §1.2, Lemma 3.5.1 and Proposition 4.4.6, local reduction
(blueprint: lem-trf-valuation-curve-projective-preparation). -/
def ValuationMarkingPreparation (B : HorizontalValuationBase.{u}) : Prop :=
  ∀ (Y : Scheme.{u}) (y : Y ⟶ B.T), RelativeCurve y →
    (∀ z : Y, IsDomain (Y.presheaf.stalk z) ∧ IsIntegrallyClosed (Y.presheaf.stalk z)) →
    ∀ (Eη : Scheme.{u}) (jη : Eη ⟶ pullback y B.genericMap),
      IsClosedImmersion jη → Etale (jη ≫ pullback.snd y B.genericMap) →
      QuasiCompact (jη ≫ pullback.snd y B.genericMap) →
      ∃ (E : Scheme.{u}) (e : E ⟶ Y), FlatClosure y B.genericMap jη e ∧
        ClosureRestrictionStable y (jη ≫ pullback.fst y B.genericMap) e ∧
        (∀ (F : Scheme.{u}) (a : F ⟶ Y), IsClosedImmersion a →
          Flat (a ≫ y) → a.ker.comap (pullback.fst y B.genericMap) = jη.ker →
          ∃! r : F ⟶ E, r ≫ e = a) ∧
        ∀ (Z : Scheme.{u}) (z : Z ⟶ B.T) (f : Z ⟶ Y) (hf : f ≫ y = z),
          RelativeCurve z →
          (∀ t : Z, IsDomain (Z.presheaf.stalk t) ∧ IsIntegrallyClosed (Z.presheaf.stalk t)) →
          EtaModification B.genericMap f y →
          ∀ (aη : Eη ⟶ pullback z B.genericMap),
            aη ≫ ((Over.pullback B.genericMap).map
              (Over.homMk f hf : Over.mk z ⟶ Over.mk y)).left = jη →
            ∀ (F : Scheme.{u}) (a : F ⟶ Z), FlatClosure z B.genericMap aη a →
              ∃! r : F ⟶ E, r ≫ e = a ≫ f ∧ EtaModification B.genericMap r (e ≫ y)

/-- The marking on a normal modification maps to the original marking, even when the
original curve is nonnormal. It is the closure of the inverse image of the actual generic
marking, and the compatible pair is an eta-modification on both parts.
Source: Temkin, §1.2 and Proposition 4.4.6, local reduction
(blueprint: lem-trf-valuation-curve-projective-preparation). -/
def ValuationMarkedModificationPreparation (B : HorizontalValuationBase.{u}) : Prop :=
  ∀ (P : MultipointedCurve B.T), Smooth (pullback.snd P.x B.genericMap) →
    Etale (pullback.snd P.d B.genericMap) →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ P.X), EtaModification B.genericMap q P.x →
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) →
      ∃ (hy : RelativeCurve (q ≫ P.x)) (E : Scheme.{u}) (e : E ⟶ Y)
        (he : FlatClosure (q ≫ P.x) B.genericMap (horizontalGenericMarkingι P B.genericMap q) e)
        (r : E ⟶ P.D) (hr : r ≫ P.d = e ≫ q ≫ P.x) (hi : r ≫ P.i = e ≫ q),
        (horizontalClosurePairMap P B.genericMap q e hy he r hr hi).IsEtaModification
          B.genericMap

/-- Normal projective preparation and compatible locality for valuation curves.
Source: Temkin, Stable modification of relative curves, Lemma 4.4.1(i),(ii),
Lemma 4.2.1 and Proposition 4.4.6, local reduction
(blueprint: lem-trf-valuation-curve-projective-preparation).

Proof plan (the twenty-three steps of the DAG node):
1. The ring $V$ and its localizations are normal domains. Indeed, if an integral element $b$ of
   the fraction field is outside a valuation ring, $b^{-1}$ lies in its maximal ideal; dividing a
   monic equation by its leading power gives $1$ in that maximal ideal. The base is affine,
   integral and qcqs. The generic point is a principal open: choose an element of the smallest
   nonzero prime, or use $T=\eta$ if $V$ is a field. Flatness gives $A\hookrightarrow A_K$ for
   every affine ring of $X$, by torsion-freeness and the localization base-change formula. Hence
   $X_\eta$ is schematically dense, $X$ is reduced because $X_\eta$ is reduced, and every nonempty
   affine open meets $X_\eta$. The empty curve satisfies the normalization assertions vacuously.
   Dependencies: lem-sc-flat-invertible-sections-torsion-free, lem-weil-pbc-localization-base-
   change, sbc-lem-smooth-geometrically-reduced.
2. For nonempty $X$, apply the reduced-fibre modification theorem to $X\to T$. It is dominant by
   the preceding injectivity, finitely presented by hypothesis, and has geometrically reduced
   generic fibre by smoothness. Obtain $r:T'\to T$ and a finite generic-fibre isomorphism $Q'\to
   X\times_TT'$ with $Q'/T'$ flat finitely presented and with reduced geometric fibres. The
   generic field of $T'$ is a finite separable extension of $K$, hence is $K$. The proper
   valuative criterion extends this generic section to $\sigma:T\to T'$. Pulling back along
   $\sigma$ gives a finite map $q:Q\to X$, an isomorphism over $X_\eta$, with $Q/T$ flat finitely
   presented and geometrically reduced fibres. Flatness is preserved by tensor base change, finite
   presentation and geometric reducedness by the cited base-change statements. Dependencies: lem-
   trf-reduced-fibre-modification, def-kun-separably-closed, lemma-nagata-proper-valuative-
   criterion-existence-api, lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-qcqs-morphism-
   permanence, lem-pc-relatively-flat-module-pullback, lem-trf-geometric-reduced-fibre-locus-base-
   change.
3. Apply generic normality of geometrically reduced families to $Q/T$. It is reduced and every
   finite $\eta$-modification of $Q$ is an isomorphism. Its generic fibre is normal by smoothness.
   The same theorem applies separately to every affine open of $Q$: restriction preserves flatness
   and reduced geometric fibres; affine source and base give qcqs, so the locally finitely
   presented restriction is finitely presented. On an affine open $\operatorname{Spec}B\subset Q$,
   flatness gives $B\hookrightarrow B_K$. The smooth affine generic fibre is Noetherian, so has
   finitely many irreducible components; normal local rings are domains, so two such components
   cannot meet (at a common point their distinct minimal primes would give distinct minimal primes
   of the local ring). Thus these finitely many components are disjoint open-and-closed integral
   normal schemes and $B_K$ is a finite product of normal domains. Dependencies: lem-trf-
   geometrically-reduced-eta-normal, lem-sc-smooth-normal, lem-sc-flat-invertible-sections-
   torsion-free, lem-weil-pbc-localization-base-change, lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-finite-components, lem-weil-pbc-qcqs-morphism-permanence.
4. Each component idempotent $e\in B_K$ satisfies $e^2-e=0$. Consequently $B[e]$ is finite over
   $B$ and is a subalgebra of $B_K$. It agrees with $B$ after inverting one nonzero element $a\in
   V$. Multiplication by $a$ is injective in both rings, so $D(a)$ is schematically dense on both
   spectra. The finite map is proper and is a finite $\eta$-modification. The preceding
   $\eta$-normality makes it an isomorphism. Hence all these idempotents lie in $B$, which
   therefore decomposes as a finite product $\prod_iB_i$ of domains with $(B_i)_K$ normal domains.
   Dependencies: lem-weil-pbc-finite-proper, lem-trf-geometrically-reduced-eta-normal.
5. If $b\in\operatorname{Frac}(B_i)$ is integral over $B_i$, it is integral over the normal domain
   $(B_i)_K$, whose fraction field is the same, and therefore belongs to $(B_i)_K$. Write $b=c/a$
   with $c\in B_i$ and $a\in V\setminus0$. The finite algebra $B_i[b]$ is a subring of this
   fraction field and equals $B_i$ over $D(a)$; as above it defines a finite $\eta$-modification
   of the open-and-closed component. Extend it by the identity on the other components to apply
   the $\eta$-normality of $\operatorname{Spec}B$. Thus $b\in B_i$. Integral closure commutes with
   localization, so every local ring of $B$ is an integrally closed domain. This proves $Q$
   normal. The argument of these two steps uses only normality of $Q_\eta$, not smoothness.
   Dependencies: lem-weil-pbc-finite-proper, lem-weil-pbc-integral-closure-commutes-localization,
   lem-trf-geometrically-reduced-eta-normal.
6. On an affine open $\operatorname{Spec}A\subset X$ the finite preimage is
   $\operatorname{Spec}B$. The generic isomorphism identifies both algebras inside the product of
   the function fields of the generic components. The algebra $B$ is integral over $A$, hence
   contained in its integral closure. Conversely any element of that product integral over $A$ is
   integral over $B$ and belongs to $B$, since the normal factors of $B$ are integrally closed.
   Thus $B$ is exactly the integral closure of $A$. The identifications agree on localizations, so
   $Q=X^\nu$ with the normalization convention in the statement. The map is finite proper,
   generically an isomorphism between schematically dense opens. Its source is flat finitely
   presented; its generic fibre has pure dimension one, so the dense-generic-fibre dimension
   theorem gives the same purity on all fibres. This proves the normalization clause, including
   geometrically reduced fibres. Dependencies: lem-weil-pbc-finite-algebra-is-integral, lem-weil-
   pbc-integral-closure-commutes-localization, def-sc-normalization, lem-weil-pbc-finite-proper,
   lem-trf-flat-dense-generic-fibre-pure-dimension.
7. For a normal modification source $Y$, there are finitely many components, by the horizontal
   curve-model statement with empty marking. They are disjoint open and closed: every local ring
   is a domain and a point cannot lie on two of finitely many components. Each component maps
   dominantly to the corresponding reduced component of $X$; the defining ideal of that reduced
   component pulls back to zero because it vanishes on the dense generic fibre and $Y$ is reduced.
   Apply the dominant normalization lifting theorem on each component. The componentwise
   normalizations form $X^\nu$, so the lifts give $Y\to X^\nu$. Uniqueness follows componentwise
   from the same theorem, or from schematic density and separatedness of the finite map $X^\nu\to
   X$. Dependencies: lem-trf-valuation-horizontal-curve-models, lem-sbc-normalization-dominant-
   lift, sk-lem-nagata-sketch-closure.
8. Now let $X$ be normal affine. For empty $X$, use the empty closed subscheme of $\mathbf P^0_T$
   as its compactification. Otherwise choose finitely many generators of its finite-type
   $V$-algebra to embed it as a closed subscheme of $\mathbf A^n_T$. Take its schematic closure
   $C'\subset\mathbf P^n_T$. The schematic-image theorem gives a schematically dense open
   immersion $X\hookrightarrow C'$. On each standard affine chart, the closure ring injects into
   the ring of sections on its intersection with $X$ and then into the generic-fibre sections.
   Hence it is $V$-torsion-free, and is flat over $V$. It is a finite-type $V$-algebra. Apply the
   finite-type module presentation theorem to this algebra as a cyclic module over a polynomial
   $V$-algebra: its kernel ideal is finitely generated, so the chart algebra is finitely presented
   over $V$. Thus $C'/T$ is flat finitely presented and projective. Dependencies: sk-lem-nagata-
   sketch-closure, lem-trf-valuation-torsionfree-flat, lem-trf-valuation-finite-type-module-
   presentation.
9. The generic closure $C'_\eta$ is reduced and has the same generic function fields as $X_\eta$.
   After any field extension each affine chart ring injects into the product of the corresponding
   generic function fields after scalar extension; these are reduced because they are
   localizations of the geometrically reduced $X_\eta$. Scalar extension preserves the injection.
   Thus $C'_\eta$ is geometrically reduced and pure one-dimensional. The dense-generic-fibre
   dimension theorem makes $C'$ a $T$-curve. Its generic fibre need not be normal at the boundary:
   this is why one must normalize the generic closure before invoking the normality argument
   above. Dependencies: lem-trf-flat-dense-generic-fibre-pure-dimension.
10. Let $N_\eta\to C'_\eta$ be the normalization of the projective generic curve. It is finite,
   normal and projective by projective-curve normalization; it is an isomorphism on the normal
   open $X_\eta$. The same injection into the scalar-extended generic function fields shows that
   $N_\eta$ is geometrically reduced. On the quasi-compact open $O=X\cup C'_\eta\subset C'$ glue
   $X$ and $N_\eta$ along their identified opens $X_\eta$. Scheme gluing and morphism gluing
   produce a finite morphism $F\to O$: on the two target opens it is respectively the identity and
   the finite normalization. Finiteness is affine-local on the target, directly by gluing the
   finite algebra sheaves. It is separated and quasi-finite. Dependencies: lem-weil-pbc-
   normalization-projective-components, lem-weil-pbc-reduced-algebraic-normalization-field-change,
   lem-weil-pbc-glue-schemes, lem-weil-pbc-scheme-morphism-gluing, def-weil-finite-integral-
   morphism.
11. The composite $F\to C'$ is separated quasi-finite and of finite type: $O\to C'$ is a quasi-
   compact open immersion and $F\to O$ is finite. Apply Zariski main to embed $F$ as a quasi-
   compact open in a finite $C'$-scheme $H$. Take the schematic closure $E$ of $F$ in $H$. Over
   $O$, the immersion $F\to H_O$ is proper: its graph is closed because $H_O/O$ is separated, and
   projection from $F\times_OH_O$ is the base change of the finite map $F\to O$. Hence it is a
   closed immersion. It follows that $E_O=F$, since the schematic closure restricts to the
   original closed subscheme there. The scheme $E$ is finite over $C'$ and has dense generic fibre
   $N_\eta$. Dependencies: thm-pqf-zmt-factorization, sk-lem-nagata-sketch-closure, lem-weil-pbc-
   proper-immersion-closed, lem-weil-pbc-closed-immersion-proper, lem-weil-pbc-proper-base-change,
   lem-weil-pbc-proper-composition.
12. The generic fibre is schematically dense in $E$: it is so in $F$ (locally this is $X$ or
   $N_\eta$), and $F$ is schematically dense in $E$. Therefore each affine ring of $E$ injects
   into its generic localization and is torsion-free over $V$. The torsion-free flatness theorem
   and the cyclic-polynomial-module argument of the closure step show that $E/T$ is flat and
   finitely presented. Its generic fibre is normal and geometrically reduced. Apply the reduced-
   fibre modification theorem to $E/T$, eliminate the separable base alteration with the proper
   valuative section as before, and obtain a finite $\eta$-modification $\bar X\to E$ with flat
   finitely presented source and geometrically reduced fibres. The idempotent and integral-element
   arguments above, now using normal $N_\eta$, show that $\bar X$ is normal. The dimension theorem
   makes it a $T$-curve. Dependencies: lem-trf-valuation-torsionfree-flat, lem-trf-valuation-
   finite-type-module-presentation, lem-trf-reduced-fibre-modification, def-kun-separably-closed,
   lemma-nagata-proper-valuative-criterion-existence-api, lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-qcqs-morphism-permanence, lem-pc-relatively-flat-module-pullback, lem-trf-
   geometric-reduced-fibre-locus-base-change, lem-trf-geometrically-reduced-eta-normal, lem-trf-
   flat-dense-generic-fibre-pure-dimension.
13. The map $\bar X\to C'$ is finite, and over the normal open $X$ it is an isomorphism. Indeed,
   componentwise this is a finite birational map onto a normal integral scheme, so the finite
   birational normal-target theorem applies. For projectivity, the finite map is projective in the
   projective-bundle convention. The projective scheme $C'$ over the affine base has an ample
   invertible sheaf; the projective-bundle-to-H-projective theorem therefore gives a closed
   immersion of $\bar X$ into a finite projective space over $C'$. Composing H-projective
   morphisms gives the required closed immersion into some $\mathbf P^m_T$. This uses no
   Noetherian hypothesis on $V$. Dependencies: lem-trf-finite-birational-normal-iso, lem-trf-
   finite-projective-bundle, lem-weil-pbc-projective-ample-invertible, lem-trf-projective-bundle-
   to-h-projective, lem-trf-h-projective-composition.
14. For $f:Y\to X$ between normal curves, the horizontal curve-model theorem gives finitely many
   components of $X$. Apply the modification-locus theorem: its locus $L$ is quasi-finite over
   $T$. Since $T$ has finitely many points and every fibre of $L/T$ is finite, the set $|L|$ is
   finite. Give it its reduced closed structure. The locus has no point over $\eta$ because
   $f_\eta$ is an isomorphism. Dependencies: lem-trf-valuation-horizontal-curve-models, lem-trf-
   modification-fibre-centre-finite.
15. Let $x$ be closed in $L$ and let $s\in T$ be its image. It is closed in $X$ since $L$ is
   closed. The localization $\operatorname{Spec}V_s$ is an open of $T$: if there is a prime
   immediately above $s$, choose $a$ in it and outside $s$, giving $D(a)=\{t:t\text{ generalizes
   }s\}$; if $s$ is maximal use $D(1)$. Thus localization does not require spreading across an
   inverse limit. In the finite $T_0$-space $L$, the set of generalizations of $x$ is open
   (intersect all its finitely many open neighbourhoods). Realize it as $L\cap U_0$ for an open
   $U_0$ of $X$. Choose a connected affine neighbourhood $U$ of $x$ inside
   $U_0\times_T\operatorname{Spec}V_s$. Such a choice is possible because the finitely many normal
   components of $X$ are disjoint open and closed. Then $L_U$ has $x$ as its unique closed point.
   Dependencies: .
16. Over the localized base, $L_U$ is finite, not merely a finite topological set. To check this,
   the normal integral local scheme $\operatorname{Spec}V_s$ has separably closed function field
   $K$, so its local ring is strictly henselian by the etale-over-normal theorem. The separated
   quasi-finite affine scheme $L_U$ embeds openly in a finite scheme by Zariski main. A finite
   algebra over this henselian local ring splits as a product of local finite algebras. The closed
   point $x$ lies in one factor. An open containing the closed point of a local scheme is the
   entire factor. No point of another factor belongs to $L_U$, since the finite space $L_U$ has
   only one closed point and every point specializes to one. Therefore $L_U$ is that finite
   factor. Dependencies: sbc-lem-etale-over-normal, thm-pqf-zmt-factorization, lem-weil-pbc-
   finite-over-henselian-local-product.
17. Compactify the normal affine curve $U$ by the preceding construction over $V_s$, obtaining
   normal projective $\bar X$. The finite scheme $L_U$ over this base is closed in $\bar X$: its
   map has closed graph in $L_U\times_T\bar X$, since $\bar X/T$ is separated, and the projection
   to $\bar X$ is proper as a base change of $L_U/T$. Thus this map is proper and its image is
   closed. This justifies using $\bar X\setminus L_U$ as an open chart; finiteness of the set
   alone would not justify that step. Dependencies: lem-weil-pbc-finite-proper, lem-weil-pbc-
   closed-immersion-proper, lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition.
18. Over $U\setminus L_U$ the map $f$ is the identity. Glue $Y_U$ to $\bar X\setminus L_U$ along
   this identification. Scheme gluing gives $\bar Y$, and morphism gluing gives $\bar f:\bar
   Y\to\bar X$. On the target cover $U,\bar X\setminus L_U$, the map is respectively the proper
   map $f_U$ and an identity. Thus it is proper by target locality; it is a generic-fibre
   isomorphism. The two charts are normal. The original normal $Y$ has geometrically reduced
   fibres by the normalization result proved above (its normalization is the identity), and the
   other chart inherits this property from $\bar X$. Flatness, local finite presentation and fibre
   purity are chart-local. The cover and its overlap are quasi-compact by the finite-algebra
   calculation in the next step, applied also in the finitely many affine charts of $\bar X$.
   Consequently the glued scheme is qcqs and finitely presented. It is a normal proper $T$-curve
   with geometrically reduced fibres, agreeing with $f$ near $f^{-1}(x)$. Dependencies: lem-weil-
   pbc-glue-schemes, lem-weil-pbc-scheme-morphism-gluing, lemma-nagata-projective-target-local,
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence.
19. For completeness, let $U=\operatorname{Spec}A$ and $J$ define the finite subscheme $L_U$.
   Choose finite $V$-algebra generators $t_1,\ldots,t_n$ of $A$. Their images in the finite
   $V$-algebra $A/J$ satisfy monic equations $p_i$. Thus $I=(p_i(t_i))\subset J$ and $A/I$ is a
   finite $V$-module, generated by the monomials with each exponent below the degree of $p_i$. The
   finite scheme $H=V(I)$ has finitely many points, because $T$ is finite and its fibres are
   finite. The open $H\setminus L_U$ is therefore quasi-compact and is covered by finitely many
   $D(g_j)\cap H$ with $g_j\in J$. Now $$U\setminus L_U=\bigcup_iD(p_i(t_i))\ \cup\
   \bigcup_jD(g_j).$$ This finite basic-open cover proves the required quasi-compactness. The
   calculation works on every affine chart containing part of a finite closed subscheme.
   Dependencies: lem-weil-pbc-finite-algebra-is-integral.
20. Any intermediate diagram of normal $\eta$-modifications of $\bar f$ restricts to $U$ by taking
   fibre products. Properness survives base change; the generic-fibre isomorphisms, flatness,
   finite presentation and geometric fibre properties restrict to opens. Schematic density
   restricts as injectivity of the restricted structure-sheaf map. Normality is local. Thus the
   restricted diagram is the asserted original local intermediate diagram. Dependencies: lem-weil-
   pbc-proper-base-change, lem-weil-pbc-qcqs-morphism-permanence.
21. For the corrected global locality assertion, put $B=X\setminus W$. On $U\cap B=U\setminus W$,
   the given isomorphism $h_U$ identifies $(Z_U,k_U)$ with $(Y_U,f_U)$. Glue $Z_U$ and $Y_B$ using
   exactly this isomorphism, and glue their maps to $X$. Also glue $h_U$ and the identity of
   $Y_B$. The two-chart cocycle is just the chosen isomorphism and its inverse; both resulting
   compositions agree with $f$ on each chart, hence agree globally. This produces $Y\xrightarrow h
   Z\xrightarrow k X$ with $kh=f$. The explicit quasi-compact overlap assumptions give qcqs gluing
   and finite presentation. Its charts are normal flat finitely presented curves. Properness of
   $k$ is target-local on $U,B$, and properness of $h$ is target-local on the corresponding charts
   of $Z$. The generic fibres are identities between dense generic opens, so both maps are
   $\eta$-modifications. By construction $h$ is the identity over $B$, and restriction near $x$
   recovers the prescribed local diagram. Dependencies: lem-weil-pbc-glue-schemes, lem-weil-pbc-
   scheme-morphism-gluing, lemma-nagata-projective-target-local, lem-weil-pbc-qcqs-morphism-
   permanence.
22. For the multipointed assertion, $D_\eta$ is finite etale over the separably closed field $K$,
   hence is a finite disjoint union of $K$-points. Each point extends uniquely to a section of the
   proper curve $\bar X$ by the proper separated valuative criterion. These sections are closed
   immersions since $\bar X/T$ is separated. Their schematic union is the closure of $D_\eta$: its
   local rings inject into products of the section rings and have no $V$-torsion. It is therefore
   flat by the valuation torsion-free criterion. It is proper as a closed subscheme of $\bar X$,
   of finite type, and has finite fibres (its support is the union of finitely many sections).
   Thus it is quasi-finite, and proper quasi-finite implies finite. On its affine coordinate ring
   apply the cyclic-polynomial-module finite-presentation argument used above. Its generic fibre
   is pure dimension zero, so the dense-generic-fibre dimension theorem gives pure relative
   dimension zero. Dependencies: def-kun-separably-closed, lemma-nagata-proper-separated-
   valuation-extension, lem-trf-valuation-torsionfree-flat, lem-weil-pbc-closed-immersion-proper,
   pqf-lem-qf-finitefibres, cor-pqf-proper-quasifinite-finite, lem-trf-valuation-finite-type-
   module-presentation, lem-trf-flat-dense-generic-fibre-pure-dimension, lem-weil-pbc-etale-fibre-
   discrete-separable-points.
23. Schematic generic closures are unique among flat closed subschemes: on an affine chart a flat
   quotient injects into its generic localization, so its ideal is the kernel of generic
   restriction. On every proper intermediate curve repeat the section-closure argument of the
   preceding step; it requires properness, not smoothness at the generic boundary. A map between
   these proper models sends the source marking into the target marking because the target ideal
   vanishes on the schematically dense generic marking. The induced marking map is proper: both
   markings are finite over $T$ and the target is separated, so use the closed graph and proper
   projection argument. It is generically an isomorphism. On models over the original smooth-
   generic open, the horizontal curve-model theorem gives the flat finitely presented marking and
   its proper modification maps. The uniqueness calculation identifies all these closures on the
   quasi-compact gluing overlaps. Gluing them supplies the multipointed diagrams. Empty marking
   stays empty. Dependencies: lem-trf-valuation-horizontal-curve-models, lem-weil-pbc-closed-
   immersion-proper, lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition.
-/
theorem valuation_curve_projective_preparation (B : HorizontalValuationBase.{u}) :
    ValuationNormalizationPreparation B ∧ ValuationProjectivePreparation B ∧
    ValuationLocalPreparation B ∧ ValuationGluingPreparation B ∧ ValuationMarkingPreparation B ∧
    ValuationMarkedModificationPreparation B := by
  sorry

end AlgebraicGeometry.Temkin
