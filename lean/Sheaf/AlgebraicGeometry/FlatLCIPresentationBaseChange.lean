/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.LciCotangentPresentation
public import Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.RingTheory.RelativeRegularEquationsBaseChange
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Regular presentations and their intrinsic determinant after base change

Source: Stacks Project, Tags 0FUD, 0CEP, 08QQ and 0FJY
(blueprint: lem-trf-flat-lci-presentation-base-change).

The presentation, tensor pullback, conormal, exterior powers, intrinsic cotangent
construction and determinant functor are the existing dependency constructions.
The records below retain their comparison maps and their normalizations together;
no choice of an unspecified line or of an arbitrary scalar comparison is made.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open Algebra.CotangentResolution AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local irreducible] CotangentPresentation.System.model

variable [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The two-term model of a given regular presentation, retaining its actual terms,
ranks, conormal differential and globally specified intrinsic comparison.
Source: Stacks, Tags 08SL and 0FJX
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
structure FlatLCIIntrinsicChart {C₀ : Coherence.{u}} (D : CotangentPresentation.System C₀)
    (F : CotangentPresentation.AffineIdentifications D) (κ : Naive.Comparison C₀)
    (E : CotangentPresentation.LciIdentifications D F κ)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (U : X.Opens)
    (C : FlatLCIPresentation f d U) where
  koszul : CotangentPresentation.IsKoszulImmersion C.i
  conormal_free : C.conormal.IsFiniteLocallyFreeOfRank C.c
  differentials_free : C.differentials.IsFiniteLocallyFreeOfRank C.n
  differential : C.conormal ⟶ C.differentials
  differential_normal : C.IsConormalDifferential differential

/-- The existing geometric lci presentation with the same ambient chart and equations.
Source: Stacks, Tags 08SJ and 08SL
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
def FlatLCIIntrinsicChart.presentation {C₀ : Coherence.{u}}
    {D : CotangentPresentation.System C₀} {F : CotangentPresentation.AffineIdentifications D}
    {κ : Naive.Comparison C₀} {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation f d U} (A : FlatLCIIntrinsicChart D F κ E f d U C) :
    CotangentPresentation.LciPresentation C.i (C.ambient ≫ pullback.fst _ _) :=
  ⟨C.n, C.ambient, C.closed, C.ambient_open, rfl, A.koszul⟩

/-- The actual double complex with terms `I/I²` and restricted ambient differentials.
Source: Stacks, Tags 08SL and 0FJX
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
def FlatLCIIntrinsicChart.model {C₀ : Coherence.{u}}
    {D : CotangentPresentation.System C₀} {F : CotangentPresentation.AffineIdentifications D}
    {κ : Naive.Comparison C₀} {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation f d U} (A : FlatLCIIntrinsicChart D F κ E f d U C) :
    TwoTermDeterminantModel U.toScheme :=
  ⟨C.conormal, C.differentials, A.differential, C.c, C.n,
    A.conormal_free, A.differentials_free⟩

/-- The section-normalized square comparing the local family with the global family.
The factorization in the presentation supplies its commutativity.
Source: Stacks, Tags 08QL and 08SL
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
def FlatLCIPresentation.intrinsicSquare {C₀ : Coherence.{u}}
    (D : CotangentPresentation.System C₀) {X S : Scheme.{u}} {f : X ⟶ S}
    {d : ℕ} {U : X.Opens} (C : FlatLCIPresentation f d U) :
    CotangentPresentation.BaseSquare f (C.i ≫ C.ambient ≫ pullback.fst _ _) U.ι (𝟙 S) :=
  D.square f (C.i ≫ C.ambient ≫ pullback.fst _ _) U.ι (𝟙 S)
    (by simpa only [Category.comp_id] using C.factor.symm)

/-- A chart comparison uses the specified global conormal identification of the
cotangent dependency, rather than a new derived isomorphism fixed only on affines.
The bridge is the identity on both actual conormal and differential terms.
Source: Stacks, Tags 08SL, 08QQ and 0FJX
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
structure FlatLCIIntrinsicChart.Comparison {C₀ : Coherence.{u}}
    {D : CotangentPresentation.System C₀} {F : CotangentPresentation.AffineIdentifications D}
    {κ : Naive.Comparison C₀} {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation f d U} (A : FlatLCIIntrinsicChart D F κ E f d U C) where
  bridge : A.model.complex ≅
    (E.identification C.i (C.ambient ≫ pullback.fst _ _) A.presentation).model.complex
  negative :
    (HomologicalComplex.doubleXIso₀ A.differential (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).inv ≫ bridge.hom.f (-1) ≫
        (E.identification C.i (C.ambient ≫ pullback.fst _ _)
          A.presentation).model.negative.hom = 𝟙 C.conormal
  zero :
    (HomologicalComplex.doubleXIso₁ A.differential (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide) (by decide)).inv ≫ bridge.hom.f 0 ≫
        (E.identification C.i (C.ambient ≫ pullback.fst _ _)
          A.presentation).model.zero.hom = 𝟙 C.differentials
  restriction :
    CotangentPresentation.cotangent (D.model (C.i ≫ C.ambient ≫ pullback.fst _ _)) ≅
      (derivedPullback U.ι).obj (CotangentPresentation.cotangent (D.model f))
  restriction_inv : restriction.inv =
    CotangentPresentation.derivedChange D (C.intrinsicSquare D)

/-- The intrinsic comparison of the displayed two-term model with the restricted
cotangent complex, assembled from the fixed conormal and open-restriction arrows.
Source: Stacks, Tags 08SL and 08QQ
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
def FlatLCIIntrinsicChart.Comparison.iso {C₀ : Coherence.{u}}
    {D : CotangentPresentation.System C₀} {F : CotangentPresentation.AffineIdentifications D}
    {κ : Naive.Comparison C₀} {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation f d U} {A : FlatLCIIntrinsicChart D F κ E f d U C}
    (a : A.Comparison) :
    DerivedCategory.Q.{w}.obj A.model.complex ≅
      (derivedPullback U.ι).obj (CotangentPresentation.cotangent (D.model f)) :=
  DerivedCategory.Q.mapIso a.bridge ≪≫
    (E.identification C.i (C.ambient ≫ pullback.fst _ _) A.presentation).iso ≪≫ a.restriction

/-- The determinant system is identified with the determinant of the intrinsic
cotangent complex on every base change. Its maps are the canonical determinant of
`derivedChange`, and its charts are fixed by the same global conormal comparisons.
Identity and composition are the fields of the reused `FlatLCIAdjunctionSystem`.
Source: Stacks, Tags 08QQ and 0FJY
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
structure FlatLCIIntrinsicDeterminantData {C₀ : Coherence.{u}}
    (D : CotangentPresentation.System C₀) (F : CotangentPresentation.AffineIdentifications D)
    (κ : Naive.Comparison C₀) (E : CotangentPresentation.LciIdentifications D F κ)
    (T : TwoTermPerfectDeterminantData.{u, w}) {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) where
  twoTerm : ∀ B : FlatLCIBaseChange f,
    isTwoTermPerfect B.X' (CotangentPresentation.cotangent (D.model B.p'))
  system : FlatLCIAdjunctionSystem f d
  intrinsic : ∀ B : FlatLCIBaseChange f,
    system.line B ≅ twoTermDeterminantValue (T.functor B.X')
      (CotangentPresentation.cotangent (D.model B.p')) (twoTerm B)
  chart : ∀ (B : FlatLCIBaseChange f) (U : B.X'.Opens) (C : FlatLCIPresentation B.p' d U),
    FlatLCIIntrinsicChart D F κ E B.p' d U C
  comparison : ∀ (B : FlatLCIBaseChange f) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' d U), (chart B U C).Comparison
  local_normal : ∀ (B : FlatLCIBaseChange f) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' d U),
    (system.localIso B U C).hom ≫ (tensorPullback U.ι).map (intrinsic B).hom =
      (T.modelIso (chart B U C).model).inv ≫
        (twoTermDeterminantIso (T.functor U.toScheme) (T.model_mem (chart B U C).model)
          (T.pullback_mem U.ι _ (twoTerm B)) (comparison B U C).iso).hom ≫
            (T.pullbackIso U.ι _ (twoTerm B)).inv
  baseIso : ∀ (B B' : FlatLCIBaseChange f) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (_hc : IsPullback g B'.p' B.p' b),
    (derivedPullback g).obj (CotangentPresentation.cotangent (D.model B.p')) ≅
      CotangentPresentation.cotangent (D.model B'.p')
  base_normal : ∀ (B B' : FlatLCIBaseChange f) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (hc : IsPullback g B'.p' B.p' b),
    (baseIso B B' g b hc).hom =
      CotangentPresentation.derivedChange D (D.square B.p' B'.p' g b hc.w)
  base_determinant : ∀ (B B' : FlatLCIBaseChange f) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (hc : IsPullback g B'.p' B.p' b) (hg : g ≫ B.g = B'.g) (hb : b ≫ B.b = B'.b),
    (system.baseChange B B' g b hc hg hb).hom ≫ (intrinsic B').hom =
      (tensorPullback g).map (intrinsic B).hom ≫
        (T.pullbackIso g _ (twoTerm B)).hom ≫
          (twoTermDeterminantIso (T.functor B'.X')
            (T.pullback_mem g _ (twoTerm B)) (twoTerm B') (baseIso B B' g b hc)).hom

/-- The complete equation-level assertion on a pulled-back affine ambient chart.
The hypothesis is regularity at the original closed locus. The conclusion gives
regularity at the new closed locus, the pulled-back ideal, and Koszul exactness on
the whole chart, including its complement of the closed subscheme.
Source: Stacks, Tags 0FUD, 0CEP and 062F
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
def FlatLCIPresentation.RegularEquationsBaseChange {X S : Scheme.{u}} {f : X ⟶ S}
    {d : ℕ} {U : X.Opens} (C : FlatLCIPresentation f d U) : Prop :=
  ∀ (S' U' P' : Scheme.{u}) (i' : U' ⟶ P') (p' : P' ⟶ S')
    (g : U' ⟶ U.toScheme) (q : P' ⟶ C.P) (b : S' ⟶ S),
    IsPullback g i' C.i q →
    IsPullback q p' (C.ambient ≫ pullback.fst _ _) b →
    ∀ (W : C.P.affineOpens) (a : Fin C.c → Γ(C.P, W.1)),
      Ideal.span (Set.range a) = C.i.ker.ideal W →
      (∀ z : PrimeSpectrum Γ(C.P, W.1), C.i.ker.ideal W ≤ z.asIdeal →
        RingTheory.Sequence.IsRegular (Localization.AtPrime z.asIdeal)
          (List.ofFn fun j ↦ algebraMap Γ(C.P, W.1) (Localization.AtPrime z.asIdeal) (a j))) →
    ∀ (W' : P'.affineOpens) (e : W'.1 ≤ q ⁻¹ᵁ W.1),
      Ideal.span (Set.range fun j ↦ q.appLE W.1 W'.1 e (a j)) = i'.ker.ideal W' ∧
      RingTheory.Sequence.IsKoszulRegular (fun j ↦ q.appLE W.1 W'.1 e (a j)) ∧
      ∀ z : PrimeSpectrum Γ(P', W'.1), i'.ker.ideal W' ≤ z.asIdeal →
        RingTheory.Sequence.IsRegular (Localization.AtPrime z.asIdeal)
          (List.ofFn fun j ↦ algebraMap Γ(P', W'.1) (Localization.AtPrime z.asIdeal)
            (q.appLE W.1 W'.1 e (a j)))

/-- The local base-change line map is the pure-wedge tensor/exterior/dual map of
the specified conormal and differential isomorphisms. The transition equation uses
these same local maps and the transitions through the single intrinsic determinant
line, so it applies to unrelated presentations as well as ambient refinements.
Source: Stacks, Tags 08QQ and 0FJY
(blueprint: lem-trf-flat-lci-presentation-base-change). -/
def FlatLCIIntrinsicDeterminantData.LocalCompatibility {C₀ : Coherence.{u}}
    {D : CotangentPresentation.System C₀} {F : CotangentPresentation.AffineIdentifications D}
    {κ : Naive.Comparison C₀} {E : CotangentPresentation.LciIdentifications D F κ}
    {T : TwoTermPerfectDeterminantData.{u, w}} {X S : Scheme.{u}}
    {f : X ⟶ S} {d : ℕ} (J : FlatLCIIntrinsicDeterminantData D F κ E T f d) : Prop :=
  ∀ (B B' : FlatLCIBaseChange f) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (hc : IsPullback g B'.p' B.p' b) (hg : g ≫ B.g = B'.g) (hb : b ≫ B.b = B'.b)
    (U : B.X'.Opens) (V : B'.X'.Opens)
    (C : FlatLCIPresentation B.p' d U) (C' : FlatLCIPresentation B'.p' d V)
    (h : V.toScheme ⟶ U.toScheme) (q : C'.P ⟶ C.P),
    h ≫ U.ι = V.ι ≫ g →
    IsPullback h C'.i C.i q →
    IsPullback q (C'.ambient ≫ pullback.fst _ _) (C.ambient ≫ pullback.fst _ _) b →
    ∀ (ha : C.c = C'.c) (hn : C.n = C'.n),
    ∃ (r : FlatLCIPresentationPullback C C') (hw : r.h ≫ U.ι = V.ι ≫ g),
      r.h = h ∧ r.q = q ∧ r.k = b ∧
      IsFlatLCIPullbackDeterminantComparison r.h C.conormal C.differentials
        C'.conormal C'.differentials C.c C'.c C.n C'.n ha hn
        r.conormalMap r.differentialsMap
        (J.system.localBaseChange B B' g b hc hg hb U V C C' r hw)

/-- Regular presentations and the determinant of the intrinsic cotangent complex
commute with arbitrary base change, with the stated local generator normalizations.
No Noetherian condition is imposed on a changed base. Construction data for the
standard cotangent resolution and the canonical determinant are explicit parameters;
their recorded existence theorems supply them without geometric assumptions.
Source: Stacks Project, Tags 0FUD, 0CEP, 08QQ and 0FJY
(blueprint: lem-trf-flat-lci-presentation-base-change).

Proof (the eight steps of the node):
1. On a principal ambient affine chart A=R[x_1,...,x_n]_h, put B=A/(f).
The affine flatness criterion, polynomial flatness and localization give R-flatness
of A and B. A is finitely presented by adjoining t with ht=1. The canonical
quotient-tensor isomorphism describes the new closed chart and its equations
(lem-weil-pbc-flat-morphism-affine-criterion, lem-nagata-polynomial-projection-flat,
lem-pc-affine-flat-module-localization-preserves-flatness,
lem-weil-pbc-tensor-quotient-base-change).
2. Apply lem-pur-relative-regular-equations-base-change. It gives regularity at
all primes containing the new ideal, without a condition on the changing ring.
3. Regular sequences are Koszul-regular. Localize the new Koszul complex at every
prime (lem-sc-koszul-base-change-iso). On the closed locus use step 2; elsewhere
some equation f_j is a unit, and h(w)=f_j^{-1}e_j wedge w satisfies dh+hd=1.
Exactness of localization and the annihilator argument detect zero homology globally
(lem-weil-pbc-regular-sequence-koszul-regular,
lem-weil-pbc-localization-module-exact). This includes the empty sequence.
4. The conormal classes form bases by lem-sc-koszul-conormal-basis. The canonical
ideal-induced map sends 1 tensor [f_j] to [f'_j], so is an isomorphism of rank c.
The affine tilde-pullback comparison glues this formula
(lem-weil-pbc-ideal-cotangent-flat-base-change-ring,
lem-weil-pbc-tilde-pullback-base-change).
5. Relative differentials commute with base change, with 1 tensor da mapping to
d(a tensor 1). The coordinate bases and localization give rank n and the same
formula on all overlaps (lem-trf-relative-differential-sheaf-base-change,
lem-weil-pbc-polynomial-ring-kahler-basis-any-variables,
lem-weil-pbc-kahler-differentials-localization).
6. Flatness gives Tor independence (lem-trf-base-flat-polynomial-tor-bound with
zero variables). Apply lem-trf-lci-cotangent-presentation to its specified global
conormal comparisons: the intrinsic beta is represented by the two maps above.
7. Apply lem-trf-two-term-perfect-determinant to beta. Its canonical normalization
sends the dual equation wedge tensor the coordinate wedge to the corresponding
pulled-back orientation, with inverse transpose on the dual factor.
8. Write lambda_i for the intrinsic model comparisons and u_ij=lambda_j^{-1}lambda_i.
Conormal compatibility gives b_j Lg^*u_ij=u'_ij b_i. Determinant naturality gives
 delta_j g^*t_ij=t'_ij delta_i. Cotangent composition and determinant pullback
composition give delta_gk=delta_k k^*delta_g; the identity square gives identity.
These are equalities of the global maps specified in the dependency interfaces,
so they hold also on non-affine overlaps. Empty wedges are 1, including c=n=0.
-/
theorem exists_flatLCIPresentationBaseChange (C₀ : Coherence.{u})
    (κ : Naive.Comparison C₀) (D : CotangentPresentation.System C₀)
    (F : CotangentPresentation.AffineIdentifications D)
    (E : CotangentPresentation.LciIdentifications D F κ)
    (hD : CotangentPresentation.Properties D F κ E)
    (T : TwoTermPerfectDeterminantData.{u, w}) (hT : T.IsCanonical)
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [Flat f]
    [LocallyOfFinitePresentation f] (d : ℕ)
    (hcover : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (FlatLCIPresentation f d U)) :
    (∀ (U : X.Opens) (C : FlatLCIPresentation f d U), C.RegularEquationsBaseChange) ∧
    (∀ B : FlatLCIBaseChange f, PullbackStalkTensor.IsTorIndependent f B.b) ∧
    ∃ J : FlatLCIIntrinsicDeterminantData D F κ E T f d, J.LocalCompatibility := by
  sorry

end AlgebraicGeometry
