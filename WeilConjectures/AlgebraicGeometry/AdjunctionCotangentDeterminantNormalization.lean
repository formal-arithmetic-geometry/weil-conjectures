/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.LciCotangentPresentation
public import WeilConjectures.TraceFormula.CanonicalTwoTermPerfectDeterminant
public import WeilConjectures.TraceFormula.TwoTermPerfectDeterminantData
public import WeilConjectures.RingTheory.CotangentResolutionCoherence
public import WeilConjectures.RingTheory.NaiveCotangentComparison

import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.AlgebraicGeometry.RelativeDualityPolynomialChart
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import WeilConjectures.TraceFormula.AffineTwoTermDeterminant
import WeilConjectures.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.RingTheory.MvPolynomial.Localization
import WeilConjectures.RingTheory.RelativeRegularEquationsBaseChange
import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalBasis

/-! # Cotangent determinant normalization of adjunction

Source: Stacks, Duality, Tags 0B6V and 0BQZ; Perfect Complexes, Tags 0FJX and 0FJY;
Dualizing Complexes, Tag 0BZJ. The comparison of the specified maps is agent-formulated.
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Algebra.CotangentResolution
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The actual two-term conormal model of a regular presentation. The freeness witnesses
are representation data, not extra geometric hypotheses in the existence theorem.
Source: Stacks, Tags 08SL and 0FJX
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization). -/
def FlatLCIPresentation.determinantModel {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C : FlatLCIPresentation p d U)
    (δ : C.conormal ⟶ C.differentials)
    (hC : C.conormal.IsFiniteLocallyFreeOfRank C.c)
    (hV : C.differentials.IsFiniteLocallyFreeOfRank C.n) : TwoTermDeterminantModel U.toScheme :=
  ⟨C.conormal, C.differentials, δ, C.c, C.n, hC, hV⟩

/-- Bridge to the recorded intrinsic conormal comparison. The chain isomorphism is fixed
on both nonzero terms, so the bridge cannot replace the intrinsic comparison by an
arbitrary derived isomorphism. The restriction square retains the canonical inverse-image
ring maps and their unit normalization, including the identity chart.
Source: Stacks, Tags 08SL, 08T3 and 08QL
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization). -/
structure FlatLCICotangentChart {A : Coherence.{u}} (D : CotangentPresentation.System A)
    (F : CotangentPresentation.AffineIdentifications D) (κ : Naive.Comparison A)
    (E : CotangentPresentation.LciIdentifications D F κ)
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : FlatLCIPresentation p d U) where
  presentation : CotangentPresentation.LciPresentation C.i
    (C.ambient ≫ pullback.fst _ _)
  dimension : presentation.dimension = C.n
  ambient : HEq presentation.ambient C.ambient
  differential : C.conormal ⟶ C.differentials
  differential_normalization : C.IsConormalDifferential differential
  conormal_free : C.conormal.IsFiniteLocallyFreeOfRank C.c
  differentials_free : C.differentials.IsFiniteLocallyFreeOfRank C.n
  comparison :
    (C.determinantModel differential conormal_free differentials_free).complex ≅
      (E.identification C.i (C.ambient ≫ pullback.fst _ _) presentation).model.complex
  negative : comparison.hom.f (-1) ≫
      (E.identification C.i (C.ambient ≫ pullback.fst _ _) presentation).model.negative.hom =
    (HomologicalComplex.doubleXIso₀ differential (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).hom
  zero : comparison.hom.f 0 ≫
      (E.identification C.i (C.ambient ≫ pullback.fst _ _) presentation).model.zero.hom =
    (HomologicalComplex.doubleXIso₁ differential (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide) (by decide)).hom
  restriction : CotangentPresentation.BaseSquare p
    (C.i ≫ (C.ambient ≫ pullback.fst _ _)) U.ι (𝟙 S)
  restriction_iso : IsIso (CotangentPresentation.derivedChange D restriction)

/-- The prescribed local map λ, obtained from the dependency's global lci comparison
and inverse of its canonical restriction map, rather than chosen independently.
Source: Stacks, Tags 08SL and 08T3
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization). -/
def FlatLCICotangentChart.lambda {A : Coherence.{u}} {D : CotangentPresentation.System A}
    {F : CotangentPresentation.AffineIdentifications D} {κ : Naive.Comparison A}
    {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation p d U} (H : FlatLCICotangentChart D F κ E C) :
    DerivedCategory.Q.obj
        (C.determinantModel H.differential H.conormal_free H.differentials_free).complex ≅
      (derivedPullback U.ι).obj (CotangentPresentation.cotangent (D.model p)) :=
  DerivedCategory.Q.mapIso H.comparison ≪≫
    (E.identification C.i (C.ambient ≫ pullback.fst _ _) H.presentation).iso ≪≫
      (@asIso _ _ _ _ (CotangentPresentation.derivedChange D H.restriction)
        H.restriction_iso).symm

/-- The local exterior-model map followed by det(λ), expressed as a map to the
ordinary restriction of det(L). All three comparisons are those of the recorded functor.
Source: Stacks, Tags 0FJX and 0FJY
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization). -/
def FlatLCICotangentChart.determinantComparison
    {A : Coherence.{u}} {D : CotangentPresentation.System A}
    {F : CotangentPresentation.AffineIdentifications D} {κ : Naive.Comparison A}
    {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation p d U} (H : FlatLCICotangentChart D F κ E C)
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model p))) :
    C.line ≅ (tensorPullback U.ι).obj
      (twoTermDeterminantValue (T.functor X) (CotangentPresentation.cotangent (D.model p)) hL) :=
  (T.modelIso (C.determinantModel H.differential H.conormal_free H.differentials_free)).symm ≪≫
    twoTermDeterminantIso (T.functor U.toScheme)
      (T.model_mem (C.determinantModel H.differential H.conormal_free H.differentials_free))
      (T.pullback_mem U.ι _ hL) H.lambda ≪≫ (T.pullbackIso U.ι _ hL).symm

/-- The normalized global comparison, including its overlap equation and the arbitrary
base-change square. Base-changed schemes have no Noetherian hypothesis. `change_hom`
fixes the intrinsic base-change comparison to the recorded natural map.
Source: Stacks, Tags 0B6V, 08QQ, 0FJX and 0FJY
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization). -/
structure FlatLCIAdjunctionCotangentNormalization {A : Coherence.{u}}
    (D : CotangentPresentation.System A) (F : CotangentPresentation.AffineIdentifications D)
    (κ : Naive.Comparison A) (E : CotangentPresentation.LciIdentifications D F κ)
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} (K : FlatLCIAdjunctionSystem p d)
    (T : TwoTermPerfectDeterminantData.{u, w}) where
  perfect : ∀ B : FlatLCIBaseChange p,
    isTwoTermPerfect B.X' (CotangentPresentation.cotangent (D.model B.p'))
  chart : ∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' d U), FlatLCICotangentChart D F κ E C
  theta : ∀ B : FlatLCIBaseChange p, K.line B ≅
    twoTermDeterminantValue (T.functor B.X')
      (CotangentPresentation.cotangent (D.model B.p')) (perfect B)
  normalization : ∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' d U),
    (K.localIso B U C).hom ≫ (tensorPullback U.ι).map (theta B).hom =
      ((chart B U C).determinantComparison T (perfect B)).hom
  overlap : ∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C C' : FlatLCIPresentation B.p' d U),
    (K.localIso B U C).hom ≫ (K.localIso B U C').inv =
      ((chart B U C).determinantComparison T (perfect B)).hom ≫
        ((chart B U C').determinantComparison T (perfect B)).inv
  square : ∀ (B B' : FlatLCIBaseChange p) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S'),
    IsPullback g B'.p' B.p' b → CotangentPresentation.BaseSquare B.p' B'.p' g b
  change : ∀ (B B' : FlatLCIBaseChange p) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (_q : CotangentPresentation.BaseSquare B.p' B'.p' g b),
    IsPullback g B'.p' B.p' b → g ≫ B.g = B'.g → b ≫ B.b = B'.b →
    ((derivedPullback g).obj (CotangentPresentation.cotangent (D.model B.p')) ≅
      CotangentPresentation.cotangent (D.model B'.p'))
  change_hom : ∀ (B B' : FlatLCIBaseChange p) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (q : CotangentPresentation.BaseSquare B.p' B'.p' g b)
    (hc : IsPullback g B'.p' B.p' b) (hg : g ≫ B.g = B'.g) (hb : b ≫ B.b = B'.b),
    (change B B' g b q hc hg hb).hom = CotangentPresentation.derivedChange D q
  baseChange : ∀ (B B' : FlatLCIBaseChange p) (g : B'.X' ⟶ B.X') (b : B'.S' ⟶ B.S')
    (q : CotangentPresentation.BaseSquare B.p' B'.p' g b)
    (hc : IsPullback g B'.p' B.p' b) (hg : g ≫ B.g = B'.g) (hb : b ≫ B.b = B'.b),
    (tensorPullback g).map (theta B).hom ≫
        (T.pullbackIso g _ (perfect B)).hom ≫
        (twoTermDeterminantIso (T.functor B'.X')
          (T.pullback_mem g _ (perfect B)) (perfect B')
          (change B B' g b q hc hg hb)).hom =
      (K.baseChange B B' g b hc hg hb).hom ≫ (theta B').hom

/-- The canonical adjunction line is the determinant of the intrinsic cotangent complex,
with its specified local normalization, overlap transitions and arbitrary base change.
The determinant datum is universally quantified with its exact-cone and pure-wedge
canonicity predicate. Its model and pullback comparisons are fixed independently of K
and θ; they cannot be chosen to force the normalization equations.
Source: Stacks, Tags 0B6V, 0BQZ, 08SL, 0FJX and 0FJY; normalized polynomial refinements
in Dualizing Complexes, Tag 0BZJ
(blueprint: lem-sfb-adjunction-cotangent-determinant-normalization).

Proof (the accepted DAG argument, step by step):
1. Write $a_i:K_i\to K|_U$ for the specified adjunction comparisons. A regular sequence is
   Koszul-regular by [lem-weil-pbc-regular-sequence-koszul-regular], so the conormal model theorem
   [lem-trf-lci-cotangent-presentation] applies to every presentation in the statement. Apply
   [lem-trf-two-term-perfect-determinant] to $\lambda_i:E_i\simeq L|_U$ and set
   $\alpha_i=\det(\lambda_i):K_i=D(E_i)\to(\det L)|_U$. The issue is to compare the specified
   $a_j^{-1}a_i$ with $\alpha_j^{-1}\alpha_i$; an abstract isomorphism between the underlying
   lines would not suffice. The fixed datum T satisfies T.IsCanonical: its model clause
   identifies det of each chain quasi-isomorphism with the signed exact-cone formula,
   and its pullback clause identifies scalar extension with the pure-wedge formula.

2. Work on affine subcharts over an affine open of $S$. These source charts are separated over
   that base, so [lem-trf-relative-duality-polynomial-chart] applies: flatness and local finite
   presentation are inherited from $p$, and the base is locally Noetherian. Its statement supplies
   the normalized comparisons of the local dualizing models under polynomial refinement. By
   [lem-trf-flat-lci-canonical-adjunction], the adjunction line shifted by $d=n-c$ is precisely
   this relative dualizing object, locally with its specified Koszul Ext identification. Thus the
   comparisons defining $a_i$ are obtained by restricting those polynomial-model comparisons to
   their single nonzero cohomology module. This uses the dualizing and Ext clauses of the cited
   statements, not the construction of $K$ inside a cited proof. It remains to calculate their
   effect on the displayed generators.

3. On a fixed ambient chart choose equations $f_1,\ldots,f_c$. Their classes are a basis of $C$ by
   [lem-weil-pbc-regular-sequence-conormal-free]. The ideal-independent top Ext identification of
   [lem-sc-koszul-regular-sequence-dual-complex] is the dual of their top conormal wedge.
   Replacing that basis by $\bar f'=M\bar f$ multiplies its dual top wedge by $\det(M)^{-1}$,
   exactly as in $D(E)=(\bigwedge^c C)^\vee\otimes\bigwedge^n V$; a change of basis in $V$ acts by
   its top wedge on both sides. Consequently the Koszul and determinant identifications agree
   under changing regular equations or differential frames. They agree under restriction as well:
   the Koszul comparison commutes with localization by its cited statement, and the determinant
   comparison commutes with restriction by [lem-trf-two-term-perfect-determinant]. No
   invertibility of the coefficient matrix over the ambient ring is needed: its reduction on $C$
   is a basis change over the quotient.

4. For a one-coordinate refinement put $Q=A[t]$, $h=t-a$, and let $B=A/I$ be the source ring. The
   new conormal module is $Bh\oplus C$ and the new differential module is $B\,dh\oplus V$, where
   $dh=dt-da$; substitution $t=a$ projects their complex onto $E=[C\to V]$, with kernel
   $[Bh\xrightarrow{1}B\,dh]$. Naturality in [lem-trf-lci-naive-cotangent-model] identifies this
   projection in the derived category with the intrinsic model comparison
   $\lambda_i^{-1}\lambda_{\mathrm{new}}$. The determinant is the kernel-first map of
   [lem-trf-affine-two-term-determinant] and [lem-trf-surjective-two-term-determinant-calculus].
   It sends $$ (\bar h\wedge\bar f_1\wedge\cdots\wedge\bar f_c)^\vee\otimes(dh\wedge
   v_1\wedge\cdots\wedge v_n)\quad\hbox{to}\quad(\bar f_1\wedge\cdots\wedge\bar
   f_c)^\vee\otimes(v_1\wedge\cdots\wedge v_n). $$ Indeed the kernel differential sends $\bar h$
   to $dh$, so its determinant has value $1$. The polynomial dualizing comparison of
   [lem-trf-relative-duality-polynomial-chart] contracts exactly $\bar h^\vee\otimes dh$ to $1$ in
   this order, giving the same formula. There is no implicit exchange of ordered factors: writing
   $h$ last instead multiplies this displayed generator by $(-1)^{c+n}$ on both sides of the
   comparison. Iteration uses the same successive kernel-first contractions, and the cited
   dualizing comparison includes the cohomological tensor signs. Thus determinant and adjunction
   agree for every iterated polynomial refinement.

5. Locally two polynomial presentations have a common combined-coordinate refinement. Explicitly,
   for polynomial surjections $R[x]\twoheadrightarrow B$ and $R[y]\twoheadrightarrow B$, lift each
   image of $y_j$ to $a_j(x)$. Then the combined kernel is generated by the first kernel and
   $y_j-a_j(x)$: substitution reduces any polynomial to one in $x$, and a polynomial in the kernel
   then reduces to the first kernel. These added equations are successive monic coordinate
   equations, so their conormal complexes are precisely the successive refinements just
   calculated. Reversing $x,y$ gives the other comparison. For ambient opens, restrict around the
   point to principal pieces and invert the denominators; their images in $B$ are units, so the
   same substitutions extend after localization. These are the polynomial refinements in
   [lem-trf-relative-duality-polynomial-chart]. That node gives their composition law;
   [lem-trf-lci-naive-cotangent-model] identifies their complex maps with the intrinsic
   comparisons; [lem-trf-two-term-perfect-determinant] gives the determinant composition law.
   Steps 3 and 4 therefore imply, on an open cover of every overlap,
   $$a_j^{-1}a_i=\det(\lambda_j^{-1}\lambda_i)=\alpha_j^{-1}\alpha_i.$$ The equality holds on the
   whole overlap because two sheaf maps agreeing on an open cover agree on every section by the
   sheaf uniqueness axiom. No affine-intersection hypothesis is used.

6. Define on each chart $\theta_i=\alpha_i a_i^{-1}:K|_U\to(\det L)|_U$. The equality in Step 5
   gives $\theta_i=\theta_j$ on overlaps. For a section $s$ of $K$ on an open $T$, glue the
   sections $\theta_i(s|_{T\cap U_i})$ using the sheaf axiom of $\det L$; their agreement gives a
   unique section, and uniqueness proves linearity and commutation with restrictions. Applying the
   same construction to $\theta_i^{-1}$ gives its inverse. This constructs a unique global
   isomorphism $\theta$ with $\theta a_i=\det(\lambda_i)$ for every chart. The construction is
   forced by these equations, so it is independent of the cover and has precisely the stated
   normalization.

7. For $S'\to S$ use affine base rings $R\to R'$. The pulled-back presentations are again conormal
   models. Shrink the ambient chart to a principal affine piece $A=R[x_1,\ldots,x_n]_h$ of $P$ on
   which $I$ is generated by a regular sequence $f_1,\ldots,f_c$ in $A$, so $B=A/(f)$. The
   polynomial ring is $R$-free on monomials, hence $R$-flat, so $A$ is $R$-flat by
   [lem-pc-affine-flat-module-localization-preserves-flatness]; by
   [lem-weil-pbc-localization-away-polynomial-quotient], $A\cong R[x_1,\ldots,x_n,z]/(hz-1)$ is
   finitely presented over $R$. Put $A'=A\otimes_RR'$ and $f'_j=f_j\otimes1$, so
   $A'/(f')=B\otimes_RR'$ and $A'$ is the corresponding principal piece of $\mathbf A^n_{S'}$.
   Here $B$ is $R$-flat by [lem-weil-pbc-flat-morphism-affine-criterion]. By
   [lem-pur-relative-regular-equations-base-change] the $f'_j/1$ form a regular sequence in
   $A'_{\mathfrak q'}$ for every prime $\mathfrak q'$ containing all $f'_j$, hence a
   Koszul-regular one there by [lem-weil-pbc-regular-sequence-koszul-regular]. At a prime not
   containing some $f'_j$, that $f'_j$ is a unit of $A'_{\mathfrak q'}$; multiplication by $f'_j$
   on the Koszul complex is null-homotopic (contraction with the $j$th basis vector), so its
   homology vanishes. Localization is exact and commutes with forming the Koszul complex, and a
   module whose localizations at all primes vanish is zero; hence $f'_1,\ldots,f'_c$ is
   Koszul-regular in $A'$ [def-weil-pbc-koszul-regular-sequence]. So
   [lem-trf-lci-cotangent-presentation] gives the conormal model comparison $\lambda'_i$ of the
   pulled-back presentation, and by [lem-sc-koszul-conormal-basis] the classes $\bar f'_j$ form a
   basis of $C'=I'/I'^2$; the natural map $g^*C\to C'$ sends the basis $\bar f_j$ to it and is an
   isomorphism, while coordinate differentials identify $g^*V$ with $V'$. Thus $g^*E_i\simeq E'_i$
   termwise and $g^*D(E_i)\simeq D(E'_i)$.

8. For $S'\to S$ use affine base rings $R\to R'$ and an affine source ring $B$ over $R$. By
   [lem-weil-pbc-flat-morphism-affine-criterion], $B$ is $R$-flat. Tensor a flat resolution of
   $R'$ over $R$ with $B$: flatness preserves exactness, so its only cohomology is $B\otimes_RR'$
   in degree zero. Hence the square is Tor-independent, and by the previous step the pulled-back
   presentations are conormal models with $g^*E_i\simeq E'_i$. The natural comparison
   $\beta:Lg^*L\simeq L_{W'/S'}$ of [lem-trf-lci-cotangent-presentation] is an isomorphism and
   respects the conormal models. The arbitrary-base-change clause of
   [lem-trf-flat-lci-canonical-adjunction] supplies the pulled-back adjunction presentations and
   their line comparisons, even for non-Noetherian $S'$. In particular we are not applying a
   Noetherian relative-duality existence theorem over $S'$. The determinant pullback comparison of
   [lem-trf-two-term-perfect-determinant] now gives $$b_D:g^*\det
   L\xrightarrow{\sim}\det(Lg^*L)\xrightarrow{\det(\beta)}\det L_{W'/S'}.$$ All hypotheses of the
   cotangent and adjunction base-change clauses are thus in force.

9. Let $b_K:g^*K\to K'$ be the specified adjunction base-change map. On each pulled-back
   presentation it is extension of the conormal/top-differential formula, by the
   arbitrary-base-change clause of [lem-trf-flat-lci-canonical-adjunction]. For finite locally
   free modules the pullback maps on exterior powers and duals send a basis wedge to the
   corresponding pulled-back basis wedge and its dual to that dual. Thus $g^*D(E_i)\to D(E'_i)$
   sends $1\otimes(\bar f_1\wedge\cdots\wedge\bar f_c)^\vee\otimes(v_1\wedge\cdots\wedge v_n)$ to
   the identical primed expression. By naturality of [lem-trf-two-term-perfect-determinant] and
   the conormal-model compatibility of [lem-trf-lci-cotangent-presentation], this is also the
   restriction of $b_D$ under $\alpha_i,\alpha'_i$. The generator-change and contraction formulas
   in Steps 3 and 4 are identities of finite wedges and evaluation over any ring, so they still
   compare the primed presentation transitions without a Noetherian hypothesis. The sheaf gluing
   of Step 6 defines $\theta'$ there. On these generators the two maps $\theta' b_K$ and $b_D
   g^*\theta$ agree, hence they agree on every chart and globally. Identity and successive base
   changes give the same pure-wedge formulas; alternatively their equality follows from the
   coherent cotangent and determinant comparisons in the cited statements. This proves all the
   required base-change normalization, including the assertion over arbitrary $S'$.
-/
theorem exists_adjunctionCotangentDeterminantNormalization
    {A : Coherence.{u}} (D : CotangentPresentation.System A)
    (F : CotangentPresentation.AffineIdentifications D) (κ : Naive.Comparison A)
    (E : CotangentPresentation.LciIdentifications D F κ)
    (hD : CotangentPresentation.Properties D F κ E)
    {X S : Scheme.{u}} (p : X ⟶ S) [IsNoetherian S] [Flat p]
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (d : ℕ) (hpure : HasPureFlatLCIGeometricFibres p d)
    (hlci : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (FlatLCIPresentation p d U))
    (K : FlatLCIAdjunctionSystem p d) (hK : K.IsNormalized)
    (T : TwoTermPerfectDeterminantData.{u, w}) (hT : T.IsCanonical) :
    Nonempty (FlatLCIAdjunctionCotangentNormalization D F κ E K T) := by
  sorry

end AlgebraicGeometry
