/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.AdicExceptionalCoherence
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.SemilinearDerivedSections
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.SixFunctors.IntegralOpenReductionComparison
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.Paper.PbcScalarExtension
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Arbitrary-field adic exceptional projection and coefficient coherence
Source: Bhatt--Scholze Section 6.7 and Remark 6.8.15
(blueprint: lem-per-adic-exceptional-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicExceptionalProjection

/-- The adic ordinary and exceptional adjunctions, completed projection, composition,
and all finite-coefficient and finite-extension compatibilities, over any field.
No finite-cohomological-dimension assumption on the base field is made.

Source: Bhatt--Scholze, Lemmas 6.7.2, 6.7.7, 6.7.14, 6.7.16--6.7.19 and
Remark 6.8.15 (blueprint: lem-per-adic-exceptional-projection).

Proof plan, with exactly the DAG's coherent-system construction:
1. Every scheme in a compactification of $f$ is finite type over $k$. Fields are excellent by
[lem-exc-fields-excellent], and their finite-type algebras are excellent by [lem-exc-finite-
type-localization-excellent]. Thus these schemes are quasi-excellent and $\ell$-coprime, as
required in the source; no cohomological-dimension assumption on $k$ is being made. They are
Noetherian by [lem-weil-pbc-finite-type-over-noetherian] and finite-dimensional by [lem-kun-
dimension-finite-type]. Apply [lem-weil-pbc-integral-stratified-perfect-characterization] to
identify precisely the integral category in the question, with its completed coefficient sheaf,
with the source's constructible complete category. Finite reductions have bounded etale origins
by [lem-weil-pbc-finite-ring-constructible-derived-origin]. For an integral object $P$, choose
an interval $[a,b]$ bounding $P_1$. Tensor associativity gives $(P_n)\otimes^L_{A_n}A_1=P_1$.
The etale residue test [lem-exc-residue-tor-test], transported by [det-pe-finite-tor-comparison-
noetherian], therefore gives Tor interval $[a,b]$ for all $P_n$. This supplies finite Tor
without assuming it in the item.

2. Use $\mathcal R_T$ and $\mathcal L_T$ for the coherent reduction and total-limit functors of
[lem-coef-derived-system-evaluation-calculus]. For the constructible inputs at issue,
$P\to\mathcal L_T\mathcal R_TP$ is the canonical invertible completion unit: [lem-weil-pbc-
integral-stratified-perfect-characterization] identifies this category with the Koszul-complete
constructible category, and [lem-weil-pbc-constant-completion-equivalence] identifies that
completion with the specified quotient-tower unit. This uses more than the object-only Roos-
triangle definition of completeness. On normalized systems the counit $\mathcal R_T\mathcal
L_TM\to M$ is invertible by [lem-coef-normalized-dvr-effectivity] and is a system morphism by
the evaluation calculus. Consequently $\mathcal R_T$ and $\mathcal L_T$ give inverse
equivalences between complete integral objects and normalized derived systems: the unit and
counit are the specified ones, and their triangle identities come from the stated
reduction/limit adjunction. On the constructible subcategories, a normalized system with bounded
constructible levels has uniformly bounded Tor intervals as soon as its level-one object is
bounded: apply the two residue/comparison tests of step 1 to $M_n\otimes^L_{A_n}A_1\cong M_1$.
Effectivity and the defining uniform-reduction condition then put $\mathcal L_TM$ in
$D^b_c(T,R)$. We will transport actual functors and transformations through this equivalence,
never deduce equality of maps from equality of their individual reductions.

3. Let $P_f,S_f$ be exact inverse image and total derived direct image on finite-coefficient
systems. They form $P_f\dashv S_f$, with evaluated units and counits, by [lem-coef-semilinear-
derived-sections]. On bounded constructible etale complexes $Rf_{*,n}$ preserves bounded
constructibility: [sbc-thm-finiteness-finite-type] applies to each cohomology sheaf, and the
finitely many truncation triangles give the assertion for the complex. The coefficient
projection comparison for a quotient $A_m\to A_n$ is invertible by [lem-sf-projection-finite-
constant]. Its finite-cohomological-dimension hypothesis follows from [lem-kun-0f10], uniformly
for torsion coefficients. Restriction of coefficients identifies the output with $Rf_{*,n}$ by
[lem-weil-proetale-direct-image-restriction-of-scalars]; [prop-weil-pbc-comparison-direct-image]
transports the calculation between the two sites. Thus $S_f$ carries normalized constructible
systems to normalized constructible systems. Their output level one is bounded, so step 2
supplies the required common interval. Pullback preservation and its finite comparisons are
[lem-pur-integral-operations-preserve-constructible]. The comparison [lem-pur-completed-
coefficient-pushforward-comparison] also identifies this adic direct image with ordinary ringed
direct image on completed coefficient sheaves, with the same tower projections.

4. Conjugate $P_f\dashv S_f$ through the equivalences in step 2. Explicitly, for complete
constructible $M,K$, fullness and faithfulness of these equivalences give
$$\operatorname{Hom}(\mathcal L_XP_f\mathcal R_YM,K)\cong\operatorname{Hom}(P_f\mathcal
R_YM,\mathcal R_XK)\cong\operatorname{Hom}(\mathcal R_YM,S_f\mathcal
R_XK)\cong\operatorname{Hom}(M,\mathcal L_YS_f\mathcal R_XK).$$
These bijections are natural.
Their left functor is the completed $Lf^*$ by [lem-pur-completed-operation-tower-substitution],
and their right functor is exactly the adic $Rf_*$ of [def-weil-derived-direct-image], including
its quotient transitions. The natural-bijection construction [lem-weil-pbc-adjunction-of-
natural-bijection] gives the adjunction and both triangle identities. Its units and counits are
conjugates of the system ones, rather than maps chosen independently at each level.

5. Fix one compactification $f=pj$. The finite compact-support functors have actual system
realization $\mathcal F_f=S_pJ_j$ by [lem-coef-semilinear-derived-sections]. The proper etale
projection formula [lem-etale-proper-projection-formula-finite], the open tensor identification
[lem-sf-open-tensor-normalization], and [lem-sf-class-compact-support-comparison] give, on
finite constructible inputs,
$$F_nK_n\otimes^L_{A_n}M_n\xrightarrow{\sim}F_n(K_n\otimes^L_{A_n}f_n^*M_n).$$
Here the monoidal
comparison for $\nu^*$ is [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. In particular the
same proper/open composite with the constant coefficient module $A_n$ gives normalization across
$A_m\to A_n$. These maps are formed from tensor comparisons and the proper counit on the system
category itself, as specified in [lem-coef-semilinear-derived-sections]; their evaluation is the
displayed finite map. Thus this is a coherent system transformation. The finite inputs and
tensor products are bounded by the Tor intervals of step 1. Compact support preserves the
integral category by [lem-sf-integral-compact-support-constructible], and its defining total-
limit tower is precisely $\mathcal L_Y\mathcal F_f\mathcal R_X$.

6. Apply [lem-per-finite-exceptional-system-adjunction] on the etale coefficient systems. It
supplies $\mathcal F_f\dashv\mathcal G_f$ on normalized finite-Tor constructible systems with
the actual finite exceptional units and counits. Step 1 checks that $\mathcal R_YM$ belongs to
its domain. Its output is normalized and has bounded constructible level one $G_1M_1$; the
residue argument of step 2 therefore makes all its levels uniformly bounded. Transport this
system and the adjunction to the pro-etale site by [lem-pur-coefficient-system-derived-
comparison] and [thm-weil-pbc-site-comparison]. This is legitimate on these bounded-below
systems, whose bounds were just proved; the comparison counit is invertible, including the
transition maps. The left functor becomes exactly the pro-etale $\mathcal F_f$ by [lem-sf-class-
compact-support-comparison]. Define
$$f^!M=\mathcal L_X\nu_X^*\mathcal G_fR\nu_{Y,*}\mathcal
R_YM.$$
All maps are images of maps of derived systems. Step 2 proves that this object is in the
indicated integral category, with canonical reduction $\nu_X^*G_nR\nu_{Y,*}M_n=f_n^!M_n$.

7. The equivalences of step 2 and the system adjunction of step 6 give natural bijections
$$\operatorname{Hom}_Y(Rf_!K,M)\cong\operatorname{Hom}(\mathcal F_f\mathcal R_XK,\mathcal
R_YM)\cong\operatorname{Hom}(\mathcal R_XK,\mathcal G_f\mathcal
R_YM)\cong\operatorname{Hom}_X(K,f^!M),$$
where the etale/pro-etale equivalences of step 6 are
inserted in the middle terms. Use [lem-weil-pbc-adjunction-of-natural-bijection] to obtain
$Rf_!\dashv f^!$. Its counit is the total-limit image of the system counit, conjugated by the
reduction/limit unit and counit. The triangle identities of that equivalence cancel the inserted
comparisons; evaluation of the resulting system counit is the finite counit by [lem-per-finite-
exceptional-system-adjunction]. This proves the asserted reduction of the specified integral
counit, not just existence of an adjunction having isomorphic right-functor objects.

8. Take the coherent projection transformation of step 5 and apply $\mathcal L_Y$. Its source is
$(Rf_!K)\widehat\otimes^L_RM$ and its target is $Rf_!(K\widehat\otimes^L_RLf^*M)$: insert the
coherent counits $\mathcal R\mathcal L\cong1$, then apply [lem-pur-completed-operation-tower-
substitution] to the tensor and pullback expressions. The source and target systems are
normalized and the finite projection maps are invertible, so [lem-coef-semilinear-derived-
sections] makes the system projection an isomorphism before taking the limit. Its inverse
realizes the direction displayed in the item. The projection map is the canonical one: it is the
proper counit tensored with the identity followed by the open tensor comparison, all formed on
the system category and transported with its adjunctions. Its finite reduction is therefore the
finite canonical projection. This establishes both invertibility and normalization without
treating finite evaluation as faithful on derived morphisms.

9. For $X\xrightarrow fY\xrightarrow gZ$, choose compatible compactifications by [lem-weil-pbc-
compatible-compactification-triangle]: from one of $g$ it gives ones of $f$ and $gf$ with a
cartesian proper/open square. On coefficient systems use the proper/open interchange and the
direct-image and open-extension compositors. These are actual system maps with horizontal and
vertical pasting identities by [lem-sf-semilinear-proper-open-mate-pasting]. Their finite
evaluations are the canonical compact-support composition maps; [thm-sf-comp-composition] makes
each evaluation invertible. Joint conservativity in [lem-coef-semilinear-derived-sections] then
makes the system compositor invertible. After applying $\mathcal L$ and inserting $\mathcal
R\mathcal L\cong1$ as in step 8, it gives $Rg_!Rf_!\cong R(gf)_!$. The system pasting equations
give its identity and associativity equations before total limit. Take its adjunction conjugate
to get $f^!g^!\cong(gf)^!$. The mate-pasting equations [lem-weil-pbc-mate-pasting] identify the
two triple composites and identity mates, so the right-adjoint compositors satisfy exactly the
corresponding equations.

10. All reductions, system inverse images, open extensions and scalar tensors are derived from
additive functors and total complexes. Their shift comparisons are termwise cochain shifts with
the usual tensor signs. Total derived inverse limit is exact by [lem-weil-pbc-ringed-strict-
tower-homotopy-limit]. Hence the transported pullback, direct image and compact support are
exact $R$-linear functors. The system exceptional functor in [lem-per-finite-exceptional-system-
adjunction] is exact and $R$-linear, so its transported $f^!$ is too. The canonical right-
adjoint shift is the unique one compatible with the unit and counit by [lem-weil-pbc-adjunction-
shift-compatibility-unique]. Thus both adjunctions commute with shifts. Projection, reduction
and composition maps commute with those comparisons: on simultaneous resolutions they are
composites of the termwise shift-compatible unit, counit and signed tensor maps. The tensor
substitution theorem [lem-pur-completed-operation-tower-substitution] carries their signed
system comparisons to the completed ones. This also checks shift compatibility for the
exceptional mates by mate pasting.

11. Let $S=\mathcal O_L$. By [lem-weil-finite-free-completed-scalar-comparison], the completed
coefficient sheaf $\widehat S_T$ is finite free over $\widehat R_T$, and the scalar functor in
the question is ordinary derived tensor with this sheaf. Pullback and tensor comparisons with
scalar extension, including their identity and tower equations, are [lem-pur-integral-
operations-scalar-extension]. For direct image use the coherent comparison of [prop-weil-pbc-
scalar-extension]. This applies because the schemes are Noetherian and finite-dimensional, and
step 3 proved direct-image constructibility. For compact support, [lem-sf-integral-open-
reduction-comparison] and [lem-pur-completed-coefficient-pushforward-comparison] identify its
defining tower with the separately derived composite $Rp_*j_!$. Use a single compactification:
the direct-image comparison for $p$ and the coefficient version of the open tensor comparison
[lem-sf-open-tensor-normalization] give
$$C_YRp_*j_!\xrightarrow{\sim}Rp_*C_{\overline
X}j_!\xrightarrow{\sim}Rp_*j_!C_X.$$
These are the same comparisons on strict reduction systems.
At ramification index $e$, $S/t^nS=S/v^{en}$. The canonical restriction of total limits to these
levels, with all projection maps and units, is [lem-sp-strict-tower-arithmetic-restriction].
Thus the displayed comparison realizes $C_YRf_!\cong Rf_!C_X$ for exactly the compact-support
definition in the question, even for ramified extensions.

12. Write $F_R=Rf_{!,R}$ and $G_R=f_R^!$, with the analogous $S$-functors, and let
$q:C_YF_R\cong F_SC_X$ be step 11. Define $b:C_XG_R\to G_SC_Y$ to be the $F_S\dashv G_S$
transpose of $C_Y\epsilon_R\circ q_{G_R}^{-1}$. To check invertibility, restriction of scalars
$V$ is right adjoint to $C$ by [lem-pur-sheaf-ring-derived-coefficient-adjunction]. $V$
preserves the constructible categories: it is exact, keeps cohomology sheaves, and $\widehat
S_T=\widehat R_T\otimes_RS$ (limit of $(R/t^n)_T\otimes_RS=(S/t^nS)_T$, $S$ finite free over $R$
[lem-weil-finite-free-completed-scalar-comparison]), so criterion (iii) of [lem-weil-pbc-
integral-stratified-perfect-characterization] passes to $V$. Thus, naturally in $N,K$,
$$\operat
orname{Hom}(K,V_XG_SN)\cong\operatorname{Hom}(C_XK,G_SN)\cong\operatorname{Hom}(F_SC_XK,N)\cong\
operatorname{Hom}(C_YF_RK,N)\cong\operatorname{Hom}(F_RK,V_YN)\cong\operatorname{Hom}(K,G_RV_YN)
.$$
Applying this natural bijection and its inverse to the identity maps gives mutually inverse
maps (naturality proves the two composites are identities). The resulting comparison identifies
$V_XG_S$ with $G_RV_Y$, with its counit. Under this identification the underlying map of $b_M$
is $G_RM\otimes_RS\to G_R(M\otimes_RS)$. Choose an $R$-basis of $S$ just to test it. This
becomes the canonical map from the finite direct sum of copies of $G_RM$ to $G_R$ of that finite
direct sum. Its components are $G_R$ of the inclusions, as follows by transposing the defining
formula for $b$. Additivity of $G_R$ makes it invertible. Restriction of scalars detects
isomorphisms since it leaves cohomology sheaves unchanged. Therefore $b$ is an isomorphism,
canonically the mate specified in the question; its construction did not choose a basis.

13. For either adjunction, the coefficient comparison carries its counit to the extended counit:
for the exceptional pair this is the defining transpose equation
$$\epsilon_S\circ F_Sb\circ
q_{G_R}=C_Y\epsilon_R.$$
The unit equation follows by substituting this equation in the inverse
adjunction bijection and using both triangle identities. For the ordinary pair, compute the
direct-image coefficient map on a chosen $R$-basis of $S$: it is the canonical finite-sum
comparison, and the pullback coefficient map is tensor reassociation. The extended adjunction
bijection is consequently the direct sum of the original bijections. It sends the identity to
the extended unit and the inverse bijection sends the identity to the extended counit;
naturality makes this basis computation an identity for the canonical maps. Its compatibility
with completed pullback is tensor reassociation on the reduction systems, so the same triangle
argument applies. Quotient coefficient maps satisfy that reassociation identity too; hence these
equations carry every finite reduction and its finite counit to the corresponding maps after
coefficient extension. Identity extensions give identity tensor maps. For $E\subset L\subset
L'$, the two successive scalar maps agree with the single scalar map because both send
$(x\otimes s)\otimes t$ to $x\otimes st$. The open maps satisfy the same equality by their
restriction-to-the-open normalization, and direct-image maps by their adjunction transpose. Mate
pasting [lem-weil-pbc-mate-pasting] gives the tower equation for $b$, and the corresponding unit
equations. These arguments occur on the strict coefficient diagrams before total inverse limit.

14. Finally every compact-support compositor of step 9 is the proper/open mate word in its
units, counits, open comparisons and direct-image compositors. Every projection of step 8 is the
proper counit tensored with the identity followed by the open tensor map. Step 13 carries these
individual factors and their adjunction transposes to the factors over $S$; the tensor
comparison is the one in [lem-pur-integral-operations-scalar-extension]. Therefore it carries
the entire ordered composites to the specified composites over $S$. The proper/open pasting
identities in [lem-sf-semilinear-proper-open-mate-pasting] and the abstract mate-pasting
equations show the same assertion for the right-adjoint composition mates. Taking total limits
preserves these equations because they are equations of actual system maps. This proves scalar
compatibility of composition, its exceptional mate, projection, both adjunctions and finite
reductions, with their identity, tower and shift normalizations. The zero objects, empty
schemes, identity morphisms and $L=E$ are included: all their displayed system maps are the
relevant identities or zero maps.

The structures in the conclusion retain the actual canonical proper/open words,
ordinary completion units, finite counits, adjunction squares and tower associators.
The exceptional composition is defined as the adjunction conjugate; mate pasting
therefore transports identity, associativity and scalar equations to it. The finite
exceptional scalar square follows by transposing the finite compact-support reduction
square: the counit normalization in Operation and ScalarAdjunction supplies exactly
its two boundary counits, so uniqueness of the finite adjunction transpose identifies
it. No equality of derived maps is inferred merely from their finite evaluations.
-/
theorem exists_system (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    [Fact (IsUnit (l : k))] : Nonempty (System (k := k) l) := by
  sorry

end WeilConjectures.AdicExceptionalProjection
