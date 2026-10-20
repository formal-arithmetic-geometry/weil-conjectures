/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SitePerfectComplex
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.SfIntegralConstructible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.ScalarLocalization
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteProjectiveInternalHomEvaluation
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.SfRationalBoundedConeTorsion
import Sheaf.Paper.SfRationalLocalGlobalPowerTorsion
import Sheaf.Paper.RationalSliceCompletedEvaluation
import Sheaf.Paper.RationalThickEvaluation
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.ScalarExtensionExactIntrinsic

/-! # Internal Hom through the coefficient dual

Source: Weil conjectures blueprint main-20261015, sec-six-functors,
sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom
(blueprint: prop-sf-dualizable-hom).
The four conjuncts are the finite, completed integral, rational, and common-stage
coefficient choices. Their comparison is the evaluation transpose with the signed
symmetry, using the actual closed domains of the fixed six-functor datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- A site-perfect finite-Tor constructible complex has canonical evaluation
`K^∨ ⊗ M → RHom(K,M)` invertible for every finite-Tor constructible M, at each
of the four coefficient stages. The n-th index means exponent n+1.
Source: blueprint main-20261015, prop-sf-dualizable-hom; Stacks Tag 08JJ
(blueprint: prop-sf-dualizable-hom).

Proof:
1. Write $K^\vee=R\mathcal Hom(K,\Lambda_X)$ and let $\theta_{K,M}:K^\vee\otimes^L M\to R\mathcal
   Hom(K,M)$ be the adjunct of evaluation, with the symmetry placing $K$ next to its dual. First
   work at finite coefficients. Choose a covering on which $K$ has a bounded finite-projective
   representative $P$, with $P^r=0$ outside $[a,b]$. By the definition of each finite-projective
   term, choose its finite free retraction; only finitely many nonzero terms require choices.
   These are degreewise splittings, not chain splittings. Restriction is exact, derived internal
   Hom commutes with slice restriction, and derived tensor commutes with the corresponding
   ringed-topos pullback. Thus the restriction of $\theta$ is the same evaluation comparison on
   the localized site. It suffices to calculate there; retain $R=\Lambda_X|_U$ for its ring
   sheaf.
   Dependencies: def-weil-derived-pullback-tensor-hom, def-weil-site-perfect-complex, def-weil-
   pbc-strict-perfect-coefficient-package, lem-pur-site-restriction-module-adjunction-exact, lem-
   weil-pbc-ringed-internal-hom-exact-restriction, lem-weil-pbc-ringed-topoi-derived-tensor-
   pullback.
2. For each term $E=P^r$, choose $E\xrightarrow{i}R^{\oplus m}\xrightarrow{p}E$ with $pi=1$. Its
   dual is a retract of $(R^{\oplus m})^\vee=R^{\oplus m}$ by dualizing $i,p$. Consequently both
   $E$ and $E^\vee$ are flat: tensor with either is a direct summand of the exact finite-sum
   functor $B\mapsto B^{\oplus m}$. Likewise $\mathcal Hom_R(E,-)$ is a direct summand of
   $\mathcal Hom_R(R^{\oplus m},-)=(-)^{\oplus m}$ and is exact. The ordinary evaluation
   isomorphism $B\otimes E^\vee\to\mathcal Hom_R(E,B)$ is precisely the one of the cited finite-
   projective evaluation lemma, which permits arbitrary module sheaves $B$. All these conclusions
   use only the displayed retraction, so also apply when $m=0$.
   Dependencies: def-weil-pbc-strict-perfect-coefficient-package, lem-pc-finite-projective-
   internal-hom-evaluation.
3. Put $D=\mathcal Hom_R^\bullet(P,R[0])$, so $D^i=\mathcal Hom_R(P^{-i},R)$ and
   $d_D^i=(-1)^{i+1}(-\circ d_P^{-i-1})$. Step 2 verifies the exact-term hypothesis of the
   bounded-Hom lemma. For any representative $F$ of $M|_U$, that lemma applied to $F\to I(F)$
   shows that $\mathcal Hom^\bullet(P,F)$ represents $R\mathcal Hom(P,M|_U)$; applied to $R[0]\to
   I(R[0])$ it shows that $D$ represents $(K^\vee)|_U$. Neither $F$ nor $I(F)$ is required to
   have constructible terms. The complex $D$ is bounded in $[-b,-a]$ with flat terms by step 2,
   hence is K-flat by the cited bounded-above flat criterion. Choose a K-flat flat-term
   resolution $Q\to F$. The cone of $D\otimes Q\to D\otimes F$ is canonically isomorphic to
   $D\otimes\operatorname{Cone}(Q\to F)$, by the total differential formula (multiply the shifted
   summand of degree $i$ in $D$ by $(-1)^i$), and is acyclic by the definition of K-flatness of
   $D$. The K-flat descent theorem computes the ordinary derived tensor by $D\otimes Q$; hence
   $\operatorname{Tot}(D\otimes_R F)$ computes it as well.
   Dependencies: def-pur-hom-complex, def-pur-derived-internal-hom, lem-pc-bounded-exact-term-
   hom-quasi-iso, lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-site-derived-tensor-descent,
   lem-pc-kflat-resolution, def-pc-kflat-complex, def-pc-tensor-complex-sheaves.
4. In total degree $n$, both complexes involve only $a\leq r\leq b$: the source is
   $\bigoplus_{i+j=n}(P^{-i})^\vee\otimes_R F^j$, and the target is $\prod_r\mathcal
   Hom_R(P^r,F^{r+n})$. The product has only finitely many possibly nonzero factors. On the
   summand $D^i\otimes F^j$ define $e^n(\phi\otimes m)$ to have its sole nonzero component at
   $r=-i$, sending $x$ to $(-1)^{ij}\phi(x)m$. Each diagonal component is the ordinary evaluation
   isomorphism of step 2, composed with symmetry and multiplication by $(-1)^{ij}$. Taking their
   finite direct sum gives an isomorphism $e^n$; its inverse applies the inverse evaluation
   separately in each component and the same sign. No infinite-product/direct-sum interchange
   occurs.
   Dependencies: def-pur-hom-complex, def-pc-tensor-complex-sheaves, lem-pc-finite-projective-
   internal-hom-evaluation.
5. The maps $e^n$ form a chain map. For $\phi\in D^i$ and $m\in F^j$, the $d_F$ component of
   $e(d(\phi\otimes m))$ has coefficient $(-1)^i(-1)^{i(j+1)}=(-1)^{ij}$, as in
   $d_{\mathrm{Hom}}e$. The precomposition-by-$d_P$ component has coefficient
   $(-1)^{i+1+(i+1)j}=(-1)^{ij+i+j+1}$, which equals the coefficient $-(-1)^{i+j}(-1)^{ij}$ from
   the Hom differential. Thus $e$ is a chain isomorphism. To identify the map, use the tensor-Hom
   adjunction with evaluation $\mathcal Hom^\bullet(P,F)\otimes P\to F$. The transpose of
   $D\otimes F\to\mathcal Hom^\bullet(P,F)$ moves $P^r$ past $F^j$ in $D^i\otimes F^j\otimes
   P^r$, producing $(-1)^{rj}$, and then evaluates $D^i\otimes P^r\to R[0]$. The evaluation is
   zero unless $r=-i$, when $(-1)^{rj}=(-1)^{ij}$. This is exactly the displayed formula for $e$,
   so its derived image is the specified $\theta_{K,M}|_U$. This also proves compatibility with
   restriction and with morphisms of $M$, because the formula uses only composition, evaluation,
   and the coefficient action.
   Dependencies: def-pur-hom-complex, def-pc-tensor-complex-sheaves, lem-pc-finite-projective-
   internal-hom-evaluation.
6. This proves the finite-level comparison on every member of the chosen covering. Its cone
   restricts to an acyclic complex there, because restriction is exact. Each cohomology sheaf of
   the cone is therefore zero locally: every section restricts to zero on a covering and is zero
   by the separatedness axiom for a sheaf. All its cohomology sheaves vanish, so the cone is zero
   in the derived category and the global $\theta_{K,M}$ is an isomorphism. This argument uses a
   cover of the site and does not replace site-perfectness by stalkwise perfectness.
   Dependencies: lem-pur-site-restriction-module-adjunction-exact, def-weil-abstract-derived-
   category.
7. At the integral stage use the completed coefficient sheaf specified in the definitions. Every
   reduction $K_n$ is site-perfect: apply reduction to the local representative and its
   degreewise finite-free retractions. The same interval $[a,b]$ works on each chosen covering
   object; no bound independent of the covering is needed. By the coefficient-comparison lemma,
   reduction of the actual map $\theta_{K,M}$ is the finite-level map $\theta_{K_n,M_n}$,
   including the identification of the coefficient dual and evaluation. Each is an isomorphism by
   steps 1--6. Both endpoints lie in the stated integral category of the six-functor datum; hence
   so does a cone $C$ by the integral triangulated-subcategory theorem. Derived reduction is
   exact, so every reduction $C_n$ is zero. By derived completeness, $C$ occurs in its Roos
   triangle $C\to\prod_n C_n\xrightarrow{1-s}\prod_n C_n\to C[1]$. Both products are zero; thus
   $C=0$ and the integral comparison is invertible. In particular this argument uses the
   completed tensor of the datum; it never identifies that tensor with an uncompleted tensor
   without proof.
   Dependencies: def-sf-datum, def-weil-derived-pullback-tensor-hom, def-weil-site-perfect-
   complex, lem-fix-operation-reduction, lem-weil-integral-constructible-triangulated, lem-pur-
   derived-change-of-rings, def-weil-derived-complete, def-weil-derived-complete-integral-
   detailed.
8. At the rational stage $K,M\in D^b_c(X,E)$ are objects of $D^b_c(X,\mathcal O_E)$, and by the
   coefficient-operation definition the rational evaluation comparison is the image under the
   localization functor $Q$ of the integral comparison $\theta_{K,M}$ (operations act on objects
   as the integral ones and on morphisms by linear extension). Since $D^b_c(X,\mathcal O_E)$ is a
   full subcategory of $D(X_{\mathrm{proet}},\mathcal O_E)$ and both Hom groups are tensored with
   $E$, $D^b_c(X,E)$ is a full subcategory of the ambient scalar localization
   $D(X_{\mathrm{proet}},\mathcal O_E)[1/\varpi_E]$. For an object $U$, [lem-sf-rational-slice-
   completed-evaluation] makes $j_U^*K,j_U^*M$ derived complete and carries $\theta_{K,M}$, also
   after scalar localization, to $\theta_{j_U^*K,j_U^*M}$. All local work below is done in the
   ambient scalar localizations on slices, so no constructibility of slice internal Homs is
   needed.
   Dependencies: lem-sf-rational-slice-completed-evaluation, def-weil-derived-pullback-tensor-
   hom, def-pur-integral-derived-operations, def-weil-rationalization-karoubi, def-weil-linear-
   scalar-localization.
9. Fix a member $U$ of the chosen covering and put $M_U=j_U^*M$, derived complete by step 8. Let
   $\mathcal S_{M_U}$ be the class of objects $L$ of the derived category of $\widehat{\mathcal
   O}_{E,X}|_U$-modules on the slice for which $Q(\theta_{L,M_U})$ is invertible in its scalar
   localization. The exactness and closure statement [lem-sf-rational-thick-evaluation], applied
   on the slice, puts the unit and zero in $\mathcal S_{M_U}$ and makes it closed under
   isomorphisms and retracts in the scalar localization, finite sums, shifts, and extensions.
   Dependencies: lem-sf-rational-thick-evaluation, def-weil-linear-scalar-localization, lem-sf-
   triangle-morphism-iso.
10. By the rational clause of the site-perfect definition, $j_U^*K\cong P$ for a bounded complex
   $P$ of module sheaves in degrees $[a,b]$ whose terms $P^r[0]$ are direct summands, in the
   scalar-localized category on $U$, of finite sums of the unit. The isomorphism and the
   retractions are morphisms with Hom groups those of the derived category on the slice tensored
   with $E$, so they hold in the ambient scalar localization. Write $\sigma_{\geq r}P$ for the
   brutal truncation (zero below $r$, unchanged from degree $r$ on). The sequence
   $0\to\sigma_{\geq r+1}P\to\sigma_{\geq r}P\to P^r[-r]\to0$ is split in every degree, so the
   degreewise-split triangle lemma gives a distinguished triangle with these three objects; its
   image under $Q$ is distinguished [lem-weil-linear-scalar-localization-triangulated]. Start at
   $\sigma_{\geq b+1}P=0$. Each $P^r[-r]$ lies in $\mathcal S_{M_U}$ by the unit, sum, retract
   and shift clauses of step 9. Descending induction gives $P=\sigma_{\geq a}P\in\mathcal
   S_{M_U}$, hence $j_U^*K\in\mathcal S_{M_U}$: $Q(\theta_{j_U^*K,j_U^*M})$ is invertible. For
   $V\to U$ the same holds over $V$, since restriction along $V\to U$ is an exact functor
   carrying this comparison to the one over $V$ (step 8).
   Dependencies: lem-sf-rational-thick-evaluation, def-weil-site-perfect-complex, lem-weil-pbc-
   degreewise-split-derived-triangle, def-weil-rationalization-karoubi, lem-weil-linear-scalar-
   localization-triangulated, lem-sf-rational-slice-completed-evaluation.
11. For global rational detection: the rational internal Hom of the coefficient-operation
   definition is an operation only on pairs whose integral internal Hom is constructible, so the
   rational assertion concerns $M$ with $R\mathcal Hom(K,\widehat{\mathcal O}_{E,X})$ and
   $R\mathcal Hom(K,M)$ in $D^b_c(X,\mathcal O_E)$; the completed tensor then lies there by the
   same definition. The rational comparison is $Q(f)$ for the integral numerator $f=\theta_{K,M}$
   (step 8). Take an integral cone $C$ of $f$; it lies in the integral category by [lem-weil-
   integral-constructible-triangulated]. Since $Q$ is exact, $Q(f)$ is invertible exactly when
   $Q(C)$ is zero.
   Dependencies: def-weil-rationalization-karoubi, lem-weil-integral-constructible-triangulated,
   def-weil-derived-pullback-tensor-hom.
12. The finite-type definition gives a finite affine open cover of $X$. On each affine, the pro-
   etale covering definition refines the local-model cover by finitely many affine opens $W$ of
   its members. Collect these into a finite family $\{W_j\to X\}$; it is a covering, since $X$ is
   separated, so each $W_j\times_XV$ is affine for an affine open $V$ and finitely many of them
   cover $V$. By step 10 and the slice comparison, the restriction of $\theta_{K,M}$ to $W_j$
   becomes invertible in the ambient scalar localization over $W_j$. Exact slice restriction
   carries the cone triangle of $\theta_{K,M}$ to one for the restricted map, so $C|_{W_j}$ has
   zero image there. The finite-cover localization lemma gives $N\geq0$ with $\varpi_E^N\mathcal
   H^d(C)=0$ for every $d$. For the empty scheme this holds without a nonempty covering.
   Dependencies: lem-sf-rational-local-global-power-torsion, def-weil-finite-type-morphism, def-
   weil-pbc-proetale-site, def-sf-datum, lem-sf-rational-slice-completed-evaluation, lem-pur-
   site-restriction-module-adjunction-exact.
13. By the integral-category definition, the reductions of $C$ have one cohomological interval
   $[u,v]$. Exact countable products put both products in its Roos triangle in $[u,v]$ as well.
   The long exact cohomology sequence thus gives $H^d(C)=0$ outside $[u,v+1]$. Apply the bounded-
   cone torsion lemma with the exponent $N$ from the preceding step and this finite interval: a
   power of $\varpi_E$ kills $\operatorname{id}_C$. Its rational image, and hence the rational
   cone of $\theta$, is zero. This proves the global rational comparison is invertible.
   Dependencies: def-weil-derived-complete-integral-detailed, lem-sf-derived-homology-long-exact,
   lem-weil-proetale-countable-products-exact, def-weil-derived-complete, lem-sf-rational-
   bounded-cone-torsion.
14. For $\overline{\mathbf Q}_\ell$, the definition of site-perfectness gives $K$ as the common-
   stage image of a site-perfect object over some finite coefficient extension. The common-stage
   definition likewise represents $M$ over a finite extension. Choose their compositum $L$, a
   finite common coefficient field, and extend both representatives to $L$. Exact scalar
   extension preserves the unit, finite sums, retractions and the finite cone construction of the
   local perfect model. Hence the representative of $K$ at this common field is still site-
   perfect. The coefficient comparisons identify the scalar-extended dual, tensor and internal
   Hom, and preserve evaluation; therefore they identify the representative of $\theta$ with the
   rational comparison over $L$ proved invertible in steps 8--13. That inverse over $L$
   represents an inverse in the common-stage category, since its two inverse equations remain
   equations after passing to the common-stage morphism classes. Together with steps 1--7 this
   proves the assertion at every allowed coefficient stage.
   Dependencies: def-weil-site-perfect-complex, def-weil-algebraically-closed-coefficients, def-
   weil-derived-pullback-tensor-hom, lem-weil-scalar-extension-exact-triangulated, lem-fix-
   operation-reduction. -/
theorem sixFunctor_sitePerfect_dualEvaluation_isIso
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_pos n))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (∀ K M : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory,
      IsFiniteCoefficientSitePerfect C.l E X.obj.left n K.obj.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.finiteClosed X).closed
        (S.finiteClosed X).symmetric (S.finiteClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) ∧
    (∀ K M : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory,
      IsIntegralCoefficientSitePerfect C.l E X.obj.left K.obj.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.integralClosed X).closed
        (S.integralClosed X).symmetric (S.integralClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) ∧
    (∀ K M : (⊤ : ObjectProperty
        (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory,
      IsSfRationalCoefficientSitePerfect C.l E X.obj.left K.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.rationalClosed X).closed
        (S.rationalClosed X).symmetric (S.rationalClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) ∧
    (∀ K M : (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory,
      IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left K.obj →
      IsIso (ringedSiteDualEvaluationLeft (S.commonClosed X).closed
        (S.commonClosed X).symmetric (S.commonClosed X).closed.monoidal.tensorUnit
        (Iso.refl _) K M)) := by
  sorry

end WeilConjectures
