/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.LisseRationalRealizationData
public import Sheaf.Paper.LissePullbackNormalization
public import Sheaf.Paper.LisseFieldNormalization
public import Sheaf.Paper.LissePointNormalization
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback

import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage

/-! # Canonically normalized lisse realization

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
Proposition 6.8.14(2), Remark 6.8.15, pp. 58--62
(blueprint: lem-tw-lisse-rational-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The common-stage transition comparison is the finite-field comparison, including
its action on all lisse morphisms. Source: blueprint common-stage clause
(blueprint: lem-tw-lisse-rational-realization). -/
structure CommonNormalized (a : Family D l hl) (Ω : Type u) [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (X : Base D l hl)
    (c : CommonStage D l hl Ω a X) where
  transitions : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X.scheme)
    (hK : Lisse D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X K),
    HEq ((c.comparison.β h).inv.app K)
      ((a.fieldChange (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).comparison K hK).hom

/-- The simultaneous realization assertion. All structures quantified after the existential
are comparison data in the conclusion; in particular their exactness fields add no hypotheses.

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
Proposition 6.8.14(2), Remark 6.8.15, pp. 58--62
(blueprint: lem-tw-lisse-rational-realization).

Proof plan:
1. A field is noetherian (its only ideals are $0$ and the unit ideal). Apply [pqf-lem-locnoeth-
lft] to the structure map of $X$ and use its quasi-compactness, part of finite type, to see that
$X$ is noetherian. By [lem-kun-dimension-finite-type] it has finite Krull dimension. Its
underlying noetherian space has every open quasi-compact, so $X$ is qcqs even without
separatedness. The same statements apply to $X'$ and to quasi-compact etale charts of either.
The coefficient identifications of [lem-weil-pbc-continuous-coefficients-immersion-restriction]
identify $\widehat R_X$ with the continuous integral coefficient sheaf and $E_X$ with its sheaf
localization. Thus the lattice and continuity results cited below concern exactly these rings.
Uses: pqf-lem-locnoeth-lft, lem-kun-dimension-finite-type, lem-weil-pbc-continuous-coefficients-
immersion-restriction.

2. Put $B=\widehat R_X$, $t=\varpi$ and $F(K)=B[1/t]\otimes_B^LK$. Localization is exact:
sectionwise localization is flat by [lem-weil-pbc-localization-flat] and preserves kernels,
while module sheafification is exact by [lem-weil-pbc-ringed-site-module-sheafification-exact];
hence localization of an exact sheaf sequence is exact after sheafification. It follows that
$H^i(FK)=H^i(K)[1/t]$. For integral constructible $K$, [lem-weil-pbc-integral-constructible-
bounded-below-compactness] supplies bounded-below coproduct continuity of global derived Hom.
Taking $H^0$ gives the Hom continuity hypothesis of [lem-weil-pbc-scalar-localization-derived-
hom] (cohomology of a direct sum of module complexes is the direct sum of cohomology, since
cycles and boundaries have finite support). Apply that lemma to bounded integral constructible
$K,L$. It gives $$\operatorname{Hom}(K,L)\otimes_RE\cong\operatorname{Hom}_{D(E_X)}(FK,FL),\quad
u\otimes a\mapsto aF(u).$$ The same lemma gives identity and composition compatibility. By [def-
weil-rationalization-karoubi] these are precisely the Hom groups of the raw rationalization, so
$F$ descends to a fully faithful functor with exactly the prescribed arrow formula. Uses: lem-
weil-pbc-localization-flat, lem-weil-pbc-ringed-site-module-sheafification-exact, lem-weil-pbc-
integral-constructible-bounded-below-compactness, lem-weil-pbc-scalar-localization-derived-hom,
def-weil-rationalization-karoubi.

3. Restriction to a site slice commutes with sheaf tensor by [lem-sfb-localized-site-tensor-
restriction], and with the strict derived limit by [lem-sp-slice-restriction-strict-derived-
limit]. Thus it also commutes with the coefficient localization and the completed coefficient
constructions used here. The sheaf-site interpretation of a weakly etale chart is [lem-weil-
proetale-weakly-etale-localization]. On an object of the lisse source, restrict its given local
isomorphism with a finite sum of the coefficient unit and apply $F$. By [lem-weil-constant-
coefficient-objects-constructible] the unit is represented by $B[0]$, whose image is $E_X[0]$.
Consequently $FK$ is locally finite free in degree zero. This also identifies the lisse heart
with a full subcategory of ordinary sheaves: morphisms between complexes concentrated in degree
zero in a derived category are their sheaf morphisms. The standard heart is [def-weil-
constructible-heart], with the cohomological standard classes of [def-weil-constructible-
standard-tstructure]; exact localization carries both classes into their ordinary cohomological
counterparts. Uses: lem-sfb-localized-site-tensor-restriction, lem-sp-slice-restriction-strict-
derived-limit, lem-weil-proetale-weakly-etale-localization, lem-weil-constant-coefficient-
objects-constructible, def-weil-constructible-heart, def-weil-constructible-standard-tstructure.

4. Conversely let $L\in\operatorname{Loc}(X,E_X)$. By [lem-weil-pbc-lisse-e-constructible-
integral-lattice] there is a constructible integral sheaf $N$ with $N[1/t]\cong L$. By [lem-
weil-pbc-integral-stratified-perfect-characterization], $N[0]$ is an integral constructible
derived-complete object, so its rationalization is in the standard heart. To verify that this
object is lisse, use [lem-weil-pbc-lisse-lattice-etale-local] and refine its etale cover by
quasi-compact charts $Y_i$. It gives integral finite locally free $M_i$ with $M_i[1/t]\cong
L|_{Y_i}$. The same stratified-perfect characterization puts $M_i[0]$ in the integral
constructible category. Step 2 on the noetherian finite-dimensional $Y_i$ lifts the specified
isomorphism $N[1/t]|_{Y_i}\cong M_i[1/t]$ and its inverse uniquely to the rationalized category.
The lifts are inverse because their composites realize to identities and realization is
faithful. Each $M_i$ is pro-etale locally a finite free coefficient module, hence these local
lifts give the required local isomorphisms for the rationalization of $N$. Together with Step 3
and Step 2 this proves the equivalence and its exact Hom normalization; it never asserts that
$L$ has a globally lisse integral lattice. Uses: lem-weil-pbc-lisse-e-constructible-integral-
lattice, lem-weil-pbc-integral-stratified-perfect-characterization, lem-weil-pbc-lisse-lattice-
etale-local, def-weil-constructible-standard-tstructure.

5. For integral representatives $M,N$, the specified map $\chi_{M,N}$ of [lem-fix-constructible-
tensor-completion] identifies the ordinary ambient derived tensor with the completed tensor used
by [def-weil-derived-pullback-tensor-hom]. Apply scalar localization and the ordinary ringed-
topos monoidal comparison of [lem-sfb-ringed-derived-monoidal-comparisons] to obtain
$$F(M\widehat\otimes_R^LN)\cong FM\otimes_{E_X}^LFN.$$ For lisse inputs the right side is
ordinary sheaf tensor in degree zero: on a basis chart, tensoring with a finite free module is a
finite direct sum of the identity functor, hence exact. Exactness and vanishing of the higher
tensor cohomology are local statements about sheaves, so this calculation suffices. The map
sends $e_i\otimes e_j$ to the corresponding pure tensor. The unit comparison is multiplication
$E_X\otimes_BE_X\to E_X$, with $1\otimes1\mapsto1$. Uses: lem-fix-constructible-tensor-
completion, def-weil-derived-pullback-tensor-hom, lem-sfb-ringed-derived-monoidal-comparisons.

6. For an arbitrary scheme map $f:X'\to X$, apply [lem-tw-ordinary-completed-integral-pullback]
to identify completed integral pullback with $P_fK=B_{X'}\otimes^L_{f^{-1}B_X}f^{-1}K$. The two
paths of ordinary derived scalar extension around the ring square $f^{-1}B_X\to B_{X'}$,
$f^{-1}E_X\to E_{X'}$ are canonically the same, by the composition and monoidal comparisons of
[lem-sfb-ringed-derived-monoidal-comparisons]. Consequently $$F_{X'}(Lf_E^*K)\cong
E_{X'}\otimes^L_{f^{-1}E_X}f^{-1}(F_XK).$$ For lisse $K$, $f^{-1}(F_XK)$ is locally finite free
over $f^{-1}E_X$, so the displayed tensor is ordinary and in degree zero. On pulled-back bases
the comparison is $1\otimes e_i\mapsto e_i$. Both the new integral comparison and ordinary
ringed-topos composition apply to all scheme maps, so no $k$-linearity or separatedness
hypothesis has entered. Uses: lem-tw-ordinary-completed-integral-pullback, lem-sfb-ringed-
derived-monoidal-comparisons, def-weil-derived-pullback-tensor-hom.

7. For $E\subset L$ finite, [lem-weil-finite-free-completed-scalar-comparison] identifies the
integral transition functor with ordinary derived change of completed coefficient rings via its
specified quotient-cone map $\chi_{L/E,K}$. Localizing this isomorphism gives the ordinary
extension of continuous field coefficients on realized objects, with $e_i\otimes b\mapsto b
e_i$. The comparison is natural on integral arrows; the formula in Step 2 extends it to all
rationalized arrows. The scalar-operation comparisons of [lem-pur-integral-operations-scalar-
extension] therefore identify the field extensions of the tensor and pullback comparisons of
Steps 5 and 6 with the same comparisons over $L$. Uses: lem-weil-finite-free-completed-scalar-
comparison, lem-pur-integral-operations-scalar-extension, lem-sfb-ringed-derived-monoidal-
comparisons.

8. Check that these are the specified coherent comparisons. The completed tensor associators,
unitors and symmetry are the limits of the finite total-complex maps by [lem-pur-completed-
operation-tower-substitution]. The normalized integral pullback composition and its scalar
compatibility are those realized from simultaneous quotient diagrams in [lem-trf-integral-
pullback-comparison-realization]. The maps $\chi$ in Steps 5 and 7 and $\eta$ in Step 6 use
those same quotient maps, with zero shifted-product component. Thus they intertwine these finite
diagrams before realization. On the ordinary side [lem-sfb-ringed-derived-monoidal-comparisons]
supplies the corresponding monoidal and composition laws. Alternatively, after realizing lisse
inputs every resulting diagram is checked on a common local basis: associativity sends
$(e_i\otimes e_j)\otimes e_k$ to $e_i\otimes(e_j\otimes e_k)$, symmetry interchanges the two
basis vectors, units multiply by $1$, and successive pullbacks send a basis vector to the same
basis vector. The scalar maps send it to $e_i\otimes b$, with successive scalars multiplied.
Both paths therefore agree on generators, then on all sections by linearity and the sheaf axiom.
All objects here are in degree zero, so the symmetry sign is $+1$. This proves the requested
naturality, identity, composition and coherence assertions. Uses: lem-pur-completed-operation-
tower-substitution, lem-trf-integral-pullback-comparison-realization, lem-sfb-ringed-derived-
monoidal-comparisons.

9. Put $s=\operatorname{Spec}k$. By [lem-weil-point-proetale-sections-exact], sections of any
coefficient module sheaf on $s$ are exact. The continuous-coefficient identification of Step 1
gives $B_s(s)=R$ and $E_s(s)=E$, because a continuous function on the one-point space $|s|$ is
its value. For any integral constructible $C$ at $s$, the canonical sections-localization map
$$\Gamma(s,C)\otimes_RE\longrightarrow\Gamma(s,FC)$$ is an isomorphism: apply Step 2's Hom-
localization result with $K=B_s$ and $L=C[q]$ for every $q$. The unit $B_s$ is constructible by
[lem-weil-constant-coefficient-objects-constructible], and
$\operatorname{Hom}(B_s,C[q])=H^q\Gamma(s,C)$ by exact sections and evaluation at $1$. These Hom
identifications are exactly the cohomology maps of the displayed canonical map; [lem-weil-pbc-
unbounded-derived-iso-cohomology] proves invertibility. Combining it with Step 6 for $x:s\to X$
identifies the rational point fibre defined in [def-weil-finite-coefficient-point] with sections
of the ordinary pullback. All maps used are natural in $C$ and $K$. Uses: lem-weil-point-
proetale-sections-exact, lem-weil-constant-coefficient-objects-constructible, lem-weil-pbc-
scalar-localization-derived-hom, lem-weil-pbc-unbounded-derived-iso-cohomology, def-weil-finite-
coefficient-point.

10. For lisse point objects the fibre in Step 9 is a finite-dimensional vector space: [lem-weil-
point-fibre-equivalence] places it in $D^b_{\mathrm{fd}}(E)$, and exact localization and
sections put its cohomology in degree zero. Choose a finite basis of this space. Full
faithfulness of the point fibre functor in [lem-weil-point-fibre-equivalence] lifts its basis
isomorphism to an isomorphism of the point object with a finite sum of units. Hence the
sections-tensor comparison and the fibre-tensor comparison are the same map: on these finite
sums both send $e_i\otimes e_j$ to $e_i\otimes e_j$, and send the unit $1$ to $1$. Naturality
removes the choice of basis. This verifies tensor and unit compatibility of Step 9, including
rank zero. Uses: lem-weil-point-fibre-equivalence, def-weil-finite-coefficient-point, lem-weil-
point-proetale-sections-exact.

11. Let $h:s\to s$ be a scheme automorphism. By [lem-weil-proetale-isomorphism-inverse-image],
$h^{-1}$ is an exact equivalence commuting with coefficient limits and colimits, with structure
map induced by the finite coefficient maps. Use the restriction-and-coprojection construction of
[def-weil-frobenius-point-transport] with $h$ in place of $g_s$. Its integral comparison
$\kappa$ is the quotient-cone map of [def-weil-inverse-image-pullback-comparison]. Under the
normalized $\eta_h$ of Step 6 it becomes the ordinary module unit $z\mapsto1\otimes z$: both
maps into every quotient are the reduction followed by that unit, and both have zero shifted-
product component. Under Step 9, a localized section $z/t^n$ is consequently sent to
$$t^{-n}\bigl(1\otimes\operatorname{ins}(\operatorname{res}_h z)\bigr).$$ Restriction and the
inverse-image colimit coprojection commute with multiplying by $t$ and with the coefficient
maps. This is exactly restriction, then coprojection, then the ordinary module unit applied to
the localized section. Thus the point-transport maps themselves agree under realization, rather
than only being conjugate by an arbitrary fibre isomorphism. The calculation is natural in sheaf
maps and coefficient extensions. Uses: lem-weil-proetale-isomorphism-inverse-image, def-weil-
frobenius-point-transport, def-weil-inverse-image-pullback-comparison, lem-tw-ordinary-
completed-integral-pullback.

12. The equality for iterates follows by induction: for zero iterations both sides are
identities; if the identification intertwines the first $r$ transport factors, compose that
equation with the one-factor equation of Step 11 applied to the $r$-fold pulled-back object.
Step 8's pullback composition law identifies the resulting source and target. Every tensor and
scalar compatibility persists under this composition. Uses: .

13. Finally use [def-weil-algebraically-closed-coefficients]. An object, a morphism, or a finite
diagram in the common-stage category is represented over a finite field after taking a
compositum. Apply Steps 2-12 there and then extend scalars to $\Qlb$ where the fibre definition
requires it. Step 7 and Step 8 identify the results after any further finite extension. Equal
representatives therefore yield equal maps, and inverse maps remain inverse at larger stages.
This gives the stated common-stage lisse assertions and all tensor, pullback, fibre and point-
transport compatibilities for $\Sh_c(X,\Qlb)$. Uses: def-weil-algebraically-closed-coefficients,
def-weil-finite-coefficient-point.
-/
theorem lisse_rational_realization :
    ∃ a : Family D l hl,
      (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
        (X : Base D l hl), Nonempty (TensorNormalized D l hl A X
          (a.realization A X) (a.tensor A X))) ∧
      (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
        {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme),
        Nonempty (PullNormalized D l hl A f (a.realization A X) (a.realization A Y)
          (a.along A f))) ∧
      (∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
        [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
        (i : A →ₐ[ℚ_[l]] B) (X : Base D l hl),
        Nonempty (FieldNormalized D l hl A B i X (a.realization A X) (a.realization B X)
          (a.fieldChange A B i X))) ∧
      (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A],
        Nonempty (PointNormalized D l hl A (a.realization A (point D l hl)) (a.point A))) ∧
      (∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (X : Base D l hl), ∃ c : CommonStage D l hl Ω a X,
          Nonempty (CommonNormalized D l hl a Ω X c)) := by
  sorry

end WeilConjectures.LisseRealization
