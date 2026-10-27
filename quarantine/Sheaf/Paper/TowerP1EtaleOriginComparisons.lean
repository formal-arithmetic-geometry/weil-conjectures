/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.TowerP1FormulaLevelComparisons
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData
public import Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import Sheaf.Paper.TateTwistLocallyFree
import Sheaf.Paper.RingedSitePerfectProjectionFormula
import Sheaf.Paper.SmoothPurityTowerLevels
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.CartierReductionSiteComparison

/-! # Canonical projective-line comparisons on etale-origin tower domains

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Construction and Levels (blueprint: lem-sp-tower-p1-etale-origin-comparisons).

We reuse the domain, geometric presentation, and actual diagonal/trace words of
`SpTowerP1`. The adjunction theorem in that module is not used. Positive level n+1
is indexed by n : Nat. No transition-compatible choice of etale origins is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Boundedness of the source and target of a specified arrow, without a Tor condition.
Source: Construction, domains (blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
def boundedArrow {T : Scheme.{u}} {X Y : SpTowerShriek.D l E T} (_f : X ⟶ Y) : Prop :=
  (∃ a : ℤ, DerivedCategory.IsGE X a) ∧ (∃ a : ℤ, DerivedCategory.IsGE Y a)

/-- Full level assertion at the actual finite quotient. This local instance is
only the already recorded finiteness proof for the coefficient ring.
Source: Levels (blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
def levelComparisons (p : Presentation l E S hS) (d : Maps l E p)
    (hD : (diagonalImmersion S).ker.IsInvertible) (n : ℕ) : Prop :=
  letI : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
  ∃ c : ProjectiveCoordinates l E n p,
    ProjectionLevelComparisons l E n c ∧ ExchangeLevelComparisons l E n c ∧
      ClassLevelComparisons l E n c hD ∧ FormulaLevelComparisons l E n c d hD

/-- All additional assertions on the canonical words. Tensor and geometric operations
are those of the given normalized section model, not freely supplied functors or maps.
Source: Construction and Levels (blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
structure EtaleOriginComparisons (p : Presentation l E S hS) (d : Maps l E p) : Prop where
  proper_q : IsProper (ProjectiveLine S ↘ S)
  qc_q : QuasiCompact (ProjectiveLine S ↘ S)
  qs_q : QuasiSeparated (ProjectiveLine S ↘ S)
  proper_projections : ∀ a : Bool, IsProper (Etale.projectiveLineDiagonalProjection S a)
  qc_projections : ∀ a : Bool, QuasiCompact (Etale.projectiveLineDiagonalProjection S a)
  qs_projections : ∀ a : Bool, QuasiSeparated (Etale.projectiveLineDiagonalProjection S a)
  proper_diagonal : IsProper (diagonalImmersion S)
  qc_diagonal : QuasiCompact (diagonalImmersion S)
  qs_diagonal : QuasiSeparated (diagonalImmersion S)
  cartier_diagonal : (diagonalImmersion S).ker.IsInvertible
  qc_complement : QuasiCompact ((@id (diagonalSurface S).Opens
    (diagonalImmersion S).ker.support.compl).ι)
  diagonal_exact : PreservesFiniteLimits (p.operations.geometry (diagonalImmersion S)).push ∧
    PreservesFiniteColimits (p.operations.geometry (diagonalImmersion S)).push
  source_iso : ∀ M : C l E p.classes.base (ProjectiveLine S),
    IsIso (p.sourceUnit l E M.obj)
  projection_q_bounded : ∀ K : C l E p.classes.base S,
    boundedArrow l E (projection l E (p.operations.geometry (ProjectiveLine S ↘ S))
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) K.obj)
  projection_projections : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S)),
    IsIso (projection l E (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) M.obj)
  projection_projections_bounded :
    ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S)),
    boundedArrow l E
      (projection l E (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
        ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) M.obj)
  projection_diagonal : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S)),
    IsIso (projection l E (p.operations.geometry (diagonalImmersion S))
      (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
      ((SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M.obj))
  projection_diagonal_bounded : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S)),
    boundedArrow l E (projection l E (p.operations.geometry (diagonalImmersion S))
      (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
      ((SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M.obj))
  exchange_swap : ∀ M : C l E p.classes.base (ProjectiveLine S),
    IsIso (p.exchangeSwap l E M.obj)
  exchange_bounded : ∀ M : C l E p.classes.base (ProjectiveLine S),
    boundedArrow l E (p.exchange l E M.obj) ∧ boundedArrow l E (p.exchangeSwap l E M.obj)
  eta_natural : ∀ (M N : C l E p.classes.base (ProjectiveLine S)) (f : M ⟶ N),
    f.hom ≫ eta l E d N = eta l E d M ≫ (p.G l E).map ((p.F l E).map f.hom)
  epsilon_natural : ∀ (K L : C l E p.classes.base S) (f : K ⟶ L),
    (p.F l E).map ((p.G l E).map f.hom) ≫ epsilon l E d L = epsilon l E d K ≫ f.hom

  levels : ∀ n : ℕ,
    levelComparisons l E p d cartier_diagonal n

/-- The natural transformation with exactly the diagonal-defined components.
Source: Construction, eta (blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
def etaTransformation {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisons l E p d) :
    𝟭 (C l E p.classes.base (ProjectiveLine S)) ⟶ left l E d ⋙ rightRestricted l E d where
  app M := ObjectProperty.homMk (eta l E d M)
  naturality M N f := ObjectProperty.hom_ext _ (h.eta_natural M N f)

/-- The natural transformation with exactly the inverse-projection and trace components.
Source: Construction, epsilon (blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
def epsilonTransformation {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisons l E p d) :
    rightRestricted l E d ⋙ left l E d ⟶ 𝟭 (C l E p.classes.base S) where
  app K := ObjectProperty.homMk (epsilon l E d K)
  naturality K L f := ObjectProperty.hom_ext _ (h.epsilon_natural K L f)

/-- The canonical comparison from derived diagonal direct image to exact diagonal direct image.
It is the library's localization comparison, with no choice of an isomorphism.
Source: Construction, exactness (blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
def diagonalExactComparison {p : Presentation l E S hS} {d : Maps l E p}
    (h : EtaleOriginComparisons l E p d) :
    SpTowerShriek.push l E p.classes.base (p.operations.geometry (diagonalImmersion S)) ≅
      (p.operations.geometry (diagonalImmersion S)).push.mapDerivedCategory :=
  letI := p.classes.base.kinjective (ProjectiveLine S)
  letI := h.diagonal_exact.1
  letI := h.diagonal_exact.2
  (p.operations.geometry (diagonalImmersion S)).push.rightDerivedFunctorIsoMapDerivedCategory

/-- Canonical proper projection and exchange on the full bounded-below etale-origin domain,
with the diagonal/trace natural transformations and normalized finite comparison words.
No finite-Tor, constructibility, normalization, Noetherianity or base-compactness hypothesis
is imposed. The level assertions are commuting squares for the specified maps, including
the complete diagonal eta and splitting-trace epsilon formulas, for every retained origin witness.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Construction and Levels
(blueprint: lem-sp-tower-p1-etale-origin-comparisons).

Proof plan, following the reviewed DAG split:

1. The projective-space properness theorem makes $q$ proper; $p_1,p_2$ are its base changes, hence
proper. Proper means separated and finite type; finite type includes quasi-compactness, and a
separated morphism is quasi-separated. The diagonal of the separated map $q$ is closed, so
$\Delta$ is proper too and has the same qcqs consequences. Its Cartier property is supplied by the
diagonal-ideal lemma. To check the complementary open is quasi-compact as an immersion, work over
an affine base open and use the four standard affine product charts. The diagonal equations are
$t-u$, $tv-1$, $su-1$, $s-v$ on the finite/finite, finite/infinite, infinite/finite,
infinite/infinite charts. The complement on each chart is the corresponding principal open. Each
is affine, hence quasi-compact; this is a cover-local check on the target, requiring no
quasi-compactness of $S$.
Uses: lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-proper-base-change,
def-weil-proper-morphism, def-weil-finite-type-morphism, lem-pc-separated-quasi-separated,
lem-weil-pbc-closed-immersion-proper, lem-amb-p1-diagonal-cartier.

2. Apply exactness of pro-etale closed direct image with quasi-compact complementary open to
$\Delta$, separately with each constant finite ring $B_n$. Kernels and cokernels in the
varying-ring tower category are componentwise, so $\Delta_{*,\bullet}$ is exact. Its termwise
complex functor therefore computes its derived functor on bounded-below complexes: an exact
functor takes acyclic complexes to acyclic complexes, so its localization agrees with its right
derived functor. Thus $R\Delta_{*,\bullet}=\Delta_{*,\bullet}$ canonically, and it preserves every
lower bound.
Uses: lem-exc-proetale-closed-exact, det-sp-coefficient-towers-abelian.

3. Use the simultaneous section-model operations to form the tensor, projection transposes,
exchange and composition maps in the ordinary unbounded tower derived categories. Evaluation
preserves these specified words, including their units and counits. The compatible-root cover
trivializes the Tate line tower simultaneously at all levels. Tensor by this line is exact, since
it becomes tensor by the ring on that cover, and is invertible with inverse the negative twist.
The line is locally free of rank one as a module in the inverse-system topos, hence perfect there.
The perfect ringed-site projection theorem, applied with this line on the target of $q$ or $p_i$,
gives the canonical isomorphisms $Rh_*(C(1)[2])\simeq(Rh_*C)(1)[2]$. This also fixes the twist
identifications in the trace and in the displayed formulas.
Uses: lem-coef-semilinear-derived-sections, det-def-sp-tate-twist-locally-free,
lem-sbc-ringed-site-perfect-projection-formula.

4. For $h=q,p_1,p_2$, use the splitting of the tower classes lemma over the base of $h$, then the
twist identification of Step 3. It gives $Rh_{*,\bullet}(A(1)[2])\simeq A(1)[2]\oplus A$. If $K$
or $M$ has cohomology zero below $a$, its tensor with this object has zero cohomology below $a-2$:
tensor distributes over the two summands and tensor by either line is exact. Exact inverse images,
closed direct image, and twists preserve lower bounds, the shift $[2]$ lowers them by two, and
right derived direct image preserves lower bounds. The latter assertion follows by taking the
bounded-below injective resolution of a complex zero below that bound. Consequently all the
projection sources involving $q$ or $p_i$, their targets, and the exchange sources and targets
have uniform lower bounds. The remaining supported projection source is checked in Step 7.
Uses: det-sp-tower-classes, lem-coef-semilinear-derived-sections, sk-lem-sp-tower-levels.

5. Fix a level $n$ and retain an origin witness $\nu_P^*L_n\simeq M_n$. The tower direct-image
evaluation followed by the canonical direct-image mate gives $(FM)_n\simeq
Rq_{p,*}\nu_P^*L_n\simeq\nu_S^*Rq_{e,*}L_n$, a bounded-below etale origin. For a witness
$\nu_S^*H_n\simeq K_n$, exact pullback comparison, the monoidal comparison
$\nu_P^*(U\otimes^LV)\simeq\nu_P^*U\otimes^L\nu_P^*V$ of the comparison morphism with constant
rings, and the root-site isomorphism $\sigma:\nu_P^*B_{n,P}(1)_{\mathrm{et}}\simeq B_{n,P}(1)$
give $(GK)_n\simeq\nu_P^*(q_e^{-1}H_n(1)[2])$. The pro-etale twist here is the root tower of the
tower classes, whose level $n$ is the pro-etale root tensor $D_{\ell^n,P}$ of the root-site
comparison. Steps 3-4 give the uniform tower bounds, so these witnesses prove that $F$ and $G$
restrict to the displayed full subcategories. The same argument applies to $p_i$ and $\Delta$
whenever used below. There is no need to choose the $L_n$ or $H_n$ compatibly with tower
transitions.
Uses: sk-lem-sp-tower-levels, lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-weil-pbc-comparison-pullback, lem-asd-etale-finite-twist-pullback,
def-weil-pbc-etale-origin-witness, lem-sfb-ringed-derived-monoidal-comparisons,
lem-amb-finite-root-site-comparison.

6. For a qcqs map $h:U\to V$ apply the ringed exchange/tensor coherence theorem to the commutative
square with vertical maps $h_e,h_p$ and horizontal comparison maps $\nu_U,\nu_V$. This is a square
of ringed topoi with the constant rings $B_n$; cartesianness is not needed. Its exchange is
exactly $b_h:\nu_V^*Rh_{e,*}\to Rh_{p,*}\nu_U^*$, because both are the transpose of the pullback
comparison followed by the etale counit. The theorem therefore identifies the specified projection
maps, under the monoidal tensor and pullback comparisons, by $$b_{h,E\otimes
h_e^*Q}\,\nu_V^*(\pi^e_{h,E,Q})=\pi^p_{h,\nu_U^*E,\nu_V^*Q}(b_{h,E}\otimes1).$$ Here the target
also uses $\nu_U^*h_e^*Q\simeq h_p^*\nu_V^*Q$. The comparisons $b$ are used only for bounded-below
$E$ and $E\otimes h_e^*Q$, as verified in Step 7. Naturality carries the equality through any
specified origin witnesses, without asserting that a tower of witnesses exists.
Uses: lem-weil-pbc-ringed-exchange-tensor-coherence,
lem-weil-pbc-comparison-direct-image-canonical-mate, lem-sfb-ringed-derived-monoidal-comparisons.

7. At level $n$ apply the finite-ring ordinary-etale proper projection theorem to
$(h,E,Q)=(q,B_{n,P}(1)[2],H_n)$, to $(p_i,B_{n,W}(1)[2],L_n)$, and to
$(\Delta,B_{n,P},p_{i,e}^*L_n)$. All three maps are isomorphisms without a Tor hypothesis. In the
first two cases $E\otimes h_e^*Q$ is a shifted line twist of an exact inverse image, so is bounded
below. In the third it is $L_n$, using $p_i\Delta=1_P$, so again is bounded below. Step 6
transports these particular maps to the pro-etale site; Step 3 identifies them with the
evaluations of the actual tower maps. Joint conservativity of derived evaluations makes each tower
projection invertible. Moreover the supported source $\Delta_*A_P\otimes^Lp_i^*M$ has the same
lower bound as $\Delta_*M$: the evaluated isomorphisms identify their cohomology, and exact
componentwise evaluations detect vanishing of each cohomology tower. This completes the
boundedness assertion without using finite Tor amplitude of $K$ or $M$.
Uses: lem-etale-proper-projection-formula-finite-objectwise, lem-coef-semilinear-derived-sections,
lem-weil-pbc-comparison-pullback, lem-asd-etale-finite-twist-pullback.

8. The square with $q,q$ and $p_1,p_2$ is Cartesian. At level $n$, the exchange-transport theorem
identifies its specified ordinary-etale exchange with its specified pro-etale mate under the
canonical direct-image and pullback comparisons. Ordinary-etale proper base change over the
torsion ring $B_n$ makes this exchange invertible on $L_n$. Evaluation of the tower exchange is
precisely this mate by the section-model theorem. Joint conservativity therefore makes
$q_\bullet^*FM\to Rp_{2*,\bullet}p_1^*M$ invertible. Swapping the two factors gives the other
exchange; the same proof applies with $p_1$ and $p_2$ interchanged.
Uses: lem-weil-pbc-transport-identifies-exchange, lem-kun-proper-base-change-torsion-ring,
lem-coef-semilinear-derived-sections.

9. Use the canonical direct-image compositor for $p_i\Delta=1_P$ to identify $M$ with
$Rp_{i*,\bullet}\Delta_*M$, using Step 2. This identification evaluates to the finite compositor.
It also agrees with transport by $\nu^*$: the pullback comparisons $a$ respect identities and
composites, so the pullback square for $p_i\Delta$ is the pasting of those for $\Delta$ and $p_i$;
the two direct-image comparisons are the mates of this pasted pullback square, so the mate-pasting
identity identifies their composite with the comparison for the composite map. The identity clause
makes the comparison for $1_P$ the identity. The monoidal and adjunction-compatible composition
theorem gives the corresponding compatibility with tensor, symmetry and the identity pullback. The
shift comparisons in the ringed projection theorem fix the integer shifts as well. Hence these are
the specified composition source, twist and shift identifications used in $\eta$, not
independently chosen isomorphisms of their objects.
Uses: lem-coef-semilinear-derived-sections,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-mate-pasting,
lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-ringed-projection-mate-exact,
lem-weil-pbc-comparison-pullback.

10. Now compose the inverse projection and exchange isomorphisms proved in Steps 7-8 with
$Rp_{2*,\bullet}(\delta_\bullet\otimes1)$, as written in the statement, to define $\eta_M$.
Compose the inverse $q$-projection with $1\otimes t_q$ to define $\varepsilon_K$. The comparisons
are natural, and inversion of a natural isomorphism is natural (multiply its naturality square by
its two inverses), so the composites are natural transformations. Evaluation sends
$\delta_\bullet$ and $t_q$ to the finite supported diagonal class and splitting trace by the tower
classes lemma. The supported Cartier comparison identifies that class, including its source and
positive Kummer sign, with the ordinary-etale class after $\nu^*$. For the trace, the evaluated
$t_q$ is $\operatorname{pr}_2$ of the inverse of the finite unit/Chern splitting whose Chern
component is the pulled-back etale Kummer class of $\mathcal O_P(1)$, with the pro-etale root
twist. The counit normalization of the direct-image comparison $b_q$, transposed, shows that
$b_q\circ\nu_S^*$ carries the etale unit to the pro-etale unit and the etale adjoint of the Chern
class to the pro-etale adjoint of its pullback; with $\sigma$ on the twist, $b_q$ therefore
carries $\nu_S^*$ of the etale splitting to the evaluated tower splitting, hence $\nu_S^*$ of the
etale trace to the evaluated $t_q$. The same holds for $t_1,t_2$ over $P$. Steps 6, 8 and 9
identify every remaining projection, exchange and composition arrow, including inverse arrows.
Thus the evaluated composites are exactly the asserted ordinary-etale diagonal and splitting-trace
formulas after comparison. The verification concerns these composites of specified maps, and
imposes no finite-Tor or normalization condition.
Uses: det-sp-tower-classes, lem-sp-cartier-reduction-site-comparison,
lem-coef-semilinear-derived-sections, lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-amb-finite-root-site-comparison.
-/
theorem towerP1EtaleOriginComparisons (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤))) :
    ∀ p : Presentation l E S hS, ∃ d : Maps l E p, EtaleOriginComparisons l E p d := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
