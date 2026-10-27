/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.KummerLogMorphism
public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalk

/-!
# Finite Kummer étale covers of a strictly local base

Source: ILO, Exposé VI 2.1--2.3, printed pp.71--73
(blueprint: lem-per-kummer-strict-local-standard-model).

The standard models use the ordinary scheme pullback; the character diagonal is
instead a pullback in fs log schemes. The diagonal is stated by its universal property
on the disjoint union, without choosing a second fs fibre product. Invariant identities
are tested on every small étale object with the actual canonical pullback maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The final object of the small étale site, for the global charts in ILO VI 2.2
(blueprint: lem-per-kummer-strict-local-standard-model). -/
def kummerGlobalTest (X : Scheme.{u}) : X.Etale :=
  Scheme.Etale.mk (𝟙 X)

/-- The canonical pointed lift to the final étale object. Source: ILO VI 2.2
(blueprint: lem-per-kummer-strict-local-standard-model). -/
noncomputable def kummerGlobalPoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : (Scheme.pointSmallEtale t).fiber.obj (kummerGlobalTest X) :=
  ⟨t, 𝟙 _, by simp [kummerGlobalTest]⟩

/-- The germ of a global log section, using the recorded geometric stalk. Source:
ILO VI 2.2 (blueprint: lem-per-kummer-strict-local-standard-model). -/
noncomputable def kummerGlobalLogGerm (X : FineSaturatedLogScheme.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    X.logStructure.monoidSheaf.obj.obj (op (kummerGlobalTest X.scheme)) ⟶
      X.logStructure.toEtalePrelogStructure.stalk t :=
  X.logStructure.toEtalePrelogStructure.germ t (kummerGlobalTest X.scheme)
    (kummerGlobalPoint t)

/-- The global compatible sharp-chart data in the strict-local standard model.
`cartesian` is an ordinary scheme pullback of the actual chart maps. The chart conditions
make its comparison a strict log isomorphism as well. Source: ILO VI 2.2
(blueprint: lem-per-kummer-strict-local-standard-model). -/
structure KummerStrictLocalChart {V T : FineSaturatedLogScheme.{u}} (v : EtaleLogHom V T)
    where
  P : Type u
  Q : Type u
  instP : CommMonoid P
  instQ : CommMonoid Q
  fineP : @IsFineSaturatedMonoid P instP
  fineQ : @IsFineSaturatedMonoid Q instQ
  sharpP : ∀ p : P, IsUnit p → p = 1
  sharpQ : ∀ q : Q, IsUnit q → q = 1
  a : P →* T.logStructure.monoidSheaf.obj.obj (op (kummerGlobalTest T.scheme))
  b : Q →* V.logStructure.monoidSheaf.obj.obj (op (kummerGlobalTest V.scheme))
  h : P →* Q
  chartP : T.logStructure.IsChart (kummerGlobalTest T.scheme) a
  chartQ : V.logStructure.IsChart (kummerGlobalTest V.scheme) b
  compatible : ∀ p : P,
    v.sectionMap (kummerGlobalTest T.scheme) (kummerGlobalTest V.scheme) v.base
      (by change v.base ≫ 𝟙 _ = 𝟙 _ ≫ v.base
          exact (Category.comp_id _).trans (Category.id_comp _).symm) (a p) = b (h p)
  cartesian : IsPullback v.base
    (V.logStructure.chartToSpec (kummerGlobalTest V.scheme) b)
    (T.logStructure.chartToSpec (kummerGlobalTest T.scheme) a)
    (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ h)))
  injective : Function.Injective h
  multiple : ∀ q : Q, ∃ (d : ℕ) (p : P), 0 < d ∧ q ^ d = h p
  characteristicP : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T.scheme), IsClosed ({t default} : Set T.scheme) →
      Function.Bijective (fun p : P ↦
        Associates.mk (kummerGlobalLogGerm T t (a p)))
  characteristicQ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ V.scheme), IsClosed ({t default} : Set V.scheme) →
      Function.Bijective (fun q : Q ↦
        Associates.mk (kummerGlobalLogGerm V t (b q)))

attribute [instance] KummerStrictLocalChart.instP KummerStrictLocalChart.instQ

/-- The same data as a compatible chart in the recorded log étale interface. Source:
ILO VI 2.2 (blueprint: lem-per-kummer-strict-local-standard-model). -/
def KummerStrictLocalChart.toFSLogChart {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) : FSLogChart v where
  W := kummerGlobalTest T.scheme
  V := kummerGlobalTest V.scheme
  P := c.P
  Q := c.Q
  instP := c.instP
  instQ := c.instQ
  fineP := c.fineP
  fineQ := c.fineQ
  chartY := c.a
  chartX := c.b
  g := c.h
  chartY_isChart := c.chartP
  chartX_isChart := c.chartQ
  map := v.base
  map_over := by
    change v.base ≫ 𝟙 _ = 𝟙 _ ≫ v.base
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  chart_compatibility := c.compatible
  square := c.cartesian.w

/-- The chart cokernel, using the recorded group-completion construction.
Source: ILO VI 2.2--2.3 (blueprint: lem-per-kummer-strict-local-standard-model). -/
noncomputable abbrev KummerStrictLocalChart.cokernel {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) := c.toFSLogChart.cokernel

/-- The finite constant character group `Hom(C, μₙ(A))`, with `A = Γ(T,O)`.
Source: ILO VI 2.2--2.3 (blueprint: lem-per-kummer-strict-local-standard-model). -/
noncomputable abbrev KummerStrictLocalChart.characters {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) (n : ℕ) :=
  c.cokernel →* rootsOfUnity n Γ(T.scheme, ⊤)

/-- The class of a chart monomial in the canonical cokernel. Source: ILO VI 2.3,
formula (2.a) (blueprint: lem-per-kummer-strict-local-standard-model). -/
noncomputable def KummerStrictLocalChart.monomialClass {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) (q : c.Q) : c.cokernel :=
  QuotientGroup.mk (Algebra.GrothendieckGroup.of q)

/-- Actual scalar pullback to a geometric ring stalk. Source: ILO VI 2.3, formula (2.a)
(blueprint: lem-per-kummer-strict-local-standard-model). -/
noncomputable def kummerScalarGerm {V T : FineSaturatedLogScheme.{u}} (v : EtaleLogHom V T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V.scheme) :
    Γ(T.scheme, ⊤) →+* strictLocalRing V.scheme t :=
  (strictLocalGerm V.scheme t (kummerGlobalTest V.scheme) (kummerGlobalPoint t)).hom.comp
    v.base.appTop.hom

/-- Formula (2.a), on all geometric log stalks and hence on the global chart sections.
The scalar is pulled back from the specified root in the base ring and included through
`unitsIn`. Applying the structural map also gives `z^q ↦ γ([q]) z^q` on functions.
Source: ILO VI 2.3 (blueprint: lem-per-kummer-strict-local-standard-model). -/
def KummerStrictLocalChart.HasCharacterFormula {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) (n : ℕ)
    (action : FSLogGroupAction (c.characters n) V) : Prop :=
  ∀ (γ : c.characters n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ V.scheme) (q : c.Q),
    (action.logMap γ).StalkImage t
      (kummerGlobalLogGerm V (t ≫ (action.logMap γ).base) (c.b q))
      (V.logStructure.unitsIn t
        (Units.map (kummerScalarGerm v t).toMonoidHom
          ((γ (c.monomialClass q) : rootsOfUnity n Γ(T.scheme, ⊤)) : Γ(T.scheme, ⊤)ˣ)) *
        kummerGlobalLogGerm V t (c.b q))

/-- The two invariant-sheaf equalities, sectionwise on the small étale site.
Every map is the canonical pullback, and invariant sections use exactly the lifts
fixing the base test object. Source: ILO VI 2.3, printed p.73
(blueprint: lem-per-kummer-strict-local-standard-model). -/
def KummerStrictLocalChart.HasInvariantSheaves {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) (n : ℕ)
    (action : FSLogGroupAction (c.characters n) V) : Prop :=
  (∀ E : T.scheme.Etale, Function.Injective (pullback.fst E.hom v.base).appTop ∧
    ∀ s : Γ((logQuotientTest v E).left, ⊤),
      (∀ (γ : c.characters n) (k : (logQuotientTest v E).left ⟶
          (logQuotientTest v E).left),
        k ≫ (logQuotientTest v E).hom =
          (logQuotientTest v E).hom ≫ (action.logMap γ).base →
        k ≫ pullback.fst E.hom v.base = pullback.fst E.hom v.base → k.appTop s = s) ↔
      ∃ r : Γ(E.left, ⊤), (pullback.fst E.hom v.base).appTop r = s) ∧
  (∀ E : T.scheme.Etale,
    Function.Injective (v.sectionMap E (logQuotientTest v E)
      (pullback.fst E.hom v.base) pullback.condition) ∧
    ∀ s : V.logStructure.monoidSheaf.obj.obj (op (logQuotientTest v E)),
      action.IsInvariantLogSection v E s ↔
        ∃ r : T.logStructure.monoidSheaf.obj.obj (op E),
          v.sectionMap E (logQuotientTest v E)
            (pullback.fst E.hom v.base) pullback.condition r = s)

/-- The canonical character diagonal is an isomorphism: its disjoint union, with
projections `(id, γ)`, has the universal property of the fs self-product.
Strict inclusions and the ordinary scheme coproduct specify its log disjoint union.
Source: ILO VI 2.2 (blueprint: lem-per-kummer-strict-local-standard-model). -/
def KummerStrictLocalChart.HasGaloisDiagonal {V T : FineSaturatedLogScheme.{u}}
    {v : EtaleLogHom V T} (c : KummerStrictLocalChart v) (n : ℕ)
    (action : FSLogGroupAction (c.characters n) V) : Prop :=
  ∃ (D : FineSaturatedLogScheme.{u}) (ι : c.characters n → EtaleLogHom V D)
    (p₁ p₂ : EtaleLogHom D V),
    Nonempty (IsColimit (Cofan.mk D.scheme (fun γ ↦ (ι γ).base))) ∧
    (∀ γ, (ι γ).IsStrict) ∧
    (∀ γ, (ι γ).CompEq p₁ (EtaleLogHom.id V) ∧ (ι γ).CompEq p₂ (action.logMap γ)) ∧
    p₁.IsFSPullback v p₂ v

/-- All clauses of the strictly local standard-cover and character description for
one nonempty component. The root order and invertible annihilator use the base ring;
no log regularity, reducedness or flatness occurs. Source: ILO VI 2.2--2.3
(blueprint: lem-per-kummer-strict-local-standard-model). -/
def KummerStrictLocalChart.HasStandardCharacterDescription
    {V T : FineSaturatedLogScheme.{u}} {v : EtaleLogHom V T}
    (c : KummerStrictLocalChart v) : Prop :=
  Surjective v.base ∧ ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T.scheme, ⊤)) ∧
    (∀ x : c.cokernel, x ^ n = 1) ∧
    Nat.card (rootsOfUnity n Γ(T.scheme, ⊤)) = n ∧
    IsCyclic (rootsOfUnity n Γ(T.scheme, ⊤)) ∧ Finite (c.characters n) ∧
    ∃ action : FSLogGroupAction (c.characters n) V,
      (∀ γ, (action.logMap γ).CompEq v v) ∧ c.HasCharacterFormula n action ∧
      c.HasGaloisDiagonal n action ∧
      (∀ g : EtaleLogHom V V, g.IsStrict → IsIso g.base → g.CompEq v v →
        ∃! γ : c.characters n, action.logMap γ = g) ∧ c.HasInvariantSheaves n action

/-- A finite Kummer étale cover of a strictly local fs log scheme is a finite disjoint
union of strictly local standard covers, with the specified character action and both
invariant-sheaf identities. `Γ(T,O)` is the ring `A`: affineness identifies its spectrum
canonically with `T`.

Source: ILO VI 2.1--2.3, printed pp.71--73
(blueprint: lem-per-kummer-strict-local-standard-model).

Proof (the eleven steps of the reviewed DAG node):

1. Since $v$ is finite, $V=\operatorname{Spec}B$ for a finite $A$-algebra. Apply
[lem-weil-pbc-finite-over-henselian-local-product] to write $B=\prod_iB_i$, with $B_i$ local
henselian and finite over $A$, and with finite residue extensions of $k=A/\mathfrak m$. These
residue fields are separably closed by [lem-kun-sep-closed-finite-extension-sep-closed]. Thus each
nonzero factor gives a strictly local $V_i$; zero factors are omitted, and $B=0$ gives the empty
union. Restricting the log structure gives fs log schemes. All the subsequent arguments concern
one nonzero factor $B_i$, denoted $B$.

2. Apply [lem-per-very-tame-equivariant-sharp-chart] to $T$ with the trivial group. Its hypotheses
hold with order one and trivial characteristic action, so it supplies a pointed etale
neighbourhood carrying a chart $P\simeq\overline M_{T,t}$. Choose the neighbourhood affine. Its
specified closed point is rational by [lem-weil-pbc-etale-residue-field-extension-separable],
since the base residue field is separably closed. The pointed section of
[lem-weil-pbc-henselian-etale-retraction] pulls its chart back to a global sharp chart on $T$.
Apply [lem-per-kummer-fixed-sharp-chart-refinement] to $V_i\to T$ at its closed point with this
$P$. Choose both neighbourhoods affine. The same residue-field and pointed-retraction results give
a section of $U\to T$ through its selected point and then a section, through the selected point,
of the pulled-back source neighbourhood over $V_i$. Pull back the chart $Q$ by this second
section. The resulting comparison $V_i\to S=\operatorname{Spec}(A\otimes_{\mathbf Z[P]}\mathbf
Z[Q])$ is etale: sections between etale schemes over the same base are etale and etale morphisms
compose and base change, by [lem-trf-space-chartwise-etale-permanence] applied to schemes. These
operations preserve the specified characteristic charts and $h$, with invertible annihilator $n$
for $C=Q^{\rm gp}/P^{\rm gp}$.

3. Put $D=A\otimes_{\mathbf Z[P]}\mathbf Z[Q]$. The finiteness and surjectivity assertions of
[lem-per-kummer-saturated-pushout-algebra], with $R=P$ and $a=1$, show that $D$ is finite over $A$
and $S\to T$ is surjective. For each nonzero $q\in Q$ choose $m>0$ and $p\in P$ with $mq=h(p)$.
Sharpness and injectivity imply $p\ne0$: if $mq=0$, saturation makes $-q=(m-1)q$ a unit inverse,
so $q=0$. Since the chart is characteristic at the closed point, $a(p)\in\mathfrak m$. Thus every
nonconstant monomial in $D/\mathfrak mD$ is nilpotent, and its quotient by them is $k$. This
closed fibre has one point and residue field $k$. The henselian decomposition
[lem-weil-pbc-finite-over-henselian-local-product] therefore makes $D$ local henselian with
residue $k$, hence strictly henselian. It is Noetherian by
[lem-weil-pbc-finite-algebra-noetherian].

4. The comparison $D\to B$ of step 2 is finite: any finite set generating $B$ as an $A$-module
also generates it as a $D$-module. It is etale and local. By
[lem-weil-pbc-henselian-finite-etale-equivalence], it is determined by its finite etale closed
fibre over $k$. By [lem-weil-pbc-etale-algebra-over-field-product] that fibre is a product of
finite separable extensions of the separably closed field $k$, hence a product of copies of $k$.
It is nonzero and local since $B$ is local, so it is precisely $k$. The equivalence, including
full faithfulness, identifies $B$ with $D$ over $D$. The comparison is strict by the two charts,
hence is an isomorphism of log schemes. This proves the claimed ordinary-fibre-product standard
model and its surjectivity. Steps 1--4 have established this part for every finite Kummer etale
cover of a strictly local base, independently of the remaining assertions.

5. By [lem-sbc-strict-local-roots-of-unity], $\mu_n(A)$ is cyclic of order $n$ and every
nontrivial root minus one is a unit. The group $C$ is finitely generated (as a quotient of the
groups generated by finite monoid generating sets) and killed by $n$. Apply
[lem-sbc-finitely-generated-abelian-group-structure]: its free part is zero and each nontrivial
cyclic summand has order dividing $n$. A primitive $n$th root therefore gives characters
separating points of $C$, and exactly $|C|$ characters. For each
$\gamma\in\Gamma=\operatorname{Hom}(C,\mu_n(A))$, the rule $z^q\mapsto\gamma([q])z^q$ fixes all
$z^{h(p)}$, so defines an $A$-algebra automorphism of $B$. Multiplying the chart section $q$ by
the same unit defines the compatible log automorphism. Its inverse is the rule for $\gamma^{-1}$,
and composition multiplies characters.

6. Compute the fs diagonal by [lem-per-kummer-saturated-pushout-algebra]. The group completion of
$Q\oplus_PQ$ is $Q^{\rm gp}\oplus C$ under $(q_1,q_2)\mapsto(q_1+q_2,[q_2])$. Its integralization
has saturation $Q\oplus C$: if a positive multiple of $(u,c)$ lies in the integralization, then a
positive multiple of $u$ lies in $Q$, whence $u\in Q$ by saturation; conversely $n(u,c)=(nu,0)$
comes from $(nu,0)$. Consequently the fs product has chart $Q\oplus C$ and ring $B[C]$ over the
first factor. Evaluation gives $B[C]\simeq\prod_{\gamma\in\Gamma}B$. Indeed, for each cyclic
summand of order $d\mid n$, $B[t]/(t^d-1)$ is the product of the quotients $(t-\zeta)$: distinct
roots have unit differences by step 5, so the linear polynomials are pairwise coprime. Their
product is $t^d-1$: divide successively by the monic linear factors, using unit root differences
to preserve the remaining roots, and compare monic degrees. Apply
[lem-pc-crt-principal-ideal-product] to identify their ideal intersection with $(t^d-1)$, and
[lem-pc-crt-ideal-quotient-product] to split its quotient; evaluation identifies each linear
quotient with $B$. Taking the finite products for the cyclic summands proves the displayed
evaluation isomorphism. In each factor the chart $(q,c)$ becomes $z^q\gamma(c)$; the extra group
$C$ maps to units and logification gives precisely the chart log structure of $V_i$. The second
projection is $z^q\mapsto\gamma([q])z^q$. Thus this is exactly the asserted canonical map
$\coprod_\gamma V_i\simeq V_i\times_T^{\rm fs}V_i$.

7. For a log automorphism $g$ over $T$, its graph $(1,g)$ is a map to the fs product. By step 6
this is a map to $\coprod_\Gamma V_i$ over $V_i$ through the first projection. The inverse images
of the summands are open and closed and partition $V_i$. A local scheme is connected (any nonempty
closed subset contains its closed point), so exactly one summand is used. On that summand the
first projection is the identity, forcing the graph to be $(1,\gamma)$ for precisely one
character. This also proves uniqueness, including when $C=0$.

8. There is a $C$-grading on $\mathbf Z[Q]$ with monomial degree $[q]$. Its degree-zero monoid is
$Q\cap P^{\rm gp}=P$: if $q\in Q\cap P^{\rm gp}$, some positive multiple belongs to $P$, so
saturation of $P$ inside $P^{\rm gp}$ gives $q\in P$. Tensoring the direct-sum decomposition over
$\mathbf Z[P]$ with $A$ gives $B=\bigoplus_{c\in C}B_c$ with $B_0=A$; this uses distributivity of
tensor products over finite direct sums, without flatness. A character acts on $B_c$ by its scalar
value at $c$. If $c\ne0$, select $\gamma$ with $\gamma(c)\ne1$ as in step 5. The scalar
$\gamma(c)-1$ is a unit, so a fixed element has zero $c$-component. Hence $B^\Gamma=A$, and a
fixed unit of $B$ lies in $A^\times$: its inverse is fixed too. At the closed log stalk, sharpness
of the chart gives $M_{V_i,v_i}=Q\oplus B^\times$, by the pushout defining an associated log
structure. An element $(q,u)$ is fixed precisely when $\gamma(q)\gamma(u)=u$ for every $\gamma$.
All $\gamma$ act trivially on the residue field $k$; reducing this equality shows $\gamma([q])=1$
for all $\gamma$, so $q\in P$. Then $u$ is fixed and belongs to $A^\times$. Thus the closed-stalk
fixed log monoid is $P\oplus A^\times=M_{T,t}$.

9. The ring calculation in step 8 holds after every scalar extension $A\to A'$: the $C$-grading
still has degree zero $A'$, and the root differences remain units. In particular it applies to
every affine etale $U=\operatorname{Spec}A'$ over $T$. Since $v_i$ is finite, its inverse image is
$\operatorname{Spec}(A'\otimes_AB)$ by [lem-weil-pbc-finite-morphism-permanence]. The canonical
maps on sections therefore give $\mathcal O_T\simeq(v_{i*}\mathcal O_{V_i})^\Gamma$ on an affine
etale basis and hence as sheaves. This also identifies fixed units after each strict-local base
change; no exactness of arbitrary tensor products is being used.

10. For the log sheaf, fix any geometric point $\bar s$ of $T$ and strictly localize there:
$T'=\operatorname{Spec}A'$ is strictly henselian by
[lem-weil-pbc-strict-henselization-local-structure] and Noetherian by
[lem-sc-strict-henselization-noetherian]. The map $T'\to T$ is strict with its pulled-back log
structure, so [lem-per-fs-product-finite-comparison] identifies the fs base change with the
ordinary finite base change $V'=V_i\times_TT'$. It is Kummer etale by
[lem-per-kummer-etale-fs-base-change-stability]. Decompose $V'=\coprod_jW_j$ as in step 1. The fs
diagonal of step 6 base changes, by its universal property, to $\coprod_\Gamma V'\simeq
V'\times_{T'}^{\rm fs}V'$. The group is transitive on the $W_j$: for any two factors the ordinary
product has a nonempty closed fibre, and [lem-per-fs-product-finite-comparison] makes its fs
product surjective over it; the diagonal then supplies a group element taking one factor to the
other. For a chosen $W$, let $H$ be its stabilizer. Restricting the diagonal gives $\coprod_H
W\simeq W\times_{T'}^{\rm fs}W$. Steps 2--7, which use no invariant-sheaf assertion, apply to
$W\to T'$ and identify it as a sharp standard cover with its own full character group $\Gamma_W$.
Every automorphism is in $H$: its connected graph factors through precisely one summand of the
restricted diagonal, just as in step 7. Thus $H$ is exactly $\Gamma_W$ acting on $W$.

11. By [lem-trf-finite-base-strict-localization], the factors $W_j$ are the geometric strict
localizations of $V_i$ at the points above $\bar s$, so their closed log stalks are the original
log stalks. By [lem-weil-pbc-sets-finite-pushforward-stalk], the stalk of $v_{i*}M_{V_i}$ at $\bar
s$ is the product of the log stalks at the closed geometric points of the factors $W_j$ in step
10. Stalks commute with the finite equalizer defining $\Gamma$-invariants by
[lem-weil-pbc-sets-etale-stalk-finite-limits]. For a transitive action on the factors, a fixed
tuple is uniquely its component at $W$, invariant under $H$: transport that component by $\gamma$
to the factor $\gamma W$, and $H$-invariance is exactly independence of the choice of $\gamma$.
Step 8, applied to the sharp model of $W$ already established in step 10, gives
$(M_{W,w})^H=M_{T',s'}$. Strict pullback identifies this closed characteristic-and-unit log stalk
with $M_{T,\bar s}$; the maps in the calculation are the original pullback maps on charts and
units. Hence $M_T\to(v_{i*}M_{V_i})^\Gamma$ is bijective at every geometric stalk. By
[lem-weil-pbc-sets-etale-iso-on-geometric-stalks] it is an isomorphism of sheaves of sets, and its
inverse respects monoid operations since the map does. This proves the log-sheaf assertion and
completes every clause.
-/
theorem kummer_strict_local_standard_model
    (V T : FineSaturatedLogScheme.{u}) (v : EtaleLogHom V T)
    [IsAffine T.scheme] [IsStrictlyHenselianLocalRing Γ(T.scheme, ⊤)]
    [IsFinite v.base] (hk : v.IsKummer) (he : v.IsLogEtale) :
    ∃ (m : ℕ) (W : Fin m → FineSaturatedLogScheme.{u})
      (ι : ∀ i : Fin m, EtaleLogHom (W i) V) (f : ∀ i : Fin m, EtaleLogHom (W i) T)
      (c : ∀ i : Fin m, KummerStrictLocalChart (f i)),
      Nonempty (IsColimit (Cofan.mk V.scheme (fun i ↦ (ι i).base))) ∧
      (∀ i, (ι i).IsStrict ∧ (ι i).CompEq v (f i)) ∧
      (∀ i j, (c i).P = (c j).P ∧ HEq (c i).a (c j).a) ∧
      ∀ i, IsAffine (W i).scheme ∧ IsStrictlyHenselianLocalRing Γ((W i).scheme, ⊤) ∧
        (c i).HasStandardCharacterDescription := by
  sorry

end AlgebraicGeometry
