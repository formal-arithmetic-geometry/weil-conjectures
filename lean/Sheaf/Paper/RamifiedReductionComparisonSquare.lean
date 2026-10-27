/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.FiniteFreeCoefficientExtensionData

/-! # The mixed ramified extension and quotient reduction square

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 3
(blueprint: lem-sf-ramified-reduction-comparison-square).

The canonical maps are reused from the published finite coefficient calculus.
All reassociations use the balanced scalar compositor, including on the pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteFreeCoefficients
open WeilConjectures.FiniteFreeCoefficients.Sites
open scoped CategoryTheory.Functor
namespace WeilConjectures.RamifiedReduction

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The upper field at the base-uniformizer exponent n; its ring is B_n.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def level {L : Type (u + 1)} [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (n : ℕ+) : Stage l E where
  field := L
  inclusion := ι
  exponent := n

/-- The horizontal inclusion is induced by the given field embedding.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def horizontal {L : Type (u + 1)} [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (n : ℕ+) :
    Arrow (baseStage (l := l) (E := E) n) (level ι n) where
  embedding := ι
  over_base := rfl
  level := le_refl _

/-- The vertical quotient is induced by the identity of the coefficient field.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def reduction (s : Stage l E) (m : ℕ+) (h : (m : ℕ) ≤ (s.exponent : ℕ)) :
    Arrow s { s with exponent := m } where
  embedding := AlgHom.id (Padic l) s.field
  over_base := rfl
  level := h

/-- Dispatch to the existing closed-counit transpose or its specified site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def closedArrow (pro : Bool) {s t : Stage l E} (a : Arrow s t)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (K : D pro s.ring X) :
    (scalar pro a.ringMap Z).obj ((exceptional pro s.ring i).obj K) ⟶
      (exceptional pro t.ring i).obj ((scalar pro a.ringMap X).obj K) := by
  cases pro
  · exact FiniteFreeCoefficients.closedMap a.ringMap i K
  · exact proClosedMap a.ringMap i K

/-- Dispatch to the compact-support counit transpose or its specified site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def omegaArrow (pro : Bool) {s t : Stage l E} (a : Arrow s t)
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (scalar pro a.ringMap X).obj (omega pro s.ring c) ⟶ omega pro t.ring c := by
  cases pro
  · exact FiniteFreeCoefficients.omegaMap a.ringMap c
  · exact proOmegaMap a.ringMap c

/-- The specified balanced identification of the two coefficient paths.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def squareIso (pro : Bool) {s t r v : Stage l E}
    (an : Arrow s t) (qa : Arrow s r) (qb : Arrow t v) (am : Arrow r v)
    (h : qb.ringMap.comp an.ringMap = am.ringMap.comp qa.ringMap) (X : Scheme.{u}) :
    scalar pro an.ringMap X ⋙ scalar pro qb.ringMap X ≅
      scalar pro qa.ringMap X ⋙ scalar pro am.ringMap X :=
  Sites.comp pro an.ringMap qb.ringMap (am.ringMap.comp qa.ringMap) h.symm X ≪≫
    (Sites.comp pro qa.ringMap am.ringMap (am.ringMap.comp qa.ringMap) rfl X).symm

/-- Evaluation and its signed double-dual transpose for the specified coefficient arrow.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def Pairings (pro : Bool) {s t : Stage l E} (a : Arrow s t)
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    (μ : TensorComparison pro a.ringMap X)
    (σs : tensor pro s.ring X ≅ (tensor pro s.ring X).flip)
    (σt : tensor pro t.ring X ≅ (tensor pro t.ring X).flip) : Prop :=
  ∀ K : D pro s.ring X, Sites.Ctf pro s.ring X K →
    (((tensor pro t.ring X).map (Sites.dualMap pro a.ringMap c μ
        (omegaArrow pro a c) K)).app ((scalar pro a.ringMap X).obj K) ≫
      evaluation pro t.ring X σt (omega pro t.ring c)
        ((scalar pro a.ringMap X).obj K) =
      μ.inv.app ((Sites.dual pro s.ring c).obj (op K), K) ≫
        (scalar pro a.ringMap X).map
          (evaluation pro s.ring X σs (omega pro s.ring c) K) ≫ omegaArrow pro a c) ∧
    ((scalar pro a.ringMap X).map
        (bidual pro s.ring X σs (omega pro s.ring c) K) ≫
      Sites.dualMap pro a.ringMap c μ (omegaArrow pro a c)
        ((Sites.dual pro s.ring c).obj (op K)) =
      bidual pro t.ring X σt (omega pro t.ring c) ((scalar pro a.ringMap X).obj K) ≫
        (Sites.dual pro t.ring c).map
          (Sites.dualMap pro a.ringMap c μ (omegaArrow pro a c) K).op)

/-- All five mixed squares, with covariant and contravariant endpoint transports explicit.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square). -/
def Squares (pro : Bool) {s t r v : Stage l E}
    (an : Arrow s t) (qa : Arrow s r) (qb : Arrow t v) (am : Arrow r v)
    (h : qb.ringMap.comp an.ringMap = am.ringMap.comp qa.ringMap)
    {V X Z S : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μn : TensorComparison pro an.ringMap X) (μa : TensorComparison pro qa.ringMap X)
    (μb : TensorComparison pro qb.ringMap X) (μm : TensorComparison pro am.ringMap X) :
    Prop :=
  (∀ K : D pro s.ring V, Sites.Ctf pro s.ring V K →
    (scalar pro qb.ringMap X).map (direct pro an.ringMap f K) ≫
      direct pro qb.ringMap f ((scalar pro an.ringMap V).obj K) ≫
      (push pro v.ring f).map ((squareIso pro an qa qb am h V).hom.app K) =
    (squareIso pro an qa qb am h X).hom.app ((push pro s.ring f).obj K) ≫
      (scalar pro am.ringMap X).map (direct pro qa.ringMap f K) ≫
      direct pro am.ringMap f ((scalar pro qa.ringMap V).obj K)) ∧
  (∀ K : D pro s.ring X, Sites.Ctf pro s.ring X K →
    (scalar pro qb.ringMap Z).map (closedArrow pro an i K) ≫
      closedArrow pro qb i ((scalar pro an.ringMap X).obj K) ≫
      (exceptional pro v.ring i).map ((squareIso pro an qa qb am h X).hom.app K) =
    (squareIso pro an qa qb am h Z).hom.app ((exceptional pro s.ring i).obj K) ≫
      (scalar pro am.ringMap Z).map (closedArrow pro qa i K) ≫
      closedArrow pro am i ((scalar pro qa.ringMap X).obj K)) ∧
  ((scalar pro qb.ringMap X).map (omegaArrow pro an c) ≫ omegaArrow pro qb c =
    (squareIso pro an qa qb am h X).hom.app (omega pro s.ring c) ≫
      (scalar pro am.ringMap X).map (omegaArrow pro qa c) ≫ omegaArrow pro am c) ∧
  (∀ K M : D pro s.ring X, Sites.Ctf pro s.ring X K → Sites.Ctf pro s.ring X M →
    (scalar pro qb.ringMap X).map (Sites.homMap pro an.ringMap X μn K M) ≫
      Sites.homMap pro qb.ringMap X μb ((scalar pro an.ringMap X).obj K)
        ((scalar pro an.ringMap X).obj M) ≫
      homAction (Sites.hom pro v.ring X)
        ((squareIso pro an qa qb am h X).inv.app K)
        ((squareIso pro an qa qb am h X).hom.app M) =
    (squareIso pro an qa qb am h X).hom.app
        (((Sites.hom pro s.ring X).obj (op K)).obj M) ≫
      (scalar pro am.ringMap X).map (Sites.homMap pro qa.ringMap X μa K M) ≫
      Sites.homMap pro am.ringMap X μm ((scalar pro qa.ringMap X).obj K)
        ((scalar pro qa.ringMap X).obj M)) ∧
  (∀ K : D pro s.ring X, Sites.Ctf pro s.ring X K →
    (scalar pro qb.ringMap X).map
        (Sites.dualMap pro an.ringMap c μn (omegaArrow pro an c) K) ≫
      Sites.dualMap pro qb.ringMap c μb (omegaArrow pro qb c)
        ((scalar pro an.ringMap X).obj K) ≫
      (Sites.dual pro v.ring c).map ((squareIso pro an qa qb am h X).inv.app K).op =
    (squareIso pro an qa qb am h X).hom.app ((Sites.dual pro s.ring c).obj (op K)) ≫
      (scalar pro am.ringMap X).map
        (Sites.dualMap pro qa.ringMap c μa (omegaArrow pro qa c) K) ≫
      Sites.dualMap pro am.ringMap c μm (omegaArrow pro am c)
        ((scalar pro qa.ringMap X).obj K))

/-- The mixed ramified-extension and reduction square, on both actual small sites.
Source: blueprint main-20261015, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-ramified-reduction-comparison-square).

Proof:
1. Put $d=q_Ba_n=a_mq_A:A_n\to B_m$ and $S=T_d$. The equality of ring maps is equality on the
image of every element of $\mathcal O_E$. Apply the canonical derived pullback composition of
[lem-sfb-ringed-derived-monoidal-comparisons] to identity geometric morphisms with these
coefficient maps. It identifies both $R_BT_n$ and $T_mR_A$ with $S$, compatibly with tensors and
units. On flat-term K-flat representatives, [lem-pur-kflat-change-of-rings] allows successive
extension to compute these functors; the maps are multiplication of the coefficient factors. In
particular $((p\otimes a)\otimes b)\mapsto p\otimes a b$ on the $A_m$ path, and $((p\otimes
b_n)\otimes b_m)\mapsto p\otimes q_B(b_n)b_m$ on the $B_n$ path. Since $B_n$ is free over $A_n$,
its degree-zero complex computes $B_n\otimes^L_{A_n}A_m$; quotienting its reduced basis
identifies this with $B_m$. Thus these are the stipulated balanced identifications, not choices
of endpoint isomorphisms.

2. All four rings are allowable finite stages: $A_t=A_{E,t}$ and $B_t=A_{L,et}$, with $em\le
en$. The horizontal functors preserve bounded constructibility and every Tor interval by [lem-
sf-finite-free-derived-scalar-calculus]; the vertical ones do so by [lem-coef-finite-hom-domain-
calculus], applied over $E$ and over $L$. For each of the four coefficients, [lem-weil-verdier-
preservation-strata] applies to this separated finite-type $X/k$ and carries every finite-Tor
constructible input to a finite-Tor constructible dual. Apply it also to the coefficient unit:
$R\mathcal Hom_R(R_X,\omega_R)=\omega_R$, since Hom from the rank-one unit is identity. This
proves that all $\omega_R$, duals, repeated duals and their reductions used below meet the
quotient lemmas' input hypotheses; no smoothness or site-perfectness is assumed.

3. For direct image apply the successive-coefficient equation of [lem-coef-finite-direct-image]
to the two chains $A_n\to B_n\to B_m$ and $A_n\to A_m\to B_m$. Every algebra in either chain is
finite as a module over its predecessor, and the starting $K$ is bounded constructible finite-
Tor on $V$. The two composites are therefore both $c_{d;K}$ under step 1. This is exactly the
asserted $c$ square. The cited equation explicitly permits an intermediate ring not presented as
$A_{E,r}$, so it applies to the first chain. It also applies with $f=i$ and with $f$ the proper
map in the fixed compactification; these versions will be used below.

4. Write the fixed structure compactification as $X\xrightarrow j\overline X\xrightarrow
p\operatorname{Spec}k$ and $F_R=Rp_{*,R}j_{!,R}$. For an etale finite-Tor constructible $N$,
exact $j_!$ is bounded constructible by [lem-fin-extension-by-zero] applied to its finitely many
cohomology sheaves. Its Tor interval is unchanged: the projection identity
$j_!(N\otimes^Lj^*W)=j_!N\otimes^LW$ of [lem-coef-etale-open-tensor], for degree-zero $W$,
reduces this to exactness of $j_!$. Thus step 3 applies to $p$ and $j_!N$. Denote its
coefficient projection by $c^p_a$ and the open scalar comparison by $z_a$. The compact
comparison is $C_a=Rp_{*,S}(z_a)\circ c^p_a$. The successive-scalar identity for $z$ in the same
open-tensor node and that for $c^p$ in step 3 give, by naturality, $C_b\circ T_bC_a=C_{ba}$ for
each of our two coefficient chains. Hence the two mixed compact-support paths are the same
$C_d$. Their inverses have the corresponding reversed equation. The horizontal maps are the same
finite-sum normalized comparisons by [lem-sf-finite-free-image-comparison], and the vertical
compact maps are the quotient tensor comparisons of [lem-fix-compact-support-coefficient-
change].

5. For closed exceptional image let $I_R=i_{*,R}$ and write $c_a:T_aI_R\to I_ST_a$ for its
ordinary coefficient comparison. By [lem-coef-finite-etale-descent], applied also with equal
quotient levels to type $G_RK$, the objects $G_RK$, its quotient reduction, and $G_ST_aK$ in a
vertical comparison are bounded constructible finite-Tor, and the etale vertical $b$ is the
specified exceptional-counit transpose. Horizontal $b$ is the same counit construction by [lem-
sf-finite-free-exceptional-mate]. For any one of the two chains $R\xrightarrow a S\xrightarrow b
U$, [lem-weil-pbc-mate-pasting] applied to the inverse $c$ squares says the transpose of
$b_{b;T_aK}\circ T_b(b_{a;K})$ is
$$T_bT_a(\varepsilon_{R,K})\circ T_b(c_{a;G_RK}^{-1})\circ c_{b;T_aG_RK}^{-1}.$$
Step 3 identifies its last two factors with $c_{ba;G_RK}^{-1}$. Both mixed paths consequently
have transpose $S(\varepsilon_{A_n,K})\circ c_{d;G_{A_n}K}^{-1}$ under $I_{B_m}\dashv G_{B_m}$
and are equal. The pro-etale vertical maps in this recovery are exactly [lem-coef-finite-closed-
shriek], not separately chosen isomorphisms.

6. For the dualizing object use $F_R\dashv a_{X,R}^{\times}$ and its counit
$\varepsilon_R:F_R\omega_R\to R$. Its unit-valued transpose defining $u_a$ is
$T_a\varepsilon_R\circ C_{a;\omega_R}^{-1}$ followed by $T_aR\cong S$. Exactly the pasting
formula of step 5, now for $C$ and the compact adjunction, gives for either two-arrow chain the
transpose
$$T_bT_a\varepsilon_R\circ T_b(C_{a;\omega_R}^{-1})\circ C_{b;T_a\omega_R}^{-1},$$
followed by $T_bT_aR\cong U$. Step 4 and the unit compatibility of step 1 turn this into
$T_{ba}\varepsilon_R\circ C_{ba;\omega_R}^{-1}$ and the canonical unit map. Hence both paths
have the same transpose and the $u$ square commutes. At the vertical arrows these are precisely
the isomorphisms of [lem-coef-finite-dualizing], whose statement specifies this transpose. Its
hypotheses hold at $E$ with $(n,m)$ and at $L$ with $(en,em)$ by step 2.

7. For internal Hom let $R\xrightarrow a S\xrightarrow b U$ be either chain, put $H_R=R\mathcal
Hom_R(K,M)$, and let $w=v_{b;T_aK,T_aM}\circ T_b(v_{a;K,M})$. The defining transpose equation
gives
$$\operatorname{ev}_U\circ(w\otimes1)=T_b\operatorname{ev}_S\circ(T_bv_a\otimes1)=T_bT_a\operato
rname{ev}_R.$$
The first equality is the definition of $v_b$, precomposed with $T_bv_a\otimes1$; the second is
the functorial image of the defining equation for $v_a$. Monoidality and composition
compatibility in [lem-sfb-ringed-derived-monoidal-comparisons] supply exactly these
identifications with both inputs extended. The closed tensor-Hom bijection of [lem-sf-ringed-
derived-closed-symmetric-monoidal] is injective, so $w$ is the single transpose for $ba$. Both
chains have the same $d$ and the same pairing $S\operatorname{ev}_{A_n}$, proving the $v$
square. At each vertical arrow [thm-coef-finite-hom] identifies its comparison with exactly this
transpose and proves invertibility; at the horizontal arrows [lem-sf-ringed-finite-free-hom-
base-change] does so for arbitrary inputs. Thus the calculation also applies to the dualizing
and dual inputs of step 2.

8. Expand $\beta_a=H_S(1,u_a)v_a$. Naturality of $v_b$ in its second input moves $T_bH_S(1,u_a)$
past $v_b$, so the composite Verdier comparison along $a,b$ is
$$H_U(1,u_b\circ T_bu_a)\,v_{b;T_aK,T_a\omega_R}\,T_bv_{a;K,\omega_R}.$$
Step 7 replaces the last two factors by the evaluation transpose for $ba$; step 6 replaces the
first target map by $u_{ba}$. For the two chains these are identical, proving the $\beta$
square. The vertical identification is the finite Verdier comparison: [lem-coef-finite-target-
change-coherence] applied to the quotient dualizing family gives exactly $H(1,u)v$, and [cor-
coef-finite-verdier] is that evaluation-compatible comparison. The hypotheses on its target
family are supplied by step 2 and the quotient cocycle in [lem-coef-finite-dualizing].

9. For every edge $a:R\to S$, the defining equation of $v_a$ and $\beta_a=H(1,u_a)v_a$ give
$\operatorname{ev}_{S,T_aK}(\beta_{a;K}\otimes1)=u_aT_a(\operatorname{ev}_{R,K})$. It holds also
at $D_RK$, by step 2. Apply [lem-coef-finite-bidual-transpose] to these two equations:
$\beta_{a;D_RK}T_a\delta_{R,K}=D_S(\beta_{a;K})\delta_{S,T_aK}$. Thus every edge respects the
double-dual transpose, as well as evaluation. Pasting the edge equations and using the already
proved $u,v,\beta$ squares proves preservation by the mixed square itself. The tensor symmetry
is the signed symmetry in the cited lemma, which scalar extension preserves, so this argument
does not suppress a sign or assume a biduality isomorphism.

10. Finally apply [lem-sf-finite-free-etale-proetale-transport] at levels $n$ and $m$: it
identifies the horizontal $c,b,u,v,\beta$ with their named pro-etale maps, and identifies the
quotient maps at $(n,m)$ over $E$ and $(en,em)$ over $L$. It expressly carries counit,
evaluation and double-dual equations and the mixed square to the named square on the other site.
Consequently applying the comparison functors to steps 3--9 proves all five pro-etale squares
and their pairing compatibilities. The exceptional functor here is the transported constructible
one. The etale closed vertical arrow was already identified in step 5, so no ambient unbounded
pro-etale exceptional adjunction is invoked.
-/
theorem ramified_reduction_comparison_square (D₀ : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D₀.p)
    (E L : Type (u + 1)) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (m n : ℕ+) (hmn : (m : ℕ) ≤ (n : ℕ))
    (e : ℕ+)
    (_he : Ideal.span ({strictEtaleIntegerMap l ι
        (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ (e : ℕ)})
    (rank : ℕ)
    (_basis : @Module.Basis (Fin rank) (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) inferInstance inferInstance
        (strictEtaleIntegerMap l ι).toAlgebra.toModule)
    {V X Z : Scheme.{u}}
    [V.Over (Spec (.of D₀.k))] [X.Over (Spec (.of D₀.k))]
    [Z.Over (Spec (.of D₀.k))]
    [IsSeparated (V ↘ Spec (.of D₀.k))] [LocallyOfFiniteType (V ↘ Spec (.of D₀.k))]
    [QuasiCompact (V ↘ Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))] [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))]
    [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (Z ↘ Spec (.of D₀.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D₀.k))]
    [QuasiCompact (Z ↘ Spec (.of D₀.k))]
    (f : V ⟶ X) [f.IsOver (Spec (.of D₀.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D₀.k))]
    (c : Compactification (X ↘ Spec (.of D₀.k))) :
    ∃ h : (reduction (level ι n) m hmn).ringMap.comp (horizontal ι n).ringMap =
        (horizontal ι m).ringMap.comp
          (reduction (baseStage (l := l) (E := E) n) m hmn).ringMap,
      ∀ pro : Bool,
      ∃ (μ : ∀ {s t : Stage l E} (a : Arrow s t), TensorComparison pro a.ringMap X)
        (σ : ∀ s : Stage l E, tensor pro s.ring X ≅ (tensor pro s.ring X).flip),
        (∀ {s t : Stage l E} (a : Arrow s t), NormalizedTensor pro a.ringMap X (μ a)) ∧
        (∀ s : Stage l E, NormalizedSymmetry pro s.ring X (σ s)) ∧
        Squares pro (horizontal ι n) (reduction (baseStage n) m hmn)
          (reduction (level ι n) m hmn) (horizontal ι m) h f i c
          (μ (horizontal ι n)) (μ (reduction (baseStage n) m hmn))
          (μ (reduction (level ι n) m hmn)) (μ (horizontal ι m)) ∧
        Pairings pro (horizontal ι n) c (μ (horizontal ι n)) (σ (baseStage n)) (σ (level ι n)) ∧
        Pairings pro (horizontal ι m) c (μ (horizontal ι m)) (σ (baseStage m)) (σ (level ι m)) ∧
        Pairings pro (reduction (baseStage n) m hmn) c
          (μ (reduction (baseStage n) m hmn)) (σ (baseStage n)) (σ (baseStage m)) ∧
        Pairings pro (reduction (level ι n) m hmn) c
          (μ (reduction (level ι n) m hmn)) (σ (level ι n)) (σ (level ι m)) ∧
        (∀ s : Stage l E,
          (s = baseStage n ∨ s = baseStage m ∨ s = level ι n ∨ s = level ι m) →
          Sites.Ctf pro s.ring X (omega pro s.ring c) ∧
          ∀ K : D pro s.ring X, Sites.Ctf pro s.ring X K →
            Sites.Ctf pro s.ring X ((Sites.dual pro s.ring c).obj (op K))) := by
  sorry

end WeilConjectures.RamifiedReduction
