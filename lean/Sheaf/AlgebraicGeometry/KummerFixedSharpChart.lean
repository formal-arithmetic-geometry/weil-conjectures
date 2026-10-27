/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.KummerLogMorphism
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.VeryTameEquivariantSharpChart
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.LogSmoothDifferentialGenerators
import Sheaf.GroupTheory.DivisibleUnitLatticeExtension
import Sheaf.AlgebraicGeometry.KatoLatticeChartRealization

/-!
# Kummer sharp charts extending a prescribed base chart

Source: Illusie--Laszlo--Orgogozo, VI 2.2 and 3.7(a), pp.72,75;
XVI Proposition 3.6.3 and Lemma 3.6.4, pp.252--253
(blueprint: lem-per-kummer-fixed-sharp-chart-refinement).

Multiplicative powers express positive additive multiples. Characteristic isomorphisms
are bijectivity of the canonical chart-germ map modulo units. Both comparison projections
are specified, so the comparison is the canonical map to the scheme fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Compatible sharp charts refining the specified sharp base chart.
Source: ILO VI 2.2 and 3.7(a), pp.72,75; XVI 3.6.3--3.6.4, pp.252--253.
(blueprint: lem-per-kummer-fixed-sharp-chart-refinement).

Proof:

1. First show that the relative logarithmic differential sheaf $\omega_f$ is zero. The log-etale
hypothesis implies log smoothness by [lem-per-log-smooth-composition-strict-base-change]. By
[lem-per-fs-log-infinitesimal-criterion], the underlying map is locally of finite presentation and
every strict square-zero test square of fine log schemes has exactly one global log lift. In
particular lifts exist etale locally. These are the hypotheses of
[lem-per-infinitesimal-log-differential-calculus], whose final clause gives $\omega_f=0$. The
required stability of the existence hypothesis under compatible etale restriction follows by
restricting the log-etale chart data and applying the same infinitesimal criterion. Thus the
differential basis at $\bar x$ is the empty basis.

2. Put $A=\mathcal O_{X,\bar x}$, $E=M_{X,\bar x}^{\rm gp}$, $D=A^\times\subset E$, and
$R=\overline M_{X,\bar x}$. Apply [lem-per-very-tame-equivariant-sharp-chart] with the trivial
group: its order is $1$, and its action on $R$ is trivial. In particular $R$ is sharp fs. Applying
[lem-trf-fs-face-sharpening] with the unit face $\{0\}$ to $P$ and $R$ gives finite free groups
$L=P^{\rm gp}$ and $R^{\rm gp}=E/D$. Let $\varphi:L\to E$ be pullback of the given chart germ.
Apply [lem-per-log-smooth-differential-generators] to $f$ and this prescribed $P$-chart, whose
group is torsion-free. Since $\omega_{f,\bar x}=0$, its basis has length zero. The lemma supplies
an integer $n\ge1$ invertible in $A$, $n$-divisibility of $D$, and a finite cokernel of $L\to E/D$
killed by $n$. The map $P\to R$ here is precisely the characteristic map using the given
identification $P\simeq\overline M_{Y,\bar y}$.

3. Apply [lem-per-divisible-unit-lattice-extension] to $(L,E,D,\varphi,n)$. The finite-free
source, torsion-free quotient, divisible units and finite cokernel hypotheses were verified in
step 2. Obtain a finite free group $G$, an injection $i:L\hookrightarrow G$ and a lift $s:G\to E$
with $si=\varphi$, such that $G/i(L)$ is killed by $n^k$ for some $k\ge0$ and $\rho:G\to
E/D=R^{\rm gp}$ induced by $s$ is surjective. This uses the prescribed chart map $\varphi$, so it
does not replace that chart by an unrelated one.

4. The map $\rho$ is also injective. If $\rho(g)=0$, write $n^kg=i(p)$ for $p\in L$. Then the
characteristic group map sends $p$ to zero. Its monoid map $P\to R$ is injective by Kummerness
[def-per-kummer-log-morphism], so its group map is injective: equality of differences reduces to
equality of sums in the integral monoids. Hence $p=0$, and torsion-freeness of $G$ gives $g=0$.
Define $Q=s^{-1}(M_{X,\bar x})\subset G$. An element $e\in E$ belongs to $M_{X,\bar x}$ exactly
when its image in $R^{\rm gp}$ belongs to $R$: in the reverse direction choose a log element with
that characteristic and subtract the remaining unit. This uses the integral log monoid and its
quotient by units [def-trf-fs-log-blowup]. Consequently $Q=\rho^{-1}(R)$, and $\rho$ identifies
$Q$ with $R$. In particular $Q$ is sharp fs and generates $G$.

5. The homomorphism $h:P\to Q$ is $p\mapsto i(p)$: it lands in $Q$ since $si(p)=f^\flat(a(p))$. It
is injective. For $q\in Q$, characteristic Kummerness [def-per-kummer-log-morphism] supplies $d>0$
and $p\in P$ with $d\rho(q)=\rho i(p)$. Since $\rho$ is injective, $dq=i(p)=h(p)$. The group map
is $i:L\to G$ under $Q^{\rm gp}=G$, so its cokernel is killed by $n^k$. It is finite: for a finite
basis of $G$, reduce each coefficient modulo $n^k$ to obtain finitely many representatives of
$G/i(L)$. When $n^k=1$ the quotient is zero.

6. Apply [lem-per-kato-lattice-chart-realization] with base monoid $P$ (called $Q$ in that lemma),
$r=0$, the empty differential basis, and the $G,i,s,n$ of steps 2--3. All its hypotheses hold: $f$
is log smooth, $P^{\rm gp}$ is torsion-free, $n$ is invertible in $A$, $si=\varphi$, $G/i(L)$ is
killed by a power of $n$, and $G\to E/D$ is surjective. Its prescribed inverse-image monoid is
exactly our $Q$. It yields a pointed etale neighbourhood $W_0\to X$ and a chart $b_0:Q\to M_{W_0}$
with germ $s|_Q$, compatible with the given $P$-chart through $h$, and an etale comparison $W_0\to
Y\times_{\operatorname{Spec}\mathbf Z[P]}\operatorname{Spec}\mathbf Z[Q]$. The induced
characteristic map of this chart is $\rho|_Q:Q\simeq R$ by step 4. Compatibility means the
equality of log sections $b_0h=f_{W_0}^\flat a$, not merely equality of their characteristic
classes.

7. It remains to put the annihilator on the base. The geometric local ring map $\mathcal O_{Y,\bar
y}\to A$ is local; if $n$ were in the maximal ideal downstairs, its image would be in the maximal
ideal of $A$. Thus $n$ is invertible at $\bar y$. Represent its inverse by a section near $\bar y$
and restrict until its product with $n$ is $1$. This gives an open neighbourhood $U\subset Y$
where $n$, hence $N=n^k>0$, is invertible. The open immersion $U\to Y$ is etale by
[lem-weil-pbc-etale-composition-cancellation]. Put $W=W_0\times_YU$. The map $W\to X\times_YU$ is
the base change of $W_0\to X$, hence etale by [lem-weil-pbc-etale-scheme-base-change]. The
comparison for $W\to U$ is the base change of the comparison in step 6 and is etale by the same
lemma. Restrict $b_0$ and $a$ to obtain $b$ and $a|_U$. Their equality remains
$bh=f_W^\flat(a|_U)$, and their germs at the induced geometric points are unchanged by these open
restrictions. Steps 4--5 give sharpness, the characteristic isomorphism, Kummerness, injectivity
of the group map, and its finite cokernel annihilated by $N$. Rename $N$ as the statement's
integer. This proves all the required clauses.
-/
theorem exists_kummer_fixed_sharp_chart
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    (_hkummer : f.IsKummer) (_hetale : f.IsLogEtale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    {P : Type u} [CommMonoid P] (_hfs : IsFineSaturatedMonoid P)
    (_hsharp : ∀ p : P, IsUnit p → p = 1)
    (a : P →* Y.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y.scheme))))
    (_ha : Y.logStructure.IsChart (Scheme.Etale.mk (𝟙 Y.scheme)) a)
    (_hchar : Function.Bijective (fun p : P ↦ Associates.mk
      (Y.logStructure.toEtalePrelogStructure.germ (t ≫ f.base)
        (Scheme.Etale.mk (𝟙 Y.scheme)) ⟨t ≫ f.base, 𝟙 _, by simp⟩ (a p)))) :
    ∃ (U : Y.scheme.Etale) (u : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj U)
      (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
      (k : W.left ⟶ U.left) (hk : k ≫ U.hom = W.hom ≫ f.base)
      (Q : Type u) (_ : CommMonoid Q)
      (b : Q →* X.logStructure.monoidSheaf.obj.obj (op W)) (h : P →* Q)
      (aU : P →* Y.logStructure.monoidSheaf.obj.obj (op U)),
      w.left ≫ k = u.left ∧
      Etale (pullback.lift W.hom k hk.symm) ∧
      aU = (Y.logStructure.monoidSheaf.obj.map
        (MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom) :
          U ⟶ Scheme.Etale.mk (𝟙 Y.scheme)).op).hom.comp a ∧
      IsFineSaturatedMonoid Q ∧ (∀ q : Q, IsUnit q → q = 1) ∧
      X.logStructure.IsChart W b ∧
      Function.Bijective (fun q : Q ↦ Associates.mk
        (X.logStructure.toEtalePrelogStructure.germ t W w (b q))) ∧
      Function.Injective h ∧ (∀ q : Q, ∃ (d : ℕ) (p : P), 0 < d ∧ q ^ d = h p) ∧
      (∀ p : P, b (h p) = f.sectionMap U W k hk (aU p)) ∧
      ∃ hg : Algebra.GrothendieckGroup P →* Algebra.GrothendieckGroup Q,
        hg = Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := Q)).comp h) ∧
        Function.Injective hg ∧ Finite (Algebra.GrothendieckGroup Q ⧸ hg.range) ∧
        (∃ n : ℕ, 0 < n ∧
          (∀ y : U.left, IsUnit (n : U.left.presheaf.stalk y)) ∧
          ∀ c : Algebra.GrothendieckGroup Q ⧸ hg.range, c ^ n = 1) ∧
        ∃ c : W.left ⟶ pullback (Y.logStructure.chartToSpec U aU)
            (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ h))),
          c ≫ pullback.fst _ _ = k ∧
          c ≫ pullback.snd _ _ = X.logStructure.chartToSpec W b ∧ Etale c := by
  sorry

end AlgebraicGeometry
