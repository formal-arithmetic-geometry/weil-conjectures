/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Sheaf.AlgebraicGeometry.RelativeFermatKummerCurve
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Finite two-root charts of the relative Fermat hypersurface

Source: Stacks Project, curves.tex, Tag 0BYA; constructions.tex, Tag 01NG;
explicit relative Fermat calculation in the node's seven proof steps.
(blueprint: lem-sfb-fermat-finite-chart-cover)

The Bool index is false for the C-chart (a,b,x), true for the A-chart (u,v,y).
All coordinates below are the actual homogeneous fractions on the given zero scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RelativeFermatCurve

noncomputable section

/-- The denominator C or A of a Fermat chart. Source: Stacks 0BYA, affine pieces.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartDenominator (c : Bool) : ULift.{u} (Fin 3) :=
  if c then ⟨0⟩ else ⟨2⟩

/-- The numerators (A,B) or (B,C). Source: Stacks 0BYA, affine pieces.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartNumerator (c : Bool) (j : Fin 2) : ULift.{u} (Fin 3) :=
  if c then ⟨![1, 2] j⟩ else ⟨![0, 1] j⟩

/-- The C- or A-open of the given closed hypersurface. Source: Stacks 0BYA.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartOpen (S : Scheme.{u}) (n : ℕ) (c : Bool) : (curve S n).Opens :=
  ι S n ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) S (chartDenominator c)

/-- The actual fractions (a,b)=(A/C,B/C) or (u,v)=(B/A,C/A). Source: Stacks 0BYA.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartCoordinate (S : Scheme.{u}) (n : ℕ) (c : Bool) (j : Fin 2) :
    Γ(curve S n, chartOpen S n c) :=
  (ι S n).app _ (ProjectiveSpace.coordRatio (ULift.{u} (Fin 3)) S
    (chartDenominator c) (chartNumerator c j))

/-- The denominator of the x- or y-chart of the target line. Source: Stacks 01NG.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def lineDenominator (c : Bool) : ULift.{u} (Fin 2) :=
  if c then ⟨0⟩ else ⟨1⟩

/-- The numerator of x or y on the target line. Source: Stacks 01NG.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def lineNumerator (c : Bool) : ULift.{u} (Fin 2) :=
  if c then ⟨1⟩ else ⟨0⟩

/-- The two standard target opens. Source: Stacks 01NG.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def lineOpen (S : Scheme.{u}) (c : Bool) : (ProjectiveLine S).Opens :=
  ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S (lineDenominator c)

/-- The target parameter x or y. Source: Stacks 01NG.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def lineCoordinate (S : Scheme.{u}) (c : Bool) : Γ(ProjectiveLine S, lineOpen S c) :=
  ProjectiveSpace.coordRatio (ULift.{u} (Fin 2)) S (lineDenominator c) (lineNumerator c)

/-- The prescribed S-morphism formula, including its exact chart inverse images.
Source: Stacks 0BYA and 01NG, explicit power map on the two affine pieces.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def HasPowerChartFormula (S : Scheme.{u}) (n : ℕ)
    (q : curve S n ⟶ ProjectiveLine S) : Prop :=
  q ≫ ProjectiveLine S ↘ S = π S n ∧
  ∀ c : Bool, ∃ h : q ⁻¹ᵁ lineOpen S c = chartOpen S n c,
    q.appLE (lineOpen S c) (chartOpen S n c) h.ge (lineCoordinate S c) =
      chartCoordinate S n c (if c then 1 else 0) ^ n

/-- Restrict a source chart to an affine base open. Source: Stacks 0BYA and 01NG.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def localChartOpen (S : Scheme.{u}) (n : ℕ) (c : Bool) (V : S.Opens) :
    (curve S n).Opens :=
  chartOpen S n c ⊓ (π S n) ⁻¹ᵁ V

/-- The two defining monic relations over R[x] or R[y]. Source: Stacks 0BYA,
explicit redundant-coordinate presentation in proof step 4.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartRelations (R : Type u) [CommRing R] (n : ℕ) (c : Bool) :
    Ideal (MvPolynomial (Fin 2) (Polynomial R)) :=
  Ideal.span {MvPolynomial.X 0 ^ n - MvPolynomial.C
      (if c then 1 - Polynomial.X else Polynomial.X),
    MvPolynomial.X 1 ^ n - MvPolynomial.C
      (if c then Polynomial.X else Polynomial.X - 1)}

/-- The literal two-root chart algebra, not its reduced quotient. Source: Stacks 0BYA,
explicit presentations S_C and S_A in proof step 4.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartRing (R : Type u) [CommRing R] (n : ℕ) (c : Bool) :=
  MvPolynomial (Fin 2) (Polynomial R) ⧸ chartRelations R n c

/-- The quotient's commutative ring structure. Source: Stacks 0BYA, chart quotient.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
instance chartRingCommRing (R : Type u) [CommRing R] (n : ℕ) (c : Bool) :
    CommRing (chartRing R n c) :=
  inferInstanceAs (CommRing
    (MvPolynomial (Fin 2) (Polynomial R) ⧸ chartRelations R n c))

/-- The quotient's canonical algebra over the target parameter ring. Source: Stacks 0BYA.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
instance chartRingAlgebra (R : Type u) [CommRing R] (n : ℕ) (c : Bool) :
    Algebra (Polynomial R) (chartRing R n c) :=
  inferInstanceAs (Algebra (Polynomial R)
    (MvPolynomial (Fin 2) (Polynomial R) ⧸ chartRelations R n c))

/-- The class of a root variable in the two-root quotient. Source: Stacks 0BYA.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartRoot (R : Type u) [CommRing R] (n : ℕ) (c : Bool) (j : Fin 2) :
    chartRing R n c :=
  Ideal.Quotient.mk (chartRelations R n c) (MvPolynomial.X j)

/-- The actual power monomials in the two-root quotient. Source: Stacks 0BYA,
proof step 4, successive monic power bases.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def chartMonomial (R : Type u) [CommRing R] (n : ℕ) (c : Bool)
    (ij : Fin n × Fin n) : chartRing R n c :=
  chartRoot R n c 0 ^ ij.1.val * chartRoot R n c 1 ^ ij.2.val

/-- Chart affineness, the specified R[x]-algebra presentation, and the displayed basis.
The coefficient and parameter equations specify the algebra over the target chart.
Source: Stacks 0BYA, explicit presentations and two successive monic power bases.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def HasLocalChartPresentation (S : Scheme.{u}) (n : ℕ) (c : Bool) (V : S.Opens) : Prop :=
  IsAffineOpen (localChartOpen S n c V) ∧
  ∃ E : chartRing Γ(S, V) n c ≃+* Γ(curve S n, localChartOpen S n c V),
    (∀ r : Γ(S, V),
      E (algebraMap (Polynomial Γ(S, V)) (chartRing Γ(S, V) n c) (Polynomial.C r)) =
        (π S n).appLE V (localChartOpen S n c V) inf_le_right r) ∧
    E (algebraMap (Polynomial Γ(S, V)) (chartRing Γ(S, V) n c) Polynomial.X) =
      (curve S n).presheaf.map (homOfLE inf_le_left).op
        (chartCoordinate S n c (if c then 1 else 0) ^ n) ∧
    (∀ j : Fin 2, E (chartRoot Γ(S, V) n c j) =
      (curve S n).presheaf.map (homOfLE inf_le_left).op (chartCoordinate S n c j)) ∧
    ∃ b : Module.Basis (Fin n × Fin n) (Polynomial Γ(S, V)) (chartRing Γ(S, V) n c),
      ∀ ij : Fin n × Fin n, b ij = chartMonomial Γ(S, V) n c ij

/-- The C-chart fractions restricted to the intersection of the two source charts.
Source: Stacks 01M3 and 0BYA, homogeneous localization overlap.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def overlapC (S : Scheme.{u}) (n : ℕ) (j : Fin 2) :
    Γ(curve S n, chartOpen S n false ⊓ chartOpen S n true) :=
  (curve S n).presheaf.map (homOfLE inf_le_left).op (chartCoordinate S n false j)

/-- The A-chart fractions restricted to the intersection of the two source charts.
Source: Stacks 01M3 and 0BYA, homogeneous localization overlap.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def overlapA (S : Scheme.{u}) (n : ℕ) (j : Fin 2) :
    Γ(curve S n, chartOpen S n false ⊓ chartOpen S n true) :=
  (curve S n).presheaf.map (homOfLE inf_le_right).op (chartCoordinate S n true j)

/-- The displayed overlap substitutions, expressed without division in a general ring:
a*v=1, a*u=b, x*y=1 with x=a^n and y=v^n. Source: Stacks 01M3 and 0BYA.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def HasChartOverlap (S : Scheme.{u}) (n : ℕ) : Prop :=
  overlapC S n 0 * overlapA S n 1 = 1 ∧
  overlapC S n 0 * overlapA S n 0 = overlapC S n 1 ∧
  overlapC S n 0 ^ n * overlapA S n 1 ^ n = 1

/-- Both local chart descriptions and their overlap, over every affine base open.
Source: Stacks 0BYA and 01NG; proof steps 1, 2 and 4.
(blueprint: lem-sfb-fermat-finite-chart-cover) -/
def HasTwoRootCharts (S : Scheme.{u}) (n : ℕ) : Prop :=
  HasChartOverlap S n ∧
  ∀ (V : S.Opens), IsAffineOpen V → ∀ c : Bool, HasLocalChartPresentation S n c V

/-- The two-root charts and their finite, surjective map to the projective line commute
with every base change. Source: Stacks 0BYA, 01NG, 01I4, and explicit relative calculation.
(blueprint: lem-sfb-fermat-finite-chart-cover)

Proof:
1. Use [lem-weil-pbc-projective-space-standard-charts] over each affine
   $V=\operatorname{Spec}R\subset S$. On the $C$-chart the twist $\mathcal O(n)$ has frame $C^n$
   by [def-pc-projective-space-twist], so the coefficient of the defining section is
   $a^n-b^n-1$. The local zero-scheme formula [lem-pc-zero-scheme-properties] gives
   $R[a,b]/(a^n-b^n-1)$. Likewise the $A$-chart has ring $R[u,v]/(1-u^n-v^n)$. The ambient three
   standard charts cover. A point outside both the $A$- and $C$-charts would lie on the
   $B$-chart with $A/B=C/B=0$ in its residue field; the equation there would give $-1=0$. Thus
   the two claimed opens cover, without any reducedness hypothesis.
   Uses: lem-weil-pbc-projective-space-standard-charts, lem-pc-zero-scheme-properties, def-pc-
   projective-space-twist.
2. On their intersection, the degree-zero fraction restrictions of [def-pc-proj] give
   $v=C/A=a^{-1}$ and $u=B/A=b/a$. Indeed inverting $a$ in the first chart gives
   $R[a,a^{-1},b]/(a^n-b^n-1)$; substituting $v=a^{-1},u=b/a$ sends $1-u^n-v^n$ to
   $(a^n-b^n-1)/a^n=0$. Conversely $a=v^{-1},b=u/v$ sends the first equation to
   $(1-u^n-v^n)/v^n=0$. The substitutions are inverse on every generator, including coefficients
   of $R$. These formulas agree under restriction to every smaller affine base open, since the
   homogeneous fractions are the same sections.
   Uses: def-pc-proj.
3. By [lem-weil-pbc-projective-space-standard-charts] applied to $\mathbf P^1_S$, over each affine
   $V=\operatorname{Spec}R\subset S$ the standard target charts are $\operatorname{Spec}R[x]$
   and $\operatorname{Spec}R[y]$, with $y=x^{-1}$ on their overlap. Define maps from the two
   source opens to these charts by $x\mapsto a^n$ and $y\mapsto v^n$. On affine base pieces
   these ring maps give scheme morphisms by [def-weil-affine-spectrum]; they agree on base
   overlaps because $a=A/C$ and $v=C/A$ are global chart sections. Glue over $S$ using [lem-
   weil-pbc-scheme-morphism-gluing]. On the intersection, $v^n=a^{-n}$, so the two maps agree
   under the target transition $y=x^{-1}$, again the standard fractions of [def-pc-proj]. Glue
   once more to obtain $q_n$. In the $A$-chart, lying in the other target chart means $y=v^n$ is
   invertible, equivalent to $v$ invertible, hence to membership in the $C$-chart. The reverse
   assertion uses $x=a^n$ in the same way. Thus the inverse images are exactly the stated opens.
   Any morphism satisfying the specified formulas agrees on this cover, so the same gluing
   uniqueness proves uniqueness.
   Uses: lem-weil-pbc-projective-space-standard-charts, def-weil-affine-spectrum, lem-weil-pbc-
   scheme-morphism-gluing, def-pc-proj.
4. Adjoin a redundant coordinate $x=a^n$ in the $C$-chart: the map from
   $R[x,a,b]/(a^n-x,b^n-(x-1))$ to $R[a,b]/(a^n-b^n-1)$ sends $x$ to $a^n$ and fixes $a,b$. Its
   inverse fixes $a,b$, and the relations make both composites identity. Similarly $y=v^n$
   identifies the $A$-chart with the displayed $S_A$. The overlap of step 2 therefore also
   satisfies $y=v^n=a^{-n}=x^{-1}$. For $S_C$, apply [lem-sfb-monic-quotient-faithful-tensor-
   coordinates] first to $R[x][a]/(a^n-x)$ and then, over that ring, to $b^n-(x-1)$. Each
   element has a unique expression $\sum_{j<n}(\sum_{i<n}r_{ij}a^i)b^j$, with $r_{ij}\in R[x]$:
   uniqueness follows first in the $b$-basis, then in the $a$-basis. This is exactly the claimed
   product basis. For $S_A$ first adjoin $u$ with $u^n=1-y$, then $v$ with $v^n=y$, and repeat.
   The cited lemma includes the zero ring and uses the specified positive integer $n$, so no
   polynomial-degree claim over the zero ring is needed.
   Uses: lem-sfb-monic-quotient-faithful-tensor-coordinates.
5. Over the two target charts above each affine base open, step 3 identifies the inverse images
   with the affine schemes of step 4. Each coordinate algebra is generated as a module by its
   $n^2$ basis monomials, hence its structural ring map is finite. These target affines cover
   $\mathbf P^1_S$ by clauses (a) and (c) of [lem-weil-pbc-projective-space-standard-charts].
   Applying condition (2) of [lem-weil-pbc-finite-local-on-target] proves that $q_n$ is finite
   in the precise sense of [def-weil-finite-integral-morphism], even when $S$ has no finite
   affine cover.
   Uses: lem-weil-pbc-projective-space-standard-charts, lem-weil-pbc-finite-local-on-target, def-
   weil-finite-integral-morphism.
6. Each of the two successive monic quotient maps in step 4 is faithfully flat by [lem-sfb-monic-
   quotient-faithful-tensor-coordinates], since $n\geq1$. Apply [lem-weil-pbc-faithfully-flat-
   surjective-spectrum] separately to the two maps: every prime of $R[x]$ lifts first to a prime
   of $R[x][a]/(a^n-x)$ and then to a prime of $S_C$. Their composite contraction is the
   original prime, so the $C$-chart map is surjective on all points. The same two lifts using
   $u,v$ prove surjectivity over the $y$-chart. Since the target charts over all affine base
   opens cover, every point of $\mathbf P^1_S$ has a preimage under $q_n$. This argument
   includes inseparable and nonreduced charts; over an empty base it is vacuous.
   Uses: lem-sfb-monic-quotient-faithful-tensor-coordinates, lem-weil-pbc-faithfully-flat-
   surjective-spectrum.
7. For a ring map $R\to R'$, [lem-weil-pbc-fibre-product-affine-spectra] computes affine base
   change by tensor product. Explicitly, $R'\otimes_R R[a,b]/(a^n-b^n-1)\cong
   R'[a,b]/(a^n-b^n-1)$: send $r'\otimes\overline{P}$ to $r'\overline{P_{R'}}$; the inverse
   sends $r'$, $a$, $b$ to $r'\otimes1$, $1\otimes a$, $1\otimes b$. The relations vanish and
   both composites fix the generators, so this is an isomorphism with no flatness assumption.
   The identical generator argument works for the $A$-chart and both redundant-coordinate
   presentations. Projective space itself base-changes by the fibre-product definition [def-
   nagata-projective-space-base-change, def-pc-fibre-product]. By [lem-weil-pbc-projective-
   space-standard-charts] over $T$, the ambient charts of $\mathbf P^2_T$ over
   $\operatorname{Spec}R'$ are $\operatorname{Spec}R'[a,b]$ and $\operatorname{Spec}R'[u,v]$,
   with the pulled-back coordinate sections. On these ambient charts the zero scheme of the
   pulled section has exactly these quotient rings by [lem-pc-zero-scheme-properties], using
   only its local formula. The overlap substitutions still send $v$ to $a^{-1}$, $u$ to $b/a$,
   and $y$ to $x^{-1}$, and the maps still send $x$ to $a^n$, $y$ to $v^n$, because scalar
   extension fixes these monomials and fractions. For an arbitrary $T\to S$, cover $T$ by affine
   opens mapping into affine opens of $S$; the computed isomorphisms agree on overlaps on
   coefficients and coordinates and hence glue uniquely by [lem-weil-pbc-scheme-morphism-
   gluing]. They identify the base-changed closed subscheme with the stated hypersurface and
   identify its morphism with $q_n$ over $T$.
   Uses: lem-weil-pbc-projective-space-standard-charts, lem-weil-pbc-fibre-product-affine-spectra,
   def-nagata-projective-space-base-change, def-pc-fibre-product, lem-pc-zero-scheme-properties,
   lem-weil-pbc-scheme-morphism-gluing.
-/
theorem finite_chart_cover (S : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n) :
    chartOpen S n false ⊔ chartOpen S n true = ⊤ ∧
    ∃ q : curve S n ⟶ ProjectiveLine S,
      HasPowerChartFormula S n q ∧
      (∀ q' : curve S n ⟶ ProjectiveLine S, HasPowerChartFormula S n q' → q' = q) ∧
      HasTwoRootCharts S n ∧ IsFinite q ∧ Surjective q ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ S),
        ∃ (t : curve T n ⟶ curve S n) (qT : curve T n ⟶ ProjectiveLine T),
          IsPullback t (π T n) (π S n) g ∧
          IsPullback t (ι T n) (ι S n)
            (ProjectiveSpace.map (ULift.{u} (Fin 3)) g) ∧
          HasPowerChartFormula T n qT ∧ HasTwoRootCharts T n ∧
          t ≫ q = qT ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g ∧
          ∀ c : Bool, ∃ h : t ⁻¹ᵁ chartOpen S n c = chartOpen T n c,
            ∀ j : Fin 2,
              t.appLE (chartOpen S n c) (chartOpen T n c) h.ge
                (chartCoordinate S n c j) = chartCoordinate T n c j := by
  sorry

end

end AlgebraicGeometry.RelativeFermatCurve
