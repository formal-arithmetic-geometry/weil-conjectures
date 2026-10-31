/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import WeilConjectures.Blowup.Affine.ChartAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Blowup.Affine.Defs
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.RegularLocalLiftRegularSequenceQuotient
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Blowup of the closed point of a regular local surface

Source: Stacks Project, resolve.tex, Tags 0AGQ and 0AGR
(blueprint: lem-sfb-local-surface-maximal-blowup-geometry).

The centre is the kernel ideal of the residue-field closed immersion. The exceptional
scheme is its scheme-theoretic inverse image, with its canonical map to the blowup.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closed point of `Spec A`, as the kernel ideal of `Spec(A/𝔪) → Spec A`.
Source: Stacks Project, Tag 0AGQ
(blueprint: lem-sfb-local-surface-maximal-blowup-geometry). -/
noncomputable def localSurfaceMaximalBlowupCenter
    (A : Type u) [CommRing A] [IsLocalRing A] : (Spec (.of A)).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).ker

/-- The scheme-theoretic exceptional fibre of the blowup of the maximal ideal of `A`.
Its base field is literally `A/𝔪`, rather than a chosen isomorphic field.
Source: Stacks Project, Tag 0AGQ, `E = X_κ`
(blueprint: lem-sfb-local-surface-maximal-blowup-geometry). -/
noncomputable def localSurfaceMaximalBlowupExceptional
    (A : Type u) [CommRing A] [IsLocalRing A] : Scheme.{u} :=
  pullback (localSurfaceMaximalBlowupCenter A).blowupMap
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))

/-- The canonical closed immersion of the exceptional fibre in the blowup.
Source: Stacks Project, Tags 0AGQ and 0AGR
(blueprint: lem-sfb-local-surface-maximal-blowup-geometry). -/
noncomputable def localSurfaceMaximalBlowupExceptionalι
    (A : Type u) [CommRing A] [IsLocalRing A] :
    localSurfaceMaximalBlowupExceptional A ⟶ (localSurfaceMaximalBlowupCenter A).blowup :=
  pullback.fst (localSurfaceMaximalBlowupCenter A).blowupMap
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))

/-- The maximal-ideal blowup of a two-dimensional regular local ring is Noetherian and
regular; its exceptional fibre is an effective Cartier projective line over the residue
field, and the ambient stalks at closed points of that fibre have dimension two.
Source: Stacks Project, Tags 0AGQ and 0AGR
(blueprint: lem-sfb-local-surface-maximal-blowup-geometry).

Proof plan, preserving the live node's nine steps:
1. Use the singleton affine cover of $S=\operatorname{Spec}A$ in the global blowup construction;
its sole local model is the affine blowup of $\mathfrak m$. By the definition of regular local
ring, choose $x,y$ generating $\mathfrak m$. The regular-system-of-parameters theorem makes both
$(x,y)$ and $(y,x)$ regular sequences. The affine blowup chart cover and the regular-sequence
chart-presentation theorem give an open cover of $Y$ by $$U_x=\operatorname{Spec}C_x,\quad
C_x=A[\mathfrak m/x]\cong A[t]/(xt-y),\qquad U_y=\operatorname{Spec}C_y,\quad C_y=A[\mathfrak
m/y]\cong A[u]/(yu-x).$$ Here $t$ is the ratio $y/x$ and $u$ is $x/y$ under the chart
identifications. No excellence or algebraically closed residue field is assumed. Uses:
def-nagata-global-blowup, def-nagata-global-blowup-glue-data,
def-nagata-global-blowup-local-model, def-weil-regular-scheme,
lem-weil-pbc-regular-local-generators-regular-sequence, prop-nagata-affine-blowup-chart-cover,
lem-trf-blowup-chart-regular-sequence-presentation.

2. On $U_x$ the extended maximal ideal is $(x,y)C_x=(x)$ since $y=xt$; on $U_y$ it is $(y)$ since
$x=yu$. By the definition of the chart ring, $C_x$ is a subalgebra of $A_x$. Multiplication by $x$
on $C_x$ is injective: an equality $xc=0$ remains true in $A_x$, where $x$ is a unit, hence $c=0$
in that subalgebra. The same argument applies to $y$ on $C_y$. The scheme-theoretic inverse image
of the closed point is locally defined by the extended ideal: for either chart $C$, $C\otimes_A
k=C/\mathfrak m C$. Consequently $E$ is locally cut out by these nonzerodivisors, which is
precisely the effective Cartier condition. Uses: def-nagata-blowup-chart-ring,
def-nagata-effective-cartier-ideal, def-weil-pbc-localization-at-prime.

3. The ring $A$ is Noetherian by regular localness. Each of $C_x,C_y$ is a quotient of a
one-variable polynomial algebra over $A$, so the finite-type-algebra Noetherian theorem makes both
Noetherian. Thus the two-chart cover makes $Y$ locally Noetherian. It also makes $Y$
quasi-compact: each affine spectrum is quasi-compact, since a covering by basic opens $D(f_i)$
means that the $f_i$ generate the unit ideal, and an expression $1=\sum_{i\in F}a_if_i$ uses
finitely many indices. Any open cover refines to basic opens on each chart, giving finite
subcovers on the two charts, and their union is finite. Hence $Y$ is Noetherian (locally
Noetherian and quasi-compact). Uses: def-weil-regular-scheme,
lem-weil-pbc-finite-type-algebra-noetherian, pqf-def-locnoeth, def-weil-affine-spectrum,
lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact.

4. The fibre rings on the two charts are $$C_x/(x)=A[t]/(x,y)=k[t],\qquad
C_y/(y)=A[u]/(x,y)=k[u].$$ The chart map sends $t$ to $(yT)/(xT)$ in the degree-zero homogeneous
localization of the Rees algebra, and sends $u$ to $(xT)/(yT)$. In the $x$-chart the $y$-chart is
therefore exactly the basic open where $t$ is invertible, and conversely it is the open where $u$
is invertible in the $y$-chart. On this intersection the two ratios multiply to $1$. Reducing
modulo the extended maximal ideal, the overlap is $\operatorname{Spec}k[t,t^{-1}]$ with transition
$u=t^{-1}$. These are ring identities in the homogeneous localizations, so the computation
concerns the scheme-theoretic fibre, including its structure sheaf. Uses:
def-nagata-affine-blowup-chart-map, def-nagata-affine-proj.

5. Apply the projective-space standard-chart theorem with base $\operatorname{Spec}k$ and two
homogeneous coordinates $T_0,T_1$. Its charts have rings $k[T_1/T_0]$ and $k[T_0/T_1]$; their
intersection is where the displayed coordinate is invertible, because each homogeneous coordinate
is a free generator of $\mathcal O(1)$ on its own chart. The products of these ratios are $1$.
Sending $t$ to $T_1/T_0$ and $u$ to $T_0/T_1$ therefore gives chart isomorphisms agreeing on the
overlap computed in step 4. They glue, as do their inverses, to an isomorphism $E\cong\mathbf
P^1_k$. Moreover $k[t]$ and $k[u]$ are regular rings by the polynomial-regularity lemma. The
affine-open stalk-localization theorem identifies every local ring of $E$ with a prime
localization of one of them, hence it is regular local. Uses:
lem-weil-pbc-projective-space-standard-charts, lem-sc-p1-polynomial-regular,
lem-weil-pbc-affine-open-stalk-localization, def-weil-regular-scheme.

6. Let $q\in E$ be any point, choose a chart $C=C_x$ or $C_y$ containing it, and write $g=x$ or
$y$ respectively. The affine-open stalk theorem identifies $R=\mathcal O_{Y,q}$ with $C_{\mathfrak
p}$, where $g\in\mathfrak p$. The localization-Noetherian theorem makes $R$ Noetherian. The
element $g/1$ is still a nonzerodivisor: if $(g/1)(a/s)=0$, some $v\notin\mathfrak p$ kills $ga$
in $C$, so $g(va)=0$ and hence $va=0$ by step 2; thus $a/s=0$. Quotienting the fractions gives
$$R/gR\cong(C/(g))_{\mathfrak p/(g)}\cong\mathcal O_{E,q}.$$ Indeed both sides have
representatives $a/s$ with $s\notin\mathfrak p$, and setting $g=0$ imposes exactly the ideal $gR$.
Uses: lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian,
def-weil-pbc-localization-at-prime.

7. For the ring $R$ of step 6, $g$ lies in its maximal ideal, is a nonzerodivisor, and $R/gR$ is
regular local by step 5. The singleton sequence $(g)$ is regular: multiplication is injective and
its quotient is nonzero because $(g)$ lies in the maximal ideal. Apply regularity lifting from a
regular-sequence quotient with $r=1$. It proves that every $\mathcal O_{Y,q}$ with $q\in E$ is
regular local, including the generic point of $E$. Uses: def-weil-pbc-regular-sequence,
lem-exc-regular-local-lift-regular-sequence-quotient.

8. On $U_x\setminus E$ the chart ring is $(C_x)_x=A[t,x^{-1}]/(xt-y)\cong A_x$, with mutually
inverse maps given by $t\mapsto y/x$ and the coefficient map. On $U_y\setminus E$ it is similarly
$A_y$. A prime $\mathfrak p$ of $C_x$ avoiding $x$ thus corresponds to a prime $\mathfrak r$ of
$A$ avoiding $x$, and the same fractions identify $(C_x)_{\mathfrak p}$ with $(A_x)_{\mathfrak
rA_x}=A_{\mathfrak r}$. The $y$-chart is identical with $x,y$ interchanged. The
regular-local-localization theorem applied to $A$ makes these rings regular local. Together with
step 7 this proves regularity at every point of $Y$; since $Y$ is locally Noetherian by step 3,
the local-ring characterization of regular schemes proves that $Y$ is regular. Uses:
lem-weil-pbc-regular-local-localization, lem-weil-pbc-affine-open-stalk-localization,
def-weil-pbc-localization-at-prime, def-weil-regular-scheme.

9. Finally let $q$ be closed in $E$. Its intersection with a chart is closed in
$\operatorname{Spec}k[t]$ or $\operatorname{Spec}k[u]$, so its prime there is a maximal ideal
$\mathfrak n$. The maximal-localization dimension theorem with one variable gives $\dim\mathcal
O_{E,q}=\dim k[t]_{\mathfrak n}=1$ (using $u$ on the other chart). Step 6 supplies the Noetherian
local ring $R=\mathcal O_{Y,q}$, the nonzerodivisor $g$ in its maximal ideal, and
$R/gR\cong\mathcal O_{E,q}$. The nonzerodivisor quotient dimension formula now gives $\dim
R=\dim(R/gR)+1=2$. Its regular localness was already proved in step 7. No rationality of the
closed point over $k$ is used. Uses: lem-weil-pbc-polynomial-ring-maximal-localization-dimension,
lem-weil-pbc-dimension-quotient-nonzerodivisor.
-/
theorem localSurfaceMaximalBlowupGeometry
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = (2 : WithBot ℕ∞)) :
    IsNoetherian (localSurfaceMaximalBlowupCenter A).blowup ∧
    IsRegularScheme (localSurfaceMaximalBlowupCenter A).blowup ∧
    (localSurfaceMaximalBlowupExceptionalι A).ker.IsInvertible ∧
    (∃ e : localSurfaceMaximalBlowupExceptional A ≅
        ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of (IsLocalRing.ResidueField A))),
      e.hom ≫ (ProjectiveSpace (ULift.{u} (Fin 2))
          (Spec (.of (IsLocalRing.ResidueField A))) ↘ Spec (.of (IsLocalRing.ResidueField A))) =
        pullback.snd (localSurfaceMaximalBlowupCenter A).blowupMap
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ∧
    ∀ q : localSurfaceMaximalBlowupExceptional A, IsClosed ({q} : Set _) →
      IsRegularLocalRing ((localSurfaceMaximalBlowupCenter A).blowup.presheaf.stalk
        (localSurfaceMaximalBlowupExceptionalι A q)) ∧
      ringKrullDim ((localSurfaceMaximalBlowupCenter A).blowup.presheaf.stalk
        (localSurfaceMaximalBlowupExceptionalι A q)) = (2 : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
