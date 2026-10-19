/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.AlgebraicGeometry.PullbackStalkRelativeFlatExtension
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.ValuativeFibreComponentLift
import Sheaf.RingTheory.ValuationDomainFibreDimensions
import Sheaf.TraceFormula.ValuationFiniteModuleInjectivity
import Sheaf.AlgebraicGeometry.RelativeAssassinBaseChange

/-! # Specialization of a relative associated point at a flat component generic point

Source: Stacks Project, More on Morphisms, Tag 0GSI, statement and all three proof
paragraphs (blueprint: lem-trf-flat-relative-associated-specialization).

## Main definitions and statements

* `Scheme.Hom.associatedPointClosureToBase`: the reduced point closure over the base.
* `Scheme.Hom.associatedPointClosureFiberToAmbient`: its fibre's canonical map to `X`.
* `flat_relative_associated_specialization`: association and the dimension equalities.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The reduced closure of `y` mapped to the base by its closed immersion followed by `f`.
The vanishing ideal is Mathlib's actual reduced induced closed-subscheme construction.
Source: Stacks Project, More on Morphisms, Tag 0GSI
(blueprint: lem-trf-flat-relative-associated-specialization). -/
def Scheme.Hom.associatedPointClosureToBase {X S : Scheme.{u}} (f : X ⟶ S) (y : X) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subscheme ⟶ S :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subschemeι ≫ f

/-- The map `Y_s → Y → X`, for `Y` the reduced closure of `y`.
Source: Stacks Project, More on Morphisms, Tag 0GSI
(blueprint: lem-trf-flat-relative-associated-specialization). -/
def Scheme.Hom.associatedPointClosureFiberToAmbient
    {X S : Scheme.{u}} (f : X ⟶ S) (y : X) (s : S) :
    (f.associatedPointClosureToBase y).fiber s ⟶ X :=
  (f.associatedPointClosureToBase y).fiberι s ≫
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subschemeι

/-- Source: Stacks Project, More on Morphisms, Tag 0GSI, statement and proof,
including the component-dimension equality in the second proof paragraph
(blueprint: lem-trf-flat-relative-associated-specialization).

The only flatness hypothesis is at the image in `X` of the chosen component generic point.
Restriction of scalars along `f.stalkMap` supplies exactly the base-local-ring module action.

Proof plan:
1. The integral closed subscheme $Y\hookrightarrow X$ is locally of finite type by
[lem-weil-pbc-immersion-base-change-lft](2), so $Y\to S$ is locally of finite type by
[lem-weil-pbc-proper-fp-permanence](e). These assertions remain true after arbitrary base change
by [lem-weil-pbc-lft-base-change], and hold also for the integral closed subschemes $Y'$ used
below. In particular all fibres and field-extended fibres used below are locally of finite type
over their fields, hence locally Noetherian by [pqf-lem-locnoeth-lft]. The spectrum of a field is
Noetherian since its only ideals are zero and the whole field. No Noetherianity of $S$ is
asserted.

2. For each of these locally algebraic fibres, at a component generic point $z$ one has $\dim_z
Z=\dim\overline{\{z\}}$. Indeed [lem-sc-locnoeth-components-locally-finite] gives a neighbourhood
meeting only finitely many components; remove the other components, none of which contains $z$, to
obtain an open neighbourhood contained in its component $D$. On this neighbourhood the ambient
space and $D$ have the same topology. [lem-sc-dimension-locally-algebraic] gives $\dim_zD=\dim D$,
proving the assertion from the neighbourhood definition of dimension. Apply this in particular to
$x\in Y_s$ to obtain $\dim_xY_s=\dim C$. Also $Y_t$ is irreducible with generic point $y$: on
affine charts it is obtained from the domain defining $Y$ by inverting the nonzero functions on
the integral image closure of $t$.

3. Apply [lem-trf-valuative-fibre-component-lift] to $f,y,s,x$. Retain its square
$X'=X\times_SS'$, valuation base $S'=\operatorname{Spec}A$, points $t',s',y',x'$ and integral
closed subscheme $Y'=\overline{\{y'\}}$. Put $K=\operatorname{Frac}(A)$ and $k=A/\mathfrak m_A$.
Write $C'$ for the component of $Y'_{s'}$ with generic point $x'$. The generic fibre $Y'_{t'}$ is
the component of $Y_t\times_t t'$ with generic point $y'$: on affine charts taking the prime
defining the closure of $y'$ and then localizing in $A\setminus\{0\}$ recovers the prime of that
component.

4. Put $\mathcal F'=(g')^*\mathcal F$. It is quasi-coherent and finite type by
[lem-weil-pbc-module-pullback-quasi-coherent] and [lem-weil-pbc-module-pullback-finite-type]. The
stalk formula [lem-weil-pbc-module-stalk-pullback] and pointwise scalar extension
[lem-pc-pullback-stalk-relative-flat-extension], applied with $M=\mathcal F_x$, give that
$\mathcal F'_{x'}$ is $A$-flat; here $\mathcal O_{S',s'}=A$. Since $y'$ is generic in a component
of $Y_t\times_t t'$, it is generic in its fibre over the generic point $y$ (localizing at $y$
preserves minimal primes). The residual fibre is
$\operatorname{Spec}(\kappa(t')\otimes_{\kappa(t)}\kappa(y))$. As $y$ is relatively associated,
[lem-trf-relative-assassin-base-change] therefore gives $y'\in\operatorname{Ass}_{X'/S'}(\mathcal
F')$.

5. Prove $x'\in\operatorname{Ass}_{X'/S'}(\mathcal F')$ by contradiction. Set $B=\mathcal
O_{X',x'}$, $N=\mathcal F'_{x'}$, $R=B/\mathfrak m_AB$ and $L=N/\mathfrak m_AN$. Choose a finite
type affine $A$-chart around $x'$ and an affine module presentation there. By
[lem-weil-pbc-affine-open-stalk-localization] and [lem-weil-pbc-spec-tilde-stalk-localization],
$B$ is a localization at a prime of that finite type algebra and $N$ is a finite $B$-module. The
local map $A\to B$ is thus essentially of finite type. The same localization formulas on the
closed-fibre chart and [lem-weil-pbc-module-stalk-pullback] identify $R=\mathcal O_{X'_{s'},x'}$
and $L=(\mathcal F'_{s'})_{x'}$. Thus $R$ is Noetherian by step 1 and $L$ is finite. If $x'$ is
not relatively associated, the maximal ideal $\mathfrak m_R$ is not associated to $L$.

6. Let $\mathfrak q\subset B$ be the prime corresponding to $y'$, which specializes to $x'$. In
the local spectrum the closure of $y'$ is $V(\mathfrak q)$. Its closed fibre at $x'$ has just one
prime, since $x'$ is the generic point of its fibre component and localization keeps only primes
contained in $\mathfrak m_B$. Consequently $\sqrt{\mathfrak q+\mathfrak m_AB}=\mathfrak m_B$, or
$\sqrt{\overline{\mathfrak q}}=\mathfrak m_R$ for the image ideal in $R$. Apply
[lem-weil-pbc-nonzerodivisor-if-maximal-not-associated] to the Noetherian local ring $R$ and
finite module $L$: obtain $h\in\mathfrak m_R$ acting injectively on $L$. Some power $h^n$, with
$n\ge1$, lies in $\overline{\mathfrak q}$, so choose $g\in\mathfrak q$ with image $h^n$ in $R$.
Its multiplication on $L$ is injective as a composite of $n$ injective maps. This is the source's
prime-avoidance conclusion, obtained here from the existing nonzerodivisor lemma and the radical
equality.

7. Apply [lem-trf-valuation-finite-module-injectivity] to multiplication $g:N\to N$. The two
$B$-modules are finite, the target is $A$-flat by step 4, the map $A\to B$ is local essentially of
finite type, and its reduction is injective by step 6. Hence $g$ acts injectively on $N$. It
remains injective after both localizations used to reach the generic-fibre stalk at $y'$: if
$g(n/u)=0$, the fraction criterion [def-weil-pbc-module-localization] supplies a further
denominator $v$ with $vgn=0$; injectivity gives $vn=0$ and thus $n/u=0$. By the affine stalk and
pullback formulas of step 5, this localized module is $(\mathcal F'_{t'})_{y'}$, over
$(B\otimes_AK)_{\mathfrak q}=\mathcal O_{X'_{t'},y'}$. But $y'$ is relatively associated, so this
stalk has a nonzero element annihilated by its maximal ideal. The element $g\in\mathfrak q$ maps
into that maximal ideal and kills it, contradicting injectivity. Therefore $x'$ is relatively
associated.

8. By [lem-trf-relative-assassin-base-change], the associated point $x'$ maps to
$x\in\operatorname{Ass}_{X/S}(\mathcal F)$ and is generic in the residue-field fibre over $x$ of
$X'_{s'}\to X_s$. This same residual fibre occurs for $Y_s\times_s s'\to Y_s$, since $x\in Y_s$
and a closed immersion does not change its residue field. Because $x$ is a component generic point
of $Y_s$, $x'$ is a component generic point of $Y_s\times_s s'$: on affine charts, a prime
properly contained in the prime of $x'$ would contract to a prime contained in the minimal prime
of $x$, hence to that same prime; after localizing at $x$ it would contradict minimality in the
residue-field fibre. Thus the closure of $x'$ in $Y_s\times_s s'$ is an irreducible component. It
equals $C'$ topologically because $Y'_{s'}$ is a closed subscheme of this base change and contains
$x'$.

9. Choose a finite type affine $A$-chart $W=\operatorname{Spec}D\subset Y'$ containing $x'$. Its
coordinate ring is a domain and $A\to D$ is injective: every nonempty open of the integral scheme
$Y'$ contains $y'$, whose image is the generic point of $\operatorname{Spec}A$, so a nonzero
element of $A$ cannot vanish in $D$. The fibre $W_{s'}$ is nonempty. Apply
[lem-trf-valuation-domain-fibre-dimensions]: every component of $W_{s'}$ has dimension
$\dim(D\otimes_AK)$. In particular $C'\cap W$ is such a component by
[lem-sc-components-open-injection]. By [lem-sc-dimension-locally-algebraic], its dimension is
$\dim C'$, while the nonempty open $W_{t'}$ of the irreducible $Y'_{t'}$ has dimension $\dim
Y'_{t'}$. The affine spectrum/ring comparison [lem-weil-pbc-spec-topological-krull-dimension-ring]
identifies $\dim W_{t'}=\dim(D\otimes_AK)$. Hence $\dim C'=\dim Y'_{t'}$.

10. Apply [lem-sc-fibre-dimension-after-base-change] to $Y\to S$ at $y'$ over $t'$:
$\dim_{y'}(Y_t\times_t t')=\dim_yY_t$. Step 2 identifies the left side with $\dim Y'_{t'}$ and the
right side with $\dim Y_t$, since $y'$ is generic in its component and $Y_t$ is irreducible. The
same base-change lemma at $x'$ over $s'$ gives $\dim_{x'}(Y_s\times_s s')=\dim_xY_s$. By step 8,
$x'$ is a component generic point of this entire base change, so step 2 identifies its local
dimension with $\dim C'$. Combining these equalities with steps 2 and 9 gives $\dim_xY_s=\dim
C=\dim C'=\dim Y'_{t'}=\dim Y_t$. Together with step 8 this is the required conclusion.
-/
theorem flat_relative_associated_specialization
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ Scheme.Modules.relativeAssassin f F) (s : S)
    (C : Set ((f.associatedPointClosureToBase y).fiber s))
    (hC : C ∈ irreducibleComponents ((f.associatedPointClosureToBase y).fiber s))
    (x : (f.associatedPointClosureToBase y).fiber s) (hx : IsGenericPoint x C)
    (hflat : Module.Flat
      (S.presheaf.stalk (f (f.associatedPointClosureFiberToAmbient y s x)))
      ((ModuleCat.restrictScalars
        (f.stalkMap (f.associatedPointClosureFiberToAmbient y s x)).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (f.associatedPointClosureFiberToAmbient y s x)).obj F))) :
    f.associatedPointClosureFiberToAmbient y s x ∈ Scheme.Modules.relativeAssassin f F ∧
      topologicalKrullDimAt x = topologicalKrullDim C ∧
      topologicalKrullDim C =
        topologicalKrullDim ((f.associatedPointClosureToBase y).fiber (f y)) := by
  sorry

end AlgebraicGeometry
