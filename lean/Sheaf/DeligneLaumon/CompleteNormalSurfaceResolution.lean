/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback

import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.AlgebraicGeometry.ExcellentNormalSurfaceLocalData
import Sheaf.AlgebraicGeometry.NormalizedBlowupCompletionDescent
import Sheaf.AlgebraicGeometry.SurfaceResolutionNormalizedRefinement
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Mathlib.RingTheory.Algebraic.Integral
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Sheaf.RingTheory.NagataOfCompleteLocal
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.FieldTheory.PurelyInseparableDegreePIntermediate
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.RingTheory.RegularLocalLocalization
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.ExcellentNormalizedBlowupTower
import Sheaf.DeligneLaumon.NormalSurfaceCoverCompletedDegree

/-!
# Resolution of complete normal local surfaces

Source: Stacks Project, `resolve.tex`, Tag 0BGN, `resolve-lemma-resolve-complete`
(blueprint: lem-per-complete-normal-surface-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Every complete Noetherian normal local domain of dimension two admits an
integral regular proper model inducing an isomorphism of function fields.
Source: Stacks Project, `resolve.tex`, Tag 0BGN, `resolve-lemma-resolve-complete`
(blueprint: lem-per-complete-normal-surface-resolution).

Proof plan (Stacks Tag 0BGN):

1. By the complete-local finite-over-regular theorem, choose a complete regular local subring
$R\subseteq A$ with $A$ finite over $R$. Write $F=\operatorname{Frac}R$ and
$K=\operatorname{Frac}A$. Finiteness makes the inclusion integral, hence $\dim R=\dim A=2$, and
$n=[K:F]$ is finite and positive. Prove simultaneously, by strong induction on $n$, the
following assertion: every finite inclusion $R\subseteq D$ of a complete regular local domain
into a complete normal Noetherian local domain, both of dimension $2$, with
$[\operatorname{Frac}D:\operatorname{Frac}R]=n$, admits a proper birational regular integral
model of $\operatorname{Spec}D$. The chosen $R\subseteq A$ is one instance. The induction
permits all complete regular bases, not only this initial $R$.
Uses: lem-weil-pbc-complete-local-domain-finite-over-regular, lem-weil-pbc-finite-algebra-is-
integral, lem-weil-pbc-integral-injective-dimension-equal, lem-trf-finite-domain-fraction-
degree.

2. Fix an instance $R\subseteq A$ of degree $n$ and assume the induction assertion for all
smaller positive degrees. The complete rings $R,A$ are excellent and Nagata. Every ring
essentially of finite type over either is excellent by finite-type/localization stability, hence
Nagata by quasi-excellent-implies-Nagata. We use these properties below on local rings of
finite-type models. Regularity of $R$ at its maximal ideal implies regularity of all its
localizations; regular-implies-normal applied to $\operatorname{Spec}R$ makes $R$ integrally
closed in $F$. If $n=1$, identify $K=F$. Every element of $A$ is integral over $R$ and lies in
$F$, so $A=R$. Its spectrum is regular, integral, and the identity is the required proper
birational map: it is separated, finite type and remains a closed map under every base change,
as in the definition of properness.
Uses: lem-per-complete-local-excellence, lem-weil-pbc-complete-local-nagata, lem-exc-finite-
type-localization-excellent, lem-exc-quasi-excellent-nagata, lem-weil-pbc-regular-local-
localization, rem-pc-regular-normal, lem-weil-pbc-finite-algebra-is-integral, def-weil-proper-
morphism.

3. Suppose first that $F\subsetneq L\subsetneq K$. Put $B=A\cap L$. This equals the integral
closure of $R$ in $L$: elements of $A$ are integral over $R$, and an element of $L$ integral
over $R$ is integral over $A$ and hence belongs to $A$ by normality. Also $B$ is normal: an
element of $\operatorname{Frac}B\subseteq L$ integral over $B$ is integral over $A$, so lies in
$A\cap L$. Its fraction field is $L$: for $z\in L$ use its monic algebraic equation over $F$,
and choose nonzero $r\in R$ clearing the coefficients; the equation for $rz$ has coefficients
$r^ic_{m-i}\in R$, so $rz\in B$. As an $R$-submodule of finite $A$, the ring $B$ is finite. The
finite-over-complete theorem makes this domain complete Noetherian local, and the integral-
dimension theorem gives $\dim B=2$. Its maximal ideal is $\mathfrak m_A\cap B$, since the finite
inclusions are local by the uniqueness clause of that theorem. The tower formula gives $[L:F]<n$
and $[K:L]<n$. Apply induction to $R\subseteq B$ to obtain an integral regular proper birational
model $Y\to\operatorname{Spec}B$.
Uses: lem-weil-pbc-noetherian-submodule-finite, lem-weil-pbc-finite-over-complete-local-product,
lem-weil-pbc-integral-injective-dimension-equal, lem-weil-pbc-field-degree-multiplicativity.

4. The finite-type model $Y$ is excellent, Noetherian, and has dimension $2$: it is a regular
proper birational model over the excellent local surface $B$. The closed-dominant dimension
theorem applies to its proper dominant finite-type structure map with trivial extension of
function fields, and gives $\dim Y=\dim B=2$. Now normalize $Y$ in $K$ and call the result $X$.
The normalization-cover lemma, with $C=B,D=A$, gives $X$ normal, integral, excellent and
Noetherian of dimension $2$, and a proper birational $X\to\operatorname{Spec}A$. By the normal-
surface local-data lemma its singular set is a finite set of closed points $x_i$ of local
dimension $2$. At $y_i=\pi(x_i)$ the cover lemma gives a finite inclusion of complete local
domains $\widehat{\mathcal O}_{Y,y_i}\subseteq\widehat{\mathcal O}_{X,x_i}$, with regular base
of dimension $2$, normal target of dimension $2$, and field degree at most $[K:L]<n$. Apply
induction to each of these inclusions to resolve $\operatorname{Spec}\widehat{\mathcal
O}_{X,x_i}$.
Uses: lem-exc-finite-type-localization-excellent, lem-per-normal-surface-cover-completed-degree,
lem-per-excellent-normal-surface-local-data, lem-trf-closed-dominant-dimension.

5. For each singular $x_i$, refine its completed-local resolution to a finite proper normalized
point blowup tower by the normalized-refinement theorem. Descend that tower along $\mathcal
O_{X,x_i}\to\widehat{\mathcal O}_{X,x_i}$ using completion descent; the normal completion and
local dimension $2$ are supplied by local data. The descended endpoint is regular. Globalize the
finitely many towers on $X$ by local-normalized-blowup globalization. Outside the $x_i$ it is an
isomorphism to a regular open. At a point over $x_i$, its local ring is the corresponding local
ring of the regular local endpoint, by the globalization statement. Thus the global endpoint $T$
is regular. The normalized-tower geometry lemma makes $T$ integral and the tower projective and
birational; projective-bundle properness makes it proper; composing with
$X\to\operatorname{Spec}A$ preserves properness and the identity of function fields. This
completes the intermediate-field induction case, including an empty singular set.
Uses: lem-per-surface-resolution-normalized-refinement, lem-per-normalized-blowup-completion-
descent, lem-per-local-normalized-blowups-globalize, lem-per-excellent-normalized-blowup-tower,
lem-trf-projective-bundle-proper, lem-weil-pbc-proper-composition, def-weil-regular-scheme.

6. It remains to treat $n>1$ with no strict intermediate field. Let $K_s$ be the separable
closure of $F$ in $K$. The separable-first theorem says that $K_s/F$ is separable and $K/K_s$
purely inseparable. Thus $K_s=K$, in which case $K/F$ is separable, or $K_s=F$, in which case
$K/F$ is purely inseparable of positive characteristic $p$. In the latter case the degree-$p$
intermediate-step theorem gives $K/M$ of degree $p$ for some intermediate $M$; since $M\ne K$,
absence of strict intermediates forces $M=F$, so $n=p$. In the separable case, the regular-
surface-rational theorem gives rationality of $R$, hence bounded modification genus with bound
zero, and separable ascent gives bounded modification genus for $A$. In the inseparable
degree-$p$ case, $A$ is the integral closure of $R$ in $K$ (by the same integrality and
normality argument as in Step 3); apply the degree-$p$ rational-reduction theorem. In both cases
reduction to rational singularities is possible for $A$.
Uses: lem-weil-pbc-separable-first-purely-inseparable, lem-weil-pbc-finite-purely-inseparable-
degree-p-intermediate, lem-per-regular-surface-rational, def-per-rational-surface-singularity,
lem-per-separable-rational-reduction, lem-per-degree-p-rational-reduction.

7. Apply the bounded-genus rational-model theorem to $A$. Obtain a finite tower of normalized
point blowups $X\to\operatorname{Spec}A$ such that every closed local ring of dimension $2$ on
$X$ is rational. The tower-geometry theorem gives $X$ integral, normal, Noetherian, excellent
and of dimension $2$, with proper birational composite. By normal-surface local data, the
singular set is finite, say $\{x_1,\ldots,x_t\}$, and each $R_i=\mathcal O_{X,x_i}$ is a normal
excellent Nagata local domain of dimension $2$ with normal completion. It is rational by the
rational-model conclusion, and it is essentially of finite type over the complete local ring
$A$. Apply the rational-surface Gorenstein blowup theorem to each $R_i$. This gives finite
ordinary point blowup towers with normal intermediate schemes and Gorenstein local rings at the
endpoints.
Uses: lem-per-bounded-genus-rational-model, lem-per-excellent-normalized-blowup-tower, lem-per-
excellent-normal-surface-local-data, lem-exc-quasi-excellent-nagata, lem-per-rational-surface-
gorenstein-blowups.

8. Each ordinary tower just obtained is also a normalized tower: after each blowup its scheme is
already normal, so the subsequent normalization is an isomorphism (the length-zero normal-open
clause of tower geometry). Globalize these towers at $x_1,\ldots,x_t$ using local-normalized-
blowup globalization, obtaining $X'\to X$. Its endpoint local rings above $x_i$ are those of the
chosen Gorenstein endpoint. Off the $x_i$ the scheme is regular. The tower-geometry theorem
gives $X'$ normal integral excellent Noetherian of dimension $2$. Its singular points $x'_j$ are
finite and have dimension-two local rings by local data; each lies over an $x_i$, since the
complement is unchanged and regular. Hence each $S_j=\mathcal O_{X',x'_j}$ is Gorenstein by the
endpoint local-ring identification.
Uses: lem-per-excellent-normalized-blowup-tower, lem-per-local-normalized-blowups-globalize,
lem-per-excellent-normal-surface-local-data.

9. For each singular $x'_j$ over $x_i$, the local map $R_i\to S_j$ is injective, local,
essentially of finite type and induces an isomorphism of fraction fields, because it is induced
by the birational blowup tower. The rational-propagation theorem applies: $R_i$ is a rational
normal Nagata local domain of dimension $2$; $S_j$ is normal and has dimension $2$. Thus $S_j$
is rational. Normal-surface local data gives its normal completion, and excellence gives the
Nagata condition. Together with Step 8's Gorenstein property, these are exactly the hypotheses
of the rational-double-point theorem. It gives a finite ordinary blowup tower at singular closed
points over $\operatorname{Spec}S_j$, with normal intermediate schemes and regular endpoint.
Uses: lem-per-rational-singularity-birational-propagation, lem-per-excellent-normal-surface-
local-data, lem-exc-quasi-excellent-nagata, lem-per-rational-double-point-blowup-resolution.

10. The ordinary towers of Step 9 are normalized towers because their intermediate schemes are
normal, just as in Step 8. Globalize them at the finitely many singular $x'_j$ of $X'$. Call the
endpoint $T$. For a point of $T$ whose image is not one of the $x'_j$, the morphism is an
isomorphism to the regular complement. For a point over $x'_j$, globalization identifies its
local ring with that of the regular endpoint chosen over $S_j$. Thus every local ring of $T$ is
regular; $T$ is locally Noetherian by tower geometry, so $T$ is regular. Concatenating the three
finite normalized towers and applying tower geometry over $\operatorname{Spec}A$ shows that $T$
is integral and $T\to\operatorname{Spec}A$ is projective and induces an isomorphism of function
fields; projective-bundle properness gives properness. This completes the remaining induction
case. Strong induction and Step 1 therefore prove the item.
Uses: lem-per-excellent-normalized-blowup-tower, lem-per-local-normalized-blowups-globalize,
lem-trf-projective-bundle-proper, def-weil-regular-scheme. -/
theorem exists_regular_proper_model_of_complete_normal_surface
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsLocalRing A]
    (𝔪 : Ideal A) [𝔪.IsMaximal]
    (h𝔪 : 𝔪 = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = (2 : WithBot ℕ∞))
    (hcomplete : IsAdicComplete 𝔪 A) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (f : T ⟶ Spec (.of A)),
      IsProper f ∧ IsRegularScheme T ∧
        ∃ hη : f (genericPoint T) = genericPoint (Spec (.of A)),
          IsIso (f.functionFieldMap hη) := by
  sorry

end AlgebraicGeometry
