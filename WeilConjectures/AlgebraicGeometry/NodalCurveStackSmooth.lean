/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CurveModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
public import WeilConjectures.AlgebraicGeometry.OpenModuliSubstack
public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import WeilConjectures.AlgebraicGeometry.DthFittingSmoothLocus
import WeilConjectures.AlgebraicGeometry.NodalCurveLCICriterion
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Algebraicity of curves and the smooth open substack of nodal curves

Source: Stacks Project, quot.tex, Tag 0D5A; moduli-curves.tex, Tags 0DSY and 0E00
(blueprint: lem-sfb-nodal-curve-stack-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The stack of all curves is algebraic, and the full subcategory of nonempty nodal
curves is an open algebraic substack smooth over the field. No connectedness is imposed.
The same assertions hold after every field extension.

Source: Stacks Project, quot.tex, Tag 0D5A; moduli-curves.tex, Tags 0DSY and 0E00
(blueprint: lem-sfb-nodal-curve-stack-smooth).

Proof plan:
1. Work first over $\operatorname{Spec}\mathbf Z$, and write $\mathcal C$ for the same groupoid of
families over all schemes. By [lem-sfb-curve-descent-isom-spaces] it is an fppf stack, hence an
etale stack, and its isomorphism sheaves are algebraic spaces, which is precisely representability
of its diagonal. The cardinal bound in Artin\'s criterion is satisfied: over each finite type
field, finite-presentation algebraic spaces and arrows have presentations by finitely many affine
charts and finitely many ring equations and maps; the chosen scheme universe bounds these sets of
presentations [def-weil-size-convention]. This size verification does not assert effectivity or an
atlas.

2. Apply [lem-sfb-artin-representable-diagonal-criterion] over $\mathbf Z$. Its stack, diagonal,
and size assumptions were checked in step 1. Limit preservation, including descent and eventual
equality of arrows, is [lem-sfb-curve-limit-preservation]. The pushout equivalence [lem-sfb-curve-
infinitesimal-pushout] applies in particular to the Artinian pushouts in the criterion, giving
(RS). The two finite-dimensional vector spaces required there are exactly those in [lem-sfb-curve-
tangent-finiteness]. Every formal object is effective by [lem-sfb-curve-formal-effectivity]; its
statement imposes no restriction on the residue field, so it covers the required finite type ones.
Openness of versality with the same Artinian lifting definition is [lem-sfb-curve-openness-
versality]. Every premise of the criterion is therefore met, and $\mathcal C$ has a representable
diagonal and a smooth surjective scheme atlas.

3. The groupoid $\mathfrak C$ is the 2-fibre product $\mathcal C\times_{\operatorname{Spec}\mathbf
Z}\operatorname{Spec}k$: an object is a family over $T$ together with its structural map
$T\to\operatorname{Spec}k$, and the arrows on both sides are the same cartesian isomorphisms. Pull
back an atlas $U\to\mathcal C$ to the scheme $U_k$. Its diagonal tests are base changes of the
algebraic-space Isom sheaves, hence algebraic spaces by [lem-trf-space-fibre-products-etale-
covers]. Its atlas is smooth and surjective: smoothness on scheme charts is preserved by base
change by [lem-sbc-smooth-relative-dimension-permanence], after using the locally constant
relative dimension in [def-sbc-smooth-morphisms] to cover each smooth chart by fixed-dimension
opens. Surjectivity persists because a nonempty fibre over a field remains nonempty after a field
extension (a tensor product of nonzero vector spaces over a field is nonzero). Thus $\mathfrak C$
is algebraic.

4. For any $X\xrightarrow f T$ in $\mathfrak C$, let $V\subseteq X$ be the maximal nodal relative-
dimension-one open of [lem-sfb-space-nodal-locus-base-change]. Put $Z=|X|\setminus|V|$ and
$T_{\mathrm{nod}}=T\setminus|f|(Z)$. Properness, which includes universal closedness, makes this
an open subscheme. It consists exactly of the base points over which the entire geometric fibre
lies in $V$. It is compatible with arbitrary base change: $V$ pulls back by the cited lemma, its
complement therefore pulls back, and the image of that complement pulls back on point sets. Indeed
over a point $t'$ above $t$, a nonempty bad fibre over $\kappa(t)$ stays nonempty over
$\kappa(t')$, since tensoring a nonzero field-valued point with a field extension is faithfully
flat; an empty bad fibre stays empty. Thus a base change has all its fibres empty or pure one-
dimensional and at worst nodal if and only if its base map factors through $T_{\mathrm{nod}}$.

5. The locus $T_{\ne\varnothing}=|f|(|X|)$ of nonempty fibres is open by [lem-sfb-flat-lfp-space-
universally-open], and is also closed by properness. Its formation commutes with base change by
the same nonempty-field-fibre argument in step 4. Consequently $T_N=T_{\mathrm{nod}}\cap
T_{\ne\varnothing}$ is open, commutes with all base changes, and a map $T'\to T$ factors through
it exactly when the pulled-back family lies in $\mathfrak N$. These opens give the scheme
pullbacks of $\mathfrak N\to\mathfrak C$, so this is an open immersion of stacks. Explicitly
descent follows by restricting descent in $\mathfrak C$ to these compatible opens. Pulling
$\mathfrak N$ back to the scheme atlas $U_k$ restricts it to an open scheme atlas, and its Isom
sheaves are the same as those of $\mathfrak C$, so $\mathfrak N$ is algebraic.

6. Let $C/\Omega$ be any geometric fibre of a family in $\mathfrak N$, with $\Omega$ algebraically
closed. It is a separated finite-type algebraic space of dimension one, hence a scheme by [lem-
sfb-separated-space-dimension-one-scheme]. It is pure of dimension one by hypothesis and proper
and of finite type. Apply [lem-trf-nodal-curve-lci-criterion]: every closed point is smooth or an
ordinary node by our geometric-fibre hypothesis, so $C$ is a local complete intersection and its
first-Fitting singular scheme $Z_C$ is unramified over $\Omega$. Its underlying closed subset is
the nonsmooth locus by [lem-trf-dth-fitting-smooth-locus], applied with $d=1$; flatness holds over
the field, local finite presentation comes from the given family, and the required geometric
purity is exactly the nodal-fibre hypothesis, which tests all algebraically closed extensions.

7. The scheme $C$ is Noetherian: it is quasi-compact because it is of finite type over a field,
and is locally Noetherian by [pqf-lem-locnoeth-lft], since a field is Noetherian. The closed
subscheme $Z_C$ is locally of finite type over $\Omega$ (its affine rings are quotients of
finitely generated $\Omega$-algebras). Its unramifiedness and [lem-trf-unramified-over-field-
local-criterion] imply every point of $Z_C$ is closed; the closed immersion makes it closed in $C$
as well. By [lem-sc-noetherian-closed-points-finite] its underlying subset is finite. Thus $C$ is
smooth except at finitely many points, with precisely the local-complete-intersection condition
already obtained in step 6. Empty singular set, smooth fibres and disconnected fibres cause no
exception.

8. Let $\mathcal L\subseteq\mathcal C$ be the open of [lem-sfb-isolated-lci-curve-smooth-open].
Steps 6 and 7, with its field-point characterization, show that every geometric point of
$\mathfrak N$ belongs to $\mathcal L_k$. Hence $\mathfrak N$ is an open substack of $\mathcal
L_k$: for any scheme-valued object its inverse image of $\mathcal L_k$ is an open containing every
geometric point of its base and so is the whole base. Choose a smooth atlas $W\to\mathcal L$ whose
composite to $\operatorname{Spec}\mathbf Z$ is smooth. Its base change $W_k$ and its open
restriction over $\mathfrak N$ have smooth composites to $\operatorname{Spec}k$. On scheme charts
this follows from [lem-sbc-smooth-relative-dimension-permanence] and the locally constant
relative-dimension cover in [def-sbc-smooth-morphisms]; open restriction preserves the local
lifting condition defining smoothness, since a nilpotent thickening has the same underlying points
so its lift still lands in the open. This restricted atlas is surjective, so $\mathfrak N$ is
smooth over $k$. Finally all the constructions can be base changed along any field extension
$k'/k$: the atlas, the Isom sheaves, and the opens $T_N$ above pull back, and smoothness persists
by the same permanence result. This proves every asserted field-extension clause.
-/
theorem nodal_curve_stack_smooth (k : Type u) [Field k] :
    IsAlgebraicModuliStack (ProperCurveModuli.category (Spec (.of k))) ∧
    IsAlgebraicModuliStack (fullModuliSubcategory
      (ProperCurveModuli.category (Spec (.of k)))
      (fun X ↦ X.family.HasNonemptyNodalGeometricFibres)) ∧
    (∃ N : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
      N.property = fun X ↦ X.family.HasNonemptyNodalGeometricFibres) ∧
    IsSmoothModuliStack (fullModuliSubcategory
      (ProperCurveModuli.category (Spec (.of k)))
      (fun X ↦ X.family.HasNonemptyNodalGeometricFibres)) ∧
    ∀ (K : Type u) [Field K] [Algebra k K],
      IsAlgebraicModuliStack (ProperCurveModuli.category (Spec (.of K))) ∧
      IsAlgebraicModuliStack (fullModuliSubcategory
        (ProperCurveModuli.category (Spec (.of K)))
        (fun X ↦ X.family.HasNonemptyNodalGeometricFibres)) ∧
      (∃ N : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of K))),
        N.property = fun X ↦ X.family.HasNonemptyNodalGeometricFibres) ∧
      IsSmoothModuliStack (fullModuliSubcategory
        (ProperCurveModuli.category (Spec (.of K)))
        (fun X ↦ X.family.HasNonemptyNodalGeometricFibres)) := by
  sorry

end AlgebraicGeometry
