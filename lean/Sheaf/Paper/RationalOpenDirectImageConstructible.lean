/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.Paper.PadicIntegersInvertEll
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.Paper.CompletedCondensedCoefficients
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage
import Sheaf.Paper.IntegralModels
import Sheaf.SixFunctors.ScalarSixPullback

/-!
# Rational open direct images with finite constant local models

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-open-coefficients,
integral and rational paragraphs
(blueprint: lem-sfb-rational-open-direct-image-constructible).

The two conjuncts are the finite-subextension and algebraic-closure coefficient cases.
Both use the finite-constant-model predicate, rather than general local finite presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Rational derived direct image along a quasi-compact open immersion preserves bounded
constructibility with finite constant scalar models, for both rational coefficient rings.
Source: blueprint sk-prop-open-coefficients, rational paragraph
(blueprint: lem-sfb-rational-open-direct-image-constructible).

Proof:
1. The schemes $U,X$ are separated and finite type over $k$. Since every ideal of the field $k$ is
   zero or the whole field, $\operatorname{Spec}k$ is Noetherian;
   [lem-weil-pbc-finite-type-over-noetherian] makes $U,X$ Noetherian. They are qcqs by
   [lem-weil-pbc-qcqs-over-affine], and $j$ is qcqs by [lem-weil-pbc-qcqs-morphism-permanence](1).
   These are exactly the Noetherian and qcqs hypotheses used below.
2. The hypothesis $K\in\Dbc(U,\Lambda)$ is already the finite-constant-local-model category
   defined in [sk-def-sfb-constructible], so [sk-lem-integral-models](4) applies directly to this
   $K$ (this is the needed input direction, rather than an implication from the weaker
   locally-finitely-presented predicate). It gives, for $\Lambda=E$, a finite construction by
   cones and shifts from $C=(a_!L_0)[1/\ell]$. For $\Lambda=\overline{\mathbf Q}_\ell$ the same
   clause gives such a construction from $\overline{\mathbf Q}_{\ell,U}\otimes^{\mathbf
   L}_{\mathcal O_{E',U}}a_!L_0$ for some finite $E'\subset\overline{\mathbf Q}_\ell$. For each
   generator put $L=a_!L_0$. The same cited clause gives $L\in\Dbc(U,\mathcal O_{E'})$. The
   integral open-image theorem [det-thm-sf-pf-adic-open] therefore gives
   $M=Rj_*L\in\Dbc(X,\mathcal O_{E'})$. Its hypotheses hold for this same $j$ and for every finite
   $E'$. This is the integral paragraph of the source, already stated as a strictly smaller
   existing lemma. No conversion of the input $K$ to general ring-object constructibility is used.
3. Fix one such integral generator and write $E$ for its finite coefficient field. The
   localization [det-prop-sfb-qlbar-colimit-x-invert-ell] identifies $E_T=\mathcal
   O_{E,T}[1/\ell]$ and makes this extension flat, for $T=U,X$. Thus $C=E_U\otimes^{\mathbf L}L$
   is the sheafwise localization telescope $L\xrightarrow{\ell}L\to\cdots$; this follows by
   tensoring the localization cocone, since tensor is a left adjoint
   [sk-def-sfb-derived-tensor-hom, lem-weil-pbc-left-adjoint-preserves-colimits]. Choose a
   bounded-below representative of the bounded $L$ and use the same representative at every stage.
   The common lower bound and qcqs $j$ permit [lem-weil-pbc-condensed-qcqs-pushforward-continuity]
   at fixed $\mathcal O_E$ coefficients. Its canonical cohomology comparisons give
   $E_X\otimes^{\mathbf L}M\simeq Rj_*C$. For the coefficient action use
   [lem-weil-pbc-ring-sheaf-change-adjunction]: restriction commutes with derived direct image and
   reflects isomorphisms. Its coefficient square is supplied by
   [sk-prop-sfb-cartesian-coefficients] and [sk-def-sfb-coefficient-change]. The telescope
   comparison respects scalar multiplication at every stage, so this is an $E_X$-linear
   isomorphism.
4. The extension $E_T\otimes^{\mathbf L}_{\mathcal O_{E,T}}N$ is bounded with finite constant
   local models whenever $N\in\Dbc(T,\mathcal O_E)$, for $T=U,X$. Indeed flatness from
   [det-prop-sfb-qlbar-colimit-x-invert-ell] and [lem-sfb-extend-scalars-preserves-homology]
   identify its degree-$q$ cohomology with $E_T\otimes H^q(N)$ and preserve the same vanishing
   interval. On any stratum and local-model cover of [sk-def-sfb-constructible], tensor the scalar
   finite presentation matrix with $E$. It is still a finite matrix with entries in the scalar
   ring $E$, so it is exactly a finite constant local model over $E_T$. Restrictions commute with
   coefficient extension by [det-prop-scalar-six-pullback](1). In particular both $C$ and the
   extension of $M$ in step 3 are in their finite-constant-model $\Dbc$ categories. This proves
   the required image claim for every $E$-generator.
5. For each finite $F/E$, choose an $E$-basis of $F$. By [sk-prop-sfb-cartesian-coefficients](2),
   it gives $F_T\simeq E_T^{\oplus r}$, compatibly for $T=U,X$ by part (1). By
   [lem-sfb-subfield-flat], extension to $F$ is exact. After restriction to $E$, $F_T\otimes C$ is
   consequently $C^{\oplus r}$. The additive triangulated functor $Rj_*$
   [lem-pc-right-derived-functor-triangulated] sends this to $(Rj_*C)^{\oplus r}$. Thus
   $F_X\otimes^{\mathbf L}_{E_X}Rj_*C\simeq Rj_*(F_U\otimes^{\mathbf L}_{E_U}C)$. This finite-sum
   map is $F$-linear: multiplication by any $b\in F$ is its basis matrix over $E$, and the
   $E$-linear derived module direct image [sk-def-sfb-module-derived-pushpull] sends that matrix
   to the same matrix. A change of basis or inclusion $F\hookrightarrow F'$ is also an $E$-linear
   matrix, so the comparisons commute with both. Exact scalar restriction and its derived
   direct-image comparison [lem-weil-pbc-ring-sheaf-change-adjunction] give the asserted
   comparisons in the coefficient categories. This is only the finite-sum calculation, not a use
   of a general direct-image constructibility theorem.
6. By [sk-prop-sfb-qlbar-colimit-x], $\overline{\mathbf Q}_{\ell,T}=\varinjlim_{F\supset E}F_T$.
   Use the small filtered poset of finite subextensions of the fixed algebraic closure. The
   tensor-colimit and tensor-transitivity assertions of
   [lem-weil-pbc-condensed-flat-coefficient-calculus] identify the scalar extension of $C$ with
   $\varinjlim_{F\supset E}(F_U\otimes_{E_U}C)$ ; [det-prop-scalar-six-pullback](3) further
   identifies it with $\overline{\mathbf Q}_{\ell,U}\otimes^{\mathbf L}_{\mathcal O_{E,U}}L$. All
   finite stages have the same cohomological lower bound as $C$, by [lem-sfb-subfield-flat].
   Choose bounded-below representatives using these exact tensor functors. Apply
   [lem-weil-pbc-condensed-qcqs-pushforward-continuity] in the fixed $E_U$-module category and use
   the compatible comparisons of step 5. It gives $$Rj_*(\overline{\mathbf
   Q}_{\ell,U}\otimes^{\mathbf L}_{E_U}C)\simeq\overline{\mathbf Q}_{\ell,X}\otimes^{\mathbf
   L}_{E_X}Rj_*C.$$ The comparison is linear for each finite $F$ and hence for their sheaf
   colimit. As in step 3, [lem-weil-pbc-ring-sheaf-change-adjunction] transfers the
   fixed-coefficient calculation to the $\overline{\mathbf Q}_\ell$ direct image and reflects the
   isomorphism.
7. In step 6, $Rj_*C$ has the finite constant local models proved in step 4. Extension from $E_X$
   to $\overline{\mathbf Q}_{\ell,X}$ is flat by [lem-sfb-qlbar-flat]. By
   [lem-sfb-extend-scalars-preserves-homology], it preserves cohomology and the same finite
   vanishing interval. On a stratum and local-model cover, its cohomology is presented by the same
   scalar finite matrix, now with entries mapped from $E$ to $\overline{\mathbf Q}_\ell$.
   Restrictions commute with this extension by [det-prop-scalar-six-pullback](1). This is a finite
   constant local model as defined by [sk-def-sfb-constructible], so the output lies in
   $\Dbc(X,\overline{\mathbf Q}_\ell)$. Together with tensor transitivity in step 6, this proves
   the image claim for every algebraic-closure generator of step 2.
8. Return to the finite construction of $K$ in step 2. The functor $Rj_*$ commutes with shifts and
   distinguished triangles by [lem-pc-right-derived-functor-triangulated]. The target
   finite-constant-model category contains zero, is invariant under isomorphism and shifts, and is
   closed under taking the third vertex of a triangle by
   [det-cor-coefficient-heart-ii-triangulated], applied on the Noetherian $X$. Induct on the
   finite list of shifts and cones constructing $K$. The generator case was proved in step 4 for
   $E$ and in step 7 for $\overline{\mathbf Q}_\ell$; the shift and cone cases follow from the two
   cited statements. Therefore $Rj_*K\in\Dbc(X,\Lambda)$ for either coefficient choice.
-/
theorem constantModelBoundedConstructible_rational_open_direct_image
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) U)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) U K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) j).rightDerivedFunctor).obj
          K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) U K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) j).rightDerivedFunctor).obj
          K)) := by
  sorry

end AlgebraicGeometry.ProEtale
