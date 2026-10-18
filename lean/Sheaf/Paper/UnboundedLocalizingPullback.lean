/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Inverse image on localizing categories

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-proper-base-change-unbounded/sk-prop-proper-base-change-unbounded-pullback.md
(blueprint: det-proper-base-change-unbounded-pullback).

The restriction uses the ordinary unbounded derived module-object categories and the
constant-scalar-model definition of constructibility. No derived completion is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical shift-commutation of the total derived inverse image `Lg^*`: the one of the
termwise functor `D(g^*)` (Mathlib's `Functor.mapDerivedCategory`), transported along the
canonical isomorphism `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`. Exactness of
`Lg^*` is asserted for this shift structure, not for an arbitrary one.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: det-proper-base-change-unbounded-pullback). -/
@[instance_reducible]
def unboundedLocalizingPullbackCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) :
    (CondensedRing.upperStar Λ g).leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm ℤ

attribute [local instance] unboundedLocalizingPullbackCommShift

set_option maxHeartbeats 800000 in
-- Elaborating inherited full-subcategory shift structures needs a larger heartbeat budget.
/-- The clauses of inverse-image preservation, including its restriction along the full
inclusions. `Lg^*` carries its canonical shift-commutation
`unboundedLocalizingPullbackCommShift`; the restriction is Mathlib's `ObjectProperty.lift` of
`Lg^*` along the full inclusions, with its inherited shift-commutation, and the triangulations
on the restricted categories are the inherited ones.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: det-proper-base-change-unbounded-pullback). -/
structure UnboundedLocalizingPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) : Prop where
  exact : (CondensedRing.upperStar Λ g).leftDerivedFunctor.IsTriangulated
  sums : ∀ I : Type (u + 2),
    PreservesColimitsOfShape (Discrete I) (CondensedRing.upperStar Λ g).leftDerivedFunctor
  constructible : ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    (constantModelBoundedConstructible Λ Y K ∧ DerivedCategory.finiteTorAmplitude _ K) →
    constantModelBoundedConstructible Λ Y'
        ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K)
  localizing : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
    localizingClosureProEtale Λ Y'
      (((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor).obj K)
  [sourceTriangulated : (localizingClosureProEtale Λ Y).IsTriangulated]
  [targetTriangulated : (localizingClosureProEtale Λ Y').IsTriangulated]
  restrictionExact : ((localizingClosureProEtale Λ Y').lift
    ((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
    localizing).IsTriangulated
  restrictionSums : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
    ((localizingClosureProEtale Λ Y').lift
      ((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
      localizing)

set_option maxHeartbeats 800000 in
-- Elaborating all six coefficient instances needs the same heartbeat budget.
/-- Exact inverse image preserves small sums, bounded constructible finite-Tor objects,
and their localizing closure, for each of the six admissible coefficient types.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: det-proper-base-change-unbounded-pullback).

Proof (the five steps of the node):

1. *Exactness and sums.* By [sk-prop-sfb-cartesian-coefficients], the coefficient map
   $g^{-1}\Lambda_Y\to\Lambda_{Y'}$ is invertible and the module inverse image is exact. Apply
   [lem-weil-pbc-exact-functor-derived-factorization] to this exact functor: its termwise
   functor descends to a triangulated functor on the unbounded derived categories. For any
   K-flat resolution $P\to K$, exactness makes the termwise map $g^*P\to g^*K$ a quasi-
   isomorphism. The resolution computation in [sk-def-sfb-derived-categories] therefore
   identifies this descended functor with the total derived pullback $Lg^*$ of [sk-def-sfb-
   module-derived-pushpull]. The latter node supplies $Lg^*\dashv Rg_*$, so [lem-weil-pbc-left-
   adjoint-preserves-colimits] gives preservation of every existing small coproduct. Such
   coproducts exist here: module objects over the commutative coefficient ring are ordinary
   sheaves of modules, hence form a Grothendieck abelian category by [lem-pur-ringed-site-
   grothendieck-abelian]; [lem-kun-grothendieck-derived-coproducts] supplies the small derived
   coproducts, including the empty one. The small sites are taken in the fixed universe of [sk-
   def-localizing-closure].

2. *Bounded constructibility, every admissible $\Lambda$.* Both schemes are quasi-compact and
   quasi-separated: finite type of their structure maps means that they are quasi-compact [def-
   weil-finite-type-morphism], since the base $\operatorname{Spec}k$ is affine; quasi-
   separatedness follows from separatedness because the diagonal is a closed immersion, hence
   proper and quasi-compact [def-weil-proper-morphism; lem-weil-pbc-proper-fp-permanence]. Let
   $K\in\Dctf(Y,\Lambda)$, so $K$ is bounded with cohomology in some $[c,d]$ and every $H^i(K)$
   is constructible in the sense of [sk-def-sfb-constructible] (finite constant local models on
   the strata of a finite constructible stratification). By step 1, $Lg^*K$ is represented by
   the termwise inverse image $g^*K$, and since the module inverse image is exact [sk-prop-sfb-
   cartesian-coefficients], $H^i(g^*K)\cong g^*H^i(K)$ for every $i$. Hence $H^i(Lg^*K)=0$
   outside $[c,d]$, and each $g^*H^i(K)$ is constructible by [lem-sfb-pullback-constant-model-
   constructible], applied to the qcqs schemes $Y,Y'$. Thus $Lg^*K$ is bounded with
   constructible cohomology in the sense of [sk-def-sfb-constructible].

3. *Finite coefficients: Tor amplitude.* Let $A$ be finite and killed by a power of $\ell$, and
   $K\in\Dctf(Y,A)$. By step 2, $Lg^*K$ is bounded with constructible cohomology. Choose $a\le
   b$ bounding the Tor amplitude of $K$ [sk-def-sfb-constructible]. We realize the source's
   flat-model argument by the general bounded-flat-model construction, valid over the stated
   field $k$. On the ringed site $(Y_{\mathrm{pro\acute et}},A_Y)$, [lem-pur-ringed-site-
   grothendieck-abelian] and [lem-pc-sheaf-modules-tensor-closed] give an additive symmetric
   closed monoidal Grothendieck category of modules. The functorial bounded-above flat
   replacements of [lem-pc-kflat-bounded-flat-replacement], applied to $M[0]$ with upper bound
   zero, give a functor $F$ with flat values and a natural epimorphism $F(M)\to M$. Set $M_0=M$
   and $M_{r+1}=\ker(F(M_r)\to M_r)$ for $r\ge0$. The differential $F(M_{r+1})\to F(M_r)$ is the
   composite through $M_{r+1}\hookrightarrow F(M_r)$; the resulting augmented complex is exact,
   and naturality and functoriality of kernels give functorial flat resolutions. Thus all
   hypotheses of [lem-sc-source-tor-amplitude-flat-model] hold, and it gives $K\cong Q(P)$ with
   flat $P^i$ and $P^i=0$ outside $[a,b]$. By [lem-pc-bounded-above-flat-kflat-site], $P$ is
   K-flat. The morphism of pro-étale topoi [def-weil-proetale-inverse-image], together with the
   coefficient isomorphism of [sk-prop-sfb-cartesian-coefficients], is a morphism of ringed
   topoi, so [lem-weil-pbc-ringed-topos-kflat-pullback] says that $g^*P$ is K-flat with flat
   terms. Exactness from step 1 makes $Q(g^*P)$ represent $Lg^*K$, and its terms still vanish
   outside $[a,b]$. The reverse implication of the flat-model criterion [lem-sc-source-tor-
   amplitude-flat-model] is not needed: directly, K-flat derived tensor is computed by tensoring
   a K-flat argument [sk-def-sfb-derived-tensor-hom]. For any $A_{Y'}$-module sheaf $N$,
   $Lg^*K\otimes^{\mathbf L}N[0]$ is represented by the ordinary complex with terms
   $g^*P^i\otimes N$. These terms vanish outside $[a,b]$, so its cohomology vanishes there. This
   tests every sheaf $N$ on $Y'$, and proves finite Tor amplitude. Together with step 2 it
   proves $Lg^*K\in\Dctf(Y',A)$.

4. *Integral and field coefficients.* For $\Lambda=\mathbf Z_\ell,\mathcal O_E,\mathbf
   Q_\ell,E,\overline{\mathbf Q}_\ell$, [det-def-localizing-closure-ctf-equals-bc] identifies
   $\Dctf(T,\Lambda)$ with $\Dbc(T,\Lambda)$ for the qcqs schemes $T=Y,Y'$ of step 2, both in
   the constant-local-model sense of [sk-def-sfb-constructible]. For
   $K\in\Dctf(Y,\Lambda)=\Dbc(Y,\Lambda)$, step 2 gives
   $Lg^*K\in\Dbc(Y',\Lambda)=\Dctf(Y',\Lambda)$. Pullback here is the ambient, uncompleted
   inverse image of step 1.

5. *Localizing closures.* Apply [det-proper-image-localizing-principle] with $\mathcal
   T=D(Y_{\mathrm{pro\acute et}},\Lambda)$, $\mathcal T'=D(Y'_{\mathrm{pro\acute et}},\Lambda)$,
   $F=Lg^*$, $\mathcal G=\Dctf(Y,\Lambda)$ and $\mathcal G'=\Dctf(Y',\Lambda)$. Step 1 supplies
   exactness, small sums in both ambient categories, and their preservation; steps 2–4 supply
   $F(\mathcal G)\subseteq\mathcal G'\subseteq\Loc(\mathcal G')$. The cited statement therefore
   gives the asserted image of $\Loc(\mathcal G)$ and the exact, sum-preserving restriction.
-/
theorem unboundedLocalizingPullback
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    {Y' Y : Scheme.{u}} [Y'.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (g : Y' ⟶ Y) [g.IsOver (Spec (.of k))] :
    (∀ (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A],
      (∃ n : ℕ, (l ^ n : A) = 0) →
        Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj A) g)) ∧
    Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj ℤ_[l]) g) ∧
    Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj ℚ_[l]) g) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (UnboundedLocalizingPullback (Profinite.padicIntegersRingObj l E) g) ∧
      Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj E) g)) ∧
    Nonempty (UnboundedLocalizingPullback (Profinite.padicAlgClRingObj l) g) := by
  sorry

end AlgebraicGeometry.ProEtale
