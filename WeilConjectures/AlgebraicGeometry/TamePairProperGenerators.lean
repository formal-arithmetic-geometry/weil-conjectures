/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.StrictLocalKummerTameModule
public import WeilConjectures.AlgebraicGeometry.NormContinuousMonodromyData
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.SixFunctors.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionCoherence
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CondensedSupportDerivedLocalization
import WeilConjectures.AlgebraicGeometry.ScalarModelImmersionExtension
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.LisseLatticePotentialKummerTameness
import WeilConjectures.AlgebraicGeometry.NestedOpenRegularAlteration
import WeilConjectures.AlgebraicGeometry.ProperBaseChangeRational
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf

/-!
# Proper tame-pair generators with finite norm-topology coefficients

Source: the agent-stated finite-E generation input motivated by ILO IX, Theorem 1.1,
and XIII, 2.2.2. The precise generation assertion is not quoted as an ILO theorem.
(blueprint: lem-sfb-tame-pair-proper-generators).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The objects Rq_*((b_! L)[0]) from the proper tame pairs in the node. The equivalence
`components` enumerates the actual irreducible components of the reduced SNC boundary;
`outer` selects precisely those removed to form V. The square expresses V = Y times_X U.
All three schemes and all maps are over the same field. Empty boundaries, empty outer
subsets and rank zero are allowed. Isomorphism closure avoids choosing representatives.
Source: agent-stated input motivated by ILO IX, Theorem 1.1, and XIII, 2.2.2
(blueprint: lem-sfb-tame-pair-proper-generators). -/
def properTamePairGenerators (p : ℕ) (k E : Type u) [Field k] [NormedField E]
    (X U : Over (Spec (.of k))) (j : U ⟶ X) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (normContinuousRing E).X U.left))) :=
  fun G ↦ ∃ (Y V W : Over (Spec (.of k)))
    (_ : LocallyOfFiniteType Y.hom) (_ : QuasiCompact Y.hom) (_ : IsSeparated Y.hom)
    (_ : LocallyOfFiniteType V.hom) (_ : QuasiCompact V.hom) (_ : IsSeparated V.hom)
    (_ : LocallyOfFiniteType W.hom) (_ : QuasiCompact W.hom) (_ : IsSeparated W.hom)
    (π : Y ⟶ X) (_ : IsProper π.left)
    (v : V ⟶ Y) (_ : IsOpenImmersion v.left) (_ : QuasiCompact v.left)
    (q : V ⟶ U) (_ : IsProper q.left)
    (b : W ⟶ V) (_ : IsOpenImmersion b.left) (_ : QuasiCompact b.left),
    IsPullback v.left q.left π.left j.left ∧ IsRegularScheme Y.left ∧
    ∃ D : Y.left.IdealSheafData, IsStrictNormalCrossingsBoundary D ∧
      ∃ (n : ℕ)
        (components : Fin n ≃ {Z : Set (D.support : Set Y.left) //
          Z ∈ irreducibleComponents (D.support : Set Y.left)})
        (outer : Finset (Fin n)),
        Set.range v.left = (⋃ a ∈ outer, Subtype.val '' (components a).val)ᶜ ∧
        Set.range (b.left ≫ v.left) = (D.support : Set Y.left)ᶜ ∧
        ∃ L : Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
            (condensedRingObj (normContinuousRing E).X W.left),
          IsLisseCoefficientModule (normContinuousRing E).X L ∧
          IsStrictLocalKummerTameModule p (normContinuousRing E).X D (b.left ≫ v.left) L ∧
          Nonempty (G ≅
            (CondensedRing.moduleObjectDerivedPushforward (normContinuousRing E).X q.left).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.openImmersionLowerShriek (normContinuousRing E).X b.left).obj L)))

/-- Every bounded finite-constant-model constructible complex over E is in the finite
thick envelope of the stated proper tame-pair generators. Here E is literally a finite
intermediate subfield of the normed algebraic closure, with its induced norm topology.
Mathlib's triangEnvelope uses finitely many shifts, binary sums, extensions and retracts;
no infinite coproduct or totalization, and no scalar extension, occurs in the conclusion.
Source: agent-stated input motivated by ILO IX, Theorem 1.1, and XIII, 2.2.2
(blueprint: lem-sfb-tame-pair-proper-generators).

Proof (the eight steps recorded in the DAG):
1. Let $\mathcal H\subset D(U,A_E)$ be the full thick subcategory generated by the stated proper
tame-pair objects. By det-lem-integral-models-generators(1), it suffices to put $(a_!M_0)[1/\ell]$
in $\mathcal H$ for every locally closed $a:S\hookrightarrow U$ and lisse integral lattice $M_0$.
The extension/scalar formula det-lem-integral-models-operations(4) identifies this object with
$a_!M$, $M=M_0[1/\ell]$. The functor $a_!$ here has the exact, factorization-independent meaning
of lem-sfb-locally-closed-extension-coherence; thus the same notation may be used after
subdividing a stratum. Throughout, def-weil-pbc-internal-abelian-sheaf-module-equivalence
identifies internal modules with the sectionwise modules over the same ring sheaf, preserving
underlying sheaves and actions. Apply this exact equivalence and its inverse termwise to transport
the cited sheaf-module localization and composition statements to the internal module-derived
categories.

2. We prove, by Noetherian induction on closed subsets $Z\subseteq U$, that every bounded
constructible complex on $U$ with zero restriction to $U\setminus Z$ belongs to $\mathcal H$. This
induction is valid by lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. The empty support
gives zero by the closed support identification in lem-sfb-condensed-support-derived-localization.
In the inductive step all proper closed subsets of $Z$ are assumed, for every bounded
constructible complex supported on them, rather than only for sheaves. Realize $Z$ as its reduced
induced closed subscheme; localization identifies a supported complex with the exact closed direct
image of its restriction to $Z$. Restrictions preserve its finite scalar local models simply by
pulling back their covers and stratifications. Closed extension preserves these models by
lem-sfb-scalar-model-immersion-extension. Apply step 1 on $Z$ and then this exact closed
extension. We are reduced to $a_!M$ with the closure of $S$ contained in $Z$; if that closure is
proper the induction hypothesis already applies.

3. We may reduce these strata to integral ones. There are finitely many irreducible components by
lem-weil-pbc-noetherian-finitely-many-components. The complement of the pairwise intersections is
a disjoint union of dense opens of those components. Replace each such open by its reduction: its
map to the original open is a universal homeomorphism, so lem-trf-proetale-topological-invariance
and the Cartesian coefficient isomorphisms identify their module categories, lattices, and exact
extensions. The open/closed short exact sequence of lem-weil-pbc-proetale-ringed-open-closed, and
its triangle from lem-sf-derived-ses-triangle, separate these finitely many pieces from the
remaining proper closed subset. Apply the inductive hypothesis to the latter. Thus it remains to
treat an integral $S$ whose reduced closure $T$ in $X$ meets $U$ in an integral closed subscheme
$T^\circ=T\cap U$, with $S$ dense open in $T^\circ$. Its inclusion in $U$ is still $a$. All
assertions are about reduced closed structures, so no regularity of $X$, $T$, or $S$ has been
assumed.

4. Apply lem-sfb-lisse-lattice-potential-kummer-tameness to $M_0$ on this connected $S$, obtaining
$c:H\to S$. Apply lem-sfb-nested-open-regular-alteration to $S\subseteq T^\circ\subseteq T$ and
$c$. Write $h:Y\to T$, $W=h^{-1}S$, $V=h^{-1}T^\circ$, $r:W\to S$, and $S_0\subset S$ for its
data. Compose $h$ with the closed immersion $T\hookrightarrow X$ to obtain $p:Y\to X$. A closed
immersion is proper, and proper maps compose; hence $p$ is proper and $p^{-1}U=V$. Its restriction
$q:V\to U$ is proper by base change. These statements use no separability of the generic
extension. The reduced boundary and the selected outer components are exactly those of the
geometric input.

5. Set $L=r^*M$ on $W$. Exact Cartesian pullback preserves the given finite free local
trivializations, so $L$ is lisse over $A_{E,W}$. Since $r$ factors through $H$,
lem-sfb-lisse-lattice-potential-kummer-tameness says that $L$ satisfies precisely the
parameter-root tameness condition of the item, for every parameter choice, including points with
no boundary. Thus $$G=Rq_*(b_!L)[0]$$ is one of the generators of $\mathcal H$. Moreover $b_!L$ is
bounded constructible by lem-sfb-scalar-model-immersion-extension, and $G$ is bounded
constructible by det-thm-sfb-proper-base-change-rational(2), used only for the finite field $E$.
These boundedness and constructibility assertions will be needed for the error terms of the
induction.

6. Put $r_0:W_0\to S_0$ as in the geometric input and $M'=M|_{S_0}$. Its factorization
$W_0\xrightarrow{u}T_0\xrightarrow{e}S_0$ has a finite universal homeomorphism followed by a
degree-$d$ finite etale surjection. The equivalence in lem-trf-proetale-topological-invariance
lifts to internal coefficient modules by sk-prop-sfb-cartesian-coefficients: apply the
quasi-inverse functors to the action and its axioms, using the coefficient identification.
Therefore $u_*$ is exact and its unit identifies $u_*u^*e^*M'$ with $e^*M'$. On each etale
splitting of $e$ supplied by lem-weil-pbc-finite-etale-etale-local-split, the unit into $e_*e^*M'$
is the diagonal into $d$ copies. The sum of the copies is invariant under permutation of the
sheets, hence glues on overlaps to an $A_{E,S_0}$-linear trace. The local product description also
shows $e_*$ exact. Thus $Rr_{0*}r_0^*M'=r_{0*}r_0^*M'$ in degree zero and the trace composed with
the unit is $d\,1_{M'}$. Multiplication by $1/d\in E$ gives a retraction. We divide by the
separable degree $d\geq1$, not by a possibly inseparable field trace.

7. The map $r:W\to S$ is proper. The map $W\hookrightarrow V$ followed by $V\to T^\circ$ is a
dense compactification of $W\xrightarrow{r}S\hookrightarrow T^\circ$. Apply
det-sf-comp-composition-interchange(3) to the bounded constructible input $L[0]$ (it has Tor
amplitude zero since it is locally free). Composing with exact closed direct image
$T^\circ\hookrightarrow U$ and the canonical derived direct-image composition comparison yields
$$G\simeq a_!Rr_*L.$$ Exactness, mixed-factorization independence, and composition of these
locally closed extensions are supplied by lem-sfb-locally-closed-extension-coherence. In
particular $G$ has zero restriction outside the closure of $S$ in $U$, which is $Z$. Open
restriction to $S_0$ is proper base change, clause (3) of det-thm-sfb-proper-base-change-rational.
Under it $G|_{S_0}\simeq Rr_{0*}r_0^*M'$. No assertion about an SNC boundary for $W_0$ was needed.

8. Let $v:S_0\hookrightarrow S$ be the open immersion and $z:B=S\setminus S_0\hookrightarrow S$
its reduced closed complement. Write $N=Rr_*L\in\Dbc(S,A_E)$, by proper rational finiteness. Apply
the open/closed triangle to $N$, and then exact $a_!$: $$ (av)_!v^*N\longrightarrow
G\longrightarrow a_!z_*z^*N\longrightarrow (av)_!v^*N[1].$$ This triangle comes by applying the
termwise exact open/closed sequence to a representative complex, using
det-sf-open-closed-sequence-ring-sheaf and lem-weil-pbc-complex-ses-triangle; exact a_! preserves
this triangle by lem-sf-exact-functor-derived-triangulated. Its third term is bounded
constructible, since exact restrictions preserve local scalar models and locally closed extension
preserves them. Its support is contained in the closure of $B$ in $U$, a proper closed subset of
$Z$: $S_0$ is nonempty open dense in integral $Z$, and $B\subset Z\setminus S_0$. The inductive
hypothesis puts that third term in $\mathcal H$. The middle term is its generator $G$, so closure
under cones and shifts puts $(av)_!v^*N$ in $\mathcal H$.

9. Apply exact $(av)_!$ to the unit and the $1/d$-normalized trace in step 6. With the open
restriction identification of step 7 this exhibits $(av)_!M'$ as a retract of $(av)_!v^*N$. Hence
$(av)_!M'\in\mathcal H$. Apply the same open/closed triangle on $S$ to $M[0]$, then $a_!$: $$
(av)_!M'\longrightarrow a_!M\longrightarrow a_!z_*z^*M\longrightarrow (av)_!M'[1].$$ The last
nonshifted term is bounded constructible and supported on the same proper closed subset of $Z$, so
belongs to $\mathcal H$ by induction. The first term belongs by the explicit retract. Thus
$a_!M\in\mathcal H$. This completes the inductive step and then step 1 gives every
$C\in\Dbc(U,A_E)$. Each induction call removes a proper closed support, valid by the stated
Noetherian induction principle; each branch uses finitely many lattice generators and cones. The
resulting expression therefore uses finitely many generators, shifts, sums, cones and retracts,
and never an infinite totalization or scalar extension beyond $E$.
-/
theorem boundedConstructible_mem_properTamePairGenerators_triangEnvelope
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (X U : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (normContinuousRing E).X U.left)))
    (_hC : constantModelBoundedConstructible (normContinuousRing E).X U.left C) :
    (properTamePairGenerators p k E X U j).triangEnvelope C := by
  sorry

end AlgebraicGeometry.ProEtale
