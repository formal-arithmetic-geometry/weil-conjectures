/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.SixFunctors.EtaleOpenTensor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ScalarTensorPullbackNormalization
import WeilConjectures.AlgebraicGeometry.RingedComparisonTensorAdjunction

/-! # Unbounded étale compact support and restriction of scalars

Source: Stacks Project, more-etale.tex, Tag 0GL6, first square and its proper/open
construction, with the scalar-unit and projection normalizations specified by the DAG
(blueprint: lem-sf-etale-compact-scalar-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Restriction of arbitrary coefficient rings commutes with the fixed unbounded
compact-support functor, with its specified scalar unit and actual projection map.

Source: Stacks Project, Tag 0GL6, first square; sites-cohomology.tex,
Tags 0D6D, 0D6E, 07A4, 07A6 and 07A7; sites-modules.tex, Tag 0E8I
(blueprint: lem-sf-etale-compact-scalar-restriction).

The first equation fixes the proper/open paste: after composing with the canonical
geometric restriction mate v, d is Rp_* of the exact open restriction comparison.
The latter is the degreewise identity before module sheafification. The unbounded
restriction-adjunct lemma identifies v with the K-injective composition comparison.
The map c⁰ is the existing ExceptionalCoefficients.compactSupportMap, whose proper
part is scalarMate (the prescribed counit transpose) and whose open part is openIso
(the balancing isomorphism). The last equality transports both endpoints through
scalarTensorIso. Its right side expands the proper projection followed by the
open tensor comparison; coefficient pullback is identified by the fixed unit maps.

Proof:
1. Write $G_R=Rp_{*,R}$, $G_B=Rp_{*,B}$. Restriction $U_T$ is exact by the scalar-adjunction node.
Before sheafification, the two open-extension presheaves $j_{p!,R}U_XH$ and $U_Zj_{p!,B}H$ have
identical underlying abelian presheaves: they are $H(V)$ on objects factoring through $X$ and zero
otherwise, with the same restriction maps. The module-sheafification lemma says that their
underlying abelian sheafification is the same and that the extended constant-ring action is
unique. Thus the identity gives a natural isomorphism
$\alpha:j_{!,R}U_X\xrightarrow{\sim}U_Zj_{!,B}$, on morphisms as well as objects. Exactness of
$j_!$ and $U$ lets this same termwise isomorphism descend to the unbounded localizations. This
argument uses the presheaf before sheafification; it does not assert that extension by zero has
zero sections on every etale object not contained in the open. Uses:
lem-pur-sheaf-ring-derived-coefficient-adjunction, def-weil-pbc-extension-by-zero,
lem-cbc-sieve-module-sheafification, lem-weil-pbc-extension-by-zero-exact.

2. Apply the unbounded restriction-adjunct lemma to $p$ and $R\to B$. Its comparison
$v:U_YG_B\xrightarrow{\sim}G_RU_Z$ is invertible and is precisely the specified K-injective
comparison of the two ringed-topos factorizations. For $H\in D(X_{\mathrm{et}},B)$ set
$$d_H=v_{j_{!,B}H}^{-1}\circ G_R(\alpha_H).$$ Both factors are natural isomorphisms. By the
definition $L_C=G_Cj_{!,C}$ this has source $L_RU_XH$, target $U_YL_BH$, and exactly the
proper/open normalization required in the statement. In particular nothing here requires $U_Z$ to
preserve K-injective complexes. Uses: lem-sf-etale-unbounded-restriction-adjunct,
def-amb-etale-compact-support.

3. For the proper constituent, put $F_C=p_C^{-1}$ and $\lambda:F_BE_Y\xrightarrow{\sim}E_ZF_R$.
Apply the ringed comparison/adjunction lemma to the two paths from $(Z,B)$ to $(Y,R)$,
respectively through $(Z,R)$ and through $(Y,B)$. Their left composites are $E_ZF_R$ and $F_BE_Y$;
their right composites are $G_RU_Z$ and $U_YG_B$. Its canonical $\theta$ is $\lambda$: on a K-flat
complex $P$ with flat terms both derived pullbacks are computed termwise, the derived pullback
composition is the underived one, and the ringed commutation isomorphism is the identity of topoi,
so $\theta$ satisfies the representative normalization $c_{f,\mathsf
Q_AP};S_Z(g_{A,P});r=Lf_B^*(r_P);g_{B,F_WP};\mathsf Q_B(a_P)$ of the scalar/pullback isomorphism,
whose witness is unique by its definition. Its canonical $c$ is $v^{-1}$, since both are built
from the same two direct-image composition isomorphisms of the composition node. Thus the two
composite Hom bijections agree under these comparisons. For $J\in D(Z_{\mathrm{et}},R)$, transpose
$G_R(u_{Z,J}):G_RJ\to G_RU_ZE_ZJ$ first under $F_R\dashv G_R$: the result is
$u_{Z,J}\circ\varepsilon_{p,R,J}$. Its scalar transpose is $E_Z(\varepsilon_{p,R,J})$, since the
scalar counit composed with $E_Z(u_{Z,J})$ is the identity. The compared geometric transpose on
the other path is therefore precisely $b_J$, as defined in the item. Transposing back under
$E_Y\dashv U_Y$ gives the equality $$U_Y(b_J)\circ u_{Y,G_RJ}=v_{E_ZJ}^{-1}\circ G_R(u_{Z,J}).$$
This uses the normalized composite adjunction, not merely uniqueness of an unspecified right
adjoint. Uses: lem-sfb-ringed-comparison-tensor-adjunction, def-weil-pbc-composite-adjunction,
lem-pur-sheaf-ring-derived-coefficient-adjunction, def-pur-etale-scalar-pullback-iso.

4. Choose a flat-term K-flat representative $P$ of $K$. The etale open-tensor lemma says $j_!P$ is
again K-flat with flat terms and supplies the canonical balancing isomorphism $q:E_Zj_{!,R}\cong
j_{!,B}E_X$. Compute scalar extension on these representatives. The scalar-adjunction unit is the
chain map $x\mapsto x\otimes1$. Before sheafification on the open the equation
$U_Z(q_K)u_{Z,j_{!,R}K}=\alpha_{E_XK}j_{!,R}(u_{X,K})$ sends $x$ on either side to $x\otimes1$;
away from the open it is the unique map from zero. Sheafification and localization therefore give
this equality of actual derived morphisms. Under $U_TE_TC\cong C\otimes_R^{\mathbf L}B_T$, the
same representative comparison gives $$\alpha_{E_XK}^{-1}\circ U_Z(q_K)=\delta_{K,B_Z},$$ where
$\delta:(j_{!,R}K)\otimes_R^{\mathbf L}B_Z\xrightarrow{\sim}j_{!,R}(K\otimes_R^{\mathbf L}B_X)$ is
the canonical open tensor comparison. Indeed both maps on the sheafified total tensor of $j_!P$
and $B_Z[0]$ send the same pure tensor to the same pure tensor; this is an equality of chain maps
before localization, rather than a test of derived morphisms on stalks. Uses:
lem-pc-kflat-resolution, lem-coef-etale-open-tensor,
lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-pur-derived-change-of-rings,
def-kun-derived-tensor, lem-pur-etale-open-derived-tensor.

5. Set $J=j_{!,R}K$ and $H=j_{!,B}E_XK$. Using the definition $c^0_K=G_B(q_K)b_J$, the proper
equation of step 3, and naturality of $v$ for $q_K:E_ZJ\to H$, compute
$$U_Y(c^0_K)u_{Y,L_RK}=v_H^{-1}G_R(U_Z(q_K)u_{Z,J})
=v_H^{-1}G_R(\alpha_{E_XK})L_R(u_{X,K})=d_{E_XK}L_R(u_{X,K}).$$
The middle equality is the open-unit chain-map equality of step 4, and the last is the definition
in step 2. This proves the requested scalar-unit equation with its prescribed $d$ and $c^0$.

6. We identify the proper map itself, before pasting the open part. Use $a:F_RU_Y\cong U_ZF_B$
from the unbounded restriction-adjunct lemma. By its exact Hom equation the $F_R\dashv G_R$
transpose of $v_{E_ZJ}U_Y(b_J)$ is $$U_Z(E_Z(\varepsilon_{p,R,J})\circ\lambda_{G_RJ})\circ
a_{E_YG_RJ}.$$ The comparison $a$ of the restriction-adjunct lemma is the comparison $a$ named in
the normalization lemma: both are the identity on the underlying inverse-image abelian sheaves
with the scalar actions transported along $p^{-1}R_Y=R_Z$, $p^{-1}B_Y=B_Z$ (the conjugate of the
sectionwise identity $p_*U_Z=U_Yp_*$ is this identity, since the constant-ring module inverse
image is the abelian one), applied termwise to the exact functors. Take a flat-term K-flat
representative of $G_RJ$. The scalar/pullback normalization lemma applies to $\lambda$ because it
is the representative-normalized canonical scalar/pullback isomorphism: its defining
computation-counit equation is the one in scalarPullbackIso. Consequently, after
$U_TE_T=(-\otimes_R^{\mathbf L}B_T)$, the displayed transpose is
$$(\varepsilon_{p,R,J}\otimes1_{B_Z})\circ\mu_{G_RJ,B_Y},$$ with $p_R^{-1}B_Y=B_Z$ and $\mu$ the
canonical inverse-image tensor comparison. Naturality of the scalar/tensor identification moves
$U_ZE_Z(\varepsilon)$ to $\varepsilon\otimes1$. The projection-map definition says this is exactly
the transpose of $\mathrm{PF}_p(J,B_Y)$. Injectivity of the geometric Hom bijection therefore
gives $$v_{E_ZJ}\circ U_Y(b_J)=\mathrm{PF}_p(J,B_Y).$$ All cited normalization statements here are
unbounded; the bounded-below etale scalar-mate lemma is not being applied. Uses:
lem-sf-etale-unbounded-restriction-adjunct, lem-pc-kflat-resolution,
def-pur-etale-scalar-pullback-iso, lem-pur-scalar-tensor-pullback-normalization,
def-kun-projection-formula-map.

7. Keep $J,H$ from step 5. Inverting the definition of $d$ and using naturality of $v$ for $q_K$,
then steps 4 and 6, gives $$\begin{aligned} d_{E_XK}^{-1}U_Y(c^0_K)
&=G_R(\alpha_{E_XK}^{-1})v_HU_YG_B(q_K)U_Y(b_J)\\
&=G_R(\alpha_{E_XK}^{-1}U_Z(q_K))v_{E_ZJ}U_Y(b_J)\\
&=G_R(\delta_{K,B_Z})\circ\mathrm{PF}_p(j_{!,R}K,B_Y) =\pi_{K,B_Y}. \end{aligned}$$ The last
expression is precisely the compactification projection map specified in the item: proper counit
projection followed by $Rp_{*,R}$ of open tensor comparison. This is equality of natural derived
morphisms, and asserts no invertibility of either scalar extension or projection. All
constructions used exact restriction, flat-term K-flat resolutions and unbounded K-injective
derived composition, so no extra hypothesis on $R\to B$ or $K$ has entered. Uses:
def-amb-etale-compact-support, def-kun-projection-formula-map.
-/
theorem etaleCompactScalarRestriction
    {R B : Type (u + 1)} [CommRing R] [CommRing B] (φ : R →+* B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ d : Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ,
      (∀ H : DerivedCategoryModule B X,
        d.hom.app H ≫ (scalarRestrictionDirectImageMap φ c.g).app
            (D((c.i)_!open[ModuleCat.{u + 1} B]).obj H) =
          R((c.g)_*[ModuleCat.{u + 1} R]).map
            ((derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ c.i).hom.app H)) ∧
      ∀ K : DerivedCategoryModule R X,
        (Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K) ≫
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
            (ExceptionalCoefficients.compactSupportMap φ c K) =
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map
            ((Adjunction.ofIsRightAdjoint
              (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app K) ≫
            d.hom.app ((scalarExtension φ X).obj K) ∧
        (scalarTensorIso φ Y).inv.app
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K) ≫
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
            (ExceptionalCoefficients.compactSupportMap φ c K) ≫
          d.inv.app ((scalarExtension φ X).obj K) ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map
            ((scalarTensorIso φ X).hom.app K) =
          ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) c.g).app
              (D((c.i)_!open[ModuleCat.{u + 1} R]).obj K)).app (scalarCoefficient φ Y) ≫
            R((c.g)_*[ModuleCat.{u + 1} R]).map
              (((derivedTensor (ModuleCat.{u + 1} R) c.Z).obj
                  (D((c.i)_!open[ModuleCat.{u + 1} R]).obj K)).map
                  (scalarCoefficientPullbackIso φ c.g).hom ≫
                ((derivedOpenImmersionLowerShriekProjectionIso
                    (ModuleCat.{u + 1} R) c.i).inv.app K).app (scalarCoefficient φ c.Z) ≫
                D((c.i)_!open[ModuleCat.{u + 1} R]).map
                  (((derivedTensor (ModuleCat.{u + 1} R) X).obj K).map
                    (scalarCoefficientPullbackIso φ c.i).hom)) := by
  sorry

end AlgebraicGeometry.Etale
