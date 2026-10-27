module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.IntegralAmbientOperationModels
public import Sheaf.Paper.IntegralStrictReductionModel
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.CategoryTheory.ExactDerivedAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Mathlib.CategoryTheory.Localization.Predicate

/-! # Closed direct image and simultaneous strict reduction

Source: the integral closed-counit reduction obligation extracted from the localization
proof, sec-smooth-purity/sk-prop-sf-localization; Stacks Tag 09BM supplies exactness.
(blueprint: lem-sf-closed-direct-image-strict-reduction).

Strict systems are the published module sheaves on the ringed sequence site, rather
than sequences in a derived category. The comparison is normalized on one flat-term
K-flat resolution at each end by its actual sheafified pure-tensor map. All exponents
are positive: the Lean index n means exponent n+1. Scheme and coefficient universes
are independent. The records below only specify the maps belonging to this statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ClosedStrictReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Additivity of the actual sectionwise system image, inherited from its right adjoint.
Source: Stacks 03D2, 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
instance systemAdditive {X Z : Scheme.{t}} (i : Z ⟶ X) :
    (integralComparisonSequenceDirectImage.{t, u} l E i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exactness certificates needed to localize the two specified ordinary images.
These are conclusions of the closed-immersion theorem, not extra hypotheses.
Source: Stacks 09BM, applied levelwise
(blueprint: lem-sf-closed-direct-image-strict-reduction). -/
class ExactImages {X Z : Scheme.{t}} (i : Z ⟶ X) : Prop where
  pushLimits : PreservesFiniteLimits (IntegralAmbient.push.{t, u} l E i)
  pushColimits : PreservesFiniteColimits (IntegralAmbient.push.{t, u} l E i)
  systemLimits : PreservesFiniteLimits (integralComparisonSequenceDirectImage.{t, u} l E i)
  systemColimits : PreservesFiniteColimits (integralComparisonSequenceDirectImage.{t, u} l E i)

attribute [instance] ExactImages.pushLimits ExactImages.pushColimits
  ExactImages.systemLimits ExactImages.systemColimits

/-- Exact diagonal into strict completed-coefficient towers.
Source: Stacks 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
abbrev diagonal (W : Scheme.{t}) : scalarReductionSource.{t, u} l E W ⥤
    (ℕᵒᵖ ⥤ scalarReductionSource.{t, u} l E W) := Functor.const ℕᵒᵖ

/-- The quotient augmentation is specified before evaluation, by the universal
strict reduction counit and the actual ordinary quotient augmentation.
Source: extracted localization obligation, augmentation clause; Stacks 06YY, 0941
(blueprint: lem-sf-closed-direct-image-strict-reduction). -/
def IsAugmentationNormalized (W : Scheme.{t})
    (S : IntegralStrictReductionModel.{t, u} l E W)
    (a : (diagonal l E W).mapDerivedCategory ⟶
      S.reduction ⋙ coefficientSequenceDerivedRestriction.{t, u} l E W) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource.{t, u} l E W) ℤ)
    (_hP : integralOperationsGoodComplex.{t, u} l E W P),
    a.app (DerivedCategory.Q.obj P) ≫
        (coefficientSequenceDerivedRestriction.{t, u} l E W).map (S.counit.app P) ≫
        (coefficientSequenceRestriction.{t, u} l E W).mapDerivedCategoryFactors.hom.app
          ((S.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
      (diagonal l E W).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex S.augmentation (.up ℤ)).app P)

variable {X Z : Scheme.{t}} (i : Z ⟶ X) [ExactImages l E i]

/-- Termwise direct image on the strict completed-coefficient towers.
Source: Stacks 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
abbrev towerImage : (ℕᵒᵖ ⥤ scalarReductionSource.{t, u} l E Z) ⥤
    (ℕᵒᵖ ⥤ scalarReductionSource.{t, u} l E X) :=
  StrictReduction.termwise (IntegralAmbient.push.{t, u} l E i)

/-- Termwise direct image is additive, using the existing whiskering construction.
Source: Stacks 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
instance towerImageAdditive : (towerImage l E i).Additive :=
  inferInstanceAs (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (IntegralAmbient.push.{t, u} l E i)).Additive)

/-- Additivity of completed-coefficient direct image, inherited from the adjunction.
Source: Stacks 03D2 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
instance pushAdditive : (IntegralAmbient.push.{t, u} l E i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exactness of termwise direct image on completed-module towers.
Source: Stacks 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
instance towerImageLimits : PreservesFiniteLimits (towerImage l E i) :=
  StrictReduction.termwise_limits (IntegralAmbient.push.{t, u} l E i)

/-- Exactness of termwise direct image on completed-module towers.
Source: Stacks 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
instance towerImageColimits : PreservesFiniteColimits (towerImage l E i) :=
  StrictReduction.termwise_colimits (IntegralAmbient.push.{t, u} l E i)

/-- The exact localization of the scalar-restriction square, with both canonical
localization factors. Its input is normalized to the identity on every section.
Source: Stacks 0D6E (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
def derivedRestriction
    (e : integralComparisonSequenceDirectImage.{t, u} l E i ⋙
        coefficientSequenceRestriction.{t, u} l E X ≅
      coefficientSequenceRestriction.{t, u} l E Z ⋙ towerImage l E i) :
    (integralComparisonSequenceDirectImage.{t, u} l E i).mapDerivedCategory ⋙
        coefficientSequenceDerivedRestriction.{t, u} l E X ≅
      coefficientSequenceDerivedRestriction.{t, u} l E Z ⋙ (towerImage l E i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (integralComparisonSequenceDirectImage.{t, u} l E i)
    (coefficientSequenceRestriction.{t, u} l E X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
      Functor.mapDerivedCategoryCompIso
        (coefficientSequenceRestriction.{t, u} l E Z) (towerImage l E i)

/-- Additivity of direct image followed by the exact constant diagram.
Source: Stacks 0941 (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
instance pushDiagonalAdditive :
    (IntegralAmbient.push.{t, u} l E i ⋙ diagonal l E X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The canonical constant-tower square with explicit scheme and coefficient sizes.
Source: Stacks 06YY (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
def constantSquareDerived :
    (diagonal l E Z).mapDerivedCategory ⋙ (towerImage l E i).mapDerivedCategory ≅
      (IntegralAmbient.push.{t, u} l E i).mapDerivedCategory ⋙
        (diagonal l E X).mapDerivedCategory :=
  letI : (IntegralAmbient.push.{t, u} l E i ⋙ diagonal l E X).Additive :=
    pushDiagonalAdditive l E i
  letI : PreservesFiniteLimits (IntegralAmbient.push.{t, u} l E i ⋙ diagonal l E X) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (IntegralAmbient.push.{t, u} l E i ⋙ diagonal l E X) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (diagonal l E Z) (towerImage l E i)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := diagonal l E Z ⋙ towerImage l E i)
      (G := IntegralAmbient.push.{t, u} l E i ⋙ diagonal l E X)
      (StrictReduction.constantSquare (IntegralAmbient.push.{t, u} l E i)) ≪≫
      Functor.mapDerivedCategoryCompIso (IntegralAmbient.push.{t, u} l E i) (diagonal l E X)

/-- Complete normalization of the strict comparison on arbitrary resolving presentations.
The section equation is the underived closed projection formula, including its finite
coefficient action. Its localization equation specifies the actual system morphism.
Source: the extracted localization obligation, comparison and evaluation clauses;
Stacks 03EL, 09BM (blueprint: lem-sf-closed-direct-image-strict-reduction). -/
def IsProjectionNormalized
    (SX : IntegralStrictReductionModel.{t, u} l E X)
    (SZ : IntegralStrictReductionModel.{t, u} l E Z)
    (r : (IntegralAmbient.push.{t, u} l E i).mapDerivedCategory ⋙ SX.reduction ≅
      SZ.reduction ⋙ (integralComparisonSequenceDirectImage.{t, u} l E i).mapDerivedCategory) :
    Prop :=
  ∀ (P : CochainComplex (scalarReductionSource.{t, u} l E Z) ℤ)
    (Q : CochainComplex (scalarReductionSource.{t, u} l E X) ℤ)
    (f : Q ⟶ ((IntegralAmbient.push.{t, u} l E i).mapHomologicalComplex (.up ℤ)).obj P)
    (_hf : QuasiIso f)
    (_hP : integralOperationsGoodComplex.{t, u} l E Z P)
    (_hQ : integralOperationsGoodComplex.{t, u} l E X Q),
    ∃ c : (SX.ordinary.mapHomologicalComplex (.up ℤ)).obj Q ⟶
        ((integralComparisonSequenceDirectImage.{t, u} l E i).mapHomologicalComplex
          (.up ℤ)).obj ((SZ.ordinary.mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (n : ℕ) (d : ℤ) (V : X.ProEt)
        (b : (integralCoefficientCommRingSheaf.{t, u} l E X n).obj.obj (op V))
        (x : (Q.X d).val.obj (op V)),
        HEq ((c.f d).val.app (op (n, V))
          (((SX.level n).inv.app (Q.X d)).val.app (op V)
            (unrestrictedIntegralTensorSection.{t, u} l E X n (Q.X d) (op V) b x)))
          (((SZ.level n).inv.app (P.X d)).val.app
            (op ((Scheme.proEtaleBaseChange i).obj V))
            (unrestrictedIntegralTensorSection.{t, u} l E Z n (P.X d)
              (op ((Scheme.proEtaleBaseChange i).obj V))
              ((Scheme.coefficientProEtaleDirectRingMap i
                (CommRingCat.of (ULift.{t + 1}
                  (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op V) b)
              ((f.f d).val.app (op V) x)))) ∧
      SX.reduction.map (DerivedCategory.Q.map f ≫
          (IntegralAmbient.push.{t, u} l E i).mapDerivedCategoryFactors.inv.app P) ≫
          r.hom.app (DerivedCategory.Q.obj P) ≫
          (integralComparisonSequenceDirectImage.{t, u} l E i).mapDerivedCategory.map
            (SZ.counit.app P) ≫
          (integralComparisonSequenceDirectImage.{t, u} l E i).mapDerivedCategoryFactors.hom.app
            ((SZ.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
        SX.counit.app Q ≫ DerivedCategory.Q.map c

/-- One natural isomorphism in actual derived systems, with its scalar-restriction
and quotient-augmentation equations in actual derived completed-module towers.
Source: the integral closed-counit reduction obligation in the localization proof
(blueprint: lem-sf-closed-direct-image-strict-reduction). -/
structure Comparison (SX : IntegralStrictReductionModel.{t, u} l E X)
    (SZ : IntegralStrictReductionModel.{t, u} l E Z) where
  restriction : integralComparisonSequenceDirectImage.{t, u} l E i ⋙
      coefficientSequenceRestriction.{t, u} l E X ≅
    coefficientSequenceRestriction.{t, u} l E Z ⋙ towerImage l E i
  restriction_sections : ∀ (M : coefficientSequenceModules.{t, u} l E Z) (n : ℕ)
    (V : X.ProEtᵒᵖ)
    (x : (((integralComparisonSequenceDirectImage.{t, u} l E i ⋙
      coefficientSequenceRestriction.{t, u} l E X).obj M).obj (op n)).val.obj V),
    HEq (((restriction.hom.app M).app (op n)).val.app V x) x
  r : (IntegralAmbient.push.{t, u} l E i).mapDerivedCategory ⋙ SX.reduction ≅
    SZ.reduction ⋙ (integralComparisonSequenceDirectImage.{t, u} l E i).mapDerivedCategory
  projection : IsProjectionNormalized l E i SX SZ r
  aX : (diagonal l E X).mapDerivedCategory ⟶
    SX.reduction ⋙ coefficientSequenceDerivedRestriction.{t, u} l E X
  aZ : (diagonal l E Z).mapDerivedCategory ⟶
    SZ.reduction ⋙ coefficientSequenceDerivedRestriction.{t, u} l E Z
  aX_normalized : IsAugmentationNormalized l E X SX aX
  aZ_normalized : IsAugmentationNormalized l E Z SZ aZ
  augmentation : ∀ P : DerivedCategory (scalarReductionSource.{t, u} l E Z),
    aX.app ((IntegralAmbient.push.{t, u} l E i).mapDerivedCategory.obj P) ≫
        (coefficientSequenceDerivedRestriction.{t, u} l E X).map (r.hom.app P) ≫
        (derivedRestriction l E i restriction).hom.app (SZ.reduction.obj P) =
      (constantSquareDerived l E i).inv.app P ≫
        (towerImage l E i).mapDerivedCategory.map (aZ.app P)

omit [ExactImages l E i] in
/-- Closed direct image commutes with simultaneous strict derived reduction.

Source: Integral-stage closed counit reduction: agent-extracted simultaneous comparison
obligation. Exactness input: Stacks Tag 09BM, proetale.tex,
lemma-closed-immersion-complement-retrocompact-exact; the tag does not itself assert the
strict-system projection comparison.
(blueprint: lem-sf-closed-direct-image-strict-reduction).

Proof plan (the eight steps of the DAG node):
1. Identify $i^{-1}B_X=B_Z$ and $i^{-1}(A_n)_X=(A_n)_Z$ by the canonical coefficient comparisons;
these identifications commute with every projection and quotient map. Write $p=i^{-1}$ and $q=i_*$
over these coefficients. The closed and open inverse images are exact, $q$ is exact, and the
closed counit $pq\to1$ is invertible: the ringed closed-kernel adjoint statement, for an arbitrary
commutative ring sheaf and a quasi-compact open complement, says that the ordinary termwise closed
counit gives $i^*i_*\cong1$. Apply the specified exact derived adjunction to obtain $p\dashv q$ on
unbounded derived categories, with the localized original unit $\eta$ and counit $\varepsilon$.
Apply the same ordinary constructions levelwise to strict systems: the adjunction equations hold
levelwise, since inverse image, direct image, unit and counit are natural for the semilinear
transitions. Exactness is levelwise, so this gives exact termwise functors on systems and their
derived categories. No assertion about commuting a nonexact right derived functor with evaluation
is required.
Uses: lem-weil-pbc-profinite-coefficient-inverse-image,
lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-pbc-proetale-ringed-open-closed,
def-weil-exact-derived-adjunction, lem-sf-exact-functor-derived-triangulated,
lem-pur-coefficient-system-derived-comparison, lem-sf-ringed-closed-kernel-adjoint.

2. For a flat-term K-flat complex $Q$ of $B_X$-modules, put $T_X(Q)_n=Q\otimes_{B_X}(A_n)_X$.
There is a natural cochain map
$$u_{Q,n}:Q\otimes(A_n)_X\xrightarrow{\eta}q
p(Q\otimes(A_n)_X)\xrightarrow{q\sigma}q(pQ\otimes(A_n)_Z).$$
Here $\sigma$ is the ordinary inverse-image tensor isomorphism followed by the canonical
coefficient identification. The degree-$a$ section formula on a local pure tensor is $x\otimes
b\mapsto\eta_Q(x)\otimes i^{-1}b$, interpreted as a section of the direct image; it follows from
the unit's tensor normalization. This balanced bilinear formula respects restriction and hence
sheafification. Naturality in $Q$ shows commutation with the differential, which is $d_Q\otimes1$,
and with chain maps. A chain homotopy $h$ is carried to $h\otimes1$, so the maps are defined on
the homotopy category as well.
Uses: def-weil-proetale-inverse-image, lem-pur-proetale-inverse-image-tensor-comparison,
lem-weil-pbc-profinite-coefficient-inverse-image, def-pur-sheaf-tensor-product.

3. The maps of Step 2 form one strict-system map $u_Q:T_X(Q)\to qT_Z(pQ)$. Indeed, for $m\ge n$,
both paths around its transition square send $x\otimes b$ to $\eta_Q(x)\otimes q_{m,n}(i^{-1}b)$;
the other expression is $\eta_Q(x)\otimes i^{-1}(q_{m,n}b)$ and these agree by the coefficient
comparison. Equality on local pure tensors implies equality after sheafification. Before
forgetting the level coefficient action the map is $(A_n)_X$-linear, since multiplication by $a$
sends either expression to $\eta_Q(x)\otimes i^{-1}(ab)$. After restriction to $B_X$, the two
paths from $\Delta_XQ$ to $qT_Z(pQ)$ agree: both send $x$ to $\eta_Q(x)\otimes1$. Here the paths
use respectively the quotient augmentation of $T_X(Q)$ and the unit followed by $q$ of the
quotient augmentation of $T_Z(pQ)$. These are equations of maps of strict complexes, not just
evaluated derived equations.
Uses: lem-weil-pbc-profinite-coefficient-inverse-image, def-weil-integral-reduction-tower.

4. Descend this construction through the full homotopy subcategory $\mathcal P_{B_X}$ of flat-term
K-flat complexes. It localizes to $D(B_X)$ by the resolving-subcategory equivalence. For
$Q\in\mathcal P_{B_X}$, $pQ$ is flat-term K-flat by the ringed-topos pullback theorem. For any
quasi-isomorphism between such $Q$'s, tensor with each $(A_n)_X$ preserves that quasi-isomorphism;
the same holds after $p$ and after exact $q$. Thus both system-valued functors in $u_Q$ invert
those quasi-isomorphisms, since system cohomology is levelwise. The localization universal
property descends the natural transformation, giving
$$u_M:\mathcal R_X(M)\longrightarrow I\mathcal R_Z(pM)\quad(M\in D(B_X)).$$
The factorization isomorphisms are the K-flat computations specified in the statement: this
identifies the descended functors with the specified $\mathcal R_X$ and $I\mathcal R_Zp$. The same
universal property descends the augmentation square of Step 3 to the derived category of strict
$B_X$-module towers; scalar forgetting and the constant diagram are exact levelwise. Uniqueness
gives independence of resolutions and naturality on all derived morphisms.
Uses: lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-pur-derived-change-of-rings, lem-pur-coefficient-system-derived-comparison,
lem-weil-pbc-localization-universal-property.

5. For $P\in D(B_Z)$ define
$$r_P=I\mathcal R_Z(\varepsilon_P)\circ u_{qP}:\mathcal R_X(qP)\longrightarrow I\mathcal R_Z(P).$$
This is already a natural transformation with target the derived category of actual strict
systems. Its evaluation is the canonical derived closed projection comparison: before deriving,
for a sheaf $N$ on $Z$, the composite of Step 2 with $q(\varepsilon_N\otimes1)$ sends $s\otimes a$
to $s\otimes i^{-1}a$. Equivalently its $p\dashv q$-transpose is $(\varepsilon_N\otimes1)\sigma$,
precisely the characterization of the ordinary closed projection map. These identities are natural
in complexes and descend by Step 4, so evaluation gives the derived comparison for the specified
change-of-rings functors, including its $(A_n)_X$-module structure.
Uses: def-weil-exact-derived-adjunction, lem-weil-pbc-proetale-closed-underived-projection,
lem-pur-derived-change-of-rings, lem-weil-pbc-localization-universal-property.

6. Fix $n$ and view $e_nr_P$ as a morphism of $(A_n)_X$-module derived objects. Its closed
restriction is an isomorphism: derived inverse image commutes with derived tensor, and
$pqP\xrightarrow{\varepsilon_P}P$ is invertible, being the localization of the termwise closed
counit, which is invertible by the ringed closed-kernel adjoint statement; the triangle identity
identifies the restricted map with the resulting tensor identification. Its open restriction is an
isomorphism between zero objects. Indeed $j^{-1}qP=0$, and the derived tensor pullback formula
gives $j^{-1}(qP\otimes^L_{B_X}(A_n)_X)=0$; the target is a closed direct image and also restricts
to zero. Exact inverse images commute with cohomology. Hence the cohomology sheaves of the cone of
$e_nr_P$ have zero open and closed restrictions. Open/closed zero detection, applied with ring
$(A_n)_X$, makes every one of these sheaves zero. Thus the cone is acyclic and $e_nr_P$ is
invertible. This uses neither a Tor bound on $P$ nor flatness of $(A_n)_X$.
Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-pbc-proetale-ringed-open-closed,
def-weil-exact-derived-adjunction, lem-exc-open-closed-detection,
lem-sf-ringed-closed-kernel-adjoint.

7. Let $C$ be the cone of $r_P$ in the derived category of systems. Exact evaluation gives
$H^a(e_nC)=0$ for all $a,n$ by Step 6. Since kernels, cokernels and exactness in the strict-system
category are levelwise, each system $H^a(C)$ has every component zero and is zero. Consequently
$C=0$ and $r_P$ is an isomorphism of actual derived systems. Its transition compatibility is
already part of its construction as a system map; this argument uses evaluation only to test
invertibility.
Uses: lem-pur-coefficient-system-derived-comparison.

8. Write $a_T:\Delta_T\to\operatorname{Res}\mathcal R_T$ for the quotient augmentation. The
descended equation of Step 3 is $u_M a_X(M)=q a_Z(pM)\,\Delta_X\eta_M$. With $M=qP$, compose it
with $q\operatorname{Res}\mathcal R_Z(\varepsilon_P)$. Naturality of $a_Z$ changes the result to
$q a_Z(P)\,\Delta_X(q\varepsilon_P\circ\eta_{qP})=q a_Z(P)$, by the adjunction triangle identity.
Therefore
$$\operatorname{Res}(r_P)\,a_X(qP)=q a_Z(P),$$
under the canonical equality $\Delta_XqP=q\Delta_ZP$. The equation was obtained from
strict-complex equations by faithful localization precomposition, so is an equation of
transformations into the derived category of strict $B_X$-towers. Together with Steps 3 and 5 this
proves every transition, evaluation and augmentation clause of the statement.
Uses: def-weil-integral-reduction-tower, def-weil-exact-derived-adjunction,
lem-weil-pbc-localization-universal-property.
-/
theorem closed_direct_image_strict_reduction [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (SX : IntegralStrictReductionModel.{t, u} l E X)
    (SZ : IntegralStrictReductionModel.{t, u} l E Z) :
    ∃ (_h : ExactImages l E i), Nonempty (Comparison l E i SX SZ) := by
  sorry

end ClosedStrictReduction
end WeilConjectures
