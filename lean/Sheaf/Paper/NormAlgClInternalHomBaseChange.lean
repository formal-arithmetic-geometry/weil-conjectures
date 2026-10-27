/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.SectionModuleOperationsData
public import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.CategoryTheory.DerivedTensorRightExact
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Paper.AdicConstructibilityPredicateComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.ClosedSupportedScalarComparison
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.Paper.ContinuousQbarConstructibleGenerators
import Sheaf.Paper.ContinuousAlgClConstructibleTor
import Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.RingedProjectionFirstShift
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.ContinuousAlgClProperFiniteness
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Sheaf.Analysis.NormedSpace.CountableUltrametricBasis
import Sheaf.Paper.ConstructibleNormedGeometricFibres
import Sheaf.LinearAlgebra.CountableEndomorphismModuleReconstruction
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.Paper.RationalOpenDirectImageConstructible
import Sheaf.Paper.TameBoundaryScalarComparison
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.Paper.RationalClosedSupportConstructible
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom

/-!
# Norm-algebraic-closure scalar extension and constructible internal Hom

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), agent coefficient-topology obligation
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change).

The reassociation is specified by its balanced generators, its signed total-complex
summands, and its derived counit square on K-flat representatives. The comparison is
then the evaluation transpose. Existence of this normalized presentation is included
in the assertion, rather than assumed as additional input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

attribute [instance] Profinite.continuousMapRingObjOfUniverseMonObj
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
  Profinite.isMonHom_continuousMapRingObjMapOfUniverse

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.derivedCochainCounit CategoryTheory.derivedCochainComparisonFactors

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (X : Scheme.{u})
  {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [MonObj Γ] [IsCommMonObj Λ] [IsCommMonObj Γ]
  (a : Λ ⟶ Γ) [IsMonHom a]

/-- The existing internal module category, abbreviated only for the normalization below.
Source: direct-image proof (3), D(Mod) convention
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
abbrev normHomModules (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)

/-- The ordinary coequalizer scalar extension, with the pulled-back coefficient map.
Source: direct-image proof (3), S_B convention
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
abbrev normHomScalar : normHomModules X Λ ⥤ normHomModules X Γ :=
  Mod.extendScalars (coefficientMap a X)

/-- Its ordinary unbounded total left derived functor, without a flatness assumption.
Source: direct-image proof (3), S_B convention
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
def normHomDerivedScalar :
    DerivedCategory (normHomModules X Λ) ⥤ DerivedCategory (normHomModules X Γ) :=
  (normHomScalar X a).leftDerivedFunctor

/-- Its universal counit on actual cochain complexes, including quotient comparisons.
Source: direct-image proof (3), K-flat balanced-tensor reassociation
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
def normHomScalarCounit (P : CochainComplex (normHomModules X Λ) ℤ) :
    (normHomDerivedScalar X a).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj P) :=
  (derivedCochainCounit (normHomScalar X a) (normHomDerivedScalar X a)
    (normHomScalar X a).leftDerivedFunctorCounit).app P

attribute [local irreducible] normHomScalarCounit

/-- The type of natural scalar tensor reassociations for the existing derived tensors.
Source: direct-image proof (3), K-flat balanced reassociation
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
def NormHomScalarReassociation :=
  (Functor.uncurry.obj (derivedTensor Λ X)) ⋙
      normHomDerivedScalar X a ≅
    ((normHomDerivedScalar X a).prod (normHomDerivedScalar X a)) ⋙
      (Functor.uncurry.obj (derivedTensor Γ X))

/-- The specified reassociation on balanced generators, signed total-complex summands,
and K-flat derived representatives. The ordinary and total comparisons are existentially
packaged; their displayed equations fix them and the supplied derived comparison.
Source: direct-image proof (3), specified K-flat scalar reassociation
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
def NormHomScalarNormalized (d : NormHomScalarReassociation X a) : Prop :=
  ∃ ordinary : (Functor.uncurry.obj (curriedTensor (normHomModules X Λ))) ⋙ normHomScalar X a ≅
    ((normHomScalar X a).prod (normHomScalar X a)) ⋙
      (Functor.uncurry.obj (curriedTensor (normHomModules X Γ))),
    (∀ (M N : normHomModules X Λ) (V : X.ProEtᵒᵖ)
      (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((ordinary.hom.app (M, N)).hom.hom.app V)
        (((Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app (M ⊗ N)).hom.hom.app V
          (ModuleRingedComparison.internalPureTensor Λ X M N V x y)) =
      ModuleRingedComparison.internalPureTensor Γ X
        ((normHomScalar X a).obj M) ((normHomScalar X a).obj N) V
        (((Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app M).hom.hom.app V x)
        (((Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app N).hom.hom.app V y)) ∧
  ∃ total : ∀ P Q : CochainComplex (normHomModules X Λ) ℤ,
    ((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor (normHomModules X Λ))) ≅
      CochainComplex.mapBifunctor
        (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj P)
        (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor (normHomModules X Γ)),
    (∀ (P Q : CochainComplex (normHomModules X Λ) ℤ)
      (p q n : ℤ) (h : p + q = n),
    (normHomScalar X a).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫
          (total P Q).hom.f n =
      (ordinary.hom.app (P.X p, Q.X q)) ≫
        CochainComplex.ιMapBifunctor
          (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj P)
          (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj Q)
          (curriedTensor _) p q n h) ∧
    ∀ (P Q : CochainComplex (normHomModules X Λ) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    (normHomDerivedScalar X a).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        normHomScalarCounit X a
          (CochainComplex.mapBifunctor P Q (curriedTensor (normHomModules X Λ))) ≫
        DerivedCategory.Q.map (total P Q).hom =
      d.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (normHomScalarCounit X a P ⊗ₘ normHomScalarCounit X a Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj P)
          (((normHomScalar X a).mapHomologicalComplex (.up ℤ)).obj Q)

/-- The prescribed comparison is the transpose of reassociation followed by evaluation.
Mathlib uses left evaluation. Symmetry of the balanced reassociation identifies this
with the displayed right evaluation; no isomorphism of internal Hom objects is chosen.
Source: direct-image proof (3), displayed phi_B and its specified transpose
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
def normHomComparison (d : NormHomScalarReassociation X a)
    (K N : DerivedCategory (normHomModules X Λ)) :
    (normHomDerivedScalar X a).obj (((derivedHom Λ X).obj (op K)).obj N) ⟶
      ((derivedHom Γ X).obj (op ((normHomDerivedScalar X a).obj K))).obj
        ((normHomDerivedScalar X a).obj N) :=
  ((derivedTensorHomAdjunction Γ ((normHomDerivedScalar X a).obj K)).homEquiv _ _)
    (d.inv.app (K, ((derivedHom Λ X).obj (op K)).obj N) ≫
      (normHomDerivedScalar X a).map ((derivedTensorHomAdjunction Λ K).counit.app N))

/-- The two variance naturality equation for the actual evaluation transpose.
Source: direct-image proof (3), naturality in K and N
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
def NormHomComparisonNatural (d : NormHomScalarReassociation X a) : Prop :=
  ∀ (K K' N N' : DerivedCategory (normHomModules X Λ)) (f : K' ⟶ K) (g : N ⟶ N'),
    (normHomDerivedScalar X a).map
        (((derivedHom Λ X).map f.op).app N ≫ ((derivedHom Λ X).obj (op K')).map g) ≫
      normHomComparison X a d K' N' =
    normHomComparison X a d K N ≫
      ((derivedHom Γ X).map ((normHomDerivedScalar X a).map f).op).app
        ((normHomDerivedScalar X a).obj N) ≫
      ((derivedHom Γ X).obj (op ((normHomDerivedScalar X a).obj K'))).map
        ((normHomDerivedScalar X a).map g)

/-- Inclusion E into Omega on all-continuous condensed coefficients.
Source: direct-image proof (3), A to B_X
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change). -/
abbrev normAlgClHomCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) :=
  Profinite.continuousMapRingObjMapOfUniverse.{u, u}
    (T := E) (T' := Ω) E.val.toRingHom continuous_subtype_val

/-- Norm-algebraic-closure extension preserves constructible derived internal Hom,
for the evaluation-defined comparison, naturally in both variables.
The existential presentation supplies the specified reassociation, with no new hypothesis.
Source: direct-image proof (3), agent local derived internal-Hom obligation
(blueprint: lem-sfb-norm-algcl-internal-hom-base-change).

Proof plan, following all nineteen DAG steps:
1. Work in section-ring module sheaves: [lem-pd-module-ringed-topos-derived-comparison] identifies
internal relative derived tensors, geometric functors, and their actual adjunctions, while
[lem-sfb-internal-section-scalar-adjunction] identifies scalar extension and its unit. The closed
internal Homs agree by the defining right adjunction. Write $T_Y=B_Y\otimes^L_{A_{E,Y}}-$,
$H_R(-,-)=R\mathcal Hom_R(-,-)$, and $\phi_{Y;P,M}:T_YH_A(P,M)\to H_B(T_YP,T_YM)$ for the
evaluation transpose. This defines a natural map for arbitrary objects, without asserting its
invertibility. The field $k$ is Noetherian (its only ideals are $0,k$), so $X$ is Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. Its open subschemes are Noetherian and quasi-compact
by [lem-weil-pbc-noetherian-open-subscheme-noetherian]; its closed subschemes are Noetherian
because descending chains of closed subsets stabilize and affine quotient rings inherit the
ascending-chain condition on ideals. All supports below thus have quasi-compact open complements.
For finite $E$ only, [lem-sfb-adic-constructibility-predicate-comparison] identifies the finite
constant local model convention with the bounded-constructible predicate used by the finite-$E$
preservation and generation nodes below; it is never applied to $B$.
2. For any complementary closed/open pair on such a scheme, scalar extension commutes with open
extension by zero by [def-sfb-derived-open-immersion-shriek-iso], and commutes with both inverse
images by [lem-sfb-kflat-scalar-comparison-normalization]. It also commutes with exact closed
direct image through the normalized $B$-linear map $\delta$ of
[lem-sfb-closed-supported-scalar-comparison]. To check the latter's hypotheses,
[lem-weil-pbc-condensed-open-closed-recollement] gives exact sheaf functors and the degree-zero
sequence $0\to j_!j^*M\to M\to i_*i^*M\to0$, while [lem-weil-pbc-proetale-ringed-open-closed]
explicitly gives the invertible open unit and closed counit and both zero mixed restrictions.
Therefore [lem-sfb-exact-open-closed-unbounded-calculus] applies to both rings. In particular
these comparisons are valid even when a scalar extension is unbounded. Their units and counits
retain their stated normalizations; no coefficient-flatness assertion was used.
3. Derived scalar extension takes every bounded constructible finite-$E$ complex on a standing
scheme $Y$ to a bounded constructible $B_Y$-complex. Indeed
[det-cor-coefficient-heart-ii-generation] gives a finite cone-and-shift construction from
$a_!L[0]$ with $L$ finite-rank lisse. By [lem-sfb-locally-free-derived-scalars], $T_SL$ is locally
$B_S^r[0]$, including $r=0$. Step 2 identifies $T_Ya_!L$ with $a_!T_SL$. The latter objects
generate a triangulated category of bounded finite-constant-model constructible $B$-complexes by
[lem-sfb-continuous-qbar-constructible-generators]. Exactness of $T_Y$ carries the finite
construction into that category. For the representative used by
[det-sf-comp-continuous-algcl-constructible-tor], choose an algebraic-closure isomorphism
$\operatorname{PadicAlgCl}(\ell)\cong\Omega$ by [lem-pc-algebraic-closure-exists-unique]. It is
isometric on every finite subextension by [lem-weil-l-adic-extension-absolute-value], hence
everywhere. Postcomposition identifies their continuous-function rings. The exact module
equivalence carries the displayed finite local models to finite local models. Apply the Tor
theorem in its stated representative and transport the resulting finite-Tor constructible object
back by [lem-sfb-condensed-coefficient-iso-constructible]. Thus the actual $T_Y$ outputs have
finite Tor amplitude. This argument uses finite local models and the all-continuous $B$-generator
statement, not an equivalence between $C$ and $B$.
4. For any $f:Y\to V$ between standing schemes, define $\beta_{f,P}:T_VRf_{*,A}P\to Rf_{*,B}T_YP$
to be the adjunct of $f_B^*T_VRf_{*,A}P\cong T_Yf_A^*Rf_{*,A}P\xrightarrow{T_Y\varepsilon_A}T_YP$.
The pullback comparison is exactly the normalized K-flat comparison of
[lem-sfb-kflat-scalar-comparison-normalization]. Write $r$ for exact scalar restriction. By
[lem-weil-pbc-ring-sheaf-change-adjunction], $r_VRf_{*,B}\cong Rf_{*,A}r_Y$, preserving the
geometric adjunction. Under the scalar adjunction of
[lem-pur-sheaf-ring-derived-coefficient-adjunction], $\beta_{f,P}$ is therefore the adjunct of
$Rf_{*,A}(\eta_P)$, where $\eta_P:P\to r_YT_YP$ is $x\mapsto1\otimes x$ on a flat-term K-flat
resolution. To verify this normalization, transpose $Rf_*(\eta_P)$ along $f_A^*\dashv Rf_{*,A}$:
the result is $\eta_P\varepsilon_A$ by naturality of the counit. Its scalar adjunct is
$T_Y\varepsilon_A$, by the scalar triangle identity and pullback/scalar compatibility. Thus the
two prescribed adjuncts agree.
5. For fixed $f$, the two functors in $\beta_f$ are exact. We need the triangle compatibility only
after exact scalar restriction $r$, which reflects isomorphisms by
[lem-weil-pbc-ring-sheaf-change-adjunction]. The K-flat formula $x\otimes a\mapsto a\,g(x)$ of
[lem-pur-sheaf-ring-derived-coefficient-adjunction] and step 4 identify $r\beta_f$, with tensor
symmetry, with the projection map for $f_A$ and the fixed module $B_V$. The rings are pulled back,
so its source-coefficient factor is $f_A^*B_V=B_Y$. [lem-sfb-ringed-projection-first-shift] states
precisely that this projection is a transformation of exact functors in $P$, including the
connecting arrow. Consequently the locus where $r\beta_f$ is invertible, equivalently where
$\beta_f$ is invertible, is closed under shifts and distinguished-triangle extensions. No
faithfulness assertion for derived scalar restriction on morphisms is needed.
6. We prove $\beta_{f,P}$ invertible first for proper $f:Y\to V$ and bounded constructible $P$
over finite $E$. By clause (2) of [det-thm-sfb-proper-base-change-rational], $Rf_{*,A}P$ is
bounded constructible; step 3 makes $T_VRf_{*,A}P$ bounded constructible. Step 3 also makes $T_YP$
bounded constructible of finite Tor amplitude, so [det-sf-comp-continuous-algcl-finiteness] says
that each cohomology sheaf of $Rf_{*,B}T_YP$ has finite constant local models. At this point we
need no upper bound for that target. Step 3 already identified the PadicAlgCl coefficient
representative isometrically with $\Omega$ and transported its finite-Tor constructible input.
Under that exact coefficient equivalence the underlying geometric direct image and its cohomology
are unchanged. Hence this finiteness conclusion is about the actual $B$ of the item.
7. The increasing finite-field cover of [lem-sfb-algcl-countable-closed-finite-cover] implies that
$\Omega$ has at most countable algebraic dimension over $E$. Apply
[lem-sfb-countable-normed-orthogonal-basis] to the normed $E$-space $\Omega$ with prescribed
$b_0=1$. Let $D=\operatorname{End}^{\mathrm{cts}}_E(\Omega)$, let $\lambda_0$ be the first
coordinate, and set $e(v)=\lambda_0(v)1$. Each $d\in D$ gives an $A$-linear endomorphism of the
underlying $B$-module sheaf by postcomposition on continuous functions. Pullback, tensor with a
flat-term K-flat representative of $P$, and $Rf_{*,A}$ give a unital $D$-action on
$Rf_{*,A}r_YT_YP$. The idempotent $e$ splits the actual copy of $A$ off $rB$: its inclusion is
$E\hookrightarrow\Omega$, its retraction is $\lambda_0$, and their composite is $1_E$. These
induce split maps $P\xrightarrow{\eta_P}r_YT_YP\to P$ with composite $1_P$. Their other composite
is $e$, including on derived tensors. Thus after direct image and any exact additive fibre, the
$e$-summand is precisely the image of $Rf_{*,A}P$ under that fibre. Arbitrary $d$ need only be
$A$-linear; no $B$-linearity is asserted for them.
8. Fix a geometric point $y$ of $V$ and an integer $q$, and write $\Phi_{y,R}$ for the exact fibre
functor of [lem-sfb-constructible-normed-geometric-fibres]. Put
$H=H^q\Phi_{y,A}(Rf_{*,A}r_YT_YP)$. Step 4 and the fibre's scalar-restriction compatibility
identify this with the underlying $E$-space of $H^q\Phi_{y,B}(Rf_{*,B}T_YP)$. By step 6 that space
is finite-dimensional over $\Omega$, and hence at most countable-dimensional over $E$. Its
$\Omega$-action agrees with the subalgebra of $D$ consisting of multiplication maps: those maps
are $B$-linear, so the scalar-restriction/direct-image comparison is natural for them. Step 7
identifies $eH$ with $H^q\Phi_{y,A}(Rf_{*,A}P)$. All hypotheses of
[lem-sfb-countable-endomorphism-module-reconstruction] now hold, and it gives the isomorphism
$$\Omega\otimes_E H^q\Phi_{y,A}(Rf_{*,A}P)\xrightarrow{\sim}H,\qquad v\otimes
h\longmapsto\theta_vh.$$ Here $\theta_v(w)=\lambda_0(w)v=m_v e(w)$ since $b_0=1$. Thus the
displayed map is exactly multiplication by $v$ after the map on cohomology induced by
$Rf_{*,A}(\eta_P)$, not an arbitrary vector-space isomorphism.
9. The scalar/fibre comparison of [lem-sfb-constructible-normed-geometric-fibres] identifies the
degree-$q$ fibre of $T_VRf_{*,A}P$ with $\Omega\otimes_E H^q\Phi_{y,A}(Rf_{*,A}P)$; tensor over
the abstract field $E$ is exact. By the insertion-of-one normalization in step 4 its map under
$\beta_{f,P}$ is precisely the map in step 8. It is therefore invertible for every $y,q$. Outside
a finite interval the source cohomology vanishes, so every fibre of the target cohomology vanishes
there. Each target cohomology sheaf is constructible by step 6, and the degree-zero case of
constructible fibre conservativity makes those sheaves zero. The target is consequently bounded
constructible. Now both endpoints satisfy the bounded constructible conservativity assertion of
the same node, proving $\beta_{f,P}$ invertible. This used proper-image finiteness and the
algebraic reconstruction theorem, not any topology-equivalence, open-scalar, or $B$
proper-base-change assertion.
10. For a quasi-compact open immersion $j:U\hookrightarrow X$, let $\mathcal C_j$ be the bounded
constructible finite-$E$ objects $P$ for which the specified $\beta_{j,P}$ is invertible. Step 5
and [lem-sf-triangle-two-out-of-three], applied after the conservative exact scalar restriction,
make this class closed under shifts and cones. It contains zero and is closed under finite sums
and isomorphisms. It is closed under retracts as well: with $F=T_XRj_{*,A}$, $G=Rj_{*,B}T_U$, if
$P\xrightarrow{i}Q\xrightarrow{r}P$ has $ri=1$ and $\beta_Q$ is invertible, then
$F(r)\beta_Q^{-1}G(i)$ is the inverse of $\beta_P$. Multiplying on either side and using the two
naturality squares gives $G(r)G(i)=1$ and $F(r)F(i)=1$, respectively.
11. Apply [lem-sfb-tame-pair-proper-generators] to $j$. It suffices to consider $G=Rq_{*,A}K$ with
$p:Y\to X$ proper, $V=p^{-1}U$, $q:V\to U$ proper, $j':V\hookrightarrow Y$, and $K=b_!L[0]$ for
the stated regular strict-normal-crossings tame pair, including its inner extension by zero. The
finite-rank lisse $L$ has finite local $E$-models, so
[lem-sfb-coefficient-heart-lisse-extension-constructible] makes $K$ bounded constructible. The
finite-$E$ case of [lem-sfb-rational-open-direct-image-constructible] makes $Rj'_{*,A}K$ bounded
constructible. The independent proper comparison proved in steps 6--9 therefore applies to $(q,K)$
and $(p,Rj'_{*,A}K)$. The $B$-specific boundary input
[lem-sfb-continuous-algcl-tame-boundary-comparison] makes $\beta_{j',K}$ invertible: its
regularity, outer components, inner extension, and prime-to-$p$ Kummer-tameness hypotheses are
exactly the generator's data. No tameness hypothesis is imposed on the original $P$.
12. The equality $jq=pj'$ identifies $Rj_*Rq_*$ with $Rp_*Rj'_*$ in both coefficient categories by
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. The adjunction-compatible composition
and monoidal comparisons of [lem-sfb-ringed-derived-monoidal-comparisons], together with
[lem-weil-pbc-mate-pasting], identify the coefficient projections by the equality
$$Rj_{*,B}(\beta_{q,K})\circ\beta_{j,Rq_{*,A}K}=Rp_{*,B}(\beta_{j',K})\circ\beta_{p,Rj'_{*,A}K},$$
under those composition identifications. Indeed each side is the mate of the composed
inverse-image/scalar square, and that square is the same by the K-flat coherence in step 2. Every
factor on the right is invertible by step 11, as is $Rj_{*,B}(\beta_{q,K})$. Cancellation proves
$G\in\mathcal C_j$. The finite thick generation assertion and step 10 give invertibility of
$\beta_{j,P}$ for every bounded constructible finite-$E$ $P$. The map is the exact counit adjunct
from step 4 throughout.
13. For complementary $i:Z\hookrightarrow Y$ and $j:V\hookrightarrow Y$, and any $M\in D(A_Y)$,
define $\kappa_{i,M}:T_ZRi_A^!M\to Ri_B^!T_YM$ by its $i_{*,B}\dashv Ri_B^!$ adjunct
$$i_{*,B}T_ZRi_A^!M\xrightarrow{\delta_{i,Ri_A^!M}^{-1}}T_Yi_{*,A}Ri_A^!M
\xrightarrow{T_Y\varepsilon_{A,M}}T_YM.$$
The adjunction and support triangles exist on the unbounded category by
[det-lem-formal-closed-support-adjunction]; step 2 provides the invertible normalized $\delta$. In
particular the defining counit identity is $$\varepsilon_{B,T_YM}\circ
i_{*,B}(\kappa_{i,M})\circ\delta_{i,Ri_A^!M}=T_Y\varepsilon_{A,M}.$$ This defines a natural
transformation; invertibility has not been presumed.
14. Now take bounded constructible finite-$E$ $M$. Exact open inverse image preserves its finite
local models, so $j_A^*M$ is bounded constructible by
[lem-sfb-pullback-constant-model-constructible] and step 2. Compare $T_Y$ of the support triangle
of $M$ with the $B$-support triangle of $T_YM$. To construct the comparison, use
[lem-weil-pbc-ring-sheaf-change-adjunction] to identify scalar restriction of inverse/direct
images and their actual adjunction maps. The fibre formula $Ri^!M=i^*\operatorname{fib}(M\to
Rj_*j^*M)$ from [det-lem-formal-closed-support-adjunction] then identifies the restricted support
triangle. Apply the scalar unit to this triangle, then $T_Y$, then the scalar counit. This gives a
triangle morphism, including its connecting arrow. Its middle map is the identity by the scalar
triangle identity; its third map is $\beta_{j,j_A^*M}$ under $j_B^*T_Y\cong T_Vj_A^*$, since its
adjunct is $T_V$ of the open counit. Its first map is
$i_{*,B}\kappa_{i,M}\circ\delta_{i,Ri_A^!M}$: the support-counit square is exactly the identity in
step 13, which determines that adjunct. The third map is invertible by step 12. Hence
[lem-sf-triangle-morphism-iso] makes the first map invertible. Since $\delta$ is invertible and
exact $i_{*,B}$ reflects isomorphisms by its invertible closed counit in step 2, $\kappa_{i,M}$ is
invertible. This proves support change from the independent open argument, without a new
support-generator assertion.
15. First compute $\phi_{S;L,M}$ for a sheaf $L$ with a finite constant local $E$-model and
arbitrary $M\in D(A_{E,S})$. Each scalar model is a finite-dimensional vector space: a finite
generating list over a field can be reduced to a basis by deleting dependent vectors. On a
trivializing pro-étale cover, $L=A^r$ with finite $r$, including $r=0$. By
[lem-sfb-locally-free-derived-scalars], $T_SL=B^r[0]$. The internal Hom calculation
[lem-sc-finite-free-internal-hom-exact] is exact and equals the finite power functor, so its right
derived functor sends $M$ to $M^r$. The analogous calculation applies to $B^r$. The actual
comparison on each such slice is $T_S(M^r)\to(T_SM)^r$; its evaluation sends $(z\otimes
m_1,\ldots,z\otimes m_r)$ and a basis vector $e_s$ to $z\otimes m_s$. Derived scalar extension is
additive, so this map is invertible. Slice restriction commutes with internal Hom by
[lem-weil-pbc-ringed-internal-hom-exact-restriction] and with scalar extension by step 2. Joint
conservativity of cover restrictions [lem-zl-condensed-cover-restriction-conservative] proves the
asserted invertibility on $S$. No finite-type hypothesis is needed on the members of the
trivializing cover.
16. Let $N$ be bounded constructible over $E$ on $X$, and let $a=h\circ u:S\hookrightarrow
W\hookrightarrow X$, with $u$ open into the closure and $h$ closed, and $L$ lisse over $E$ on $S$.
Put $F=H_A(L,u^*Rh_A^!N)$. The support finiteness theorem
[lem-sfb-rational-closed-support-constructible] makes $Rh_A^!N$ bounded constructible on $W$.
Pullback preserves its finite constant local models by
[lem-sfb-pullback-constant-model-constructible], and is exact by
[lem-weil-pbc-condensed-open-closed-recollement]. The local finite-power formula of step 15 shows
that $F$ is bounded constructible: choose a common finite stratification for the finitely many
cohomology sheaves of $u^*Rh_A^!N$, then on a trivializing cover for $L$ each $H^q(F)$ is a finite
power of its finite local scalar model. Hence [lem-sfb-rational-open-direct-image-constructible]
makes $Ru_{*,A}F$ bounded constructible. This finiteness is needed only over $E$.
17. The two formulas of [lem-sfb-open-closed-internal-hom-formulas] identify $H_A(a_!L,N)$ with
$h_{*,A}Ru_{*,A}F$. Apply $T_X$ and use step 2 for $h_*$, step 12 for $u$ on the bounded
constructible $F$ of step 16, step 15 for $L$, and step 14 for $h$ on $N$. This gives the
composite of isomorphisms $$T_Xh_{*,A}Ru_{*,A}F\simeq h_{*,B}T_WRu_{*,A}F\simeq
h_{*,B}Ru_{*,B}T_SF\simeq h_{*,B}Ru_{*,B}H_B(T_SL,T_Su^*Rh_A^!N)\simeq
h_{*,B}Ru_{*,B}H_B(T_SL,u^*Rh_B^!T_XN).$$ The last step also uses the inverse-image comparison of
step 2. The $B$ version of the same internal-Hom formulas identifies the last object with
$H_B(h_{*,B}u_{!,B}T_SL,T_XN)$, whose first argument is $T_X(a_!L)$ by step 2. All applications to
$B$ in these formulas are on ordinary unbounded categories, not a claimed constructible
subcategory.
18. We check that step 17 gives $\phi_{X;a_!L,N}$ itself. Set $D=H_A(a_!L,N)$. The internal-Hom
formulas are evaluation-compatible. Transpose step 17 under the closed-support adjunction, the
open direct-image adjunction, and tensor/Hom adjunction in that order. For the closed step the
defining equation is $$\varepsilon_{B,T_XN}\circ
h_{*,B}\kappa_{h,N}\circ\delta_{h,Rh_A^!N}=T_X\varepsilon_{A,N}.$$ For the open step the defining
equation is $\varepsilon_{u,B}\circ u_B^*\beta_{u,F}=T_S\varepsilon_{u,A}$ under
inverse-image/scalar comparison, as computed in steps 4 and 12. The remaining lisse step evaluates
$e_s$ to the $s$th coordinate, as in step 15. Substituting these three equations into the
evaluation-compatible formulas cancels the adjunction units against counits and leaves exactly
$$T_XD\otimes^L_{B_X}T_X(a_!L)\simeq T_X(D\otimes^L_{A_X}a_!L)\xrightarrow{T_X\mathrm{ev}}T_XN.$$
The reassociation is the balanced K-flat reassociation, whose monoidal coherence is
[lem-sfb-ringed-derived-monoidal-comparisons] for the coefficient ringed-topos morphism.
Uniqueness of the tensor/Hom transpose now identifies the actual morphisms. This also proves
compatibility with maps of $L$ and $N$.
19. For fixed bounded constructible $N$, the class of $K$ for which the specified $\phi_{X;K,N}$
is invertible contains zero and, by steps 17-18, all supported lisse sheaves. It is closed under
shifts and finite triangle extensions: internal Hom is contravariantly exact with its signed shift
comparison by [lem-weil-pbc-ringed-internal-hom-exact-restriction], and scalar extension is exact.
The evaluation definition of $\phi$ commutes with these shift comparisons (transpose the shifted
evaluation), so it gives a morphism of the reversed triangles including their connecting arrow.
Apply [lem-sf-triangle-morphism-iso]. Finite generation [det-cor-coefficient-heart-ii-generation]
therefore puts every bounded constructible $K$ in this class. Finally, evaluation and the
tensor/Hom adjunction are natural in both variables, so the resulting isomorphism is natural in
$K,N$. It is precisely the map in the statement by step 18 and the same evaluation definition
throughout the finite cone induction.
-/
theorem normAlgClInternalHomBaseChange
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    ∃ d : NormHomScalarReassociation X (normAlgClHomCoefficientMap ℓ Ω E),
      NormHomScalarNormalized X (normAlgClHomCoefficientMap ℓ Ω E) d ∧
      (∀ K N : DerivedCategory
          (normHomModules X (Profinite.continuousMapRingObjOfUniverse.{u, u} E)),
        constantModelBoundedConstructible
            (Profinite.continuousMapRingObjOfUniverse.{u, u} E) X K →
        constantModelBoundedConstructible
            (Profinite.continuousMapRingObjOfUniverse.{u, u} E) X N →
        IsIso (normHomComparison X (normAlgClHomCoefficientMap ℓ Ω E) d K N)) ∧
      NormHomComparisonNatural X (normAlgClHomCoefficientMap ℓ Ω E) d := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
