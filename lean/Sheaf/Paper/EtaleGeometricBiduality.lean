/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.DualityPairing
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.TruncationHypercohomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.CoordinateGenericDimension
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Compactification.Defs
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.DeltaRestriction
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.Sites.PullbackFlat
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Whiskering
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Sheaf.Paper.SfHomTriangulated
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.Paper.CoefficientFrobenius
import Sheaf.Paper.DeltaProperPushforward

import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.EtaleClosedCoprojection
import Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed
import Sheaf.AlgebraicGeometry.EtaleLocalDualInterval
import Sheaf.AlgebraicGeometry.EtaleTwistedBidualTransport
import Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor
import Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition
import Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect
import Sheaf.Paper.DirectImageTorAmplitude
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.StratumAmbientHom
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-! # Finite-stage geometric Verdier biduality on the etale site

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2128 (blueprint: thm-weil-etale-geometric-biduality).

The coefficient ring is the actual positive-level quotient A_(E,n), canonically
lifted to the coefficient universe of the small etale site. The conclusion uses
exactly the recorded constructibility and Tor-amplitude predicates, and the
normalized evaluation transpose supplied by lem-weil-duality-pairing.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry

namespace WeilConjectures

/-- The finite-stage etale biduality conclusion, with every clause written out.
The pairing witness determines the evaluation transpose uniquely, so its existence
is part of the conclusion and imposes no extra assumption. The equivalence comparison
identifies the restricted functor on both objects and morphisms. Exactness uses the
ambient distinguished triangles whose vertices lie in the full subcategory; the
opposite category has the reversed integer shift. The local finite-ring instance
is the named finiteness theorem applied to the positive-level quotient.
Source: blueprint order 2128 (blueprint: thm-weil-etale-geometric-biduality). -/
noncomputable def FiniteEtaleGeometricBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  ∃ h : Etale.AmbientDualityPairing
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
      (Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX),
    (∀ K : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X,
      finiteTorConstructibleEtale l E n hn X K →
        IsIso (Etale.AmbientDualityPairing.bidualityMap
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X h K)) ∧
    (∀ K : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X,
      finiteTorConstructibleEtale l E n hn X K →
        finiteTorConstructibleEtale l E n hn X
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).obj
              (op K))) ∧
    (∃ e : (finiteTorConstructibleEtale l E n hn X).FullSubcategoryᵒᵖ ≌
        (finiteTorConstructibleEtale l E n hn X).FullSubcategory,
      Nonempty (e.functor ⋙ (finiteTorConstructibleEtale l E n hn X).ι ≅
        (finiteTorConstructibleEtale l E n hn X).ι.op ⋙ Etale.verdierDual
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX)) ∧
    ∃ s : (Etale.verdierDual
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).CommShift
        ℤ,
      ∀ T : Triangle (Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)ᵒᵖ,
        finiteTorConstructibleEtale l E n hn X T.obj₁.unop →
        finiteTorConstructibleEtale l E n hn X T.obj₂.unop →
        finiteTorConstructibleEtale l E n hn X T.obj₃.unop →
        T ∈ distTriang (Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)ᵒᵖ →
        Triangle.mk
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).map
              T.mor₁)
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).map
              T.mor₂)
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).map
              T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (Etale.DerivedCategoryModule
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)

/-- Finite-stage geometric Verdier biduality: the canonical double-dual map is
invertible, and Verdier duality is an exact contravariant anti-equivalence of
Dᵇ_ctf on the ordinary etale site of every separated finite-type scheme over the
global algebraically closed field. No pro-etale or integral category is substituted.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2128
(blueprint: thm-weil-etale-geometric-biduality).

Proof (the complete DAG plan, in its original order):

1. For the final specialization use the global finite-stage coefficient ring $A=A_{E,n}$ and the
   small etale categories, not the pro-etale or integral categories. The map is the transpose of
   evaluation from [lem-weil-duality-pairing]. Keep this coefficient ring fixed, but denote a
   variable algebraically closed geometric base field by $F$; it is not the global $k$ while the
   induction is running. Prove the assertion simultaneously over algebraically closed base
   fields of characteristic different from $\ell$, by strong induction on a dimension bound
   $d\geq0$: first prove it for proper schemes of dimension at most $d$, then for all separated
   finite-type schemes of that dimension. The empty scheme has only the zero sheaf and is
   immediate. Finite-type schemes over a field have finite dimension by
   [lem-kun-dimension-finite-type] and are Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian], since a field is Noetherian. At $d=0$ every point
   is closed: a proper specialization would give a chain of irreducible closed subsets of length
   one. Thus the nonclosed-point part of the argument below is vacuous at the base of induction.

2. First establish preservation independently of biduality, for every algebraically closed field
   $F$ with $\operatorname{char}F\ne\ell$. Let $X/F$ be separated of finite type with $\dim
   X\leq d$ and $K\in D^b_c(X_{\mathrm{et}},A)$ of Tor amplitude $[a,b]$. Apply
   [lem-sf-etale-smooth-stratified-ctf] to obtain the finite localization tower with pieces
   $Rs_!P$ on smooth strata $s:S\hookrightarrow X$ of pure dimensions $r\leq d$, where
   $P=s^{-1}K$ has local finite-projective models in $[a,b]$. Factor $s$ as
   $S\xrightarrow{i}V\xrightarrow{j}X$ with $i$ closed and $j$ open. The ordinary-etale clause
   of [lem-weil-delta-restriction] gives $j^*\omega_X\cong\omega_V$. The proper composition
   statement [lem-sf-unbounded-compact-support-proper-composition] applies to the closed (hence
   proper) immersion $i$ and the structure morphism $a_V$ over the actual field $F$. Together
   with the ambient adjoints [thm-amb-etale-exceptional-adjoint, lem-exc-closed-ambient], it
   gives, for every ambient complex $C$ on $S$, the natural bijections
   $$\operatorname{Hom}(C,Ri^!\omega_V)=\operatorname{Hom}(Ri_*C,\omega_V)
   =\operatorname{Hom}(Ra_{V!}Ri_*C,A)=\operatorname{Hom}(Ra_{S!}C,A)
   =\operatorname{Hom}(C,\omega_S).$$
   Yoneda identifies $Ri^!\omega_V$ with $\omega_S$, including counits. Thus
   $Rs^!\omega_X=Ri^!j^*\omega_X\cong\omega_S$. Apply [lem-weil-stratum-ambient-hom], whose
   ordinary-etale clause is unbounded and assumes neither preservation nor biduality, to get
   $$D_X(Rs_!P)\cong Rs_*R\mathcal Hom_A(P,Rs^!\omega_X)\cong Rs_*D_SP.$$ All schemes here are
   separated finite type over $F$, hence Noetherian; no step identifies $F$ with an algebraic
   closure of a finite field.

3. For the smooth stratum $S/F$ of dimension $r$, [thm-asd-smooth-tensor] gives $\omega_S\cong
   L[2r]$, with $L$ a locally constant rank-one $A$-sheaf. Its Noetherian base is
   $\operatorname{Spec}F$, its structure map is smooth separated and compactifiable by
   [thm-nagata-compactification], and the coefficient annihilator is invertible in $F$. On an
   etale cover with the finite-projective model of $P$ and $L\cong A$, internal Hom is the
   finite dual complex tensored with $L[2r]$: for a finite free module the map
   $\operatorname{Hom}(A^m,A)\otimes M\to\operatorname{Hom}(A^m,M)$ is the coordinate identity,
   and projecting this identity by a projective summand's idempotent gives the same identity for
   a finite projective module. Applying it to each term and to the Hom-complex differential
   yields $D_SP\cong P^\vee\otimes L[2r]$. The dual terms are finite projective and occupy
   $[-b,-a]$, hence the shifted complex has Tor interval $[-b-2r,-a-2r]$. Its cohomology is
   constructible by finite locally constant terms and Serre closure [thm-constructible-serre].
   Exact stalks and the tensor-stalk identification [prop-weil-pbc-geometric-stalks-exact,
   lem-pod-etale-stalk-tensor-scalar] with stalk conservativity
   [lemma-weil-pbc-geometric-stalk-conservative] test the local flatness and cohomological
   bounds, so these bounds hold on $S$. For $s:S\to X$, [lem-sf-etale-direct-image-vanishing]
   gives $R^qs_*M=0$ for all module sheaves and $q>2r$. Use the following direct-image
   calculation, valid over the actual field $F$ and also used in step 10. For any separated
   finite-type map $f:T\to Y$ between finite-type $F$-schemes with $R^pf_*M=0$ for every module
   sheaf $M$ and $p>N$, and any bounded constructible $G$ of Tor amplitude $[u,v]$,
   [thm-dg-finite-type-constructibility] makes $Rf_*G$ bounded constructible. Write
   $\kappa=A/(\varpi_E)$, a finitely presented $A$-module (one generator and the relation
   $\varpi_E=0$). The tensor $G\otimes_A^L\kappa_T$ has cohomology only in $[u,v]$ by the Tor
   hypothesis. Choose its bounded-below representative using
   [def-sbc-standard-tstructure-derived-category]. Module sheaf categories are Grothendieck by
   [lem-weil-pbc-small-module-diagrams-grothendieck] with terminal index. The convergent
   finite-filtration spectral sequence [thm-sp-truncation-e2] for $f_*$ has only $0\leq p\leq N$
   and $u\leq q\leq v$, so $Rf_*(G\otimes_A^L\kappa_T)$ has cohomology in $[u,v+N]$. The
   arbitrary-morphism ordinary-etale projection theorem [lem-sf-projection-finite-constant]
   applies: $A$ is Noetherian because it is a finite ring, $G$ is bounded above, and its
   hypothesis is exactly the displayed all-sheaf bound. It identifies this tensor image with
   $(Rf_*G)\otimes_A^L\kappa_Y$. The residue criterion [lem-exc-residue-tor-test], which is
   stated on any scheme with this coefficient ring and bounded constructible input, now gives
   Tor amplitude $[u,v+N]$ of $Rf_*G$. This derivation invokes no global-base UDV definition.
   Apply it with $f=s$, $G=D_SP$, $N=2r$, $u=-b-2r$ and $v=-a-2r$. It gives $Rs_*D_SP\in
   D^b_{ctf}$ with interval $[-b-2r,-a]$, contained in $[-b-2d,-a]$. Apply
   [lem-sf-hom-triangulated] to each triangle of the finite localization tower of step 2.
   Starting from its zero end, [lem-sf-derived-homology-long-exact, thm-constructible-serre]
   give bounded constructible cohomology of $D_XK$ by induction along the tower. For any
   degree-zero module sheaf choose a K-flat resolution by [lem-pc-kflat-resolution]. With this
   fixed tensor factor, the total tensor and differential of [def-kun-derived-tensor] carry a
   cone matrix to the cone matrix of the tensored map (including the shift sign); K-flatness
   makes this operation descend through quasi-isomorphisms. Hence tensoring each triangle gives
   a distinguished triangle and the same long exact sequence, so the common Tor interval
   $[-b-2d,-a]$ is preserved by these extensions. This proves $D_XK\in
   D^b_{ctf}(X_{\mathrm{et}},A)$ over every field in the simultaneous induction. Taking $K=A_X$
   also proves $\omega_X$ bounded constructible with finite Tor amplitude. Preservation here was
   proved from strata, not from any double-dual isomorphism.

4. Fix a proper $X/F$ with $\dim X\leq d$ and $K\in D^b_{ctf}(X_{\Et},A)$. Set
   $\Delta=\operatorname{Cone}(\delta_K)$. By the arbitrary-base preservation proved in steps
   2--3, both $D_XK$ and $D_XD_XK$ are bounded constructible. The long cohomology sequence
   [lem-sf-derived-homology-long-exact] gives, for each $q$, an exact sequence
   $$0\longrightarrow\operatorname{coker}(\mathcal H^q\delta_K)\longrightarrow\mathcal
   H^q\Delta\longrightarrow\ker(\mathcal H^{q+1}\delta_K)\longrightarrow0.$$ By
   [thm-constructible-serre] its two end terms and hence its middle term are constructible.
   Outside a finite interval both end terms vanish. Thus $\Delta$ is bounded constructible; no
   finite-Tor assertion about the cone is needed.

5. Suppose $d>0$ and $x\in X$ is nonclosed. Choose an affine open $V=\operatorname{Spec}B$
   containing $x$, with finitely many $F$-algebra generators $t_1,\ldots,t_m$ of $B$. By
   [lem-kun-closed-point-field], $\operatorname{trdeg}_F\kappa(x)>0$. If every generator had
   algebraic image in $\kappa(x)$, the fraction field of their image algebra $B/\mathfrak p_x$
   would be algebraic over $F$, a contradiction. Choose a generator $t=t_r$ with transcendental
   image. The coordinate morphism $p:V\to\mathbf A^1_F$ sends $x$ to its generic point, since
   $F[t]\to\kappa(x)$ is injective. The surjection $F[T_1,\ldots,T_m]\twoheadrightarrow B$ given
   by the generators gives a closed immersion $V\hookrightarrow\mathbf A^m_F$. Apply
   [lem-fin-coordinate-generic-dimension] with $S=\operatorname{Spec}F$, $Y=V$ and its open
   subscheme $V$ itself; $\dim V\leq\dim X\leq d$ follows by viewing chains in an open subspace.
   Hence $\dim V_\eta\leq d-1$. By [lem-kun-dimension-extension] the same holds for
   $V_{\bar\eta}$ over $L=\overline{F(t)}$. This fibre is separated and finite type over $L$: on
   affine charts its rings are obtained from finitely generated $F[t]$-algebras by scalar
   extension, and its diagonal is the base change of the closed diagonal of $V$; closedness
   survives scalar extension since $(R/I)\otimes_R R\prime=R\prime/IR\prime$ on affine charts.

6. Write $u:V\hookrightarrow X$ and $g:V_{\bar\eta}\to V$. Verify successively that $u^*K$ and
   $g^*u^*K$ meet the induction hypothesis's constructibility and Tor conditions. For each of
   the two pairs $(h,Q)=(u,K)$ and $(g,u^*K)$, [prop-weil-pbc-inverse-image-modules-exact]
   identifies constant-$A$ module pullback $h^*$ with an exact inverse-image functor, so
   $\mathcal H^q(h^*Q)=h^{-1}\mathcal H^q(Q)$ and the finite cohomological range is preserved.
   By [lem-weil-pbc-constructible-etale-set-pullback] the pulled-back cohomology sheaves are
   constructible. On a stratum where a cohomology sheaf is a finite constant $A$-module, pull
   back its trivializing etale cover and its addition and scalar maps; the result is the same
   finite constant $A$-module on the pulled-back cover. Thus this is module constructibility,
   not only constructibility of sets. For a Tor interval $[a,b]$ of $Q$,
   [lem-sf-etale-flat-model] gives a flat complex $P$ supported in $[a,b]$, representing $Q$. It
   is K-flat by [lem-pc-kflat-closure]. By [lem-weil-pbc-ringed-pullback-preserves-kflat],
   $h^*P$ has flat terms and is K-flat; it is still supported in $[a,b]$. Exactness of $h^*$
   identifies its derived object with $h^*Q$, and the converse implication of
   [lem-sf-etale-flat-model] gives the same Tor interval. Applying these checks first to $(u,K)$
   supplies the hypotheses for $(g,u^*K)$. Write $K_V=u^*K$. In particular $g^*K_V\in
   D^b_{ctf}(V_{\bar\eta,\Et},A)$. All cited pullback statements apply to arbitrary scheme
   morphisms; the geometric-generic morphism need not be finite type over the original $F$.

7. Work over the variable algebraically closed field $F$ of the induction, and set
   $L=\overline{F(t)}$ and $T=V_{\bar\eta}$. On the affine $V$ choose generators of its algebra
   over $F[t]$ to embed $i:V\hookrightarrow W=\mathbf A^r_{\mathbf A^1_F}$ as a closed
   subscheme. The same immersion after generic base change is $i_L:T\hookrightarrow\mathbf
   A^r_L$. By [cor-amb-affine-space-adjunction],
   [lem-sf-unbounded-compact-support-proper-composition] for the closed immersions, and the
   Hom-adjunction calculation of step 2, $$\omega_V\cong Ri^!A_W(r+1)[2r+2],\qquad\omega_T\cong
   Ri_L^!A_{\mathbf A^r_L}(r)[2r].$$ Apply the closed-support clause of
   [lem-sf-etale-generic-exchange-algclosed] with $B=\mathbf A^1_F$ and the bounded
   constructible input $A_W(r+1)[2r+2]$. Tate pullback and invertibility are
   [lem-asd-etale-finite-twist-pullback]. Here is the tensor identity needed for $Ri_L^!$,
   separately from compatibility of the base-change comparison. Write $h=i_L$, let $Q$ be any
   invertible locally constant rank-one coefficient sheaf on the ambient affine space, and write
   $Q_T=h^{-1}Q$. On an etale cover trivializing $Q$, the sheaf direct-image formula
   [def-weil-pbc-direct-image] gives $h_*(C\otimes Q_T^{-1})=(h_*C)\otimes Q^{-1}$: both sides
   are the same sections of $C$ on the closed base change of each etale object. These identities
   agree on overlaps, because multiplication by a transition unit acts identically on both
   sides. Closed direct image is exact by [lem-cbc-open-closed-recollement], so the identity
   applies termwise and passes to derived categories. Tensoring with either rank-one sheaf is
   exact, with its tensor inverse as inverse; on complexes these functors also commute with
   shifts. The adjunction of [lem-exc-closed-ambient] consequently gives, naturally in $C$,
   $$\operatorname{Hom}(C,Rh^!(M\otimes Q))=\operatorname{Hom}(Rh_*C,M\otimes
   Q)=\operatorname{Hom}((Rh_*C)\otimes Q^{-1},M)=\operatorname{Hom}(C\otimes
   Q_T^{-1},Rh^!M)=\operatorname{Hom}(C,(Rh^!M)\otimes Q_T).$$ Yoneda gives $Rh^!(M\otimes
   Q)\cong(Rh^!M)\otimes Q_T$, compatible with the adjunction counit by construction. Use this
   with $Q=A(1)$ and the shift $[2]$ to compare the two displayed ambient dualizing objects.
   Thus there is the canonical comparison $\theta:g^*\omega_V\xrightarrow{\sim}\omega_T\otimes
   J$ with $J=A_T(1)[2]$. Steps 2--3 make $\omega_V$, $K_V$, and $D_VK_V$ bounded constructible,
   with the last two of finite Tor amplitude, over this actual $F$. Apply the internal-Hom
   clause of the same new node first to $(K_V,\omega_V)$ and then to $(D_VK_V,\omega_V)$. It
   identifies $g^*D_VK_V$ with $D_T(g^*K_V)\otimes J$ and $g^*D_VD_VK_V$ with $D_TD_T(g^*K_V)$:
   in the latter expression $R\mathcal Hom(Q\otimes J,\omega_T\otimes J)=R\mathcal
   Hom(Q,\omega_T)$, since tensor with the invertible $J$ is an equivalence; this is the Hom
   adjunction after applying its inverse, and it respects evaluation. The evaluation identity in
   [lem-sf-etale-generic-exchange-algclosed] says that the two internal-Hom comparisons identify
   the pulled-back evaluation pairing with evaluation for $g^*K_V$ after the $J^{-1}\otimes J$
   cancellation. Transposing that identity via [lem-weil-duality-pairing] therefore identifies
   the actual arrow $g^*\delta_{K_V}$ with $\delta_{g^*K_V}$, not merely the two underlying
   objects. The induction hypothesis at dimension $d-1$ over $L$ now makes this arrow an
   isomorphism. For $u:V\hookrightarrow X$, the ordinary-etale canonical comparison of
   [lem-weil-delta-restriction] carries $u^*\delta_K$ to $\delta_{K_V}$. Thus the pullback of
   $\delta_K$ to $T$ is an isomorphism. Given a geometric point $\bar
   x:\operatorname{Spec}\Omega\to V$ over $x$, use the injection $F(t)\to\kappa(x)\to\Omega$ to
   choose $L$ inside $\Omega$: take the subfield of elements algebraic over $F(t)$. It is
   algebraically closed, since a root in $\Omega$ of a polynomial with algebraic coefficients is
   algebraic over the finite extension generated by those coefficients, and hence over $F(t)$.
   This is an allowed choice of algebraic closure in the arbitrary-base generic exchange and in
   the induction hypothesis. Thus $\bar x$ lifts to $V_{\bar\eta}$. Exact inverse image and the
   stalk comparison of [lem-weil-pbc-inverse-image-stalk-germ] identify the cohomology stalks of
   the pulled-back cone with those of $\Delta$ at $\bar x$. They vanish since the pulled-back
   arrow is an isomorphism. This proves zero stalks at every nonclosed point; exactness of
   geometric stalks is [prop-weil-pbc-geometric-stalks-exact].

8. For each of the finitely many nonzero $\mathcal H^q\Delta$, its support is constructible by
   [lem-weil-pbc-constructible-module-support-constructible]; the preceding step shows it
   consists only of closed points (also at $d=0$). By [def-weil-constructible-subset] it is a
   finite union of locally closed subsets. Give each such subset its reduced locally closed
   subscheme structure. It is Noetherian, being a locally closed subspace of the Noetherian $X$,
   and has finitely many irreducible components by
   [lem-weil-pbc-noetherian-finitely-many-components]. Each component has a generic point by
   [lem-sc-scheme-sober]. That point is closed already in $X$, so its closure in the locally
   closed subscheme is its singleton; hence each component is a singleton. Each support, and
   then their finite union $Z_0$, is therefore a finite set of closed points. This is the
   explicit finite-support argument, rather than an assumption that a constructible support is
   closed.

9. Record the coefficient identification at $s=\operatorname{Spec}F$. In
   [lem-exc-abelian-sheaves-gmodules] take $F^{\rm sep}=F$ and the identity geometric point; the
   Galois group is trivial, so the equivalence is with abelian groups. Transporting the scalar
   endomorphisms $a\cdot(-)$ for $a\in A$, and their ring identities, gives an equivalence
   between small-etale constant-$A$ module sheaves on $s$ and $A$-modules. It is exact, since an
   equivalence of abelian categories preserves kernels and cokernels, and monoidal by
   [lem-pod-etale-stalk-tensor-scalar]. Apply the exact equivalence and its exact quasi-inverse
   termwise to complexes: they preserve acyclic complexes and quasi-isomorphisms, hence induce
   inverse derived equivalences. The monoidal equivalence preserves flat objects and K-flat
   complexes because tensoring with an acyclic complex can be tested through either exact
   quasi-inverse. Thus the derived equivalence is monoidal; its tensor adjunction identifies
   derived internal Hom and its evaluation. For the structure map $\operatorname{id}_s$, use the
   compactification with both maps the identity in [thm-amb-etale-exceptional-adjoint].
   Extension by zero for the whole open is the identity by its presheaf formula
   [def-weil-pbc-extension-by-zero]; direct image along the identity is the identity since
   $W\times_s s=W$ [def-weil-pbc-direct-image]. Therefore $R(\operatorname{id}_s)_!$ is the
   identity. Its right adjoint is the identity as well: the adjunction represents
   $\operatorname{Hom}(C,-)$ itself, and Yoneda gives the identification with the identity
   functor. Hence $\omega_s=A_s$. Consequently $D_s$ and its evaluation transpose
   [lem-weil-duality-pairing] are exactly derived coefficient duality and canonical coefficient
   evaluation under this equivalence.

10. Let $a:X\to s$ be the proper structure morphism. The ring $A$ is annihilated by a power of
   $\ell$, invertible in $F$. The all-sheaf vanishing theorem
   [lem-sf-etale-direct-image-vanishing] gives $R^ra_*M=0$ for $r>2d$. Apply the arbitrary-base
   direct-image calculation established in step 3 with $f=a$, $N=2d$, and a Tor interval
   $[a_0,b_0]$ of $K$; its finite-type, separatedness, invertible-coefficient and
   bounded-constructibility hypotheses all hold. Thus $Ra_*K$ is bounded constructible with Tor
   interval $[a_0,b_0+2d]$. Under the point equivalence of step 9 it is a bounded complex of
   ordinary algebraic $A$-modules with finitely generated cohomology. Indeed constructibility on
   the one-point scheme gives finite underlying stalk sets, and the elements of each finite set
   form a finite generating list. Apply [lem-weil-coefficient-frobenius] with
   $\Lambda=A=A_{E,n}=\mathcal O_E/(\varpi_E^n)$ and $n\geq1$. Its current conventions require
   commutative coefficients and interpret finite modules as finitely generated, self-injective
   as injective over the ring itself, and derived Hom on the one-object ringed site. These
   requirements hold: $A$ is the fixed commutative quotient ring, and step 9 identifies the
   point category, its tensor, derived internal Hom and evaluation with precisely these ordinary
   algebraic module constructions. We use its finite-stage clause: $\operatorname{Hom}_A(-,A)$
   is exact on modules and evaluation is an isomorphism on finitely generated modules. No
   ordinary reflexivity assertion for $\mathcal O_E$ is used. For a representing cochain complex
   $C$, write $(C^\vee)^r=\operatorname{Hom}_A(C^{-r},A)$ with
   $d_{C^\vee}^r(\phi)=(-1)^{r+1}\phi\circ d_C^{-r-1}$. Exactness of $\operatorname{Hom}_A(-,A)$
   makes this dual send acyclic complexes to acyclic complexes, so it computes derived
   coefficient duality. The transpose of evaluation has degree-$q$ component
   $c\mapsto(\phi\mapsto(-1)^q\phi(c))$. Substitution in the two displayed differentials
   verifies that this is a cochain map. Exactness identifies $H^q(C^{\vee\vee})$ with
   $H^q(C)^{\vee\vee}$; on cocycles the displayed map is finite-module evaluation up to the
   invertible sign $(-1)^q$. Finite-module reflexivity therefore makes its cohomology an
   isomorphism for every $q$. Thus its canonical derived coefficient double-dual arrow is an
   isomorphism, and hence so is $\delta_{Ra_*K}$. Apply [lem-weil-delta-proper-pushforward] to
   the proper morphism $a$: it identifies this arrow with $Ra_*\delta_K$. Therefore
   $Ra_*\Delta=0$. Indeed [lem-weil-pbc-derived-direct-image-triangulated] applies to the
   additive left exact module direct image of [def-weil-pbc-direct-image], whose source has
   enough injectives; it preserves the cone triangle, so the image triangle has an isomorphism
   as its first arrow. This last cone calculation is independent of geometric biduality.

11. Put the reduced closed subscheme structure on $Z_0$ and write $i:Z\hookrightarrow X$,
   $j:X\setminus Z_0\hookrightarrow X$. For $M=\mathcal H^q\Delta$, its restriction $j^{-1}M$
   has zero geometric stalks by construction of $Z_0$ and
   [lem-weil-pbc-inverse-image-stalk-germ]. It is the zero sheaf by
   [lemma-weil-pbc-geometric-stalk-conservative]. Apply the recollement triangle of
   [lem-cbc-open-closed-recollement] to $M[0]$. Its first term is zero and $i_*$ is exact, so
   the unit gives $M\cong i_*G$ for the degree-zero sheaf $G=i^{-1}M$. This derives the
   finite-support representation; the definition of support alone would not give this
   isomorphism.

12. The reduced finite closed subscheme $Z$ is separated finite type over $F$ with dimension at
   most zero. The canonical degree-zero formula of [lem-weil-pbc-zero-dimensional-cohomology]
   says $\Gamma(Z,G)=\prod_{z\in Z_0}G_{\bar z}$. It is $A$-linear because the canonical maps
   commute with the scalar endomorphisms. By [lem-weil-pbc-inverse-image-stalk-germ], these
   stalks identify with $M_{\bar z}$. The direct-image formula [def-weil-pbc-direct-image],
   evaluated at the terminal object, gives $\Gamma(X,M)=\Gamma(Z,G)$. Moreover $\Gamma(Z,-)$ is
   exact on $A$-module sheaves: its formula is a finite product of exact geometric stalk
   functors [prop-weil-pbc-geometric-stalks-exact], and exactness of module sheaves is tested on
   underlying abelian sheaves [def-weil-sheaf-of-modules-category]. For $b=a i:Z\to s$, the
   point equivalence of step 9 identifies $b_*$ with this exact sections functor, so $Rb_*=b_*$.
   Since $i_*$ is exact, the ordinary-etale clause of
   [lem-weil-derived-direct-image-composition] gives $Ra_*M=Ra_*i_*G\cong Rb_*G=b_*G$. Thus
   $R^pa_*M=0$ for $p>0$ and, under the point equivalence, $a_*M=\prod_{z\in Z_0}M_{\bar z}$.
   This argument works in module sheaves directly and does not silently identify module-derived
   and abelian-derived cohomology.

13. Choose $a_0$ below the nonzero cohomology of $\Delta$. By
   [def-sbc-standard-tstructure-derived-category], $\Delta$ has a cochain representative zero
   below $a_0$; concretely the good truncation has $\operatorname{coker}(d^{a_0-1})$ in degree
   $a_0$, the original terms above, and zero terms below, and the natural quotient map is a
   quasi-isomorphism because the discarded cohomology vanishes. Apply [thm-sp-truncation-e2] to
   that bounded-below representative and the left exact additive functor $v=a_*$ on $A$-module
   sheaves. Both categories of module sheaves are Grothendieck: use
   [lem-weil-pbc-small-module-diagrams-grothendieck] with the terminal index category and a
   universe in which each small etale site is small. The spectral sequence is therefore
   $$E_2^{p,q}=R^pa_*(\mathcal H^q\Delta)\Longrightarrow\mathcal H^{p+q}(Ra_*\Delta).$$ By step
   12 all columns with $p>0$ vanish. The bounded-below hypothesis supplies the theorem's finite,
   exhaustive, separated filtration in each total degree, so there are no convergence or
   extension ambiguities: $\mathcal H^q(Ra_*\Delta)\cong a_*\mathcal H^q\Delta$. Step 10 makes
   the left side zero. The point equivalence and step 12 then give $0=\prod_{z\in Z_0}(\mathcal
   H^q\Delta)_{\bar z}$. Each factor is zero, by its inclusion and projection in a finite
   product. Outside $Z_0$ the stalks were already zero. Stalk conservativity
   [lemma-weil-pbc-geometric-stalk-conservative] gives $\mathcal H^q\Delta=0$ for every $q$,
   whence $\Delta=0$ by the definition of the derived category. Thus $\delta_K$ is an
   isomorphism for every proper $X$ of dimension at most $d$.

14. Now let $X/F$ be any separated finite-type scheme with $\dim X\leq d$. Apply
   [thm-nagata-compactification] to its structure morphism (the base $s$ is quasi-compact and
   quasi-separated), obtaining a quasi-compact open immersion $j_0:X\hookrightarrow\bar X$ with
   $\bar X$ proper over $F$, as in [def-nagata-compactification]. Replace $\bar X$ by the closed
   scheme-theoretic closure $C$ of $X$ [def-nagata-scheme-theoretic-closure]. By
   [lemma-nagata-immersion-open-in-scheme-image], the resulting $j:X\hookrightarrow C$ is a
   quasi-compact dense open immersion. The closed subscheme $C$ remains proper: its diagonal is
   the restriction of the closed diagonal of $\bar X$, its coordinate rings are quotients of
   finite-type $F$-algebras, and after every base change the closed immersion remains closed: on
   affine charts a quotient $R/I$ pulls back to $R\prime/IR\prime$, whose image is the closed
   subset $V(IR\prime)$. Composing this closed map with the closed map supplied by properness of
   $\bar X$ proves universal closedness [def-weil-proper-morphism]. These verify separatedness,
   finite type and universal closedness directly. By the dense-open clause of
   [lem-kun-dimension-extension], $\dim C=\dim X\leq d$.

15. Prove the needed preservation by ordinary etale extension by zero directly. For $K$ of Tor
   amplitude $[a,b]$, use [lem-sf-etale-flat-model] to choose a bounded flat representative $P$
   in $[a,b]$. By [lem-weil-pbc-extension-by-zero-exact], degreewise $j_!$ preserves
   quasi-isomorphisms and $\mathcal H^q(j_!K)=j_!\mathcal H^qK$, so its cohomological range is
   unchanged. On each locally closed stratum of a finite constructibility partition of $X$,
   [lem-weil-pbc-extension-by-zero-stalks] identifies the restricted extended sheaf with the
   original finite locally constant sheaf; on the complementary closed subscheme it is zero, by
   that stalk formula and [lemma-weil-pbc-geometric-stalk-conservative]. The strata are locally
   closed also in $C$ because $X$ is open. Adding the complement therefore proves
   constructibility, using the ordinary-etale definition [def-weil-pbc-constructible-complexes].
   Each term $j_!P^q$ is flat. Indeed, for an injection $M'\to M$ of module sheaves on $C$,
   [prop-weil-pbc-inverse-image-modules-exact] gives an injection $j^{-1}M'\to j^{-1}M$ on $X$.
   Tensoring with the flat $P^q$ preserves this injection. At a geometric point of $X$, exact
   stalks [prop-weil-pbc-geometric-stalks-exact], the extension stalk formula and
   [lem-pod-etale-stalk-tensor-scalar] identify the stalk of $(j_!P^q)\otimes
   M'\to(j_!P^q)\otimes M$ with the stalk of the just obtained injection $P^q\otimes j^{-1}M'\to
   P^q\otimes j^{-1}M$. At a point of $C\setminus X$ both stalks are zero. Stalk conservativity
   proves that $(j_!P^q)\otimes M'\to(j_!P^q)\otimes M$ is an injection, which is the flatness
   condition. Thus $j_!P$ is a bounded flat complex in $[a,b]$, representing $j_!K$;
   [lem-pc-kflat-closure] makes it K-flat and the converse implication of
   [lem-sf-etale-flat-model] gives the same Tor interval. Consequently $j_!K\in
   D^b_{ctf}(C_{\mathrm{et}},A)$. The proper case at the current dimension bound, proved in step
   13, gives an isomorphism $\delta_{j_!K}$. Restrict along $j$ and use the ordinary-etale
   clause of [lem-weil-delta-restriction]: its canonical comparison
   $(D_X\alpha_{j_!K})^{-1}\circ\alpha_{D_Cj_!K}$ carries $j^*\delta_{j_!K}$ to
   $\delta_{j^*j_!K}$. Here $j$ is an etale $F$-morphism between separated finite-type schemes,
   $A$ is finite with invertible additive exponent, and all derived categories have constant
   $A$-module coefficients, as that clause requires. For an etale object $W\to X$ regarded over
   $C$, the presheaf formula [def-weil-pbc-extension-by-zero] equals $K(W)$, since $W$ factors
   through $X$. Sheafification restricted to the open therefore recovers $K$, so $j^*j_!K\cong
   K$ canonically and this arrow is $\delta_K$. This proves the arbitrary separated finite-type
   case at dimension bound $d$. At $d=0$ steps 5--7 were vacuous and steps 8--15 prove the base;
   for $d>0$ the only earlier-dimension use was step 7 over $\overline{F(t)}$. The simultaneous
   strong induction is therefore well founded.

16. Finally the preservation proved in steps 2--3 makes $D_X$ an endofunctor with reversed
   arrows on $D^b_{ctf}(X_{\Et},A)$. It is exact contravariantly by [lem-sf-hom-triangulated].
   The evaluation transpose is natural by [lem-weil-duality-pairing], and the proved
   isomorphisms give $\mathrm{id}\xrightarrow{\sim}D_XD_X$. Regarding $D_X$ as a functor from
   the opposite category, its opposite functor is a quasi-inverse: the same natural double-dual
   isomorphism supplies both composites with the identity. This gives the claimed exact
   anti-equivalence, with no appeal to an unspecified choice of an isomorphism $K\cong D_XD_XK$.
   Specialize the proved simultaneous assertion to the original global $k=\overline{\mathbf
   F}_q$ and the fixed coefficient ring $A=A_{E,n}$ to obtain exactly the item statement.
-/
theorem finite_stage_etale_geometric_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    FiniteEtaleGeometricBiduality l E n hn X aX := by
  sorry

end WeilConjectures
