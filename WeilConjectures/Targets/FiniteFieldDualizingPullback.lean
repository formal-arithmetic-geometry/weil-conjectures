/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.SecSmoothPurity.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.AlgebraicGeometry.QuasiFiniteCompactSupportExact
import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
import WeilConjectures.AlgebraicGeometry.EtaleHorizontalSupportMate
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTowerConstructibleDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison

/-!
# Finite-field dualizing-object pullback

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: lem-sf-finite-field-dualizing-pullback).

The dualizing objects are specified by their constructible adjunction counits. The compact
support functors and exchange are the published compactification constructions, and the Hom
comparison is the evaluation transpose of the canonical tensorator.
-/

@[expose] public section
set_option autoImplicit false

universe u v w uC vC uD vD uB vB uB' vB'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The discrete condensed finite quotient coefficient of the finite-field comparison.
Source: blueprint finite-field paragraph, coefficient A
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDualizingCoefficient
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ) :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  let A := Padic.coefficientExtensionRing ell E n
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let R := Profinite.continuousMapRingObjOfUniverse.{u, u} A
  letI : MonObj R := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  letI : IsCommMonObj R := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
  exact CommMon.mk R

/-- The actual module-object derived category, with its relative derived tensor and Hom.
Source: blueprint finite-field paragraph, D(Mod A_V)
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
abbrev finiteFieldModuleDerived
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ.X X))

/-- The canonical dualizing-Hom comparison: evaluation transpose followed by Hom(1,w).
Source: blueprint finite-field paragraph, comparison c_K
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDualizingHomComparison
    {C : Type v} {D : Type w} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.Monoidal] (K W : C) (W' : D) (e : G.obj W ≅ W') :
    G.obj ((ihom K).obj W) ⟶ (ihom (G.obj K)).obj W' :=
  (Functor.LaxMonoidal.ihomComparison G K).natTrans.app W ≫ (ihom (G.obj K)).map e.hom

/-- The specified Koszul braiding on the actual module-object derived category.
Source: blueprint finite-field paragraph, symmetric tensor identifications
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDerivedBraiding
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) (K L : finiteFieldModuleDerived Λ X) : K ⊗ L ≅ L ⊗ K :=
  @BraidedCategory.braiding _ _ _
    (DerivedCategory.braidedCategory'
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) K L

/-- The finite-field comparison conclusions, expressed with categorical parameters so that
large derived-functor constructions are instantiated only once. In the theorem below every
category, functor, object property, braiding, and exchange is the specified published one.
The representing bijections specify the values of the constructible exceptional adjoints.
Source: blueprint finite-field paragraph, all displayed comparisons
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
structure FiniteFieldDualizingPullbackData
    {C : Type uC} {D : Type uD} {B : Type uB} {B' : Type uB'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vB} B] [Category.{vB'} B']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory B] [MonoidalCategory B']
    [MonoidalClosed C] [MonoidalClosed D]
    (constructible : ObjectProperty C) (ctf : ObjectProperty C) (ctfBar : ObjectProperty D)
    (G : C ⥤ D) [G.Monoidal] (H : B ⥤ B')
    (unitIso : H.obj (𝟙_ B) ≅ 𝟙_ B')
    (braid : ∀ K L : C, K ⊗ L ≅ L ⊗ K)
    (braidBar : ∀ K L : D, K ⊗ L ≅ L ⊗ K)
    (R : C ⥤ B) (Rbar : D ⥤ B') (alpha : R ⋙ H ⟶ G ⋙ Rbar) where
  W : C
  Wbar : D
  W_ctf : ctf W
  Wbar_ctf : ctfBar Wbar
  counit : R.obj W ⟶ 𝟙_ B
  counitBar : Rbar.obj Wbar ⟶ 𝟙_ B'
  represents : ∀ P : ctf.FullSubcategory,
    Function.Bijective (fun f : P.obj ⟶ W ↦ R.map f ≫ counit)
  representsBar : ∀ P : ctfBar.FullSubcategory,
    Function.Bijective (fun f : P.obj ⟶ Wbar ↦ Rbar.map f ≫ counitBar)
  symmetry : ∀ K L : C,
    Functor.LaxMonoidal.μ G K L ≫ G.map (braid K L).hom =
      (braidBar (G.obj K) (G.obj L)).hom ≫ Functor.LaxMonoidal.μ G L K
  preserves_ctf : ∀ K : ctf.FullSubcategory, ctfBar (G.obj K.obj)
  conservative : ∀ (K L : C) (f : K ⟶ L),
    constructible K → constructible L → IsIso (G.map f) → IsIso f
  exchange_iso : ∀ K : ctf.FullSubcategory, IsIso (alpha.app K.obj)
  dualizingIso : G.obj W ≅ Wbar
  counit_normalization : alpha.app W ≫ Rbar.map dualizingIso.hom ≫ counitBar =
    H.map counit ≫ unitIso.hom
  beta_iso : ∀ K : ctf.FullSubcategory,
    IsIso ((Functor.LaxMonoidal.ihomComparison G K.obj).natTrans.app W)
  comparison_iso : ∀ K : ctf.FullSubcategory,
    IsIso (finiteFieldDualizingHomComparison G K.obj W Wbar dualizingIso)
  comparison_natural : ∀ (K L : ctf.FullSubcategory) (f : L.obj ⟶ K.obj),
    G.map ((MonoidalClosed.pre f).app W) ≫
      finiteFieldDualizingHomComparison G L.obj W Wbar dualizingIso =
    finiteFieldDualizingHomComparison G K.obj W Wbar dualizingIso ≫
      (MonoidalClosed.pre (G.map f)).app Wbar
  evaluation : ∀ K : ctf.FullSubcategory,
    G.obj K.obj ◁ finiteFieldDualizingHomComparison G K.obj W Wbar dualizingIso ≫
      (ihom.ev (G.obj K.obj)).app Wbar =
    Functor.LaxMonoidal.μ G K.obj _ ≫ G.map ((ihom.ev K.obj).app W) ≫ dualizingIso.hom

/-- Triangulatedness component of the finite-field comparison: the derived coefficient pullback
`G = L(g^*)` along `g : T ×_k k̄ → T` is triangulated.
Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(exactness of `G`).

Proof: module pullback is exact [det-prop-sfb-module-pullback-exact-main], so `L(g^*)` is
isomorphic to the levelwise functor `D(g^*)` [prop-sfb-module-left-derived-upper-star-levelwise],
which is triangulated; the published instance of `UpperStarShift` transports this structure.
(blueprint: new-lem-sf-finite-field-dualizing-pullback-triangulated) -/
theorem finiteField_dualizing_pullback_triangulated
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (E : Type u) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a] :
    (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
      (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).IsTriangulated :=
  inferInstance

/-- Dualizing-data component of the finite-field comparison: for every compactification of `a`,
the specified data of `FiniteFieldDualizingPullbackData` (dualizing objects with their counits,
symmetric monoidality, preservation of `D^b_ctf`, conservativity, invertible compact-support
exchange, the comparison `w` with its counit normalization, and the invertible natural
evaluation-compatible Hom comparison) exist.
Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: new-lem-sf-finite-field-dualizing-pullback-data).

Proof:

1. The DVR and finite residue field in [lem-weil-l-adic-extension-integers-dvr] and the finite-
quotient assertion [lem-weil-valued-dvr-finite-quotients] make $A$ finite. Write $\ell=u\pi_E^e$
with $e>0$ and choose $r$ with $er\ge n$; then $\ell^rA=0$. All finite subextensions $k_i/k$
inside $\bar k$ are finite fields and are separable by [lem-sfb-finite-field-galois-frobenius],
hence their spectra are etale by [lem-weil-pbc-finite-separable-extension-etale]; their maps are
finite because the extension is finite dimensional. Every element of $\bar k$ belongs to one of
them, and the compositum of two is again finite. Thus $\bar k=\varinjlim_i k_i$ over a small
directed set. On each affine chart of $T$, $g$ is induced by the filtered colimit of these finite
etale scalar extensions. By [lem-weil-pbc-ind-etale-stability] it is weakly etale. The field
extension is fpqc by [lem-pc-field-extension-fpqc-cover], and its pullback remains so by [lem-
galois-fpqc-covering-base-change]. Hence $g$ is a singleton cover and an object of
$T_{\mathrm{proet}}$ [def-weil-pbc-proetale-site].

2. For all the projections use exactness of actual module pullback [det-prop-sfb-module-pullback-
exact-main]. It preserves constructible cohomology by [lem-weil-pbc-module-constructible-
pullback]. The finite discrete coefficient equivalence [lem-sf-module-object-ordinary-coefficient-
equivalence] preserves relative tensor and every Tor interval. In its ordinary constant-ring
model, [lem-sf-flat-model] supplies a bounded flat representative of any given Tor interval; its
hypothesis that $\ell$ is invertible holds on every scheme here. Transport this model back through
the exact monoidal equivalence. Pullback preserves flat objects by [new-proetale-inverse-image-
module-flat], so pulling back this representative retains that interval. Thus $G$ preserves
$D^b_{ctf}$. The canonical tensorator and unit are invertible and satisfy the monoidal laws by
[lem-sfb-derived-pullback-strong-monoidal]. They preserve symmetry: on homogeneous sections of
flat representatives both ways send $x\otimes y$ to $(-1)^{ij}y\otimes x$ in degrees $i,j$, so
their localized maps agree. This gives the specified strong symmetric monoidal exact $G$.

3. Apply [lem-zl-condensed-cover-restriction-conservative] to the singleton cover $g$ of step 1
and $\Lambda=\underline A$. It is a statement about the actual ordinary unbounded module derived
category, with pullback identified with slice restriction. It therefore detects all isomorphisms
in that category, in particular morphisms between bounded constructible complexes. This avoids
using geometric stalks on arbitrary nonclassical pro-etale sheaves. The node is stated for the
sectionwise ringed-site inverse image of module sheaves; [lem-sfb-internal-module-operations-
transport] identifies that functor, through its exact equivalences $E_T$, with the actual module-
object pullback $G$, so the detection of isomorphisms transfers to $D(\operatorname{Mod}_{A_T})$.

4. Pass between actual internal module objects and section-ring module sheaves using [lem-sfb-
internal-module-operations-transport]; their pullbacks, direct images and open extensions,
including adjunction maps, are identified. For finite discrete $A$, [lem-sf-module-object-
ordinary-coefficient-equivalence] identifies the section ring with constant $A$, and preserves
constructibility, tensor and every Tor interval. The ordinary bounded etale/pro-etale comparison
is fully faithful by [thm-weil-pbc-site-comparison], essentially surjective on bounded
constructible complexes by [lem-weil-pbc-finite-ring-constructible-derived-origin], and preserves
and reflects finite Tor amplitude by [lem-sf-comparison-tor-amplitude]. The pullback and qcqs
direct-image comparisons of [sk-thm-pe-direct-image-comparison] identify these operations with
their etale counterparts, including units, counits and composition. The open comparison is
invertible by [lem-cbc-proetale-extension-zero-comparison] and has the canonical adjunction
normalization by [lem-sf-open-comparison-unit-normalization]; exactness lets us apply these
degreewise. Pasting the proper and open comparisons therefore identifies a compact-support word,
its exchange and its composition mates with the corresponding actual-module word on bounded
constructible finite-Tor objects. This follows also directly by taking the adjoints of the same
pulled-back unit/counit composites, whose maps are identified factor by factor.

5. Write $s_i=\operatorname{Spec}k_i$, $T_i=T\times_s s_i$, with $h_i:s_i\to s$, $g_i:T_i\to T$,
and $a_i:T_i\to s_i$. All these schemes are separated finite type over the finite field $k$. The
finite or algebraically closed field bounds [sk-lem-base-field-cd] allow [sk-thm-existence] for
$a,a_i,\bar a$; the coefficient unit is constant free of rank one, so
$W_T,W_i=a_i^!A_{s_i},W_{\bar T}$ belong to their constructible finite-Tor categories. The qcqs
base $s$ allows [sk-thm-nagata-compactification]; pull it back for all $a_i$ and $\bar a$. By
[det-prop-sf-cbc] their compact-support exchanges $\alpha_i:h_i^*Ra_!\simeq Ra_{i,!}g_i^*$ and
$\alpha:H Ra_!\simeq R\bar a_!G$ are invertible and respect pasting. Its finite-coefficient clause
applies because step 4 supplies bounded etale origins. In particular it applies to $W_T$. The
limit scheme $\bar T$ is finite type over $\bar k$, as required for its own exceptional adjoint;
it need not be finite type over $k$.

6. At a finite stage use the sum/evaluation adjunction for the etale finite-type maps $h_i,g_i$
from [lem-amb-etale-adjoint-locality]. Their compact supports are canonically the exact sum
functors by the etale clause of [lem-sfb-quasifinite-compact-support-exact]. They therefore give
$Rg_{i,!}\dashv g_i^*$ and $Rh_{i,!}\dashv h_i^*$ on the full constructible finite-Tor categories,
transported through step 4's equivalences. Composition [sk-thm-sf-comp-composition] gives,
naturally in $P\in\mathcal C_{T_i}$, $$\operatorname{Hom}(P,g_i^*W_T)\cong\operatorname{Hom}(Rg_{i
,!}P,W_T)\cong\operatorname{Hom}(Ra_!Rg_{i,!}P,A_s)\cong\operatorname{Hom}(Rh_{i,!}Ra_{i,!}P,A_s)\
cong\operatorname{Hom}(Ra_{i,!}P,A_{s_i})\cong\operatorname{Hom}(P,W_i).$$ The schemes are
Noetherian since they are finite type over a field, and step 5 supplied the compactifications for
these uses. All compact-support images remain constructible finite Tor by the composition theorem,
so every use of the exceptional adjunction [sk-thm-existence] is in its domain. Applying these
bijections and their inverses to identity maps, and then using naturality, constructs inverse
arrows and hence a unique isomorphism $b_i:g_i^*W_T\simeq W_i$.

7. Use the sum/evaluation normalization of the finite-etale reverse adjunction. Under step 4's
comparisons, [lem-pur-etale-horizontal-support-mate] says exactly that the compact-support
composition bijection in step 6 has transpose the inverse of the specified exchange $\alpha_i$.
Its schemes are Noetherian (finite type over a field), its horizontal arrows $h_i,g_i$ are
separated etale finite type, and the required compactifications were supplied in step 5. Step 6
used exactly these sum/evaluation adjunctions, so this is the same Hom bijection. Consequently
$b_i$ is the transpose of $$h_i^*(\epsilon_a)\circ\alpha_{i,W_T}^{-1}:Ra_{i,!}g_i^*W_T\to
A_{s_i},$$ that is, $\epsilon_{a_i}\circ Ra_{i,!}(b_i)=h_i^*(\epsilon_a)\circ\alpha_{i,W_T}^{-1}$.
Repeating the same adjunction calculation for $k_j/k_i$ and using pasting of exchange from step 5
proves compatibility of these representing bijections with transition pullbacks: both transposes
are $h_j^*\epsilon_a\circ\alpha_{j,W_T}^{-1}$. Equality follows from injectivity of the adjunction
Hom bijection, rather than from a choice of isomorphic endpoints.

8. Use [lem-sf-finite-etale-tower-constructible-descent] with $Y=T$ and $Y=s$. For $P\in\mathcal
C_{\bar T}$ choose $P\simeq q_i^*P_i$. Its Hom continuity, the compatible bijections of steps 6-7,
and compact-support base change of step 5 give
$$\begin{aligned}\operatorname{Hom}(P,GW_T)&\cong\varinjlim_{j\ge
i}\operatorname{Hom}(t_{ji}^*P_i,g_j^*W_T)\\&\cong\varinjlim_{j\ge
i}\operatorname{Hom}(Ra_{j,!}t_{ji}^*P_i,A_{s_j})\\&\cong\operatorname{Hom}(R\bar a_!P,A_{\bar
s})\cong\operatorname{Hom}(P,W_{\bar T}).\end{aligned}$$ For the last colimit, use $Ra_{i,!}P_i$
as the object on $s_i$ and identify its later pullbacks by the specified exchanges. All objects
used are in $\mathcal C$ by step 5. Object descent and descent of morphisms/equalities in the new
node make these bijections independent of the chosen model and natural in every $P$. Taking the
two identity morphisms in these natural bijections constructs inverse maps $GW_T\rightleftarrows
W_{\bar T}$. Denote the first by $w$. For $P=GW_T$, its model at $k$ is $W_T$, and the identity
represents the counit $\epsilon_a$. Thus the same chain sends $1_{GW_T}$ to
$H\epsilon_a\circ\alpha_{W_T}^{-1}$. The last adjunction sends $w$ to $\epsilon_{\bar a}\circ
R\bar a_!(w)$, proving exactly the required counit normalization.

9. Since $g$ is a site object, [lem-sfb-proetale-object-inverse-image-restriction] identifies its
constant-coefficient pullback with slice restriction. [lem-weil-pbc-ringed-internal-hom-exact-
restriction] gives an invertible derived Hom comparison for that restriction, without a
boundedness condition on either argument. [lem-sfb-module-object-ringed-site-derived-comparison]
identifies actual internal Hom with ringed-site Hom, compatibly with evaluation and restriction to
each slice. Therefore this comparison is precisely the transpose $\beta_{K,W_T}$ in the question:
their composites with evaluation agree after the canonical tensorator, and transposition is a
bijection. In particular $\beta_{K,W_T}$ is invertible for every stated $K$.

10. Set $c_K=R\mathcal Hom(1,w)\circ\beta_{K,W_T}$. Both factors are invertible by steps 8-9.
Transposition of $G(\mathrm{ev}_K)$ gives
$\mathrm{ev}_{GK,GW_T}\circ(\beta_{K,W_T}\otimes1)=G(\mathrm{ev}_K)$ with the tensorator inserted.
Naturality of evaluation in its target gives $\mathrm{ev}_{GK,W_{\bar T}}\circ(R\mathcal
Hom(1,w)\otimes1)=w\circ\mathrm{ev}_{GK,GW_T}$. Composing these equations proves the displayed
evaluation identity for $c_K$. Naturality of the tensor-Hom adjunction [det-def-sfb-derived-
tensor-hom] makes $c_K$ natural contravariantly in $K$.
-/
theorem finiteField_dualizing_pullback_data_exists
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (E : Type u) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a] :
    ∀ c : Compactification a,
      Nonempty (FiniteFieldDualizingPullbackData
        (constantModelBoundedConstructible (finiteFieldDualizingCoefficient ell E n).X T)
        (constantModelBoundedConstructible (finiteFieldDualizingCoefficient ell E n).X T ⊓
          DerivedCategory.finiteTorAmplitude _)
        (constantModelBoundedConstructible (finiteFieldDualizingCoefficient ell E n).X
          (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) ⊓
          DerivedCategory.finiteTorAmplitude _)
        (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
          (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
        (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (leftDerivedUpperStarUnitIso (finiteFieldDualizingCoefficient ell E n).X
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (finiteFieldDerivedBraiding (finiteFieldDualizingCoefficient ell E n) T)
        (finiteFieldDerivedBraiding (finiteFieldDualizingCoefficient ell E n)
          (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
        (detSfCompactSupport (finiteFieldDualizingCoefficient ell E n).X c)
        (detSfCompactSupport (finiteFieldDualizingCoefficient ell E n).X
          (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
        (detSfCompactSupportBaseChangeComposite (finiteFieldDualizingCoefficient ell E n).X
          a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c
          (compactSupportOpenBaseChangeIso (finiteFieldDualizingCoefficient ell E n).X
            a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c))) := by
  sorry

/-- Finite-field geometric pullback of dualizing objects and internal Hom.
Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: lem-sf-finite-field-dualizing-pullback).

Proof: the first conjunct is `finiteField_dualizing_pullback_triangulated`, the second is
`finiteField_dualizing_pullback_data_exists`, whose docstring carries the proof in words.
-/
theorem finiteField_dualizing_pullback
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hell : p ≠ ell)
    (k : Type u) [Field k] [Finite k] [CharP k p]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (E : Type u) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a] :
    (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
      (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).IsTriangulated ∧
    ∀ c : Compactification a,
      Nonempty (FiniteFieldDualizingPullbackData
        (constantModelBoundedConstructible (finiteFieldDualizingCoefficient ell E n).X T)
        (constantModelBoundedConstructible (finiteFieldDualizingCoefficient ell E n).X T ⊓
          DerivedCategory.finiteTorAmplitude _)
        (constantModelBoundedConstructible (finiteFieldDualizingCoefficient ell E n).X
          (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) ⊓
          DerivedCategory.finiteTorAmplitude _)
        (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
          (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
        (detSfDerivedPullback (finiteFieldDualizingCoefficient ell E n).X
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (leftDerivedUpperStarUnitIso (finiteFieldDualizingCoefficient ell E n).X
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (finiteFieldDerivedBraiding (finiteFieldDualizingCoefficient ell E n) T)
        (finiteFieldDerivedBraiding (finiteFieldDualizingCoefficient ell E n)
          (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
        (detSfCompactSupport (finiteFieldDualizingCoefficient ell E n).X c)
        (detSfCompactSupport (finiteFieldDualizingCoefficient ell E n).X
          (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
        (detSfCompactSupportBaseChangeComposite (finiteFieldDualizingCoefficient ell E n).X
          a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c
          (compactSupportOpenBaseChangeIso (finiteFieldDualizingCoefficient ell E n).X
            a (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) c))) := by
  refine ⟨finiteField_dualizing_pullback_triangulated p ell hell k kbar E n hn T a, ?_⟩
  intro c
  exact finiteField_dualizing_pullback_data_exists p ell hell k kbar E n hn T a c

end AlgebraicGeometry.ProEtale.CondensedRing
