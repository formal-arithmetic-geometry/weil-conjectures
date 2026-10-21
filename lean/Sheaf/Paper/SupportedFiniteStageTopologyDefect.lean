/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ConstructibleAlgClTopologyComparison
public import Sheaf.Paper.CoefficientHeartFiltration
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import Sheaf.Paper.CondensedOpenClosedRecollement

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.Paper.FiniteSubextensionsDirected
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.ClosedSupportedScalarComparison
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.Paper.ConstructibleInternalHomContinuity
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction

/-!
# Supported finite-stage local systems and the scalar-unit topology defect

Source: blueprint main-20261015, six-functors direct-image stability proof,
paragraph (3), explicit agent coefficient-topology obligation
(blueprint: lem-sfb-supported-finite-stage-topology-defect).

C is the finite-subextension-valued condensed ring and B is the full norm-continuous
condensed ring. The existing inclusion and derived scalar adjunction are used unchanged.
The supported objects are constructed by exact termwise extension through their closures.
The theorem is only a statement: its proof remains postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The specified object a_!(C_S tensor^L_{A_E,S} L[0]), using the canonical
scheme-theoretic closure factorization already defining
`coefficientHeartLocallyClosedExtension`. No lisse hypothesis is needed to construct it.
Source: blueprint direct-image stability proof (3), supported finite-stage
scalar-unit defect obligation, displayed definition of G (and independently H)
(blueprint: lem-sfb-supported-finite-stage-topology-defect).

Finite type over the field supplies the Noetherian structures by the recorded Mathlib
lemmas. Exactness of the closed factor is the proof-irrelevant witness in the recorded
recollement theorem. Only that property is selected, never a functor or an object.
The exact composite is localized termwise using `mapDerivedCategory`, after applying
the existing K-flat derived scalar extension to the degree-zero complex. -/
def supportedFiniteStageTopologyObject (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {S : Scheme.{u}} (a : S ⟶ X.left) (ha : IsImmersion a)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := ⟨⟩
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  letI : PreservesFiniteColimits
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι) :=
    (CondensedRing.condensed_open_closed_recollement (Profinite.padicAlgClRingObj ℓ)
      a.imageι (Scheme.openComplementOfIsClosedImmersion a.imageι).ι
      (Scheme.Opens.range_ι _)).choose
  letI : PreservesFiniteLimits
      (coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ) a ha) :=
    inferInstanceAs (PreservesFiniteLimits
      (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) a.toImage ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι))
  letI : PreservesFiniteColimits
      (coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ) a ha) :=
    inferInstanceAs (PreservesFiniteColimits
      (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) a.toImage ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι))
  letI : (coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ) a ha).Additive :=
    Functor.additive_of_preserves_binary_products _
  ((coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ)
    a ha).mapDerivedCategory).obj
      (((Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) S)
          ).leftDerivedFunctor).obj ((DerivedCategory.singleFunctor _ 0).obj L))

/-- Two independently supported finite-stage lisse modules are left orthogonal to
every shift of every cone of the specified derived scalar adjunction unit.
`Subsingleton` says precisely that the Hom group is zero: its existing zero morphism
supplies an element. The algebraic closure is the fixed model `PadicAlgCl` used by the
recorded coefficient definitions, with its extended ell-adic norm.

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
agent supported finite-stage scalar-unit defect obligation
(blueprint: lem-sfb-supported-finite-stage-topology-defect).

Proof plan (exact literature proof WANTED; HRS Lemma 7.9 only treats C):
1. Pass to the small-site section-ring model using [lem-pd-module-ringed-topos-derived-comparison]
and [lem-sfb-internal-section-scalar-adjunction]. The first identifies the specified derived
tensors and exact open extension; closed internal Homs are identified by uniqueness of their right
adjunctions. The second identifies scalar extension/restriction AND their actual units, including
$v\mapsto1\otimes v$; thus this passage does not change the triangle in the assertion. A field is
Noetherian (its only ideals are zero and itself); hence $X$ is Noetherian by [lem-weil-pbc-finite-
type-over-noetherian]. Every open in $X$ is quasi-compact by [lem-weil-pbc-noetherian-open-
subscheme-noetherian]. Closed subschemes are Noetherian too: on a Noetherian affine their rings
are quotients, whose ascending chains of ideals lift to chains of ideals upstairs, and closed
subsets of a Noetherian space are quasi-compact. These observations apply also to the closures
used to define $a_!,b_!$.

2. Take the finite compositum $E_0=EF\subset\Omega$ by [det-def-sfb-qlbar-condensed-
subextensions], and write $A_V=A_{E_0,V}$. Extend $L,M$ on their respective supports to
$L_0=A_S\otimes_{A_{E,S}}L$ and $M_0=A_T\otimes_{A_{F,T}}M$. These are ordinary degree-zero
modules: finite-field scalar extension is exact by [lem-sfb-subfield-flat]. They are lisse: pull
back to the covers trivializing $L,M$; [lem-sfb-kflat-scalar-comparison-normalization] identifies
the pullbacks of these tensors with the tensors of the pullbacks, hence with $A^r,A^s$. Define
$K=(a_!L_0)[0]$, $N=(b_!M_0)[0]$ in $D(A_X)$. They are bounded constructible by [lem-sfb-
coefficient-heart-lisse-extension-constructible], since $X$ is Noetherian. The two supports and
ranks have not been identified.

3. Scalar extension along each coefficient map used here commutes with $a_!$ and $b_!$. For their
open factors this is [lem-sf-open-tensor-normalization], with the identity geometric map and the
given change of rings. For the closed factors use [lem-sfb-closed-supported-scalar-comparison]
with inverse-image comparisons [lem-sfb-kflat-scalar-comparison-normalization]. Its unbounded-
calculus hypothesis follows from [lem-weil-pbc-condensed-open-closed-recollement] and [lem-sfb-
exact-open-closed-unbounded-calculus]: all four sheaf functors are exact; the open unit and closed
counit are isomorphisms; the mixed restrictions are zero by extension by zero and disjoint
supports. Applying the first recollement triangle to a degree-zero sheaf gives the required short
exact sequence $0\to j_!j^*M\to M\to i_*i^*M\to0$. Complements are quasi-compact by step 1. Thus
the cited unbounded calculus applies, without assuming that the scalar extensions are bounded or
flat. The resulting closed comparison is linear over the new coefficient ring, with the precise
counit normalization of that node.

4. For $R=C_X,B_X$ put $S_R(V)=R\otimes_{A_X}^L V$. Apply step 3 first to $E\to E_0\to C$ on $S$,
and to $F\to E_0\to C$ on $T$. The scalar reassociations of [lem-sfb-successive-derived-quotient-
normalization] give $G\simeq S_CK$, $H\simeq S_CN$. Applying the same reassociation to $A_X\to
C_X\to B_X$ gives $J_XG\simeq S_BK$, $J_XH\simeq S_BN$. All identifications are natural, and the
cited reassociation takes successive scalar units to the direct unit, by $(v\otimes z)\otimes
w\mapsto v\otimes c(z)w$. We may therefore make these identifications when computing the actual
scalar-extension map on morphisms.

5. Put $D=R\mathcal Hom_{A_X}(K,N)$. The predicate comparison [lem-sfb-adic-constructibility-
predicate-comparison] for the field $E_0$ on the Noetherian $X$ shows that $K,N$ are bounded
constructible in the stratified local-finite-presentation sense. So $D$ is bounded constructible
in that sense by [lem-sfb-dc-hom-preserves], applied to $E_0$ in the standing setting. By the same
comparison $D$ also has finite constant local models. The complex $K$ has the internal filtered-
colimit continuity property of [lem-sfb-constructible-internal-hom-continuity]: $X$ is Noetherian
and $K$ has the finite constant local model from step 2. Since $N$ is degree zero, it is bounded
below. Consequently [lem-sfb-qlbar-internal-hom-coefficient-comparison] gives the evaluation-
transpose isomorphism $\phi_C:S_CD\simeq R\mathcal Hom_{C_X}(S_CK,S_CN)$. Independently, [lem-sfb-
norm-algcl-internal-hom-base-change] gives the evaluation-transpose isomorphism $\phi_B:S_BD\simeq
R\mathcal Hom_{B_X}(S_BK,S_BN)$. This second input is about the norm coefficient ring, so it is
not inferred from the colimit-coefficient result.

6. Apply [lem-sfb-norm-algcl-cohomology-topology-comparison] to the bounded constructible
$A_X$-complex $D$ from step 5. It makes the actual map $R\Gamma(m_D):R\Gamma(S_CD)\to
R\Gamma(S_BD)$ invertible. Under $\phi_C,\phi_B$ this is the morphism on derived global Hom
induced by $J_X$. Indeed both evaluation transposes are scalar extension of the same evaluation
$D\otimes_{A_X}^L K\to N$. Reassociating balanced tensors, their evaluations after $c_X$ agree:
both are $B_X\otimes_{A_X}^L(D\otimes_{A_X}^L K)\xrightarrow{1\otimes\mathrm{ev}}S_BN$. The
defining tensor/internal-Hom adjunction [sk-def-sfb-derived-tensor-hom] makes the transpose
unique. Thus this equality identifies the actual map, including its naturality in arrows, rather
than merely identifying its endpoints. Derived global sections of a $C_X$- or $B_X$-complex agree
with those of its restriction to $A_X$: by [lem-pur-sheaf-ring-derived-coefficient-adjunction]
applied to $A_X\to R$ and the unit $R$ itself,
$\operatorname{Hom}_{D(R)}(R,M[n])=\operatorname{Hom}_{D(A_X)}(A_X,M[n])$. Taking degree-$n$
cohomology and using [lem-sfb-derived-internal-hom-sections-model] yields a bijection $u\mapsto
J_Xu$ from $\operatorname{Hom}_{D(C_X)}(G,H[n])$ to $\operatorname{Hom}_{D(B_X)}(J_XG,J_XH[n])$
for every integer $n$. The module equivalences in step 1 preserve these constructions and
underlying abelian sheaves.

7. Use [lem-pur-sheaf-ring-derived-coefficient-adjunction] for $c_X:C_X\to B_X$. The right adjoint
is exact restriction, and the normalized derived unit is exactly the one in the statement. The
adjunction sends $J_Xu:J_XG\to J_XH[n]$ to $U_XJ_Xu\circ\eta_G=\eta_{H[n]}\circ u$ by naturality
of the unit. Since these exact derived functors and their units commute with shifts, this is
$\eta_H[n]\circ u$. Composing with the bijections from step 6 therefore shows that the maps
$\operatorname{Hom}(G,H[n])\xrightarrow{\eta_H[n]\circ-}\operatorname{Hom}(G,U_XJ_XH[n])$ are
bijections for all integers $n$. This step uses no flatness of $c_X$.

8. Let the triangle in the assertion be arbitrary and let $q:G\to Q_H[n]$. By [lem-weil-pbc-hom-
into-triangle-exact] applied also to the shifted and rotated distinguished triangles [def-weil-
triangulated-category], its boundary $dq:G\to H[n+1]$ is killed by $\eta_H[n+1]$. Step 7 makes
that map on Hom injective, so $dq=0$. Exactness at $Q_H[n]$ gives $q=vh$ for some $h:G\to
U_XJ_XH[n]$. Surjectivity in step 7 writes $h=\eta_H[n]u$; consecutive triangle arrows compose to
zero, so $q=v\eta_H[n]u=0$. Thus every element of the asserted Hom group is zero. Nothing depended
on a chosen cone, a nonempty support, a positive rank, or a relation between $S,T$ or $E,F$, so
the asserted edge cases are included. -/
theorem supported_finiteStage_topology_defect
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (S T : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (haCons : Topology.IsConstructible (Set.range a))
    (b : T ⟶ X.left) (hb : IsImmersion b)
    (hbCons : Topology.IsConstructible (Set.range b))
    (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S))
    (hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj F) T))
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj F) M)
    (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (v : ((Mod.comap (coefficientMap (algClTopologyInclusion ℓ) X.left)).mapDerivedCategory).obj
          ((algClTopologyScalarExtension ℓ X.left).obj
            (supportedFiniteStageTopologyObject ℓ X b hb F M)) ⟶ Q)
    (w : Q ⟶ (supportedFiniteStageTopologyObject ℓ X b hb F M)⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (algClTopologyInclusion ℓ) X.left)).unit.app
          (supportedFiniteStageTopologyObject ℓ X b hb F M)) v w ∈ distTriang _)
    (n : ℤ) :
    Subsingleton (supportedFiniteStageTopologyObject ℓ X a ha E L ⟶ Q⟦n⟧) := by
  sorry

end AlgebraicGeometry.ProEtale
