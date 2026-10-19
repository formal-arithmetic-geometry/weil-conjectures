/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.LocallyConstantPerfectComplex
public import Sheaf.SixFunctors.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Paper.CondensedConstantConstructibility

import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.Paper.ConstantModelTorAmplitude
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.CoefficientHeartFiltration
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Paper.InternalHomDualConstructibleModels
import Sheaf.Paper.InternalHomDualTorAmplitude
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.Paper.IntegralConstructibleHeart
import Sheaf.Paper.IntegralHeartLocalModel
import Sheaf.SixFunctors.CtfStabilityDirectImages

/-!
# Internal Hom stability on constructible finite-Tor complexes

Source: blueprint main-20261015, sec-six-functors-basics/
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom`
(blueprint: det-thm-sf-ctf-stability-internal-hom).

The theorem states closure of the constructible finite-Tor category under the relative derived
internal Hom, its locally closed generator formula, and finite-cone generation.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonObj Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient unbounded relative module derived category.
Source: sk-def-sfb-derived-tensor-hom (blueprint: det-thm-sf-ctf-stability-internal-hom). -/
abbrev moduleDerived (T : Scheme.{u}) :=
  DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))

/-- The object property defining the recorded full subcategory Dctf; this abbreviation
expands its exact predicate, with constant scalar constructibility and ambient Tor amplitude.
Source: sk-def-sfb-constructible (blueprint: det-thm-sf-ctf-stability-internal-hom). -/
abbrev dctfPred (T : Scheme.{u}) : ObjectProperty (moduleDerived Λ T) :=
  constantModelBoundedConstructible Λ T ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K


/-- Ambient derived internal Hom object.
Source: blueprint internal-Hom stability statement
(blueprint: det-thm-sf-ctf-stability-internal-hom). -/
noncomputable abbrev internalHomObj (T : Scheme.{u})
    (P Q : moduleDerived Λ T) : moduleDerived Λ T :=
  ((CondensedRing.derivedHom Λ T).obj (Opposite.op P)).obj Q

/-- The dual-tensor expression in the locally closed formula.
Source: blueprint internal-Hom stability statement
(blueprint: det-thm-sf-ctf-stability-internal-hom). -/
noncomputable abbrev dualTensorObj (T : Scheme.{u}) (P H : moduleDerived Λ T) :
    moduleDerived Λ T :=
  ((CondensedRing.derivedTensor Λ T).obj
    (relativeInternalHomDual (Mon.mk Λ) T P)).obj H

/-- Derived extension by zero for a chosen locally closed factorization.
Source: blueprint `det-thm-sf-ctf-stability-internal-hom`, extension-by-zero convention
(blueprint: det-thm-sf-ctf-stability-internal-hom). -/
noncomputable def locallyClosedExtension {S Sbar X : Scheme.{u}}
    (u : S ⟶ Sbar) (i : Sbar ⟶ X) (hu : IsOpenImmersion u)
    (hi : IsClosedImmersion i) : moduleDerived Λ S ⥤ moduleDerived Λ X :=
  letI := hu
  letI := hi
  CondensedRing.openImmersionLowerShriek Λ u |>.mapDerivedCategory ⋙
    (CondensedRing.lowerStar Λ i).rightDerivedFunctor

/-- The actual extension-by-zero functor restricted to the localizing closures. The
membership argument affects only the full-subcategory property, not its objects or arrows.
A right adjoint to this functor is a^!, by sk-prop-sf-existence and uniqueness of adjoints.
Source: internal-Hom stability proof, formula paragraph
(blueprint: det-thm-sf-ctf-stability-internal-hom). -/
noncomputable def localizingLocallyClosedExtension {S Sbar X : Scheme.{u}}
    (u : S ⟶ Sbar) (i : Sbar ⟶ X) (hu : IsOpenImmersion u) (hi : IsClosedImmersion i)
    (h : ∀ N, localizingClosureProEtale Λ S N → localizingClosureProEtale Λ X
      ((locallyClosedExtension Λ u i hu hi).obj N)) :
    (localizingClosureProEtale Λ S).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ S).ι ⋙ locallyClosedExtension Λ u i hu hi)
    (fun N ↦ h N.obj N.property)

/-- The generator family occurring in the finite dévissage clause.
Source: blueprint internal-Hom stability, finite generator convention
(blueprint: det-thm-sf-ctf-stability-internal-hom). -/
def internalHomGenerator (X : Scheme.{u}) : ObjectProperty (moduleDerived Λ X) :=
  fun K ↦ ∃ (S Sbar : Scheme.{u}) (u : S ⟶ Sbar) (i : Sbar ⟶ X),
    ∃ (hu : IsOpenImmersion u) (hi : IsClosedImmersion i),
      ∃ P : moduleDerived Λ S,
        IsLocallyConstantPerfectComplex Λ S P ∧
        Nonempty (K ≅ (locallyClosedExtension Λ u i hu hi).obj P)

/-- Internal Hom on Dctf, its locally closed formula, and finite-cone generation.
Source: blueprint main-20261015, sk-thm-sf-ctf-stability-internal-hom, full statement
(blueprint: det-thm-sf-ctf-stability-internal-hom).

The right adjoint is specified by an adjunction to the actual extension on the recorded
localizing closures. It is therefore precisely a^!, unique up to adjunction-compatible
isomorphism, rather than an arbitrary ambient object substituted in the formula.
The last clause uses the intersection of all replete triangulated subcategories containing
the generators: this is exactly finite shifts and cones, without adjoining retracts.

Proof, following every step of the DAG node:
1. The scheme and coefficient conventions are [sk-def-sfb-dc-setting] and
[sk-def-localizing-closure]. A field is Noetherian (its only ideals are zero and the unit
ideal), so [lem-weil-pbc-finite-type-over-noetherian] makes all standing schemes Noetherian,
hence qcqs; their open subsets are quasi-compact. The coefficient pullbacks are exact and
identify the inverse-image coefficient rings by [sk-prop-sfb-cartesian-coefficients]. We will
use only the relative module-sheaf operations over these rings, including the completed integral
coefficient sheaf, never tensor over the discrete scalar field in place of the condensed field.
2. The categories $\Dctf$ are triangulated. For finite $A$, constructible sheaves are weak Serre
by [lem-sfb-discrete-noetherian-constructible-serre], so
[prop-weil-pbc-module-bounded-constructible-triangulated], with coefficient category $\Ab$ and
ring object $A_X$, makes $\Dbc$ triangulated. For integral coefficients use
[sk-lem-int-integral-heart](1), and for rational coefficients use
[det-cor-coefficient-heart-ii-triangulated]. Finally [det-def-sfb-constructible-tor-amplitude]
makes finite Tor amplitude thick and identifies $\Dctf$ with its intersection with $\Dbc$. These
facts give closure under zero, isomorphisms, finite cones and shifts in every coefficient case.
3. We spell out the finite stratification dévissage used below. By the geometric clause (1) of
[det-lem-coefficient-heart-common-stratification], any given finite locally closed
stratification can be refined and ordered $S_1,\ldots,S_m$ with $V_r=S_1\cup\cdots\cup S_r$
open. This clause is independent of its auxiliary coefficient $E$ or $\Qlb$; fix $E=\mathbf
Q_\ell$ when applying it even to finite or integral coefficient objects. For a complex $C$
adapted to these strata, let $v_r:V_r\hookrightarrow X$ and put $C_r=v_{r!}v_r^*C$ on $X$. Apply
the short exact open--closed sequence of [lem-weil-pbc-proetale-ringed-open-closed] termwise on
$V_r$ to its open $V_{r-1}$ and closed complement $S_r$. Exact extension by zero gives a
degreewise short exact sequence $0\to C_{r-1}\to C_r\to a_{r!}(C|_{S_r})\to0$. The corresponding
derived triangle is [lem-weil-pbc-complex-ses-triangle]. The composition and factorization
identifications, including agreement of closed-then-open with open-then-closed extension, are
precisely [lem-sfb-locally-closed-extension-coherence]. With $C_0=0$ and $C_m=C$, induction on
$r$ expresses $C$ as finite cones of the displayed pieces. Exactness also shows that the same
construction applies to any representing complex, independently of its representative.
4. For finite $A$, use [det-pe-finite-tor-comparison-noetherian] to descend $K$ to an étale
bounded constructible finite-Tor complex, and choose an ordered Tor interval $[a,b]$. The finite
ring $A$ is Noetherian, since each ideal is a finite set of generators. By
[lem-sf-etale-flat-constructible] choose a bounded complex $F$ of flat constructible sheaves
representing the descent. On a common finite stratification of the étale terms
[lem-weil-pbc-constructible-stratification-intersection], each term has a finite locally
constant $A$-module model. Check its flatness on the étale site, before pulling back: for a
geometric point $x$ of the stratum and any scalar $A$-module $M$, apply
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the geometric-point inverse image and
$F^r\otimes_A^{\mathbf L}\underline M$. Exactness of the étale stalk functor
[prop-weil-pbc-geometric-stalks-exact] and flatness of $F^r$ imply that $F^r_x\otimes_A^{\mathbf
L}M$ is concentrated in degree zero. Thus the scalar model $F^r_x$ is flat. It is finitely
presented: it is finite, and the kernel of a finite free surjection onto it is finitely
generated by [lem-weil-pbc-noetherian-submodule-finite]. Now
[lem-weil-pbc-finitely-presented-flat-module-projective] makes this model finite projective.
Pull $F$ back exactly to the pro-étale site. Its étale local constant models give pro-étale
local constant models on the same strata. Apply Step 3 to each of the finitely many terms. Each
term is consequently obtained by finite cones of sheaves $a_!P$ with $P$ locally constant finite
projective in degree zero. The stupid truncations of the bounded complex $F$ have degreewise
split short exact successive sequences with quotients $F^r[-r]$;
[lem-weil-pbc-complex-ses-triangle] supplies their triangles. Induction through its finitely
many nonzero degrees proves the required finite-cone-and-shift generation of $K$. In particular
this does not replace a finite-Tor complex by its cohomology sheaves.
5. For $\Lambda=\mathcal O_E$, clause (1) of [det-lem-int-integral-heart-local-model] gives a
finite stratification on which $K$ is pro-étale locally the completed scalar extension of a
bounded complex of finite free $\mathcal O_E$-modules. Thus each restriction is a locally
constant perfect complex in the statement's sense. Apply Step 3 directly to $K$ on this
stratification, giving finitely many pieces $a_!(K|_S)$ and no retract operation. The case
$\mathbf Z_\ell$ is $E=\mathbf Q_\ell$. For $\Lambda=E$ or $\Qlb$,
[det-lem-coefficient-heart-filtration] gives a finite filtration of each constructible
cohomology sheaf by $a_!P$ with $P$ lisse finite free, hence perfect in degree zero. Since $K$
is bounded, finitely many truncation triangles [lem-pc-derived-lower-truncation-step-triangle],
followed by the triangles of these sheaf filtrations [lem-weil-pbc-complex-ses-triangle],
express $K$ by finite cones and shifts of those pieces. This includes $\mathbf Q_\ell$ and
proves the generation clause at every stage.
6. By [lem-sfb-ringed-site-perfect-duality], $P^\vee$ is perfect and $\cHom_S(P,N)\simeq
P^\vee\otimes^{\mathbf L}N$ for every ambient $N$. The slice-restriction assertion of
[lem-weil-pbc-ringed-internal-hom-exact-restriction] identifies its restrictions with the duals
of the local models. The scalar-cohomology formulas of
[lem-sfb-internal-hom-dual-constructible-models] apply to the locally constant perfect models in
the statement and put both $P$ and $P^\vee$ in $\Dbc(S,\Lambda)$, including completed integral
coefficients. Finite Tor amplitude is established separately in Step 7.
7. Apply [lem-sfb-internal-hom-dual-tor-amplitude] to the same local scalar models. It gives a
single interval $[a,b]$ for $P$ and $[-b,-a]$ for $P^\vee$, tested against every module sheaf;
for empty $S$ it gives $[0,0]$. Together with the bounded-constructibility conclusion of Step 6
and the definition [sk-def-sfb-constructible], this proves $P,P^\vee\in\Dctf(S,\Lambda)$. This
uses no finite global dimension assumption on a finite coefficient ring.
8. Let $a:S\hookrightarrow X$ be as in the statement. By
[lem-pqf-qc-immersion-open-closed-factor], write it $S\xrightarrow{u}Z\xrightarrow{i}X$ with $u$
open and $i$ closed, and let $j:X\setminus Z\hookrightarrow X$ be the complementary open. Put
$T=u^*R\underline\Gamma_ZL$, using the ambient derived support adjoint of
[det-lem-formal-closed-support-adjunction]. Its fiber formula is $R\underline\Gamma_ZL\simeq
i^*\operatorname{fib}(L\to Rj_*j^*L)$. Each of $j^*$, $Rj_*$ and $i^*$ preserves $\Dctf$ by
[det-thm-sf-ctf-stability-direct-images](1),(3). Step 2 therefore puts this fiber and then
$R\underline\Gamma_ZL$ in $\Dctf$, and the same node's pullback clause puts $T$ in
$\Dctf(S,\Lambda)$. This establishes support preservation without inferring it from existence of
a right adjoint.
9. The closed immersion $i$ is proper by [lem-weil-pbc-closed-immersion-proper](a), so $(u,i)$
is a compactification of $a$. It computes $Ra_!=Ri_*u_!=i_*u_!=a_!$, because $i_*$ and $u_!$ are
exact [lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-exact-functor-derived-functor];
this is the compactification formula of [sk-def-sfb-module-derived-lower-shriek]. Its comparison
with the chosen compactification on the localizing closure is [det-sf-comp-coherence-cocycle].
For any $B\in\Loc(\Dctf(S,\Lambda))$, the ambient adjunction $i_*\dashv R\underline\Gamma_Z$
[det-lem-formal-closed-support-adjunction], followed by the ambient derived open adjunction
$u_!\dashv u^*$ [def-sfb-dc-open-lower-shriek-adjunction], gives
$\Hom_X(a_!B,L)\cong\Hom_S(B,T)$. By [sk-prop-sf-existence], the same functor is represented by
$a^!L$. Both representing objects lie in the full localizing closure: $T$ by Step 8, and $a^!L$
by its definition. Transpose each counit under the other adjunction; the two resulting maps
$T\rightleftarrows a^!L$ compose to the identities by the adjunction triangle identities. Thus
$T\simeq a^!L$, naturally in $L$. This comparison tests only objects of the localizing closure,
where that adjunction is actually defined.
10. Now apply the ambient internal-Hom formulas of [lem-sfb-open-closed-internal-hom-formulas],
first to $i$ and then to $u$ with target $R\underline\Gamma_ZL$. They give
$$\cHom_X(i_*u_!P,L)\simeq i_*\cHom_Z(u_!P,R\underline\Gamma_ZL)\simeq
i_*Ru_*\cHom_S(P,u^*R\underline\Gamma_ZL).$$ The ringed-topos composition comparison
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], with exact $i_*$, identifies
$i_*Ru_*=Ra_*$. Step 9 replaces $u^*R\underline\Gamma_ZL$ by $a^!L$. We obtain the first stated
isomorphism in the entire ambient $D(X_{\mathrm{proét}},\Lambda)$, naturally in $P,L$. Unlike a
calculation of global Hom alone, the cited formulas are identities of internal sheaf-valued
derived Hom, without constructibility assumptions.
11. Step 6 with $N=a^!L$ gives the second isomorphism after applying $Ra_*$. Steps 8 and 9 give
$a^!L\in\Dctf$, and Steps 6 and 7 give $P^\vee\in\Dctf$. The tensor and direct-image clauses of
[det-thm-sf-ctf-stability-direct-images](1),(3) therefore show that $Ra_*(P^\vee\otimes^{\mathbf
L}a^!L)$ belongs to $\Dctf(X,\Lambda)$. By Step 10 this is $\cHom_X(a_!P,L)$, proving membership
for every generator and both displayed isomorphisms.
12. Fix $L$. By [lem-weil-pbc-ringed-internal-hom-exact-restriction], $\cHom(-,L)$ sends
distinguished triangles contravariantly to distinguished triangles and commutes with shifts with
the opposite sign. Step 2 therefore shows that the objects $B$ for which $\cHom(B,L)\in\Dctf$
form a full triangulated class: a triangle with two vertices satisfying the property has the
third by the image triangle. It contains all $a_!P$ by Step 11. The finite constructions of
Steps 3--5 now prove the property for every $K\in\Dctf$. Only finitely many cones and shifts
have been used, exactly as asserted.
-/
theorem internalHom_stability
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (K L : moduleDerived Λ X)
    (_hK : dctfPred Λ X K)
    (_hL : dctfPred Λ X L) :
    dctfPred Λ X (internalHomObj Λ X K L) ∧
      (∀ (S Sbar : Scheme.{u}) (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X),
        (hu : IsOpenImmersion u) → (hi : IsClosedImmersion i) → a = u ≫ i →
        ∀ (P : moduleDerived Λ S), IsLocallyConstantPerfectComplex Λ S P →
          ∃ (h : ∀ N, localizingClosureProEtale Λ S N → localizingClosureProEtale Λ X
                ((locallyClosedExtension Λ u i hu hi).obj N))
            (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
              (localizingClosureProEtale Λ S).FullSubcategory),
            Nonempty (localizingLocallyClosedExtension Λ u i hu hi h ⊣ G) ∧
            ∃ N : (localizingClosureProEtale Λ X).FullSubcategory,
              N.obj = L ∧
              Nonempty (internalHomObj Λ X ((locallyClosedExtension Λ u i hu hi).obj P) L ≅
                (CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj
                  (internalHomObj Λ S P (G.obj N).obj)) ∧
              Nonempty ((CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj
                  (internalHomObj Λ S P (G.obj N).obj) ≅
                (CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj
                  (dualTensorObj Λ S P (G.obj N).obj))) ∧
      ∀ K' : moduleDerived Λ X, dctfPred Λ X K' →
        ∀ Q : ObjectProperty (moduleDerived Λ X),
          Q.IsTriangulated → Q.IsClosedUnderIsomorphisms →
            (∀ J : moduleDerived Λ X, internalHomGenerator Λ X J → Q J) → Q K' := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
