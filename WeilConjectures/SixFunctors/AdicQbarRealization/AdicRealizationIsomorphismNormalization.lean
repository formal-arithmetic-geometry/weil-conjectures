/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
public import WeilConjectures.SixFunctors.Sf.SfQbarLocalizationCommonStage

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicRealizationData

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicFiniteNormalization

import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingCore
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingFunctoriality
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingTensor
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingHom
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalization of isomorphism reindexing for adic realization

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach,
Lemma 7.9 (blueprint: lem-sf-adic-realization-isomorphism-normalization).

The conclusion constructs the existing `Family` package for the given realizations.
It retains their exact objectwise data and supplies the comparison maps,
coefficient transitions, tensorator, coefficient unit, evaluation-transpose Hom map,
and identity/composition laws, together with the actual mixed scalar square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.AdicQbarRealization

/-- Transport full faithfulness and essential image through the exact section equivalence. -/
private def spaceDataOfPresentation
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : GeometricSpace D)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (P : (sectionFunctor l T.base.left R).IsEquivalence)
    (A : letI := fun x ↦
          sfQbarLocalizationResidueInvertible l D hl T.base.left T.base.hom x
      At l T.base.left R)
    (N : ∀ E, letI := fun x ↦
             sfQbarLocalizationResidueInvertible l D hl T.base.left T.base.hom x
      FiniteNormalization l T.base.left R A E)
    (H : letI := fun x ↦
          sfQbarLocalizationResidueInvertible l D hl T.base.left T.base.hom x
      HomLaws l T.base.left R A) : SpaceData l D T := by
  letI := fun x ↦ sfQbarLocalizationResidueInvertible l D hl
    T.base.left T.base.hom x
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  letI := P
  letI : (LocallyFiniteAdicRealization.sections l T.base.left).IsEquivalence := P
  letI := R.shift
  letI := R.triangulated
  refine
    { realization := R
      presentation := P
      shift := (inferInstance : (R.J ⋙
        (LocallyFiniteAdicRealization.sections l T.base.left).mapDerivedCategory).CommShift ℤ)
      exact := (inferInstance : (R.J ⋙
        (LocallyFiniteAdicRealization.sections l T.base.left).mapDerivedCategory).IsTriangulated)
      fully_faithful := ?_
      image := ?_
      tensor := A
      finite := N
      hom := H }
  · intro K L
    let F := (LocallyFiniteAdicRealization.sections l T.base.left).mapDerivedCategory
    exact Function.Bijective.comp (g := F.map) (f := R.J.map)
      ⟨F.map_injective, F.map_surjective⟩ (R.fully_faithful K L)
  · intro K
    constructor
    · rintro ⟨L, hL, ⟨e⟩⟩
      obtain ⟨M, ⟨i⟩⟩ := (R.image L).mp hL
      exact ⟨M, ⟨((sectionDerived l T.base.left R).mapIso i) ≪≫ e⟩⟩
    · rintro ⟨M, ⟨e⟩⟩
      exact ⟨R.J.obj M, (R.image _).mpr ⟨M, ⟨Iso.refl _⟩⟩, ⟨e⟩⟩

/-- The normalized comparison package for arbitrary scheme isomorphism reindexing.

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9
(blueprint: lem-sf-adic-realization-isomorphism-normalization).

The given realization at each space comes with its section-module equivalence `P` and the
naturality, evaluation and transpose laws `H` of its Hom map; these are the established
properties of the fixed realization and are not part of the reindexing assertion. The
remaining fields of `SpaceData` (exactness, full faithfulness, essential image) follow from
`R` and `P`; the conclusion constructs only the reindexing comparisons and their laws.

Step 1. Write $G_g$ for inverse-image reindexing. The site-equivalence theorem identifies its
sections at $(V\to T)$ with sections at $(V\to T\xrightarrow gU)$ and makes it exact and
limit/colimit preserving. Apply its coefficient naturality to every finite quotient and
transition. Taking the inverse images of the limit projections gives $G_gB_{E,U}\simeq B_{E,T}$
with $\pi_n c_E=c_{E,n}G_g\pi_n$. The pulled-back condensed coefficient theorem and its
limit/localization identifications give compatible identifications of $G_gE_U$ and $G_gR_U$ with
$E_T$ and $R_T$. Thus all coefficient inclusions, quotient projections and balanced actions in
the question are preserved. None of these results requires $g$ to be a $k$-morphism.
Dependencies: lem-weil-proetale-isomorphism-inverse-image, sk-prop-sfb-cartesian-coefficients,
sk-prop-sfb-qlbar-colimit-x.

Step 2. The tensor/Hom reindexing theorem makes $G_g$ a symmetric monoidal equivalence on
completed-ring modules. The exact-monoidal-equivalence theorem therefore preserves flat terms,
K-flat complexes, quasi-isomorphisms and signed total tensor maps. Apply it to the flat-term
K-flat representatives used in the specified operations. On the quotient tower its comparison is
termwise reindexing; on the product mapping fiber it applies the product comparison on BOTH
coordinates. A strict quotient coaugmentation $(0,(q_n(x))_n)$ is sent to $(0,(G_gq_n(x))_n)$,
since reindexing preserves zero. The completion-unit normalization theorem identifies this
entire-cone map with the specified $\kappa^g_K:G_gK\to Lg^*K$ and proves it invertible for
derived-complete $K$. Its naturality theorem supplies naturality for all derived morphisms. This
fixes the integral comparison, without replacing $\kappa$ by an arbitrary isomorphism with the
same reductions. Dependencies: lem-pur-isomorphism-inverse-image-tensor-hom,
lem-sfb-exact-monoidal-equivalence-total-kflat,
lem-weil-isomorphism-derived-pullback-comparison-normalization,
lem-weil-isomorphism-comparison-natural.

Step 3. For an integral constructible representative $K$ over $E$ define $b_{g,E,K}$ as the
composite $$R_T\otimes^L_{B_{E,T}}
Lg^*K\xrightarrow{1\otimes(\kappa^g_K)^{-1}}
R_T\otimes^L_{B_{E,T}}G_gK\xrightarrow{\sim}G_g(R_U\otimes^L_{B_{E,U}}K).$$
The last arrow is balanced tensor reindexing.
Associating
$R_W\otimes^L_{E_W}(E_W\otimes^L_{B_{E,W}}K)$ with $R_W\otimes^L_{B_{E,W}}K$ identifies this
with the requested component. The signed total-tensor coherence theorem gives this association
and its natural chain maps on the same K-flat models. Each arrow is invertible and natural.
Integral pullback preserves constructibility by the isomorphism-pullback theorem. On the target,
reindex a finite locally closed stratification and its trivializing pro-etale covers; exactness
identifies cohomology and carries a finite free module to a finite free module of the same rank.
Thus the component has the required constructible target. Localizing the naturality equation is
legitimate: $b$ commutes with multiplication by $\varpi_E$, whose action is invertible on $R_T$,
so it commutes with every rationalized arrow $u\otimes a$. Dependencies:
lem-pur-isomorphism-inverse-image-tensor-hom, lem-pur-cochain-pullback-tensor-coherence,
lem-weil-isomorphism-derived-pullback, def-weil-rationalization-karoubi.

Step 4. For $E\subset F$, use the SPECIFIED finite-free completion comparison $\chi_{F/E,K}$,
not an unspecified scalar-extension isomorphism. Its quotient coaugmentation has zero shifted
component, so Step 2 carries it to the corresponding coaugmentation over $T$. The
scalar-compatibility theorem gives $\alpha_K T_T(\kappa^{g,E}_K)=\kappa^{g,F}_{T_UK}\beta_K$,
with $\beta=G_g(\chi_U)b^{\rm bal}\chi_T^{-1}$. The cited theorem applies because $K$ and its
isomorphism pullback are constructible and derived complete, and $B_F$ is finite free over
$B_E$. Since both specified $\kappa$ maps are invertible, this equation gives
$$(\kappa^{g,F}_{T_UK})^{-1}\alpha_K=\beta_K\,T_T((\kappa^{g,E}_K)^{-1}).$$ Tensor this equality
with $R_T$. In the definition of Step 3 the rightmost inverse comparisons are therefore
identical on the two routes of the mixed scalar square. The remaining factors associate
coefficient tensors and multiply their scalars; the coefficient-transition equations of the
cochain tensor theorem identify them. Thus the mixed square commutes for the actual $\chi$ and
$\alpha$, including the completion quotient cocone. Dependencies:
lem-weil-finite-free-completed-scalar-comparison,
lem-weil-isomorphism-comparison-scalar-extension, lem-pur-cochain-pullback-tensor-coherence.

Step 5. Write $\theta_{E,F}:S_{F/E}g_E^*\xrightarrow{\sim}g_F^*S_{F/E}$ for the specified scalar
comparison. A common-stage arrow $[F,u]:(E,K)\to(E',K')$ acts under pullback by
$\theta_{E',F}^{-1}g_F^*(u)\theta_{E,F}$. Substitute this expression into the naturality square
for $b_g$. Step 4 moves each $\theta$ through the corresponding $b$; the remaining equation is
Step 3's naturality equation for $u$ at $F$. If two representatives agree after extension to
$F'$, Step 4 makes their squares agree at $F'$, so the equality holds in the directed-colimit
Hom group. Composites are represented over a common field and the intermediate
$\theta\theta^{-1}$ cancels. The inverse components obey the inverted mixed square. Hence these
components define a natural isomorphism on $\mathcal C_U$, using the actual raw rationalizations
and common-stage Hom groups, without adjoining idempotents. Dependencies:
def-weil-algebraically-closed-coefficients, def-weil-derived-pullback-tensor-hom.

Step 6. The tensorator is balanced scalar multiplication after the actual quotient completion
map $\chi_{K,L}$. That map is the quotient-augmentation comparison of the tensor-completion
theorem. On total K-flat representatives both routes through the tensorator square send
$r\otimes x\otimes s\otimes y$ to $rs\otimes(x\otimes y)$, followed in the completed target by
the relabeled quotient augmentations. The cochain tensor theorem supplies compatibility of this
formula with the signed differential, scalar transitions, and associators. Step 2 identifies the
full augmentation maps, including the zero shifted coordinate, so the equality holds before
localization and hence in the derived category. On the coefficient unit both routes send
$r\otimes1$ to $r$; the same theorem gives the unitors. Here the integral pullback tensor
comparison $\mu_g$ inside $\rho_Tg^*$ is the specified one of the pullback-tensor theorem: the
derived inverse limit of the finite ringed-topos comparisons, which on representatives are the
cochain maps $c_{g_n}$ commuting with all quotient transitions. Hence the route through
$\rho_T(\mu_g)$ and $\kappa$ is computed levelwise by the same formula. For common-stage inputs
$(E,M),(E',N)$ the tensor is formed at $EE'$; that theorem makes $\mu_g$ commute with the
scalar-extension comparisons, and Step 4 does so for $b_g$, so the integral square at $EE'$
gives the common-stage square. Therefore $b_g$ respects the specified tensorator and unit.
Dependencies: lem-fix-constructible-tensor-completion,
lem-pur-cochain-pullback-tensor-coherence, lem-pur-derived-pullback-tensor-iso.

Step 7. Consider a permitted pair $(M,N)$ and its evaluation-transpose realization map. The
isomorphism-pullback Hom theorem identifies pullback of its source internal Hom with the
internal Hom of the pulled-back pair and identifies its evaluation. For the ambient $R$-module
categories the corresponding comparison is likewise evaluation-normalized: tensor reindexing and
its inverse equivalence identify $\operatorname{Hom}(A\otimes G_gM,G_gN)$ with
$\operatorname{Hom}(G_g^{-1}A\otimes M,N)$, and the ringed derived closed adjunction identifies
these with the respective Hom tests for internal Hom. Thus the comparison and its inverse are
the transposes of reindexed evaluation. Transpose the desired square for the realized Hom map.
The two resulting maps are the same reindexed realized evaluation by Step 6 and naturality of
$b_g$ applied to evaluation. Injectivity of the tensor-Hom adjunction implies equality of the
original maps. The permitted-pair hypothesis is retained throughout; no site-perfectness of $M$
is asserted. Dependencies: lem-pod-derived-automorphism-hom-evaluation,
lem-pur-isomorphism-inverse-image-tensor-hom, lem-sf-ringed-derived-closed-symmetric-monoidal.

Step 8. For $g=1$, reindexing leaves every object, section, coefficient, and quotient
augmentation unchanged. Hence Step 3 gives the identity under the specified identity pullbacks.
For $T\xrightarrow gU\xrightarrow hV$, reindexing an object successively gives exactly $(W\to
T\xrightarrow{hg}V)$. On ordinary total tensors the specified composition comparison obeys the
cochain composition equation; on quotient completions Step 2 applies that equation on BOTH cone
coordinates, carrying $(0,(q_n(x)))$ to the same augmentation. For the completed integral
pullbacks, the inverse-image composition theorem gives
$c^E_{g,h,N}\kappa^{hg}_Nd_{g,h,N}=\kappa^g_{Lh^*N}g^{-1}(\kappa^h_N)$ as derived morphisms,
with $c^E$ the specified pullback compositor. Inserting the inverses of these $\kappa$ maps into
the Step 3 composites, the direct and successive versions of $b$ agree with the actual pullback
compositors, before passage to rational or common-stage morphisms. Steps 4-5 preserve this
equality there. If a finite-field descent datum supplies geometric Frobenius, it is an
underlying-scheme isomorphism, so these constructions apply unchanged. No step used linearity
over $k$. Dependencies: lem-weil-proetale-isomorphism-inverse-image,
lem-pur-cochain-pullback-tensor-coherence,
lem-weil-isomorphism-derived-pullback-comparison-normalization,
lem-trf-integral-inverse-image-comparison-composition.
-/
theorem adic_realization_isomorphism_normalization
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (R : ∀ T : GeometricSpace D, LocallyFiniteAdicRealization.Realization l T.base.left)
    (A : ∀ T : GeometricSpace D,
      letI := fun x ↦ sfQbarLocalizationResidueInvertible l D hl
        T.base.left T.base.hom x
      At l T.base.left (R T))
    (N : ∀ (T : GeometricSpace D) (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
      letI := fun x ↦ sfQbarLocalizationResidueInvertible l D hl
        T.base.left T.base.hom x
      FiniteNormalization l T.base.left (R T) (A T) E)
    (P : ∀ T : GeometricSpace D, (sectionFunctor l T.base.left (R T)).IsEquivalence)
    (H : ∀ T : GeometricSpace D,
      letI := fun x ↦ sfQbarLocalizationResidueInvertible l D hl
        T.base.left T.base.hom x
      HomLaws l T.base.left (R T) (A T)) :
    ∃ F : Family l D,
      (∀ T, (F.data T).realization = R T) ∧
      (∀ T, HEq (F.data T).tensor (A T)) ∧
      (∀ T E, HEq ((F.data T).finite E) (N T E)) ∧
      ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
        (K : GeneralAlgebraicallyClosedCoefficients.Pair l (PadicAlgCl l) U.base.left)
        (L : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) (h : K.stage ≤ L),
        letI := (F.data T).units
        letI := (F.data U).units
        (ordinary l T.base.left (F.data T).realization).map
            ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).map
              (StageSystem.isoToStage
                (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l)
                  U.base.left) K h).hom) ≫
          (F.comparison T U g).hom.app
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := PadicAlgCl l) (Y := U.base.left) L).obj (K.toStage h)) =
        (F.comparison T U g).hom.app K ≫
          (derivedPull l T.base.left g.hom (F.ring T U g)).map
            ((ordinary l U.base.left (F.data U).realization).map
              (StageSystem.isoToStage
                (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l)
                  U.base.left) K h).hom) := by
  classical
  let d := fun T ↦ spaceDataOfPresentation l D hl T (R T) (P T) (A T) (N T) (H T)
  obtain ⟨C, hd, hId, hComp, hIntegral, hSource⟩ :=
    exists_normalized_reindexing_core l D d
  obtain ⟨hIdentity, hComposition⟩ :=
    normalized_reindexing_functoriality l D C hId hComp hIntegral hSource
  obtain ⟨hTensor, hUnit⟩ := normalized_reindexing_tensor l D C hIntegral
  have hHom := normalized_reindexing_hom l D C hTensor
  let F : Family l D :=
    { toFamilyCore := C
      moduleId_sections := hId
      moduleComp_sections := hComp
      integral_normalization := hIntegral
      sourceId_unit := hSource
      identity := hIdentity
      composition := hComposition
      tensor_compatibility := hTensor
      unit_compatibility := hUnit
      hom_compatibility := hHom }
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro T
    change (C.data T).realization = R T
    rw [hd]
    rfl
  · intro T
    change HEq (C.data T).tensor (A T)
    rw [hd]
    rfl
  · intro T E
    change HEq ((C.data T).finite E) (N T E)
    rw [hd]
    rfl
  · intro T U g K L h
    exact (F.comparison T U g).hom.naturality
      (StageSystem.isoToStage
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l)
          U.base.left) K h).hom

end WeilConjectures.AdicQbarRealization
