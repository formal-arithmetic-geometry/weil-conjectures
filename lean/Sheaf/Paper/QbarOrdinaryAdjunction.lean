/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.AdicHeartPullbackFibres
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.PbcCommonStageCones
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.RationalDirectImageRealization
import Sheaf.Paper.CompletedPullbackTriangles
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.ArbitraryFieldAdjunctionScalars

/-! # Ordinary adic adjunction over an arbitrary field

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-per-qbar-ordinary-adjunction).

Use the recorded raw finite-stage pair category and its actual completed pullback.
The direct image is specified by its integral restriction, rationalization and
normalized scalar mate. The finite adjunctions descend to the same pair category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.PerAdic

/-- Ordinary pullback/direct-image adjunction on the recorded adic pair categories.
Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14, Remark 6.8.15
(blueprint: lem-per-qbar-ordinary-adjunction).

Proof:
1. A field is Noetherian. Apply [lem-weil-pbc-finite-type-over-noetherian] to $X,Y$ over
$\operatorname{Spec}k$, and [lem-kun-dimension-finite-type] to obtain Noetherian finite-
dimensional schemes. Invertibility of $\ell$ pulls back from $k$. Thus both schemes satisfy the
hypotheses of the raw finite-stage categories and the scalar-extension comparisons [prop-weil-pbc-
scalar-extension]. The separated finite-type $k$-morphism in the item satisfies the morphism
hypothesis of [lem-a1-rational-direct-image-realization], which in fact allows any $k$-morphism
between these separated finite-type schemes.

2. At each finite field $E$ write $\mathcal C_E(W)=D^b_c(W,E)$ using [def-weil-pbc-rational-
category], $P_E=Lf^*_{\mathrm{comp},E}$ and $D_E=Rf_{*,E}$. The completed pullback is precisely
[def-weil-pbc-completed-pullback]; only the finite and integral constructions of [def-weil-
derived-direct-image] are used to define $D_E$, followed by raw rationalization. By
[lem-a1-rational-direct-image-realization] these functors preserve the bounded constructible
categories and have the canonical adjunction $h_E$. The equivalence $J$ of [lem-per-continuous-
rational-derived-realization] identifies this with the ambient continuous-module adjunction,
including its actual unit and counit. Exactness requires no change of triangulation: [lem-cbc-
completed-pullback-triangles] gives the shift and triangle comparisons of the specified integral
completed pullback, and [lem-pc-right-derived-functor-triangulated] gives them for the ordinary
ringed-topos direct image identified with the strict-tower operation by the realization statement.
The coefficient integers are Noetherian DVRs by [lem-weil-l-adic-extension-integers-dvr], so the
quotients used for the completed pullback are perfect, with the two-term resolution given by
multiplication by $\varpi^n$. Both integral functors are coefficient-linear: their complex and
strict-tower maps preserve the constant coefficient action, so applying either construction to $c
u$ gives $c$ times its value on $u$; the same equality holds on derived morphisms. Their raw
rationalizations are exact by [prop-weil-pbc-rational-transport].

3. For $E\subset L$, abbreviate the specified comparisons of [prop-weil-pbc-scalar-extension] by
$a_{L/E}:T_XP_E\to P_LT_Y$ and $b_{L/E}:T_YD_E\to D_LT_X$. Apply [lem-per-arbitrary-field-
adjunction-scalars] to this arbitrary field $k$, the given morphism, and these raw rationalized
stages. Its mate equation gives, for $u:P_EA\to B$, $$h_L(T_X(u)a_A^{-1})=b_B T_Y(h_E(u)).$$ It
gives the inverse equation as well, for these exact $a,b$, and identity, tower and shift
compatibility. This is the needed scalar-naturality input; compatibility of a direct-image
realization alone would not imply this equation. No finite-field datum or Karoubi coefficient
category is used.

4. Construct functors directly on the pair category of [def-weil-pbc-qbar-category, def-weil-pbc-
finite-stage-pair-category]. On objects put $P(E,A)=(E,P_EA)$ and $D(E,B)=(E,D_EB)$. For $F=P$ or
$D$ write $c^P=a$, $c^D=b$. If $[M,u]:(E,K)\to(E',K')$, define
$$F[M,u]=[M,(c^F_{M/E',K'})^{-1}F_M(u)c^F_{M/E,K}].$$ The map inside brackets goes from
$T_{M/E}F_EK$ to $T_{M/E'}F_{E'}K'$, so has the required pair-category type. For an extension
$M\subset N$, the tower equation for $c^F$ in [prop-weil-pbc-scalar-extension], followed by
naturality, identifies this formula at $N$ with the associator-conjugate extension of the formula
at $M$. Hence eventually equal representatives have eventually equal images. The unit comparison
makes identities map to identities. At a common stage the middle $c^F(c^F)^{-1}$ cancels in a
composite, proving composition; additivity follows there too. These formulas define the completed
pullback and rationalized direct image on this pair category, using their given finite-stage
operations.

5. Let $A=(E,A_E)$ and $B=(F,B_F)$. An arrow $P A\to B$ is represented by $u:T_{M/E}P_EA_E\to
T_{M/F}B_F$. Define $$\Psi[M,u]=[M,b_{M/F,B_F}^{-1}\,h_M(u\,a_{M/E,A_E}^{-1})].$$ Here $u a^{-1}$
has source $P_MT_{M/E}A_E$, and the displayed adjunct has target $T_{M/F}D_FB_F$, as required for
an arrow $A\to D B$. Conversely define $$\Phi[M,v]=[M,h_M^{-1}(b_{M/F,B_F}v)\,a_{M/E,A_E}].$$ For
$M\subset N$, use the scalar equation of Step 3 with input $u a^{-1}$ and then the tower equations
for $a,b$. This gives $\Psi_N(u_N)=(\Psi_M(u))_N$, with both transports precisely the associator
conjugations in [def-weil-pbc-finite-stage-pair-category]. The inverse scalar equation gives the
same identity for $\Phi$. Thus both formulas respect eventual equality and define maps on the pair
Hom sets. At one stage, $h_M^{-1}h_M=1$ and $h_Mh_M^{-1}=1$, and the neighboring $a,a^{-1}$ and
$b,b^{-1}$ cancel. Consequently $\Phi\Psi=1$ and $\Psi\Phi=1$.

6. Naturality is checked at one common finite stage. Substitute the formula of Step 4 for a map in
either variable into Step 5. Naturality of $a,b$ moves these comparisons through the maps, and
naturality of the finite-stage bijection $h_M$ identifies precomposition by $P$ of a map with
precomposition by that map, and postcomposition with postcomposition by $D$ of that map. The
inverse comparisons cancel, yielding the two pair-category naturality equations. The finite-stage
naturality is supplied by [lem-a1-rational-direct-image-realization]. By the shift clause of [lem-
per-arbitrary-field-adjunction-scalars], shifting $u$ and inserting the operation shift
comparisons in the formula for $\Psi$ gives the shifted formula for $\Psi(u)$. The scalar shift
comparisons commute with $a,b$ by [prop-weil-pbc-scalar-extension], so this calculation also holds
for pairs represented at different fields and for all integer shifts.

7. It remains to verify exactness with the actual common-stage cones [def-weil-pbc-common-stage-
cones]. Let $[M,u]:(E,K)\to(F,L)$ and choose its stage-$M$ distinguished triangle $T_{M/E}K\to
T_{M/F}L\to C(u)\to(T_{M/E}K)[1]$. For $F=P$ or $D$, apply the exact finite-stage functor $F_M$
from Step 2. The resulting distinguished triangle defines a distinguished common-stage triangle.
The image under the pair functor of the original common-stage cone triangle is isomorphic to this
triangle: on the first two vertices the isomorphisms are $c^F_{M/E,K}$ and $c^F_{M/F,L}$, and on
the cone vertex it is the identity on $F_M C(u)$. On arrows this follows by the conjugation
formula of Step 4. On the closing arrow, the definition uses $\sigma_{M/E,K}^{-1}p_u$; the shift
compatibility of $c^F$ in [prop-weil-pbc-scalar-extension] identifies its image with the closing
arrow of the $F_M$-image triangle. The same operation shift comparisons define the pair functor's
commutation with shift. Since every distinguished pair triangle is isomorphic to such a cone
triangle, both pair functors are exact triangulated.

8. For a representative already over $E$, the formulas of Steps 4 and 5 reduce to $P_E,D_E,h_E$ by
the identity comparisons. Moving it to a further finite field $L$ changes its adjunct by exactly
$h_L(T_Xu\,a^{-1})=b\,T_Yh_E(u)$ of [lem-per-arbitrary-field-adjunction-scalars]. Thus the
constructed adjunction is compatible with every finite coefficient extension, with the prescribed
units and counits: they are the adjuncts of the identity arrows, so the same equation applies to
them. Tower compatibility gives the same result after successive extensions. With Steps 6 and 7
this proves all clauses of the unchanged statement on $\mathcal C_X,\mathcal C_Y$.

The shift witnesses in the signature are normalized rather than free: `ip` and `ir` are the
actual integral restrictions, `ep` and `er` are identity-component comparisons to the ambient
operations, and `qp` and `qr` are the identity-component localization comparisons. Requiring
all four comparisons to commute with shifts fixes the rational finite-stage shift structures
to the existing ambient ones. Requiring the inclusion comparisons to commute with shifts
then fixes the pair-category shift structures. The clause `(a E).CommShift` is thus about
these fixed structures, before any appeal to the global adjunction. The integral transpose
formula uses the actual completed-pullback unit and the actual derived adjunction; its
localization formula fixes `a E`, so neither adjunction is an arbitrary adjunction structure.
-/
theorem qbarOrdinaryAdjunction (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : pbcIntegralStage l Ω X.scheme E),
        PbcIsBoundedConstructibleComplete Y.scheme (pbcStageDatum.{u} l Ω E)
          ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
      (Rf : StageSystem.Morphism (stages l Ω X) (stages l Ω Y)),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        Rf.Φ E = pbcDescentDirectImage l Ω f pres E) ∧
      PbcDirectImageBetaSpec l Ω f pres Rf ∧
      ∃ (a : ∀ E : Padic.FiniteCoefficientFields l Ω,
          (pbcQbarPullFamily l Ω f).Φ E ⊣ Rf.Φ E)
        (adj : (pbcQbarPullFamily l Ω f).functor ⊣ Rf.functor),
        (∀ (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)
          (A : pbcStageCategory l Ω Y.scheme E)
          (B : pbcStageCategory l Ω X.scheme E)
          (w : ((pbcQbarPullFamily l Ω f).Φ E).obj A ⟶ B),
          (a F).homEquiv (((stages l Ω Y).T h).obj A) (((stages l Ω X).T h).obj B)
              (((pbcQbarPullFamily l Ω f).β h).inv.app A ≫
                ((stages l Ω X).T h).map w) =
            ((stages l Ω Y).T h).map ((a E).homEquiv A B w) ≫
              (Rf.β h).hom.app B) ∧
        (∀ (E : Padic.FiniteCoefficientFields l Ω)
          (A : pbcStageCategory l Ω Y.scheme E)
          (B : pbcStageCategory l Ω X.scheme E)
          (w : ((pbcQbarPullFamily l Ω f).Φ E).obj A ⟶ B),
          adj.homEquiv ((inclusion l Ω Y E).obj A) ((inclusion l Ω X E).obj B)
              ((inclusion l Ω X E).map w) =
            (inclusion l Ω Y E).map ((a E).homEquiv A B w)) ∧
        ∃ (ip : ∀ E : Padic.FiniteCoefficientFields l Ω,
            pbcIntegralStage l Ω Y.scheme E ⥤ pbcIntegralStage l Ω X.scheme E)
          (ir : ∀ E : Padic.FiniteCoefficientFields l Ω,
            pbcIntegralStage l Ω X.scheme E ⥤ pbcIntegralStage l Ω Y.scheme E),
          (∀ E, ip E = pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E))
              (pbcQbarIntegralPull_mem l Ω f E)) ∧
          (∀ E, ir E = pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)) ∧
          ∃ (ep : ∀ E, ip E ⋙ pbcStageInclusion l Ω X.scheme E ≅
              pbcStageInclusion l Ω Y.scheme E ⋙
                pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E))
            (er : ∀ E, ir E ⋙ pbcStageInclusion l Ω Y.scheme E ≅
              pbcStageInclusion l Ω X.scheme E ⋙
                pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E))
            (qp : ∀ E, pbcStageLocalization l Ω Y.scheme E ⋙
                (pbcQbarPullFamily l Ω f).Φ E ≅
              ip E ⋙ pbcStageLocalization l Ω X.scheme E)
            (qr : ∀ E, pbcStageLocalization l Ω X.scheme E ⋙ Rf.Φ E ≅
              ir E ⋙ pbcStageLocalization l Ω Y.scheme E),
            (∀ (E : Padic.FiniteCoefficientFields l Ω)
                (K : pbcIntegralStage l Ω Y.scheme E),
              HEq ((ep E).hom.app K)
                (𝟙 ((pbcActualCompletedPull f (pbcStageDatum.{u} l Ω E)).obj K.obj)) ∧
              HEq ((qp E).hom.app K)
                (𝟙 ((pbcStageLocalization l Ω X.scheme E).obj ((ip E).obj K)))) ∧
            (∀ (E : Padic.FiniteCoefficientFields l Ω)
                (K : pbcIntegralStage l Ω X.scheme E),
              HEq ((er E).hom.app K)
                (𝟙 ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)) ∧
              HEq ((qr E).hom.app K)
                (𝟙 ((pbcStageLocalization l Ω Y.scheme E).obj ((ir E).obj K)))) ∧
            ∃ ai : ∀ E, ip E ⊣ ir E,
              (∀ (E : Padic.FiniteCoefficientFields l Ω)
                  (M : pbcIntegralStage l Ω Y.scheme E)
                  (K : pbcIntegralStage l Ω X.scheme E) (w : (ip E).obj M ⟶ K),
                (pbcStageInclusion l Ω Y.scheme E).map ((ai E).homEquiv M K w) ≫
                    (er E).hom.app K =
                  (pbcActualDerivedAdjunction f (pbcStageDatum.{u} l Ω E)).homEquiv M.obj K.obj
                    ((pbcActualCompletedPullUnit f (pbcStageDatum.{u} l Ω E)).app M.obj ≫
                      (ep E).inv.app M ≫ (pbcStageInclusion l Ω X.scheme E).map w)) ∧
              (∀ (E : Padic.FiniteCoefficientFields l Ω)
                  (M : pbcIntegralStage l Ω Y.scheme E)
                  (K : pbcIntegralStage l Ω X.scheme E) (w : (ip E).obj M ⟶ K),
                (a E).homEquiv ((pbcStageLocalization l Ω Y.scheme E).obj M)
                    ((pbcStageLocalization l Ω X.scheme E).obj K)
                    ((qp E).hom.app M ≫ (pbcStageLocalization l Ω X.scheme E).map w) =
                  (pbcStageLocalization l Ω Y.scheme E).map ((ai E).homEquiv M K w) ≫
                    (qr E).inv.app K) ∧
            ∃ (sIP : ∀ E, (ip E).CommShift ℤ) (sIR : ∀ E, (ir E).CommShift ℤ)
              (sPE : ∀ E, ((pbcQbarPullFamily l Ω f).Φ E).CommShift ℤ)
              (sRE : ∀ E, (Rf.Φ E).CommShift ℤ)
              (sP : (pbcQbarPullFamily l Ω f).functor.CommShift ℤ)
              (sR : Rf.functor.CommShift ℤ),
              (fun [ipInst : ∀ E, (ip E).CommShift ℤ]
                  [irInst : ∀ E, (ir E).CommShift ℤ]
                  [peInst : ∀ E, ((pbcQbarPullFamily l Ω f).Φ E).CommShift ℤ]
                  [reInst : ∀ E, (Rf.Φ E).CommShift ℤ]
                  [pInst : (pbcQbarPullFamily l Ω f).functor.CommShift ℤ]
                  [rInst : Rf.functor.CommShift ℤ] ↦
                (∀ E : Padic.FiniteCoefficientFields l Ω,
                  NatTrans.CommShift (ep E).hom ℤ ∧ NatTrans.CommShift (er E).hom ℤ ∧
                    NatTrans.CommShift (qp E).hom ℤ ∧ NatTrans.CommShift (qr E).hom ℤ ∧
                    NatTrans.CommShift ((pbcQbarPullFamily l Ω f).ιCompFunctorIso E).hom ℤ ∧
                    NatTrans.CommShift (Rf.ιCompFunctorIso E).hom ℤ ∧ (a E).CommShift ℤ) ∧
                (pbcQbarPullFamily l Ω f).functor.Additive ∧ Rf.functor.Additive ∧
                  (pbcQbarPullFamily l Ω f).functor.IsTriangulated ∧
                  Rf.functor.IsTriangulated ∧ adj.CommShift ℤ)
                (ipInst := sIP) (irInst := sIR) (peInst := sPE) (reInst := sRE)
                (pInst := sP) (rInst := sR) := by
  sorry

end AlgebraicGeometry.Scheme.PerAdic
