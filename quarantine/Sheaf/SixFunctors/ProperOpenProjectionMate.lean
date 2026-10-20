/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Normalized proper/open interchange commutes with projection

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D; the normalized proper/open
projection calculation in the blueprint (blueprint: lem-sf-proper-open-projection-mate).

The ordinary comparison is constructed from open base change and the canonical clopen
projection. The second statement uses the intrinsic comparison of the published system
realization, in the unbounded derived category of strict semilinear systems itself.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- A finite commutative coefficient ring is noetherian.
Source: Stacks 00IU (blueprint: lem-sf-proper-open-projection-mate). -/
instance finiteRingIsNoetherian (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    IsNoetherianRing Λ :=
  @instIsNoetherianRingOfIsArtinianRing Λ _
    (isArtinian_of_finite : IsArtinianRing Λ)

/-- The ordinary unbounded derived category of constant `Λ`-module sheaves.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenDerived (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

/-- Derived inverse image on the ordinary pro-etale module categories.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenPull (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProperOpenDerived Λ Y ⥤ ProperOpenDerived Λ X :=
  (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor

/-- Derived direct image on the ordinary pro-etale module categories.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenPush (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProperOpenDerived Λ X ⥤ ProperOpenDerived Λ Y :=
  (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor

/-- Exact extension by zero on the ordinary pro-etale derived categories.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenShriek (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ProperOpenDerived Λ U ⥤ ProperOpenDerived Λ X :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory

/-- The derived tensor bifunctor on a pro-etale site.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenTensor (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  derivedTensor (ModuleCat.{u + 1} Λ) X

/-- Component of the published counit-defined projection, used by def-exchange-projection.
Source: Stacks 0E48 (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev properOpenProjection (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ProperOpenDerived Λ X)
    (N : ProperOpenDerived Λ Y) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app M).app N

/-- The unit-normalized open tensor comparison.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
noncomputable def properOpenTensorIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    ((ProperOpenTensor Λ X).obj ((ProperOpenShriek Λ j).obj M)).obj N ≅
      (ProperOpenShriek Λ j).obj
        (((ProperOpenTensor Λ U).obj M).obj ((ProperOpenPull Λ j).obj N)) :=
  asIso (((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).inv.app M).app N)

/-- The open adjunction, transported to the canonical total derived inverse image.
Source: Stacks 03DI (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenAdj (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ProperOpenShriek Λ j ⊣ ProperOpenPull Λ j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm

/-- Canonical composition of open extensions, fixed by the pullback compositor and
adjunctions. Source: Stacks 03DI (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenShriekComp (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    ProperOpenShriek Λ j ⋙ ProperOpenShriek Λ k ≅ ProperOpenShriek Λ (j ≫ k) :=
  Adjunction.leftAdjointCompIso (properOpenAdj Λ j) (properOpenAdj Λ k)
    (properOpenAdj Λ (j ≫ k))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j k).symm

/-- Equality transport of open extensions via the canonical pullback identification.
Source: Stacks 03DI (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenShriekCongr (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) : ProperOpenShriek Λ j ≅ ProperOpenShriek Λ k :=
  ((properOpenAdj Λ j).ofNatIsoRight
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h)).leftAdjointUniq (properOpenAdj Λ k)

/-- The clopen projection: the direct-image unit followed by the canonical identification
of clopen direct image with extension by zero. It is identity on the image and zero on
its complement. Source: Stacks 09AE (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenClopenProjection (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (ProperOpenDerived Λ X) ⟶ ProperOpenPull Λ s ⋙ ProperOpenShriek Λ s :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit ≫
    Functor.whiskerLeft (ProperOpenPull Λ s)
      (rightDerivedLowerStarIsoOfIsClosedRange (ModuleCat.{u + 1} Λ) s
        s.isClosedEmbedding.isClosed_range).hom

/-- Ordinary canonical open base change, with total derived pullbacks.
Source: Stacks 09AE (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenBeta (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g) :
    ProperOpenShriek Λ j ⋙ ProperOpenPull Λ g ≅
      ProperOpenPull Λ a ⋙ ProperOpenShriek Λ j' :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g) ≪≫
    ordinaryOpenExtensionBaseChangeIso Λ a j' j g sq ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) a).symm _

/-- The prescribed ordinary-site alpha: beta, then b_! of the clopen projection for
s=(k,r), then the canonical open/pullback compositors. No comparison is supplied as a
parameter. The lift and its clopenness are those of the recorded strict-tower calculus.
Source: Stacks 0F7B and node Step 1 (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenAlpha (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ProperOpenShriek Λ i ⋙ ProperOpenPull Λ p ⟶
      ProperOpenPull Λ r ⋙ ProperOpenShriek Λ k :=
  (properOpenBeta Λ (pullback.snd p i) (pullback.fst p i) i p
    (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (ProperOpenPull Λ (pullback.snd p i))
    (properOpenClopenProjection Λ (StrictTower.squareLift k r p i h)))
      (ProperOpenShriek Λ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (ProperOpenPull Λ (pullback.snd p i))
      (ProperOpenPull Λ (StrictTower.squareLift k r p i h))
      (ProperOpenShriek Λ (StrictTower.squareLift k r p i h))).inv
    (ProperOpenShriek Λ (pullback.fst p i)) ≫
  (Functor.associator
    (ProperOpenPull Λ (pullback.snd p i) ⋙ ProperOpenPull Λ (StrictTower.squareLift k r p i h))
    (ProperOpenShriek Λ (StrictTower.squareLift k r p i h))
    (ProperOpenShriek Λ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft
    (ProperOpenPull Λ (pullback.snd p i) ⋙ ProperOpenPull Λ (StrictTower.squareLift k r p i h))
    ((properOpenShriekComp Λ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (properOpenShriekCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) (pullback.lift_snd k r h)).hom)
    (ProperOpenShriek Λ k)

/-- The proper-adjunction mate of the canonical clopen-projection alpha.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenMate (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ProperOpenPush Λ r ⋙ ProperOpenShriek Λ i ⟶
      ProperOpenShriek Λ k ⋙ ProperOpenPush Λ p :=
  mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (properOpenAlpha Λ k r p i h))

/-- Tensoring the mate component with the identity on the second variable, with the
definitional functor-composition casts made explicit.
Source: node Step 5 (blueprint: lem-sf-proper-open-projection-mate). -/
noncomputable def properOpenMateTensorMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ D) (i : C ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (M : ProperOpenDerived Λ A) (N : ProperOpenDerived Λ D) :
    ((ProperOpenTensor Λ D).obj ((ProperOpenShriek Λ i).obj ((ProperOpenPush Λ r).obj M))).obj N ⟶
      ((ProperOpenTensor Λ D).obj
        ((ProperOpenPush Λ p).obj ((ProperOpenShriek Λ k).obj M))).obj N :=
  eqToHom (by rfl) ≫
      ((ProperOpenTensor Λ D).map ((properOpenMate Λ k r p i h).app M)).app N ≫
    eqToHom (by rfl)

/-- The canonical derived pullback comparison attached to the commutative square.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
noncomputable def properOpenPullSquareIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ D) (i : C ⟶ D) (_h : k ≫ p = r ≫ i) :
    ProperOpenPull Λ i ⋙ ProperOpenPull Λ r ≅
      ProperOpenPull Λ p ⋙ ProperOpenPull Λ k :=
  leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) (CommSq.mk _h)

/-- The normalized proper/open mate commutes with projection on arbitrary unbounded
ordinary constant-coefficient inputs. Source: Stacks 0F7B--0F7D and the agent tensor/counit
calculation (blueprint: lem-sf-proper-open-projection-mate).

Proof, following all eight steps of the DAG node:

1. Use [lem-cbc-strict-tower-proper-open-calculus] for the geometry of the square: $s=(k,r):A\to
B_C$ is clopen, $bs=k$, $qs=r$, and $\alpha$ is exactly the specified base-change map followed by
projection onto $s(A)$. This geometric assertion has no hypothesis on an input complex. Write
$J=i_!$, $K=k_!$, $E=R_rM$, $X=P_iN$, $Y=P_pN$, and $T=P_rX=P_kY$. All tensors below are derived;
canonical pullback/tensor identifications are understood. For an open $j$ write
$\delta_j(U,V):j_!U\otimes V\to j_!(U\otimes P_jV)$. The normalizations in
[lem-sf-open-tensor-normalization] make these maps and the open base-change map identities after
restriction and the open units.

2. First check the tensor square for the base-change factor $\beta:P_pJ\to b_!P_q$. For arbitrary
$H$ on $C$, its two routes have source $P_p(JH\otimes N)$ and target $b_!(P_qH\otimes P_bY)$: one
applies $P_p\delta_i$, then $\beta_{H\otimes X}$ and the pullback tensor comparison; the other
applies $\mu_p$, then $\beta_H\otimes1_Y$ and $\delta_b$. Both source and target lie in the image
of $b_!$: use $\beta_H$ and the open tensor isomorphism to identify the source with
$b_!(P_qH\otimes P_bY)$. Thus full faithfulness of $b_!$ reduces equality to restriction by $P_b$.
Under the open units, $P_b\beta$ and $P_i\delta_i$ are identities. The remaining maps on both
routes are the canonical pullback/tensor comparison on $P_qH\otimes P_bY$, using $P_bP_p=P_qP_i$.
Hence the square commutes. Here the comparison is the canonical one for the commutative ringed
pullback square, as in [lem-weil-pbc-ringed-exchange-tensor-coherence].

3. The clopen-projection factor also respects tensor: in $B_C=s(A)\amalg(B_C\setminus s(A))$,
$\pi_s$ acts by $(1,0)$. Tensoring it with $P_bY$ still acts by $(1,0)$ on the two components. The
open tensor comparison for $s$ restricts to the identity on $s(A)$; on the complementary component
its target is zero. Consequently projection before tensor and projection after tensor agree,
followed by $\delta_s$. This is an identity of the given termwise clopen projections on complexes
and hence of their derived classes, using the canonical tensor comparisons. The comparisons for
the composite open $bs=k$ agree with $\delta_k$: both are maps between objects in the image of
$k_!$, and after restriction to $k$ they are identities, so full faithfulness gives equality.
Combining this calculation with Step 2 gives, for every $H$ on $C$, the explicit identity
$$K(\mu_r)\,\alpha_{H\otimes X}\,P_p(\delta_i)=\delta_k\,(\alpha_H\otimes1_Y)\,\mu_p.$$ Both sides
run from $P_p(JH\otimes N)$ to $K(P_rH\otimes T)$.

4. Put $Z=M\otimes T$ and $a_r=(\varepsilon_{r,M}\otimes1_T)\mu_r:P_r(E\otimes X)\to Z$. The
counit definition of $\pi_r$ gives $\varepsilon_{r,Z}P_r(\pi_r)=a_r$. The mate definition of
$\gamma$ gives $\varepsilon_{p,KW}P_p(\gamma_W)=K(\varepsilon_{r,W})\alpha_{R_rW}$ for every $W$.
Therefore the transpose under $P_p\dashv R_p$ of the left side of the claimed identity is
$$K(\varepsilon_{r,Z})\,\alpha_{R_rZ}\,P_pJ(\pi_r)\,P_p\delta_i
=K(\varepsilon_{r,Z}P_r\pi_r)\,\alpha_{E\otimes X}\,P_p\delta_i =K(a_r)\,\alpha_{E\otimes
X}\,P_p\delta_i.$$ The middle equality is naturality of $\alpha$ for the arrow $\pi_r:E\otimes
X\to R_rZ$.

5. Transpose the right side under the same adjunction. Naturality of $\varepsilon_p$ first moves
$R_p\delta_k$ out of the transpose; the defining adjunct equation of $\pi_p$ then gives
$$\delta_k\,(\varepsilon_{p,KM}\otimes1_Y)\,\mu_p\,P_p(\gamma_M\otimes1_N).$$ Naturality of
$\mu_p$ replaces this by $$\delta_k\,((\varepsilon_{p,KM}P_p\gamma_M)\otimes1_Y)\,\mu_p
=\delta_k\,((K\varepsilon_{r,M}\,\alpha_E)\otimes1_Y)\,\mu_p.$$ Now apply naturality of $\delta_k$
to $\varepsilon_{r,M}:P_rE\to M$, and then the identity of Step 3 with $H=E$. The result is
$$K(\varepsilon_{r,M}\otimes1_T)\,K(\mu_r)\,\alpha_{E\otimes X}\,P_p\delta_i
=K(a_r)\,\alpha_{E\otimes X}\,P_p\delta_i,$$ which is the transpose computed in Step 4. The
adjunction Hom bijection is injective, so the original maps agree. All substitutions are natural
in $M,N$.

6. These calculations use arbitrary inputs in the unbounded ringed-site derived categories. In
particular [lem-weil-pbc-ringed-projection-mate-exact] supplies the counit-defined map for
arbitrary sheaves of commutative rings and all objects, so the use of its formula does not
specialize the finite ring $\Lambda$ to a quotient DVR or impose invertibility of its order.
[lem-sf-open-tensor-normalization] also has no boundedness or Tor hypothesis. We never invert
$\pi_p$, $\pi_r$ or $\gamma$, nor invoke a proper projection formula or proper base-change
isomorphism on these inputs. This proves precisely the finite constant-coefficient identity
claimed.

7. We identify the stipulated system $\Gamma_Q$ intrinsically, rather than from its finite
evaluations. Let $\widetilde\gamma$ be the proper-adjunction mate of the clopen $\alpha$. The
realization node characterizes $\Gamma_Q$ by $\lambda_QP_i\Gamma_Q=1$ under the open unit, where
$\lambda_Q:P_iS_pJ_k\cong S_r$ is obtained by open restriction, $k=bs$, $J_s=S_s$ for the clopen
$s$, and direct-image composition. Make exactly those identifications in $P_i\widetilde\gamma$.
Mate pasting identifies the restricted unit/counit maps with the unit/counit of $P_r\dashv S_r$;
the restricted open base-change map is the identity by open normalization, and the clopen
projection acts as identity on $J_sM$. Thus the composite $\lambda_QP_i\widetilde\gamma$ is
$S_r\varepsilon_r\circ\eta_rS_r=1_{S_r}$ by the triangle identity. Since $J_i\dashv P_i$ gives a
bijection on the relevant Hom sets, its adjunct characterization implies
$\widetilde\gamma=\Gamma_Q$. This argument uses only the intrinsic open-restriction
characterization and canonical composite adjunctions, and is independent of the total-limit
comparisons or the finite evaluated arrows.

8. For the system assertion, apply Steps 1--5 inside the unbounded derived module categories of
the ringed diagram sites themselves. [lem-pur-coefficient-system-derived-comparison] supplies the
exact system inverse images and their derived adjunctions on these unbounded categories.
[lem-sf-open-tensor-normalization] explicitly supplies the same open-unit, tensor and base-change
normalization on the diagram topoi. The operations and intrinsic $\Gamma_Q$ are the simultaneous
ringed-diagram constructions stipulated in [lem-sf-integral-compactification-system-realization];
Step 7 identifies $\Gamma_Q$ with the proper mate of the same clopen-projection $\alpha$. Thus the
system analogue of the mate equation in Step 4 is an equation in the system category. On system
complexes the clopen projection in Step 3 is literally identity on the open component and zero on
its complement; these are morphisms of systems, compatible with every coefficient transition.
Steps 4--5 now compare the two system maps by the single system adjunction Hom bijection and the
displayed common transpose, before applying any evaluation. The generic ringed tensor/projection
nodes apply to these small ringed diagram sites without change. Only the unbounded operations and
intrinsic-map clauses of the realization node are used; no total-limit realization or
constructible-domain claim is needed.
-/
theorem properOpenProjectionMate
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ D) (i : C ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (M : ProperOpenDerived Λ A) (N : ProperOpenDerived Λ D) :
    (properOpenTensorIso Λ i ((ProperOpenPush Λ r).obj M) N).hom ≫
      (ProperOpenShriek Λ i).map (properOpenProjection Λ r M ((ProperOpenPull Λ i).obj N)) ≫
      (ProperOpenShriek Λ i).map ((ProperOpenPush Λ r).map
        (((ProperOpenTensor Λ A).obj M).map
          ((properOpenPullSquareIso Λ k r p i h).hom.app N))) ≫
      (properOpenMate Λ k r p i h).app
        (((ProperOpenTensor Λ A).obj M).obj
          ((ProperOpenPull Λ k).obj ((ProperOpenPull Λ p).obj N))) =
    properOpenMateTensorMap Λ k r p i h M N ≫
      properOpenProjection Λ p ((ProperOpenShriek Λ k).obj M) N ≫
      (ProperOpenPush Λ p).map
        (properOpenTensorIso Λ k M ((ProperOpenPull Λ p).obj N)).hom := sorry

end AlgebraicGeometry.ProEtale


namespace WeilConjectures.IntegralSystemRealization

/-- The same projection-mate identity, for the intrinsic Gamma of the recorded simultaneous
realization, as equality of maps of unbounded strict semilinear systems before evaluation.
The realization argument supplies canonical operations and their normalized comparisons;
there is no boundedness, normalization or Tor hypothesis on the two input objects.
Source: Stacks 0F7B--0F7D and the node's ringed-diagram-site calculation
(blueprint: lem-sf-proper-open-projection-mate).

Proof: perform Steps 1--6 of the preceding theorem on the ringed diagram sites. In Step 1,
use the clopen lift from lem-cbc-strict-tower-proper-open-calculus. Step 2 restricts the
beta/tensor square to the open and uses full faithfulness and the open-unit normalization
of lem-sf-open-tensor-normalization. Step 3 checks the (identity,zero) clopen projection
on strict complexes, including every coefficient transition, and pastes with Step 2 to
obtain the alpha/tensor square. Step 4 transposes the left composite under the system
proper adjunction and obtains K(a_r) alpha_(R_r M tensor P_i N) P_p(delta_i). Step 5
transposes the right composite: use counit and tensor-comparison naturality, the proper
mate equation and the alpha/tensor square to obtain that same transpose. Step 6 observes
that the operations and comparisons act on all unbounded objects, without inverting
projection or the proper/open comparison.

Step 7 identifies this proper mate with z.properOpen.gamma, using exactly its intrinsic
adjunct characterization: restrict to i, factor k=b s, use the open unit, the clopen
identification J_s=S_s and direct-image composition. The normalized beta and projector
become identity; mate pasting reduces lambda P_i(gamma) to S_r epsilon_r followed by
eta_r S_r, which is identity by the triangle equation. The open Hom bijection makes this
the Gamma_Q of lem-sf-integral-compactification-system-realization.

Step 8 applies the single system adjunction Hom bijection to the equal transposes from
Steps 4--5. The equality is in System l E D, whose objects are derived complexes of strict
semilinear module systems. No evaluation or total-limit functor is applied; no faithfulness
of derived evaluation is assumed. All comparisons are natural in M and N. -/
theorem properOpenProjectionMateSystems
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E F o)
    {A B C D : Scheme.{u}}
    [A.Over (Spec (.of F.k))] [B.Over (Spec (.of F.k))]
    [C.Over (Spec (.of F.k))] [D.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of F.k))] [QuasiCompact (A ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of F.k))] [QuasiCompact (B ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (C ↘ Spec (.of F.k))] [QuasiCompact (C ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (D ↘ Spec (.of F.k))] [QuasiCompact (D ↘ Spec (.of F.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : System l E A) (N : System l E D) :
    (z.openComparisons.projection i).hom.app ((Operations.push l E o r).obj M, N) ≫
      (Operations.shriek l E o i).map
        (((properProjection l E o r).app M).app ((pull l E i).obj N)) ≫
      (Operations.shriek l E o i).map ((Operations.push l E o r).map
        ((calculus l E A).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M) ((z.compositors.square l E k r p i h).hom.app N)))) ≫
      (z.properOpen.gamma k r p i h).app
        ((calculus l E A).systemClosed.tensor.obj
          (M, (pull l E k).obj ((pull l E p).obj N))) =
    (calculus l E D).systemClosed.tensor.map
        (Prod.mkHom ((z.properOpen.gamma k r p i h).app M) (𝟙 N)) ≫
      ((properProjection l E o p).app ((Operations.shriek l E o k).obj M)).app N ≫
      (Operations.push l E o p).map
        ((z.openComparisons.projection k).hom.app (M, (pull l E p).obj N)) := sorry

end WeilConjectures.IntegralSystemRealization
