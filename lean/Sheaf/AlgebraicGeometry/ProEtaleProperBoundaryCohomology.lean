/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation
import Sheaf.Paper.FiniteLevelProEtaleBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction

/-!
# Boundary cohomology over a w-contractible affine base

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence; the etale motivation is Stacks Project, Tag 0F7B.
The pro-etale argument uses Tags 09AF, 09AH, 09C9, 09AG, 098H and 0946.
(blueprint: lem-sp-proetale-proper-boundary-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- The intrinsic constant-ring module category admits injective resolutions.
This reuses the recorded Grothendieck-category theorem at the actual site universes;
no equality of its object and morphism universes is imposed.
Source: Stacks Project, Section 07A5 and Theorem 079P, together with enough injectives
in a Grothendieck category (blueprint: lem-sp-proetale-proper-boundary-cohomology). -/
noncomputable instance properBoundary_hasInjectiveResolutions (X : Scheme.{u})
    (A : Type u) [CommRing A] :
    HasInjectiveResolutions (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  letI : IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
      (ProEt.topology X) (proEtaleConstantRing X A)).1
  inferInstance

/-- An injective constant-coefficient module sheaf of etale origin, extended by zero
from the specified clopen component over the open base, has zero positive cohomology.

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence; Stacks Tag 0F7B is only the etale motivation.
(blueprint: lem-sp-proetale-proper-boundary-cohomology).

Proof plan:

1. Put $F=j_!J$ and choose the supplied witness $\alpha:\nu_U^*J_0\cong J$. By [lem-cbc-proetale-
   extension-zero-comparison] there is an isomorphism $\nu_P^*(j^{\mathrm{et}}_!J_0)\cong
   j_!\nu_U^*J_0\cong F$. Regard both sheaves as complexes concentrated in degree zero: their
   degree-zero cohomology is the sheaf and all other cohomology is zero. This is an etale-origin
   witness for $F[0]$ in the sense of [def-weil-pbc-etale-origin-witness]. Exactness of $j_!$
   identifies its action on these degree-zero complexes with the sheaf $F$. No injectivity of
   $J_0$ is required.

2. Let $a:P_Z=P\times_Q Z\hookrightarrow P$ and $b:P_E\hookrightarrow P$ be the base changes of
   $z$ and $e$. They are complementary closed and open immersions, and $b$ is quasi-compact. These
   statements follow respectively from [lem-weil-pbc-closed-immersion-base-change], [lem-weil-pbc-
   open-immersion-base-change] and [lem-pc-quasi-compact-base-change]; complementarity is the
   inverse-image equality of the two subsets. Since $j=bh$, the adjunction of [lem-weil-extension-
   by-zero-adjunction] identifies $j_!$ with $b_!h_!$: both are left adjoint to $h^*b^*=j^*$, and
   the adjunction bijections give the canonical identification. Thus $a^*F=a^*b_!h_!J=0$ by the
   $i^{-1}j_!=0$ clause of [lem-weil-pbc-proetale-ringed-open-closed] on $P$. All coefficient
   rings are the inverse images of the same constant ring $A$.

3. Write $p_Z:P_Z\to Z$ for the projection. Apply [thm-weil-pbc-finite-level-proetale] to the
   Cartesian square with horizontal arrows $a,z$, vertical arrows $p_Z,p$, and input $F[0]$.
   Properness of $p$ and finiteness of the discrete commutative ring $A$ are hypotheses of the
   item; step 1 supplies exactly the etale-origin witness required by the theorem. It gives
   $z^*Rp_*F[0]\cong Rp_{Z,*}a^*F[0]=0$ by step 2. The derived direct image carries zero to zero
   because its additive injective-resolution construction carries the zero resolution to zero.

4. For an integer $q$ set $G_q=\mathcal H^q(Rp_*F[0])$. The module inverse image $z^*$ is exact by
   [lem-weil-pbc-proetale-immersion-limit-preservation]. Applying it to the kernels and images
   defining cohomology therefore gives $z^*G_q=\mathcal H^q(z^*Rp_*F[0])=0$. Apply the exact open-
   closed sequence of [lem-weil-pbc-proetale-ringed-open-closed] on $Q$ to $G_q$. Its final term
   is zero, so its counit identifies $G_q\cong e_!e^*G_q$. The hypothesis that $e$ is quasi-
   compact is exactly the hypothesis needed for this sequence.

5. Apply [lem-weil-pbc-proetale-shriek-specialization-zero] with $X=Q$, $U=E$, the given closed
   immersion $z$, and the affine site object $V=Q$ with its identity map. An open immersion is
   weakly etale, $E\times_Q Z$ is empty, and every point of $Q$ specializes into $Z$ by
   hypothesis. It gives $(e_!H)(Q)=0$ for every abelian sheaf $H$ on $E$. The same vanishing holds
   for constant-$A$ module sheaves: [def-weil-extension-by-zero] defines their extension by
   sheafifying the identical zero-or-one-summand presheaf, and [def-weil-presheaf-modules-
   sheafification] explicitly takes the underlying abelian sheafification and then extends the
   scalar action. Forgetting the action therefore gives exactly the abelian extension used by the
   lemma. With $H$ underlying $e^*G_q$, step 4 yields $G_q(Q)=0$.

6. Use [lem-weil-pbc-wcontractible-affine-weakly-contractible] with $X=Q$ and its identity site
   object. The ring-retraction assumption in the item makes this object weakly contractible in the
   full small pro-etale site, with the stipulated universes. By [lem-weil-pbc-proetale-weakly-
   contractible-evaluation-exact], evaluation at this object on constant-$A$ module sheaves
   preserves homology. In particular, for every complex $C^\bullet$ of such sheaves, $\mathcal
   H^q(C^\bullet)(Q)=H^q(C^\bullet(Q))$.

7. The small-site module category on $P$ is Grothendieck by [prop-pur-kinjective-resolutions-
   exist], hence has enough injectives by [lem-sp-grothendieck-enough-injectives]. Choose an
   injective resolution $F\to I^\bullet$ with $I^n=0$ for $n<0$ [def-sp-injective-resolutions]; by
   definition $H^q(P_{\mathrm{proet}},F)=H^q(I^\bullet(P))$. By part (2) of [lem-weil-pbc-dplus-
   injective-representative] the bounded-below injective complex $I^\bullet$ is K-injective. In
   [def-weil-pbc-proetale-operations], $Rp_*(QI^\bullet)=Q(p_*I(I^\bullet))$ for the functorial
   K-injective resolution $I^\bullet\to I(I^\bullet)$. This is a quasi-isomorphism between
   K-injective complexes, hence a homotopy equivalence by [lem-weil-pbc-kinjective-hom-derived];
   the additive termwise functor $p_*$ preserves homotopy equivalences, so $p_*I^\bullet$
   represents $Rp_*F[0]$, as $QI^\bullet\cong F[0]$. The direct-image section formula of [def-
   weil-pbc-proetale-operations] gives $(p_*I^n)(Q)=I^n(P)$, since $P\times_Q Q=P$. Thus, by step
   6 and then step 5,
   $H^q(P_{\mathrm{proet}},F)=H^q(I^\bullet(P))=H^q((p_*I^\bullet)(Q))=G_q(Q)=0$. This proves the
   requested $q>0$ vanishing (and also degree zero). This argument resolves $F$ on $P$ and never
   assumes that $j_!J$ is injective.
-/
theorem proEtale_proper_boundary_cohomology
    (R : Type u) [CommRing R]
    (hR : ∀ (S : Type u) [CommRing S] (φ : R →+* S),
      φ.FaithfullyFlat → φ.WeaklyEtale →
        ∃ r : S →+* R, r.comp φ = RingHom.id R)
    {Z E P U : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion z] (e : E ⟶ Spec (CommRingCat.of R))
    [IsOpenImmersion e] [QuasiCompact e]
    (hcomplement : Set.range e = (Set.range z)ᶜ)
    (hspecializes : ∀ x : Spec (CommRingCat.of R), ∃ t : Z, Specializes x (z t))
    (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (h : U ⟶ pullback p e) [IsOpenImmersion h]
    (hclosed : IsClosed (Set.range h))
    [QuasiCompact (h ≫ pullback.fst p e)]
    (A : Type u) [CommRing A] [Finite A]
    (J : proEtaleRingModules U (proEtaleConstantRing U A)) [Injective J]
    (hetale : ∃ J₀ : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)),
      Nonempty ((sfIntrinsicModuleEquivalence U A).functor.obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).obj J₀) ≅ J))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((SheafOfModules.toSheaf
      ((sheafCompose (ProEt.topology P)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing P A)) ⋙
        sheafToPresheaf (ProEt.topology P) AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation P.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
            (op (ProEt.mk (𝟙 P)))).rightDerived q).obj
              ((sfIntrinsicExtensionByZero (h ≫ pullback.fst p e) A).obj J)) := by
  sorry

end AlgebraicGeometry.Scheme
