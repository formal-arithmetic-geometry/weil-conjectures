/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence

/-!
# Constructible finite-ring sheaves have etale origin

Source: Stacks Project, Tags 09AK and 099Y, with the blueprint's global finite partitions
(blueprint: lem-weil-pbc-finite-ring-constructible-sheaf-origin).

The two recorded constructibility predicates use different equivalent encodings of
constant-coefficient module sheaves. The equivalence below is identified with the
recorded comparison pullback on underlying additive sheaves, and the last clause
requires that identification to respect the constant scalar action. Thus it specifies
the given pullback, including its module structure.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The comparison pullback induces the equivalence of constructible module sheaves.
The finite ring is allowed to be zero and the scheme is arbitrary, including empty.
The natural isomorphism identifies the equivalence with `comparisonUpperStar`;
its constant-scalar compatibility makes this an identification of module sheaves.
Source: Stacks Project, Tag 09AK, lemma-compare-constructible, and Tag 099Y,
lemma-compare-locally-constant, with global finite partitions as in the blueprint
(blueprint: lem-weil-pbc-finite-ring-constructible-sheaf-origin).

Proof plan (the node's six steps):
1. Let $G$ be a constructible etale $B$-module sheaf, with its finite global partition
$i_k:S_k\to T$. By [lem-weil-pbc-finite-locally-constant-module-values], its finite constant
values give locally constant restrictions with finite stalks. The isomorphism
$i_{k,\mathrm{proet}}^*\nu_T^*G\cong\nu_{S_k}^*i_{k,\mathrm{Et}}^*G$ of [lem-weil-pbc-
comparison-pullback] and clause (a) of [lem-sf-proetale-locally-constant-origin] show that each
restriction of $\nu_T^*G$ is lisse. The same partition, with the same subscheme structures,
therefore witnesses intrinsic constructibility. No affine-local-to-global constructibility
criterion is used.

2. Write $F_T=\nu_T^*$ and $R_T=\nu_{T,*}$. The unit $\eta_G:G\to R_TF_TG$ is invertible for
every etale $B$-module sheaf by [prop-weil-pbc-site-comparison-finite-level]. The adjunction
[def-weil-pbc-site-comparison-morphism] identifies $\operatorname{Hom}(F_TG,F_TH)$ with
$\operatorname{Hom}(G,R_TF_TH)$, and postcomposition with $\eta_H^{-1}$ identifies the latter
with $\operatorname{Hom}(G,H)$. Thus $F_T$ is fully faithful on all module sheaves. Call a pro-
etale sheaf classical if it is isomorphic to $F_TG$ for some etale sheaf. It is classical
exactly when its counit $\epsilon_P:F_TR_TP\to P$ is invertible: one implication takes $G=R_TP$,
and the other uses naturality and the triangle identity $\epsilon_{F_TG}\circ F_T\eta_G=1$. In
particular fully faithful $F_T$ lifts an isomorphism between two of its images uniquely,
together with the inverse.

3. Being classical is Zariski-local. For an open immersion $v:V\to T$, restriction of a pro-
etale sheaf is evaluation on objects over $V$, by [lem-weil-proetale-weakly-etale-localization].
The explicit direct-image formula in [def-weil-pbc-site-comparison-morphism] consequently gives
$(R_TP)|_V=R_V(P|_V)$: both evaluate to $P(W)$ for etale $W\to V$. Together with [lem-weil-pbc-
comparison-pullback], this identifies $\epsilon_P|_V$ with $\epsilon_{P|_V}$, since the
evaluation counit and its adjoint restriction are the same maps. If $P$ is classical on an open
cover, these restricted counits are invertible by step 2. The open family is a pro-etale cover:
its pullbacks cover each affine object, and quasi-compactness of that object supplies a finite
subcover by quasi-compact affine opens. Locality for covering families, clause (1) of [lem-cbc-
proetale-stalk-conservative], then makes $\epsilon_P$ invertible globally. Only covering
locality is used, never conservativity of geometric stalks on arbitrary pro-etale sheaves.

4. Classical $B$-module sheaves are closed under extensions. For $0\to F_TG'\to P\to
F_TG''\to0$, [lem-sf-derived-ses-triangle] gives its distinguished triangle with boundary
$\delta:F_TG''\to(F_TG')[1]$. Exactness of $F_T$ follows from [prop-weil-pbc-site-comparison-
finite-level]; [lem-sf-exact-functor-derived-triangulated] makes its termwise derived functor
triangulated. Full faithfulness on $D^+$ in [thm-weil-pbc-site-comparison] uniquely lifts
$\delta$ to $\varphi:G''\to G'[1]$, since both arguments are bounded below. By TR1 and inverse
rotation TR2 in [def-weil-triangulated-category], choose a triangle in $D^+$ (which is closed
under shifts and cones) $G'\to H\to G''\xrightarrow{\varphi}G'[1]$. Rotate its image and the
triangle of the extension to start with $\delta$, and apply TR3 with identities on the first two
objects. [lem-sf-triangle-morphism-iso] gives $F_TH\cong P$. The long exact cohomology sequence
[lem-sf-derived-homology-long-exact] shows $H$ has zero cohomology outside degree zero; by [lem-
sf-derived-concentrated-single], $H\cong G[0]$ for $G=H^0(H)$. Applying $H^0$ gives an
isomorphism of sheaves $F_TG\cong P$, since exactness computes $H^0(F_TG[0])=F_TG$. No
constructibility of $G$ is claimed at this step.

5. Prove by induction on $N\geq0$, for every scheme $Y$, that every pro-etale $B$-module sheaf
$P$ lisse on a finite constructible locally closed partition with at most $N$ nonempty strata is
classical. If $N=0$, $Y$ is empty and the sheaf is the zero sheaf, namely $\nu_Y^*0$. If $N=1$,
the immersion of the unique nonempty stratum has image all of $Y$; it need not be an
isomorphism. Avoid assuming otherwise: use the local argument below with its closed-stratum
restriction, which applies for every $N\geq1$. Given $y\in Y_k$, [lem-sf-constructible-
partition-local-closed-stratum] supplies affine open $V\ni y$ where $S_k\cap V$ is closed and
$U=V\setminus(S_k\cap V)$ is quasi-compact. Give each restricted stratum the fibre-product
structure $S_i\times_Y V$, not an arbitrary factorization through $V$. Restrictions of lisse
sheaves to these open subschemes are lisse: restrict their trivializing covers and constant
values; geometric stalks on an open are the same stalks. The immersion $i:Z=S_k\times_YV\to V$
is closed: by [def-weil-closed-immersion] an immersion is locally a closed immersion in an open
neighbourhood of its image. Since its image here is closed in $V$, cover $V$ by that
neighbourhood and its image complement; the structure-sheaf map is surjective on the former and
has zero target on the latter, so it is surjective everywhere. Together with the closed
topological embedding this is the definition of closed immersion, and $j:U\to V$ is quasi-
compact because $V$ is affine and $U$ is quasi-compact. On $U$ the remaining strata have at most
$N-1$ nonempty members, so induction gives $j^*P_V\cong\nu_U^*G_U$. On $Z$, $i^*P_V$ is lisse,
so clause (b) of [lem-sf-proetale-locally-constant-origin] gives $i^*P_V\cong\nu_Z^*G_Z$. By
[lem-sf-proetale-open-closed-sequence], $0\to j_!j^*P_V\to P_V\to i_*i^*P_V\to0$ is exact. By
[lem-cbc-proetale-extension-zero-comparison] its first term is $\nu_V^*(j_!G_U)$. By [lem-weil-
pbc-closed-immersion-integral-separated-uc] a closed immersion is affine, and [lem-weil-pbc-
affine-morphism-permanence] makes it quasi-compact and quasi-separated; [prop-weil-pbc-
comparison-direct-image] applied to $G_Z[0]\in D^+$ and followed by $H^0$ identifies its last
term with $\nu_V^*(i_*G_Z)$. The degree-zero identification follows from [lem-weil-pbc-left-
exact-injective-resolution-degree-zero]: direct image is left exact, being a right adjoint, and
these small-site module sheaf categories are Grothendieck by [lem-weil-pbc-ring-sheaves-
grothendieck], hence have enough injectives by [lem-sp-grothendieck-enough-injectives]. Thus
both end terms are classical. Step 4 makes $P_V$ classical and step 3 makes $P$ classical. When
$U$ is empty the first term is zero; the argument still applies.

6. Let $P$ be intrinsically constructible, and choose $G$ with $\nu_T^*G\cong P$ by step 5.
Retain the original global finite partition $i_k:S_k\to T$ of $P$. By [lem-weil-pbc-comparison-
pullback], $\nu_{S_k}^*(i_k^{-1}G)\cong i_k^*P$. Clause (b) of [lem-sf-proetale-locally-
constant-origin] gives a lisse etale sheaf $H_k$ with $\nu_{S_k}^*H_k\cong i_k^*P$. Full
faithfulness from step 2, applied on $S_k$, lifts the resulting isomorphism to $i_k^{-1}G\cong
H_k$. By [lem-weil-pbc-finite-locally-constant-module-values], each $H_k$ admits etale local
trivializations with finite constant $B$-module values. Thus precisely the original partition
witnesses constructibility of $G$ in [def-weil-pbc-etale-constructible-sheaf]. Combined with
preservation in step 1 and full faithfulness in step 2, this proves the asserted equivalence.
The argument works for arbitrary $T$, the zero finite ring, zero sheaves, and empty strata; it
neither replaces $B$ by a valuation-ring quotient nor equates global finite partitions with
affine-local constructibility.
-/
theorem finiteRing_constructibleSheaf_origin (T : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B] :
    ∃ e :
      ObjectProperty.FullSubcategory (IsConstructibleEtaleModuleSheaf (T := T)
        (Λ := ULift.{u + 1, u} B)) ≌
      ObjectProperty.FullSubcategory (IsConstructibleProEtaleModuleSheaf T B),
    ∃ α :
      ObjectProperty.ι (IsConstructibleEtaleModuleSheaf (T := T)
          (Λ := ULift.{u + 1, u} B)) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
        sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) ≅
      e.functor ⋙ ObjectProperty.ι (IsConstructibleProEtaleModuleSheaf T B) ⋙
        SheafOfModules.toSheaf
          ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B)),
    ∀ (G : ObjectProperty.FullSubcategory (IsConstructibleEtaleModuleSheaf (T := T)
        (Λ := ULift.{u + 1, u} B)))
      (U : T.ProEtᵒᵖ) (b : ULift.{u + 1, u} B)
      (m : ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).obj G.obj).obj.obj U),
      ((α.hom.app G).hom.app U) (b • m) =
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} B)))).app U).hom b •
          (@id ((e.functor.obj G).obj.val.obj U) (((α.hom.app G).hom.app U) m)) := by
  sorry

end AlgebraicGeometry.Scheme
