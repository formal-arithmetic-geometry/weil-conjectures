/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison

public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.GeometricStalkCohomology
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ComparisonTorInterval

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Scalar projection formula and Tor bound for an open immersion

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-cor-sf-direct-image-ctf/det-cor-sf-direct-image-ctf-open-tor.md
(blueprint: det-cor-sf-direct-image-ctf-open-tor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Scalar projection and the all-module-sheaf Tor bound for an open immersion.
Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-sf-direct-image-ctf,
node det-cor-sf-direct-image-ctf-open-tor; Stacks Tags 0F10, 0F12 and 09A6.
(blueprint: det-cor-sf-direct-image-ctf-open-tor)

Proof (the node's ten steps):

1. Test the Tor hypothesis with the tensor unit $\underline A_U$: $K\otimes_A^{\mathbf
   L}\underline A_U\cong K$, so $\mathcal H^q(K)=0$ outside $[a,b]$. If $a>b$, all these sheaves
   vanish, hence $K=0$ and all three conclusions hold for the zero object. We henceforth have
   $a\le b$.
   Dependencies: def-kun-tor-amplitude, def-kun-derived-tensor,
   lem-weil-pbc-unbounded-derived-iso-cohomology.

2. The finite-type schemes $X,U$ are Noetherian: apply finite type over a Noetherian base to
   $\operatorname{Spec}k$ (a field has just the ideals $0,k$). They are quasi-compact, and are
   quasi-separated by the locally Noetherian criterion. Every open subscheme of a Noetherian
   scheme is Noetherian; thus the inverse image in $U$ of each affine open of $X$ is
   quasi-compact. Consequently $j$ is quasi-compact. Its diagonal is an isomorphism since $j$ is a
   monomorphism, so $j$ is quasi-separated. Test on a basis of affine étale $V\to X$ factoring
   through an affine open of $X$, with the first arrow of finite presentation. These form a basis
   by the local definition of étale morphisms and affine open coverings. Write $W\subseteq X$ for
   that affine open. For any affine open $T\subseteq X$, the open $W\cap T\subseteq W$ is
   quasi-compact because $X$ is Noetherian. Cover it by finitely many distinguished opens $D(f_i)$
   of $W$. Their inverse images in the affine $V$ are the distinguished opens $D(f_i|_V)$, hence
   are quasi-compact; their finite union is $V\times_XT$. Thus $V\to X$ is quasi-compact. By the
   étale finite-presentation lemma $V$ is of finite type over $k$. Its open subscheme
   $V_U=V\times_XU$ is Noetherian and quasi-compact; its inclusion in $V$ is a quasi-compact open
   immersion, hence of finite type. Thus $V_U$ is also of finite type over $k$ (on affine charts,
   composing finite lists of algebra generators again gives a finite list). Both $V$ and $V_U$ are
   qcqs and have finite torsion étale cohomological dimension by clause (2) of the finite-cd
   theorem. Clause (1) also gives finiteness of $\operatorname{cd}(j)$.
   Dependencies: lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qc-open-immersion-finite-type,
   lem-kun-etale-lfp, def-weil-etale-morphism, lem-kun-0f10, def-sbc-locally-finite-presentation,
   def-weil-finite-type-morphism.

3. We first record the cohomological bound, without tensoring. For any $E\in D(U_{\mathrm{ét}},A)$
   concentrated in $[a,b]$, apply the truncation spectral sequence to $j_*$. The module-sheaf
   categories on small representatives of these sites are Grothendieck abelian. A bounded-below
   injective representative is available, as required by that spectral sequence. Forgetting
   $A$-modules to abelian sheaves commutes with bounded-below derived direct image. Since $A$ is
   killed by a power of $\ell$, each underlying cohomology sheaf is torsion. The definition of
   $d\ge\operatorname{cd}(j)$ therefore gives $R^pj_*\mathcal H^q(E)=0$ for $p>d$. The spectral
   sequence is $E_2^{p,q}=R^pj_*\mathcal H^q(E)\Rightarrow\mathcal H^{p+q}(Rj_*E)$; its finite,
   exhaustive, separated filtration has associated graded $E_\infty^{p,q}$. Nonzero entries can
   occur only for $0\le p\le d$ and $a\le q\le b$, so every associated graded in total degree
   outside $[a,b+d]$ is zero. A finite filtration with all its successive quotients zero has zero
   underlying object, giving $Rj_*E\in D^{[a,b+d]}$. In particular this applies to $K$.
   Dependencies: lem-weil-pbc-ring-sheaves-grothendieck,
   lem-weil-pbc-dplus-injective-representative,
   lem-weil-pbc-module-abelian-derived-direct-image-comparison, def-kun-cd, thm-sp-truncation-e2.

4. For a testing object $V$ as in step 2, write $V_U=V\times_XU$. The localized étale site at $V$
   is the small étale site of $V$; the equivalence extends to constant $A$-module sheaves by using
   on each corresponding object the identical abelian group and scalar endomorphisms. Restriction
   of a K-injective module complex to a localized ringed site is K-injective. Also $j_*$ sends
   K-injective complexes to K-injective complexes: its left adjoint $j^*$ on constant-coefficient
   modules is exact. Thus if $I$ is a K-injective representative of any $E\in
   D(U_{\mathrm{ét}},A)$, both sides of the natural comparison
   $$\lambda_E:R\Gamma(V,Rj_*E)\xrightarrow{\sim}R\Gamma(V_U,E|_{V_U})$$ are computed by the
   identical complex $\Gamma(V,j_*I)=\Gamma(V_U,I)$. More generally, for every étale $W\to V$, the
   equality $(j_*I)|_V(W)=I(W\times_XU)=j_{V,*}(I|_{V_U})(W)$ identifies the complexes $(j_*I)|_V$
   and $j_{V,*}(I|_{V_U})$ section by section. Since both $I|_{V_U}$ and $(j_*I)|_V$ are
   K-injective, this also identifies $(Rj_*E)|_V$ with $Rj_{V,*}(E|_{V_U})$. The sheaf counits on
   both sides send a section on $W\times_XU$ to its restriction on the same object; hence they
   coincide under these identities. Computing the derived adjunction on these K-injective models
   gives the same counits. Thus $\lambda$ is natural and identifies the counit of the composite
   right adjoint with the composite of counits. Restriction of derived tensor agrees with derived
   tensor of restrictions by the ringed-topos derived tensor pullback theorem, since slice
   restriction is exact. These observations apply to unbounded $E$; no boundedness of a tensor
   with an arbitrary module is being presumed.
   Dependencies: lem-weil-pbc-etale-site-localization-open, def-pur-localized-ringed-site,
   lem-pur-kinjective-restrict-localized, prop-weil-pbc-inverse-image-modules-exact,
   lem-weil-pbc-right-adjoint-preserves-kinjective,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-kinjective-total-derived.

5. Put $P_V(E,M)=\mathrm{PF}_{V,A}(E,M)$ for the scalar projection map, and let
   $p=\mathrm{PF}_j(K,\underline M_X)$ be the projection map in the statement. The canonical maps
   satisfy $$\lambda_{K\otimes^{\mathbf L}\underline M_U}\circ R\Gamma(V,p)\circ
   P_V((Rj_*K)|_V,M)=P_{V_U}(K|_{V_U},M)\circ(\lambda_K\otimes1_M).$$ Use step 4 to identify
   $(Rj_*K)|_V$ with $Rj_{V,*}(K|_{V_U})$, and write $K$ for its restriction in the following
   calculation. Restricting the defining adjunct of $p$ gives the adjunct for $j_V$: the counits
   agree by step 4, and restriction of the tensor comparison is the tensor comparison on the
   localized site. Here is the adjunction calculation establishing equality of arrows. On the
   localized sites write $c_V^*$ for the constant-complex functor, $J^*$ for restriction along
   $j_V:V_U\hookrightarrow V$, and $c_{V_U}^*=J^*c_V^*$. Their right adjoints are $R\Gamma(V,-)$,
   $Rj_{V,*}$, and $R\Gamma(V_U,-)$, respectively. Under $\lambda$, the counit for the composite
   left adjoint $J^*c_V^*$ is $$\varepsilon^{c_{V_U}}_K=\varepsilon^J_K\circ
   J^*\varepsilon^{c_V}_{Rj_{V,*}K}.$$ By the two definitions of projection morphisms, taking the
   adjunct of either side of the displayed equality gives this same composite tensored with
   $1_{c_{V_U}^*M}$, preceded by the same pullback tensor comparison. Indeed the left side first
   uses $\varepsilon^{c_V}$ and then $\varepsilon^J$, while the right side uses their displayed
   composite. The comparisons for $J^*c_V^*$ and for $J^*$ after $c_V^*$ agree: on K-flat
   representatives their ordinary constant-presheaf comparisons have identity components, and
   restriction leaves each sectionwise tensor $s\otimes m$ unchanged; sheafification and
   localization therefore give identical derived comparisons. Naturality now moves the two counits
   past these comparisons, and the adjunction triangle identities cancel the inserted unit-counit
   pairs. Hence the adjuncts, and therefore the arrows, agree. This supplies the compatibility
   assertion needed in the blueprint's chain of isomorphisms.
   Dependencies: def-kun-constant-projection-morphism, def-kun-projection-formula-map,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-kinjective-total-derived,
   lem-pur-kinjective-restrict-localized.

6. Apply the scalar projection theorem on $V$ to $((Rj_*K)|_V,M)$ and on $V_U$ to $(K|_{V_U},M)$.
   Its hypotheses hold by step 2 and because $A$ is a torsion ring. It permits arbitrary derived
   objects and arbitrary modules, so no finite presentation of $M$ or finite projective dimension
   is assumed. Both maps $P_V,P_{V_U}$ in step 5 are isomorphisms. The comparisons $\lambda$ are
   isomorphisms by step 4. The equality of step 5 therefore shows that $R\Gamma(V,p)$ is an
   isomorphism for every testing $V$.
   Dependencies: lem-kun-0f12, lem-kun-0f10.

7. These tests detect $p$ even when its source has not yet been proved bounded below. To see this
   explicitly, take an arbitrary K-injective representative $I$ of its cone $C$. Slice restriction
   is K-injective, so $H^n(V,C)=H^n(I(V))$. The presheaf $V\mapsto H^n(I(V))$ is the sectionwise
   kernel of $d^n$ modulo the sectionwise image of $d^{n-1}$. Exact sheafification identifies its
   associated sheaf with $\ker d^n_I/\operatorname{im}d^{n-1}_I=\mathcal H^n(C)$. Step 6 makes the
   presheaf zero on the testing basis. Every object has a covering by basis objects, so its
   associated sheaf is zero. Hence every $\mathcal H^n(C)$ vanishes and the cohomology criterion
   for the unbounded derived category makes $C=0$ and $p$ invertible. This proves clause (1).
   Dependencies: prop-weil-pbc-kinjective-resolutions-exist,
   lem-pur-kinjective-restrict-localized, lem-weil-pbc-sheafification-exact,
   lem-weil-pbc-unbounded-derived-iso-cohomology.

8. For any $A$-module $M$ put $E_M=K\otimes_A^{\mathbf L}\underline M_U$. By the Tor hypothesis
   $E_M$ has cohomology in $[a,b]$, so step 3 gives $Rj_*E_M$ in $[a,b+d]$. Clause (1) identifies
   it with $Q\otimes_A^{\mathbf L}\underline M_X$, where $Q=Rj_*K$. Thus every constant-module
   test of $Q$ has cohomology in $[a,b+d]$.
   Dependencies: def-kun-tor-amplitude.

9. Fix a geometric point $\bar x$ of $X$. A derived stalk is pullback to that point, and pullback
   is compatible with derived tensor. Stalks commute with cohomology, and the stalk of a constant
   sheaf $\underline M_X$ is $M$. Step 8 therefore gives $$H^r(Q_{\bar x}\otimes_A^{\mathbf
   L}M)=0\quad(r\notin[a,b+d])$$ for every $A$-module $M$. For an arbitrary sheaf $N$ of
   $A$-modules on $X_{\mathrm{ét}}$, take the particular module $M=N_{\bar x}$ separately at each
   geometric point. The same derived-tensor comparison gives $$(Q\otimes_A^{\mathbf L}N)_{\bar
   x}\cong Q_{\bar x}\otimes_A^{\mathbf L}N_{\bar x},$$ so $\mathcal H^r(Q\otimes_A^{\mathbf L}N)$
   has zero stalks for $r\notin[a,b+d]$. Conservativity of geometric stalks applied to the map
   from this abelian sheaf to zero makes it zero. This proves the all-module-sheaf Tor bound of
   clause (2), with no constructibility assumption on $K,N$ and without asserting that geometric
   stalks are conservative on the pro-étale site.
   Dependencies: lem-kun-stalk-as-pullback, lem-kun-inverse-image-monoidal,
   lem-kun-stalks-of-cohomology, lem-weil-pbc-constant-sheaf-geometric-stalk,
   lemma-weil-pbc-geometric-stalk-conservative, def-kun-tor-amplitude.

10. Step 1 gives $K\in D^+$ and step 3 gives $Q=Rj_*K\in D^{[a,b+d]}$. The morphism $j$ is qcqs by
   step 2. The bounded-below comparison theorem therefore identifies
   $Rj_{\mathrm{proét},*}\nu_U^*K$ with $\nu_X^*Q$. Apply the comparison Tor-interval theorem to
   the finite commutative ring $A$, the bounded-below étale object $Q$, and the interval $[a,b+d]$
   (nonempty since $d\ge0$). By clause (2) its étale Tor-amplitude hypothesis holds, and the
   theorem gives the same bound against every pro-étale module sheaf. For every pro-étale module
   sheaf $N$, tensor the displayed isomorphism with $N$ and take cohomology. This identifies each
   $\mathcal H^r(Rj_{\mathrm{proét},*}\nu_U^*K\otimes_A^{\mathbf L}N)$ with $\mathcal
   H^r(\nu_X^*Q\otimes_A^{\mathbf L}N)$, which vanishes for $r\notin[a,b+d]$. This proves clause
   (3).
   Dependencies: prop-weil-pbc-comparison-direct-image, lem-exc-comparison-tor-interval,
   def-weil-proetale-tor-amplitude.
-/
theorem sf_directImage_ctf_open_tor
    (k : Type u) [Field k] [IsSepClosed k]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (l ^ n) • x = 0)
    {U X : Scheme.{u}}
    (aU : U ⟶ Spec (.of k)) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aU] [QuasiCompact aU]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ X) (_hj : j ≫ aX = aU) [IsOpenImmersion j]
    (d : ℕ)
    (_hd : @Scheme.Hom.torsionEtaleCohomologicalDimension _ _ j
      (@quasiCompact_of_compactSpace U X j
        ((quasiCompact_iff_compactSpace aU).mp inferInstance)
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian aX)))
      (@QuasiSeparated.of_quasiSeparatedSpace U X j
        (@IsLocallyNoetherian.quasiSeparatedSpace U
          (LocallyOfFiniteType.isLocallyNoetherian aU))) ≤ (d : ℕ∞))
    (a b : ℤ)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hK : Etale.DerivedCategory.hasTorAmplitudeIn A U a b K) :
    (∀ (M : ModuleCat.{u + 1} A),
      IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)))) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A X a (b + (d : ℤ))
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj K) ∧
    (Nonempty
      (((ProEtale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
          ((AlgebraicGeometry.ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj K)) ≅
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj K)))) ∧
    AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} A) X a (b + (d : ℤ))
      (((ProEtale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj K))) := by
  sorry

end AlgebraicGeometry.Etale
