/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import Sheaf.AlgebraicGeometry.EtaleGenericStratumMate
import Sheaf.Paper.StratumAmbientProjectionData

/-! # Internal Hom from extension along a stratum

Source: Weil blueprint, six functors, sk-prop-sf-rf-shriek-preservation,
node order 2069 (blueprint: lem-weil-stratum-ambient-hom).

Both formulas are natural isomorphisms on the product of the opposite source derived
category and the target derived category. All derived categories are ordinary and unbounded.
The etale category uses the recorded fixed-scalar presentation. The pro-etale category
uses the recorded intrinsic constant-ring presentation and its canonical coefficient map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The étale ambient stratum identity, natural in both arguments.
Source: blueprint six-functors basics, stratum preservation
(blueprint: lem-weil-stratum-ambient-hom).

The evaluation-normalized immersion internal-Hom isomorphism supplies the result by
forgetting its additional evaluation compatibility. Its two immersion functors are exactly
`j_! Ri_*` and `Ri^! j^*`, by their definitions. -/
theorem nonempty_stratumAmbientHomIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty ((immersionLowerShriek A i j).op.prod
        (𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X) ≅
      (𝟭 (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))ᵒᵖ).prod
        (immersionUpperShriek A i j) ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) S) ⋙
          R((i ≫ j)_*[ModuleCat.{u + 1} A])) := by
  exact ⟨(immersionInternalHomIso A i j).choose⟩

end Etale

/-- The pro-etale ambient stratum identity on a Noetherian target.
Source: Weil blueprint, order 2069 (blueprint: lem-weil-stratum-ambient-hom).

Proof: U and its open complement to i(S) are Noetherian, so the complement is quasi-compact.
Use the pro-etale ringed open-closed localization sequence to get exactness of closed
pushforward, its invertible inverse-image counit, disjoint-support vanishing, and joint
acyclicity detection by closed and complementary-open restrictions. The ambient closed
adjunction is computed by the right derived functor of i* ker(N → v* v* N), and composes
with the exact open extension/restriction adjunction. Pullback preserves K-flat complexes
and derived tensor. Apply the ringed-slice projection formula to a K-flat representative
of the target tensor factor; extension by zero commutes with direct sums, hence with its
total tensor complex. Check the closed projection formula on the two restrictions using
the counit and disjoint-support vanishing, then compose the open and closed formulas.
K-injective resolutions compute ordinary direct image and its composition. Hom-complex
currying with K-flat/K-injective representatives gives tensor-Hom adjunction on both sites.
For a test Q, tensor-Hom, the composed projection formula, shriek adjunction, tensor-Hom
on S, and ordinary direct-image adjunction give the natural bijection of representable
Hom functors. Evaluating this bijection and its inverse on identities gives the isomorphism,
and naturality in P and M makes it a bifunctor isomorphism. No constructible preservation,
boundedness, finite Tor amplitude, or biduality is used.

Complete DAG proof plan:
1. Use the chosen closed-then-open factorization $s=ji$. In the pro-etale case, $U$ is Noetherian
by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Apply the same statement to the open
complement $V=U\setminus i(S)$ and to its intersections with affine opens of $U$: all are
quasi-compact. Thus $v:V\hookrightarrow U$ is a quasi-compact morphism. This verifies the
hypotheses of the pro-etale closed-localization and closed-support statements used below. No such
hypothesis is needed on the etale side. The Noetherian assumption restores the scheme context of
the enclosing unit; the imported standalone node did not state it. Dependencies:
lem-weil-pbc-noetherian-open-subscheme-noetherian.

2. The etale closed direct image $i_*$ is exact: at points of $i(S)$ its stalk is the
corresponding stalk on $S$ by [lemma-openclosed-stalk-lowerstar]; outside $i(S)$ it is zero, since
a neighbourhood disjoint from $i(S)$ has empty pullback. Exactness of geometric stalks and their
conservativity therefore check exactness of $i_*$ on every short exact sequence. The same
assertions hold for constant-coefficient modules by forgetting the module action. Its
inverse-image counit is an isomorphism by [lem-kun-04ca]. In the pro-etale case
[lem-weil-pbc-proetale-ringed-open-closed], applied on $U$ with the quasi-compact complement from
step 1, directly gives exactness, the closed counit isomorphism, and $v^{-1}i_*=0$. Consequently
$Ri_*=i_*$, computed termwise, in both cases. Moreover $i^{-1}$ and $v^{-1}$ detect zero sheaves:
in the etale case a sheaf zero on $V$ is supported on $i(S)$ and [lem-kun-04ca] identifies it with
$i_*G$, so its inverse image on $S$ is $G$; in the pro-etale case the short exact localization
sequence of [lem-weil-pbc-proetale-ringed-open-closed] proves this directly. Since both inverse
images are exact, they also jointly detect acyclic complexes, by applying this argument to each
cohomology sheaf. Dependencies: lemma-openclosed-stalk-lowerstar,
prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative, lem-kun-04ca,
lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-site-pullback-abelian-exact.

3. For any of the scheme maps in this argument, inverse image with constant coefficients is exact:
its underlying abelian functor is the exact site inverse image, and the inverse image of the
constant ring is the same constant ring. The module adjunction is
[lem-weil-pbc-ringed-topoi-module-adjunction]. It derives on the whole unbounded categories as
follows. Choose a K-injective resolution $N\to I$ on the source site using
[prop-pur-kinjective-resolutions-exist]. The direct image of $I$ is K-injective by
[lem-weil-pbc-right-adjoint-preserves-kinjective], since inverse image is exact. The
homotopy-category adjunction [lem-weil-pbc-termwise-adjunction-homotopy] and
[lem-weil-pbc-kinjective-hom-derived] then give
$$\operatorname{Hom}(t^{-1}Q,N)=\operatorname{Hom}_{K}(t^{-1}Q,I)=\operatorname{Hom}_{K}(Q,t_*I)=
\operatorname{Hom}(Q,Rt_*N).$$
Here any representative of $Q$ can be used. Thus $t^{-1}\dashv Rt_*$. The total derived functor
used here exists by [lem-weil-pbc-kinjective-total-derived]. The same K-injective calculation
derives $j_!\dashv j^{-1}$ from the etale sheaf adjunction and exactness
[lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-extension-by-zero-exact], or from the
pro-etale exact adjunction [lem-cbc-proetale-extension-zero]; for this calculation $j^{-1}I$ is
K-injective because $j_!$ is exact. All these bijections are natural. Composing this open
adjunction with the ambient closed adjunction of [lem-exc-closed-ambient] or
[lem-exc-proetale-closed-support] gives $Rs_!=j_!i_*\dashv Ri^!j^{-1}=Rs^!$. Dependencies:
lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-ringed-topoi-module-adjunction,
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-right-adjoint-preserves-kinjective,
lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-extension-by-zero-adjunction,
lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero, lem-exc-closed-ambient,
lem-exc-proetale-closed-support.

4. Inverse image on each of these constant-coefficient ringed sites has a canonical derived tensor
comparison $$t^{-1}(Q\otimes_A^LQ')\cong t^{-1}Q\otimes_A^Lt^{-1}Q'$$ by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. The same cited statement says that pullback
of a K-flat complex with flat terms is K-flat with flat terms. We will use both assertions for
$i$, $j$, and the complementary $v$. The constant-coefficient pullback is termwise inverse image
because it is exact; no finite Tor-amplitude condition on $Q,Q'$ occurs in this result. We will
also use the following direct consequence of K-flatness [def-pc-kflat-complex]: if one tensor
factor is K-flat, the other may be represented by an arbitrary complex. Indeed, replace that other
complex by a K-flat resolution; the cone of its resolution map is acyclic, and tensoring this cone
with the fixed K-flat factor is acyclic by the definition. Thus the induced map of total tensor
complexes is a quasi-isomorphism. This justifies the arbitrary first-factor representatives in
steps 5 and 8. Dependencies: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
def-pc-kflat-complex.

5. First establish the open projection formula on both sites. An open immersion is an etale site
object by [lem-weil-pbc-open-immersion-etale], and inverse image there is restriction by
[lem-weil-pbc-etale-inverse-image-restriction]. For the pro-etale site use the localization
identification [lem-weil-proetale-weakly-etale-localization]. The ringed-slice formula
[lem-weil-pbc-ringed-slice-extension-tensor] therefore gives, for module sheaves, $j_!(F\otimes
j^{-1}G)\cong j_!F\otimes G$. Choose a K-flat resolution with flat terms $Q_0\to Q$ on $X$ using
[lem-pc-kflat-resolution]. By step 4, $j^{-1}Q_0$ is K-flat. Use any complex representing $P'$ on
$U$. In each total degree the sheaf formula identifies the summands of $j_!(P'\otimes j^{-1}Q_0)$
with those of $j_!P'\otimes Q_0$, and it commutes with both differentials by naturality. Extension
by zero commutes with their direct sums: the coproduct comparison follows directly from its
adjunction, since maps from either candidate to $N$ are families of maps from the summands to
$j^{-1}N$. Hence it identifies the total complexes. Exactness of $j_!$ from step 3 and the derived
tensor construction [lem-weil-pbc-site-derived-tensor-descent] give a natural isomorphism
$$j_!P'\otimes_A^L Q\cong j_!(P'\otimes_A^Lj^{-1}Q).$$ The pro-etale assertion is also exactly
[lem-cbc-extension-zero-projection-formula]. Dependencies: lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-inverse-image-restriction, lem-weil-proetale-weakly-etale-localization,
lem-weil-pbc-ringed-slice-extension-tensor, lem-pc-kflat-resolution,
lem-weil-pbc-site-derived-tensor-descent, lem-cbc-extension-zero-projection-formula.

6. Next establish the closed projection formula without using geometric stalks on the pro-etale
site. Form $$c:i_*P\otimes_A^LQ'\longrightarrow i_*(P\otimes_A^Li^{-1}Q')$$ as the adjoint under
$i^{-1}\dashv Ri_*=i_*$ of $$i^{-1}(i_*P\otimes_A^LQ')\cong
i^{-1}i_*P\otimes_A^Li^{-1}Q'\xrightarrow{\varepsilon_P\otimes1}P\otimes_A^Li^{-1}Q'.$$ The
comparison in step 4 and the closed counit isomorphism in step 2 identify $i^{-1}c$ with an
isomorphism. Both sides have zero restriction to $V$: for the source use $v^{-1}i_*P=0$ and the
tensor comparison, and for the target use $v^{-1}i_*=0$. The cone of $c$ therefore has zero
inverse images on $S$ and $V$, so it is acyclic by the joint detection on complexes proved in step
2. Thus $c$ is an isomorphism. This proves $i_*P\otimes_A^LQ'\cong i_*(P\otimes_A^Li^{-1}Q')$,
naturally in the two arbitrary complexes. The exactness and counit facts are precisely those of
[lem-kun-04ca] in the etale case and [lem-weil-pbc-proetale-ringed-open-closed] in the pro-etale
case; the tensor assertion is [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Dependencies:
lem-kun-04ca, lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

7. Compose the open and closed formulas of steps 5 and 6, with $P'=i_*P$ and $Q'=j^{-1}Q$, to
obtain $$Rs_!P\otimes_A^LQ=j_!i_*P\otimes_A^LQ\cong j_!(i_*P\otimes_A^Lj^{-1}Q)\cong
j_!i_*(P\otimes_A^Li^{-1}j^{-1}Q)=Rs_!(P\otimes_A^Ls^{-1}Q).$$ Here $s^{-1}=i^{-1}j^{-1}$: the
composite is left adjoint to the composite sheaf direct image $j_*i_*=s_*$, so identifies with
inverse image, including its unit and counit. On K-injectives, $Ri_*=i_*$ preserves K-injectives
by the exact inverse-image adjunction and [lem-weil-pbc-right-adjoint-preserves-kinjective]. Thus
$Rj_*Ri_*=Rs_*$ as well: on a K-injective $I$ the two constructions both give $j_*i_*I=s_*I$. All
comparisons in the displayed projection formula are natural. Dependencies:
lem-weil-pbc-right-adjoint-preserves-kinjective.

8. Derive the tensor-internal-Hom bijection on either ringed site, rather than taking it from a
definition of the operations. For arbitrary $K,L,N$, choose a K-flat representative $L_0$ of $L$
and a K-injective representative $I$ of $N$. The Hom complex $\mathcal Hom^\bullet(L_0,I)$ is
K-injective by [lem-pur-hom-kflat-into-kinjective]. For any representative $K_0$,
[lem-sc-derived-hom-tensor-total] gives $$\mathcal Hom^\bullet(K_0,\mathcal
Hom^\bullet(L_0,I))\cong\mathcal Hom^\bullet(\operatorname{Tot}(K_0\otimes L_0),I).$$ The two
sides represent $R\mathcal Hom(K,R\mathcal Hom(L,N))$ and $R\mathcal Hom(K\otimes_A^LL,N)$. Taking
$H^0$ of derived global sections and using [lem-pur-rhom-global-sections] on each side gives
$$\operatorname{Hom}(K,R\mathcal Hom(L,N))\cong\operatorname{Hom}(K\otimes_A^LL,N),$$ natural in
all three derived objects. Existence of $L_0$ and $I$ is [lem-pc-kflat-resolution,
prop-pur-kinjective-resolutions-exist]; the models and their descent are
[def-pur-derived-internal-hom, lem-weil-pbc-site-derived-tensor-descent]. Symmetry used to resolve
the second tensor variable is induced by the symmetric sheaf tensor
[lem-pc-sheaf-modules-tensor-closed]; swapping the degree-$p,q$ summands with sign $(-1)^{pq}$
commutes with the total differential and squares to the identity, hence gives the corresponding
derived symmetry. Dependencies: lem-pur-hom-kflat-into-kinjective,
lem-sc-derived-hom-tensor-total, lem-pur-rhom-global-sections, lem-pc-kflat-resolution,
prop-pur-kinjective-resolutions-exist, def-pur-derived-internal-hom,
lem-weil-pbc-site-derived-tensor-descent, lem-pc-sheaf-modules-tensor-closed.

9. For every $Q\in D_\tau(X,A)$, apply step 8, the projection formula of step 7 (with tensor
symmetry), the shriek adjunction of step 3, step 8 on $S$, and the star adjunction of step 3, in
that order: $$\begin{aligned} \operatorname{Hom}_X(Q,R\mathcal Hom_X(Rs_!P,M))
&\cong\operatorname{Hom}_X(Q\otimes_A^LRs_!P,M)\\
&\cong\operatorname{Hom}_X(Rs_!(s^{-1}Q\otimes_A^LP),M)\\
&\cong\operatorname{Hom}_S(s^{-1}Q\otimes_A^LP,Rs^!M)\\
&\cong\operatorname{Hom}_S(s^{-1}Q,R\mathcal Hom_S(P,Rs^!M))\\
&\cong\operatorname{Hom}_X(Q,Rs_*R\mathcal Hom_S(P,Rs^!M)). \end{aligned}$$ Every object here
belongs to its ordinary ambient derived category, by the constructions already checked; none of
the bijections requires a constructible or perfect input. Their composite is natural in $Q$,
contravariantly in $P$, and covariantly in $M$. No additional dependencies.

10. Write $B=R\mathcal Hom_X(Rs_!P,M)$, $C=Rs_*R\mathcal Hom_S(P,Rs^!M)$, and
$\theta_Q:\operatorname{Hom}(Q,B)\cong\operatorname{Hom}(Q,C)$ for step 9. Set
$\alpha=\theta_B(1_B):B\to C$ and $\beta=\theta_C^{-1}(1_C):C\to B$. Naturality in $Q$ gives
$\theta_Q(f)=\alpha f$ and $\theta_Q^{-1}(g)=\beta g$; evaluating their inverse composites at the
identities gives $\beta\alpha=1_B$ and $\alpha\beta=1_C$. Thus $\alpha$ is the desired
isomorphism. Naturality of $\theta$ in $P,M$ gives naturality of $\alpha$. This writes out the
required representable-functor argument directly, without applying the scheme-specific Yoneda node
to a derived category. No additional dependencies. -/
theorem ProEtale.nonempty_stratumAmbientHomIso
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A) ≅
        ((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor) := by
  obtain ⟨α, hα⟩ := ProEtale.stratumAmbientHomComparison A i j
  refine ⟨NatIso.ofComponents (fun p ↦ asIso (α.app p)) ?_⟩
  intro p q f
  simpa only [asIso_hom] using α.naturality f

end AlgebraicGeometry
