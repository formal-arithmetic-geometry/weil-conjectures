/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Sheaf.AlgebraicGeometry.ClopenSectionDirectImage
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Proper/open interchange and its coherence

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B, 0F7C, 0F7D, 0F7F
(blueprint: lem-cbc-proper-open-interchange-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical proper/open interchange isomorphism, normalized by the derived units,
with refinement normalization, vertical and horizontal composition, identities and base change.
The ordinary isomorphism `δ` is fixed by equality in the common ordinary direct image.
The unit equation is the resolution-independent form of the K-injective normalization:
on an injective representative the left unit is invertible; the right unit is represented
by applying `p_*` to a K-injective replacement of `k_!J`.
Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F
(blueprint: lem-cbc-proper-open-interchange-coherence).

Proof:
1. Write $h=ir=pk$. Proper maps are separated and of finite type by [def-weil-proper-morphism],
hence locally of finite type by [def-weil-finite-type-morphism]. An open immersion identifies its
source with an open subscheme [def-weil-open-immersion]; its diagonal is an isomorphism, hence a
closed immersion, and locally on that open subscheme its ring map is the identity, a finite-type
map. Thus the separated and locally finite-type hypotheses of
[lem-cbc-proper-support-sheaf-composition] hold. That node gives, for every module sheaf $F$ on
$A$, the canonical identification
$$\delta_Q(F):i_!r_*F=i_!^{\mathrm{supp}}r_!^{\mathrm{supp}}F
=h_!^{\mathrm{supp}}F=p_!^{\mathrm{supp}}k_!^{\mathrm{supp}}F=p_*k_!F.$$
All the equalities mean the same subsheaf of $h_*F$: a section is carried to the same section,
rather than to an arbitrary abstract isomorphism. Thus $\delta_Q$ is natural and $\Lambda$-linear,
and extends degreewise to complexes. For successive squares, all identifications of the underlying
sheaves are identities on these common sections. In particular the sheaf versions of both stated
composition equations hold. The proper-support composition result applies without Cartesian or
quasi-compact-open assumptions. Uses: lem-cbc-proper-support-sheaf-composition,
def-weil-proper-morphism, def-weil-finite-type-morphism, def-weil-open-immersion.
2. Choose a universe in which the small etale sites are small. By
[prop-pur-kinjective-resolutions-exist] their constant-ring module-sheaf categories are
Grothendieck abelian. They have enough injectives by
[lem-weil-pbc-module-sheaves-enough-injectives]. Represent $K$ by a bounded-below complex $J$ of
injective module sheaves using [lem-weil-pbc-dplus-injective-representative], and choose a
bounded-below injective resolution $t:k_!J\to I$. Exactness [lem-weil-pbc-extension-by-zero-exact]
makes $k_!J$ a bounded-below representative of $k_!K$. Each $k_!J^n$ is $p_*$-acyclic by
[lem-cbc-open-extended-injective-proper-acyclic]. Clause (3) of [lemma-weil-pbc-leray-acyclicity]
therefore says that $p_*t:p_*k_!J\to p_*I$ is a quasi-isomorphism and computes the derived-functor
comparison. Since $r_*J$ computes $Rr_*K$ by [def-weil-pbc-direct-image], the composite
$i_!r_*J\xrightarrow{\delta_Q}p_*k_!J\xrightarrow{p_*t}p_*I$ gives the required isomorphism.
Finite $\Lambda$ is torsion: multiplying positive integers annihilating its finitely many additive
elements gives $N>0$ with $N\Lambda=0$, hence $NM=0$ for every $\Lambda$-module $M$. This is
precisely case (b) of 0F7B, with no residue-characteristic restriction. Uses:
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-module-sheaves-enough-injectives,
lem-weil-pbc-dplus-injective-representative, lem-weil-pbc-extension-by-zero-exact,
lem-cbc-open-extended-injective-proper-acyclic, lemma-weil-pbc-leray-acyclicity,
def-weil-pbc-direct-image.
3. Morphisms into a K-injective complex are uniquely represented up to homotopy by
[lem-weil-pbc-kinjective-hom-derived]. Given any other K-injective representative $J'$ of $K$, its
identification with $J$ lifts to a homotopy equivalence. Applying the additive functors $i_!r_*$
and $p_*k_!$ preserves that homotopy equivalence. Write $h:J\to J'$ for this homotopy equivalence
and $t:k_!J\to I$, $t':k_!J'\to I'$ for the resolutions. The derived morphism $Q(t')\circ
Q(k_!h)\circ Q(t)^{-1}:QI\to QI'$ lifts to a chain map $u:I\to I'$ by the Hom bijection. Since
$I'$ is K-injective, equality of the derived classes of $ut$ and $t'k_!h$ gives the homotopy
$ut\simeq t'k_!h$. Naturality of $\delta_Q$ makes the corresponding comparison diagram commute up
to homotopy, and applying $p_*$ preserves the homotopy. The resulting derived arrow is independent
of all these choices and is natural in $K$, again by the Hom bijection. This also proves the
stated normalization for any K-injective representative, even if it is not itself bounded below
termwise. Exactness of $k_!$ is used to descend it through localization; no claim that $k_!$
preserves injectives is made. Uses: lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-extension-by-zero-exact.
4. In the refinement case use [def-weil-pbc-proper-open-comparison]. Its construction identifies
$V=u^{-1}(j_2(X))$ and its clopen component $s(X)$, with $bs=j_1$, $ps=\mathrm{id}_X$. Restrict
the arrow just constructed to $j_2$. Under the restriction isomorphism
[lem-weil-pbc-derived-open-restriction], the extension-by-zero comparison
[cor-cbc-derived-extension-zero-base-change], and the component restriction
[lem-weil-pbc-clopen-section-direct-image], its source and target become $K$. The underived
$\delta$ sends a section on $X$ to itself on $s(X)$ and zero on the other component. Thus this
restricted arrow is exactly $\theta_{u,K}^{-1}$ from the comparison definition; the resolution map
is the canonical derived comparison and does not change that identity on the component. The
adjunction [lem-weil-pbc-extension-by-zero-adjunction], descended degreewise since extension by
zero and inverse image are exact [lem-weil-pbc-extension-by-zero-exact]
[prop-weil-pbc-inverse-image-modules-exact], makes the arrow $j_{2!}K\to Ru_*j_{1!}K$ uniquely
determined by this restriction. It is consequently $\alpha_{u,K}$, the adjoint of
$\theta_{u,K}^{-1}$. Uses: def-weil-pbc-proper-open-comparison,
lem-weil-pbc-derived-open-restriction, cor-cbc-derived-extension-zero-base-change,
lem-weil-pbc-clopen-section-direct-image, lem-weil-pbc-extension-by-zero-adjunction,
lem-weil-pbc-extension-by-zero-exact, prop-weil-pbc-inverse-image-modules-exact.
5. For vertically stacked $Q_1,Q_2$, choose $J$ bounded-below injective on the upper-left scheme
and $t:k_{1!}J\to I$ bounded-below injective on the upper-right scheme. Direct image preserves
injectives by [lem-weil-pbc-direct-image-preserves-injectives], so $r_{1,*}J$ and $p_{1,*}I$ are
bounded-below injective complexes. Put $E=i_{1!}r_{1,*}J$ and $a=p_{1,*}t\circ\delta_{Q_1}:E\to
p_{1,*}I$. This is a quasi-isomorphism by step 2. For $Q_2$, every term of $E$ is
$p_{2,*}$-acyclic by [lem-cbc-open-extended-injective-proper-acyclic], applied to the injective
terms of $r_{1,*}J$. Clause (3) of [lemma-weil-pbc-leray-acyclicity] shows that $E$ computes
$Rp_{2,*}E$; thus $Rp_{2,*}(\gamma_{Q_1})$ is represented by $p_{2,*}a$. The two-square composite
is represented by
$$i_{2!}r_{2,*}r_{1,*}J\xrightarrow{\delta_{Q_2}}p_{2,*}i_{1!}r_{1,*}J
\xrightarrow{p_{2,*}a}p_{2,*}p_{1,*}I.$$
Step 1 identifies this composite with $\delta_{Q_2Q_1}$ followed by $(p_2p_1)_*t$. The compositor
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition] is normalized on these injective
direct images with the identity as the extra resolution. Consequently these are exactly the
representatives of the displayed vertical equation, with the canonical compositors inserted. Uses:
lem-weil-pbc-direct-image-preserves-injectives, lem-cbc-open-extended-injective-proper-acyclic,
lemma-weil-pbc-leray-acyclicity, lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
6. For horizontal composition choose bounded-below injective $J$ on the left, $t:k_!J\to I$ in the
middle, and $v:l_!I\to L$ on the right. By [lem-weil-pbc-extension-by-zero-exact], $w=v\circ
l_!t:l_!k_!J\to L$ is a quasi-isomorphism. The two-square comparison is represented by
$$j_!i_!r_*J\xrightarrow{j_!(p_*t\circ\delta_{Q_1})}j_!p_*I
\xrightarrow{q_*v\circ\delta_{Q_2}}q_*L.$$
Naturality of the sheaf identification $\delta_{Q_2}$ moves $t$ through it. The sheaf composition
equality in step 1 then makes this map $q_*w\circ\delta_{Q_2Q_1}$, the representative for the
outer rectangle. The identification $j_!i_!\cong(ji)_!$ is the sheaf support-composition equality
in [lem-cbc-proper-support-sheaf-composition], applied degreewise; its exactness just cited lets
it descend to $D^+$. This proves the stated horizontal equation. For horizontal identities take
$t=\mathrm{id}_J$; $\delta$ is the identity and one obtains the identity on derived pushforward.
For vertical identities $k=i$ and $p=r=\mathrm{id}$, so the constructed arrow is the
quasi-isomorphism $k_!J\to I$, which represents the identity of $k_!K$. Uses:
lem-weil-pbc-extension-by-zero-exact, lem-cbc-proper-support-sheaf-composition.
7. For base change first work with sheaves. The support inclusions into ordinary direct images in
[lem-cbc-proper-support-sheaf-composition] identify $i_!r_*$ and $p_*k_!$ inside $(ir)_*=(pk)_*$.
Its pullback-composition clause says that the two paths consisting of the ordinary comparisons and
the extension-by-zero comparisons give the pullback comparison for that same composite morphism.
Thus the ordinary version of the required base-change diagram commutes. More explicitly, after
inclusion into $(p_1k_1)_*d^{-1}F=(i_1r_1)_*d^{-1}F$, either path pulls a local section of $F$ to
the same section on the base-changed test scheme. These are injective inclusions; inverse image
preserves them by [prop-weil-pbc-inverse-image-modules-exact]. Hence equality in the common
ordinary direct image is equality in the support subsheaf. The open comparisons here are the
specific $\beta_i,\beta_k$ of [cor-cbc-derived-extension-zero-base-change], not isomorphisms
chosen independently of the pullback maps. Their construction is the restriction of the ordinary
pullback comparison to the support subsheaf. The ordinary-comparison pasting is also the
unit/counit mate equation in clauses (1),(2) of [lem-weil-pbc-mate-pasting] for the module
inverse-image adjunctions; all constant-ring pullbacks are the identifications of
[prop-weil-pbc-inverse-image-modules-exact]. Uses: lem-cbc-proper-support-sheaf-composition,
prop-weil-pbc-inverse-image-modules-exact, cor-cbc-derived-extension-zero-base-change,
lem-weil-pbc-mate-pasting.
8. Now take $J,t:k_!J\to I$ as in step 2, and choose a bounded-below injective resolution
$s:d^{-1}J\to J_1$. Exact inverse image and exact extension by zero
[prop-weil-pbc-inverse-image-modules-exact] [lem-weil-pbc-extension-by-zero-exact] make the
diagram start with quasi-isomorphisms $$k_{1!}d^{-1}J\xrightarrow{k_{1!}s}k_{1!}J_1,\qquad
k_{1!}d^{-1}J\xrightarrow{\beta_k^{-1}}a^{-1}k_!J\xrightarrow{a^{-1}t}a^{-1}I.$$ Choose a
bounded-below injective resolution $v:k_{1!}J_1\to I_1$. By [lem-weil-pbc-kinjective-hom-derived],
the morphism from $a^{-1}I$ to $I_1$ corresponding in the derived category to $v\circ
k_{1!}s\circ\beta_k\circ(a^{-1}t)^{-1}$ is represented by a chain map $z:a^{-1}I\to I_1$. It
satisfies $$z\circ a^{-1}t\circ\beta_k^{-1}\simeq v\circ k_{1!}s,$$ because the maps from
$k_{1!}d^{-1}J$ into the K-injective $I_1$ have the same derived class. This is the needed
homotopy-commutative resolution diagram, not a claim that $d^{-1}J$ or $a^{-1}I$ is injective. The
module exchange maps are represented by the ordinary comparisons $b^{-1}p_*I\to p_{1,*}a^{-1}I$
followed by $p_{1,*}z$, and $c^{-1}r_*J\to r_{1,*}d^{-1}J$ followed by $r_{1,*}s$. To verify this
computation rather than take it from a definition, use the exact module adjunction of
[prop-weil-pbc-inverse-image-modules-exact], its termwise adjunction on homotopy categories
[lem-weil-pbc-termwise-adjunction-homotopy], and the K-injective Hom bijection. Exactness of
inverse image shows its additive right adjoint preserves K-injectives: if $H$ is acyclic and $P$
is K-injective, $\operatorname{Hom}_K(H,p_*P)=\operatorname{Hom}_K(p^{-1}H,P)=0$. Thus the two
homotopy-category Hom sets in this adjunction identify with the corresponding derived Hom sets for
injective target resolutions, with the same counit represented by $\varepsilon_{p,P}$. For a
source representative $P$ and a target resolution $z:a^{-1}P\to I_1$, the transpose of
$p_{1,*}z\circ\operatorname{Ex}^0_P$ is the chain map $z\circ a^{-1}\varepsilon_{p,P}\circ\theta$,
by the defining adjoint formula of [def-weil-pbc-underived-exchange] and the underived adjunction
triangle identities. That formula is stated for abelian sheaves;
[prop-weil-pbc-inverse-image-modules-exact] gives exactly those same units and counits on
constant-ring modules, and its section-restriction maps are linear, so the displayed formula is
the module formula too. Maps into $I_1$ are computed modulo homotopy by
[lem-weil-pbc-kinjective-hom-derived], so this is also its derived transpose. This is exactly the
defining derived mate in [def-weil-pbc-derived-exchange], formed for module adjunctions as
specified in [lem-weil-pbc-exchange-forget-coefficients]. For the left proper map, the chain map
$r_{1,*}s\circ\operatorname{Ex}^0_{r,J}$ has transpose $s\circ
d^{-1}\varepsilon_{r,J}\circ\theta_r:r_1^{-1}c^{-1}r_*J\to J_1$. The termwise adjunction and the
Hom bijection into $J_1$ identify this transpose with the derived composite
$d^{-1}\varepsilon_r\circ\theta_r$ followed by the resolution identification. Hence this chain map
represents $\operatorname{Ex}_r$. No module computation is being inferred from the abelian-only
termwise-exchange theorem. Apply the ordinary equality of step 7 degreewise to $J$. Naturality of
$\delta_{Q_1}$ with respect to $s$ gives equality for the next segment. For the last segment apply
$p_{1,*}$ to the displayed homotopy: it remains a homotopy since direct image is additive. The
outside paths are therefore equal in the homotopy category after passing through $p_{1,*}I_1$, and
hence in $D^+$. Written using the normalization of step 2 these paths are exactly
$$(Rp_{1,*}\beta_k)\circ(\operatorname{Ex}_p k_!)\circ(b^{-1}\gamma_Q)
=(\gamma_{Q_1}d^{-1})\circ(i_{1!}\operatorname{Ex}_r)\circ(\beta_iRr_*).$$ Properness and openness
in $Q_1$ hold by [lem-weil-pbc-proper-base-change] and [lem-weil-pbc-open-immersion-base-change],
respectively. Thus all comparisons used here are of the stated kind for arbitrary $b$. The
exchanges stay in the constant-$\Lambda$ module categories; the comparison
[lem-weil-pbc-exchange-forget-coefficients] identifies their underlying abelian exchanges but is
not used to infer equality from derived forgetting. Uses:
prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-extension-by-zero-exact,
lem-weil-pbc-kinjective-hom-derived, def-weil-pbc-derived-exchange,
lem-weil-pbc-proper-base-change, lem-weil-pbc-open-immersion-base-change,
lem-weil-pbc-exchange-forget-coefficients, def-weil-pbc-underived-exchange,
lem-weil-pbc-termwise-adjunction-homotopy.
-/
theorem properOpenInterchangeCoherence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p)),
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (J :
        HomotopyCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map ((lowerStar
        (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusUnit.app J) ≫
        (γ k i r p h).hom.app (DerivedCategory.Plus.Qh.obj J) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus (δ k i r p h).hom).app J) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusUnit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus.obj J) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusFactorsh.inv.app J)) ∧
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar
        (ModuleCat.{u + 1} Λ) r₂) (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)).hom.app K) ≫
        (γ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom.app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar
        (ModuleCat.{u + 1} Λ) p₂) (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (γ i j r₂ p₂ h₂).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r₁).obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₂).map ((γ k i r₁ p₁ h₁).hom.app K)) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1}
        Λ) r).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q).map ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ k k (𝟙 A) (𝟙 B) ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom.app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom.app K)) ∧
    (∀ {A C : Scheme.{u}} (r : A ⟶ C) [IsProper r]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ (𝟙 A) (𝟙 C) r r ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).map
        ((Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A)) (upperStarId
        (ModuleCat.{u + 1} Λ) A)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C)) (upperStarId
        (ModuleCat.{u + 1} Λ) C)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj K)) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₁).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u
        + 1} Λ) r).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K)) := by
  sorry

end AlgebraicGeometry.Etale
