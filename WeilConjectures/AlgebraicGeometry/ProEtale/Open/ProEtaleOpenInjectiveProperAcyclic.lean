/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage

import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclicFromWitness

/-!
# Proper-direct-image acyclicity of open-extended pro-etale injectives

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence (blueprint: lem-sp-proetale-open-injective-proper-acyclic).
Stacks Project, Tag 0F7B, case (b), is the motivating etale analogue only.
The statement concerns ordinary uncompleted derived direct image of all constant-ring
module sheaves on the small pro-etale sites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- In a commutative proper/open square, not necessarily Cartesian, extension by zero
of any injective constant-ring module sheaf is acyclic for the proper direct image.
There is no etale-origin hypothesis.

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence (blueprint: lem-sp-proetale-open-injective-proper-acyclic).
The etale Tag 0F7B motivates the assertion but is not a proof on the pro-etale site.

Proof plan (the node's seven steps):

1. Form the fibre product $V=B\times_D E$ with projections $b:V\to B$ and $s:V\to E$. Base change
   preserves proper morphisms, so $s$ is proper, while base change of the open immersion $i$ makes
   $b$ an open immersion. The equation $pk=ir$ gives a unique map $t=(k,r):C\to V$ with $b t=k$
   and $s t=r$. Since $k$ is an open immersion and $b$ identifies $V$ with the open $p^{-1}(E)$ in
   $B$, the map $t$ is an open immersion. The morphism $s$ is separated (proper), and $r=s t$ is
   proper; hence $t$ is proper by properness over a separated target. A proper immersion is a
   closed immersion, so $t(C)$ is both open and closed in $V$.
   Uses: `def-pc-fibre-product`, `def-weil-open-immersion`, `def-weil-proper-morphism`, `lem-weil-
   pbc-open-immersion-base-change`, `lem-weil-pbc-proper-base-change`, `lem-weil-pbc-proper-over-
   separated`, `lem-weil-pbc-proper-immersion-closed`.

2. On the clopen decomposition $V=t(C)\amalg(V\setminus t(C))$, extension by zero identifies a
   module sheaf on $C$ with the pair consisting of that sheaf on the first component and the zero
   sheaf on the second. This follows by the pro-etale open-closed exact sequence and the open-
   extension adjunction, evaluated on the two components. Consequently $t_!J$ is injective: for a
   monomorphism $M\hookrightarrow N$ and a map $M\to t_!J$, restrict to $C$, extend the resulting
   map to $N|_C$ using injectivity of $J$, and glue it with the zero map on the complementary
   clopen component. The glued map is the required lift. The same componentwise description
   identifies $t_!J$ with $t_*J$; no exactness of a general open direct image is being used.
   Uses: `lem-sf-proetale-open-closed-sequence`, `lem-weil-extension-by-zero-adjunction`, `lem-
   weil-extension-by-zero-exact`, `def-sp-injective-resolutions`, `def-weil-pbc-proetale-
   operations`.

3. Put $F=k_!J$ and $M=Rp_*(F[0])$. Apply the derived open-restriction isomorphism to the
   Cartesian square with source open $b:V\hookrightarrow B$ and base open $i:E\hookrightarrow D$.
   It gives $i^*M\cong Rs_*(b^*F[0])$. The extension-by-zero base-change isomorphism identifies
   $b^*k_!J$ with $t_!J$: the pullback $C\times_BV$ is $C$, since $k$ factors through $V$.
   Consequently $i^*M\cong Rs_*(t_*J[0])$. By step 2 this input is injective. The module category
   is Grothendieck by the resolution-existence statement, hence has enough injectives by the cited
   Grothendieck theorem. The one-term complex $t_*J[0]$ is a bounded-below complex of injectives,
   hence K-injective by the bounded-below representative theorem, so the defined $Rs_*$ is
   computed on it termwise; the right-derived injective computation likewise makes the right side
   $s_*t_*J$ concentrated in degree zero. Exactness of the identified-coefficient inverse image
   therefore gives $i^*R^qp_*F=0$ for $q>0$. This proves only the restriction to $E$; it makes no
   identification of $M$ with an open direct image.
   Uses: `lem-exc-proetale-derived-open-restriction`, `lem-cbc-proetale-extension-zero-base-
   change`, `lem-weil-pbc-right-derived-plus-injective`, `prop-pur-kinjective-resolutions-exist`,
   `def-weil-pbc-proetale-operations`, `lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-
   dplus-injective-representative`.

4. Fix $q>0$ and write $G=R^qp_*F$. To prove $G=0$ it suffices to show it vanishes locally on
   every site object, by the sheaf equalizer axiom. First cover such an object by affine opens.
   For an affine object $Q_0=\operatorname{Spec}R_0\to D$, the w-contractible-ring extension gives
   a one-member pro-etale cover $Q=\operatorname{Spec}R\to Q_0$ with every faithfully flat weakly
   etale $R$-algebra admitting a retraction. Choose its cardinal parameter large enough to contain
   $R_0$, in the fixed site universes. Composition of weakly etale maps makes $Q\to D$ a site
   object. It is enough to prove $G(Q)=0$ for each such cover. The pullback $E_Q=E\times_DQ$ is a
   quasi-compact open of $Q$. Since principal opens form a basis, quasi-compactness supplies
   finitely many $f_1,\ldots,f_m\in R$ with $E_Q=\bigcup_aD(f_a)$; the empty list is permitted.
   Put $I=(f_1,\ldots,f_m)$ and $Z_Q=\operatorname{Spec}(R/I)$.
   Uses: `def-weil-pbc-proetale-site`, `lem-weil-pbc-wcontractible-ring-extension`, `lem-weil-pbc-
   weakly-etale-composition-base-change`, `lem-weil-pbc-open-immersion-base-change`, `lem-pc-
   quasi-compact-base-change`, `def-weil-affine-spectrum`.

5. Let $S=\{s\in R:s\bmod I\in(R/I)^\times\}$ and $Q^\sim=\operatorname{Spec}(S^{-1}R)$. The
   closed-localization lemma gives a pro-etale cover of $Q$ consisting of the $D(f_a)$ and
   $Q^\sim$. Every point of $Q^\sim$ specializes to $Z^\sim=Q^\sim\times_Q Z_Q$, and $S^{-1}R$ has
   the same ring-retraction property as $R$. Since the $D(f_a)$ factor through $E$, step 3 gives
   $G(D(f_a))=0$. It remains to show $G(Q^\sim)=0$. The localization is a site object over $D$ by
   composition of weakly etale maps. The ring-to-site weak-contractibility statement, followed by
   exact module evaluation, shows evaluation on $Q^\sim$ preserves homology of complexes of
   constant-$A$ module sheaves on $D$.
   Uses: `lem-weil-pbc-wcontractible-closed-localization`, `lem-weil-pbc-weakly-etale-composition-
   base-change`, `lem-weil-pbc-wcontractible-affine-weakly-contractible`, `lem-weil-pbc-proetale-
   weakly-contractible-evaluation-exact`.

6. Put $P=B\times_DQ^\sim$, $U=C\times_DQ^\sim$, $E^\sim=E\times_DQ^\sim$, and let $p^\sim:P\to
   Q^\sim$ and $k^\sim:U\hookrightarrow P$ be the projections. Properness and quasi-compact
   openness are preserved by base change. The map $U\hookrightarrow P\times_{Q^\sim}E^\sim$ is the
   base change of the clopen map $t$ of step 1, hence is clopen: its image is the inverse image of
   the clopen subset $t(C)$, and base change preserves its open-immersion identification. The
   projection $U\to C$ is weakly etale, so the restriction $J^\sim$ of $J$ is injective.
   Extension-by-zero base change gives $F|_P\cong k^\sim_!J^\sim$. Choose a bounded-below
   injective representative $I^\bullet$ of $F[0]$; it exists by the Grothendieck property, the
   enough-injectives theorem, and the bounded-below representative theorem. It computes $Rp_*F$.
   Exact evaluation from step 5 gives $$G(Q^\sim)=H^q((p_*I^\bullet)(Q^\sim))=H^q(I^\bullet(P))=H^
   q(P_{\mathrm{proet}},k^\sim_!J^\sim).$$ The middle equality is the direct-image section
   formula. For the last equality, restriction along the weakly etale projection $P\to B$ is exact
   and preserves injectives, so $I^\bullet|_P$ computes derived global sections of $F|_P$. This
   resolves $F$ on $B$, not $J$ on $C$, and assumes no acyclicity of $k_!J$.
   Uses: `lem-weil-pbc-proper-base-change`, `lem-weil-pbc-open-immersion-base-change`, `lem-pc-
   quasi-compact-base-change`, `lem-weil-pbc-weakly-etale-composition-base-change`, `lem-weil-pbc-
   proetale-restriction-injectives`, `lem-cbc-proetale-extension-zero-base-change`, `prop-pur-
   kinjective-resolutions-exist`, `lem-weil-pbc-dplus-injective-representative`, `lem-weil-pbc-
   right-derived-plus-injective`, `def-weil-pbc-proetale-operations`, `lem-sp-grothendieck-enough-
   injectives`.

7. Apply [lem-sp-proetale-proper-boundary-cohomology] to $Q^\sim$, its closed subscheme $Z^\sim$,
   its quasi-compact open complement $E^\sim$, the proper map $p^\sim$, and the clopen open
   $U\subset P\times_{Q^\sim}E^\sim$. Step 5 verifies both the ring-retraction and specialization
   hypotheses; step 6 verifies properness, quasi-compactness of $k^\sim$, and injectivity of
   $J^\sim$. It gives $H^q(P_{\mathrm{proet}},k^\sim_!J^\sim)=0$, so $G(Q^\sim)=0$. On the cover
   of step 5 every restriction of a section of $G(Q)$ is now zero. Separatedness of $G$ gives
   $G(Q)=0$. The covers in step 4 then give $G=0$ on every site object. This proves
   $R^qp_*(k_!J)=0$ for all $q>0$. The new cited statement is precisely the boundary-cohomology
   input; neither degree-zero specialization vanishing nor the etale Tag 0F7B is used as its
   proof.
   Uses: `lem-sp-proetale-proper-boundary-cohomology`, `def-weil-pbc-proetale-site`.
-/
theorem isZero_higherDirectImage_open_injective_of_proper
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J] :
    ∀ q : ℕ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules D (proEtaleConstantRing D A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
            ((sfIntrinsicExtensionByZero k A).obj J)))) := by
  obtain ⟨w⟩ := exists_openProperClopenWitness p r k i hcomm
  exact isZero_higherDirectImage_open_injective_of_proper_of_witness
    A p r k i hcomm J w

end AlgebraicGeometry.Scheme
