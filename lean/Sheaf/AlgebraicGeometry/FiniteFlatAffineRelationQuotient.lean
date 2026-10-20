/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.AlgebraicGeometry.FinitePushforwardLocallyFree
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Sheaf.RingTheory.SemilocalSubmoduleBasis

/-!
# The affine quotient of a finite locally free equivalence relation

Source: Stacks Project, Groupoids, Tag 03BM, proposition-finite-flat-equivalence
(blueprint: lem-a1-finite-flat-affine-relation-quotient).

The coequalizer of the Yoneda maps is the pointwise quotient presheaf. The conclusion
specifies its sheafification by the universal property, including its canonical unit.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The invariant subring C = {a | s♯(a) = t♯(a)} for an affine relation.
This is Mathlib's ring-homomorphism equalizer, applied to the affine coordinate maps.
Source: Stacks Project, Groupoids, Tag 03BM, equation-invariants
(blueprint: lem-a1-finite-flat-affine-relation-quotient). -/
noncomputable def affineRelationInvariants {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A) :
    Subring A :=
  (Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom

/-- The canonical morphism to the spectrum of the invariant subring, induced by inclusion.
Source: Stacks Project, Groupoids, Tag 03BM, proposition-finite-flat-equivalence
(blueprint: lem-a1-finite-flat-affine-relation-quotient). -/
noncomputable def affineRelationQuotientMap {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A) :
    Spec A ⟶ Spec (CommRingCat.of (affineRelationInvariants s t)) :=
  Spec.map (CommRingCat.ofHom (affineRelationInvariants s t).subtype)

/-- A finite locally free affine equivalence relation has its affine invariant-spectrum
quotient. The quotient map is finite locally free and surjective, its kernel pair is the
original relation, and its unique descended S-structure represents the fppf sheafification.
Here `η` is the unit from the quotient presheaf, and bijectivity of precomposition by `η`
is precisely the universal property of sheafification, as in `sheafificationAdjunction`.

Source: Stacks Project, Groupoids, Tag 03BM, proposition-finite-flat-equivalence
(blueprint: lem-a1-finite-flat-affine-relation-quotient).

Proof plan (the node's steps):
1. An equivalence relation on all $S$-valued test schemes supplies identity, inverse and
   composition uniquely: send $u$ to $(u,u)$, reverse $(u,v)$, and send a composable pair
   $(u,v),(v,w)$ to $(u,w)$. These operations are natural; full faithfulness of Yoneda turns them
   into morphisms, and equality on all test points proves the groupoid laws. They also give a
   groupoid on arbitrary test schemes by considering each possible structure map to $S$. Write
   $\sigma=s^\sharp$, $\tau=t^\sharp$. Since they agree on $C$, the canonical map $q:U\to
   M=\operatorname{Spec}C$ equalizes $s,t$. The affine fibre-product formula gives $U\times_M
   U=\operatorname{Spec}(A\otimes_C A)$, and the comparison is induced by $\phi(a\otimes
   a_2)=\sigma(a)\tau(a_2)$. If $A=0$, the maps $A\to B$ force $B=C=0$; all schemes concerned are
   empty and the assertions follow. Henceforth $A\ne0$.
   Uses: lem-weil-pbc-fibre-product-affine-spectra.
   Uses: lem-galois-yoneda-fully-faithful.
2. The comparison $k:R\to U\times_MU$ is a monomorphism: equality after its two projections
   implies equality after $j$, and the hypothesis on $H$-points gives equality of the original
   maps. It is finite: a finite list generating $B$ over $A$ via $\sigma$ also generates it over
   $A\otimes_C A$ via $\phi$, because this larger scalar action includes $\sigma(A)$. The
   finite-monomorphism lemma makes $k$ a closed immersion. On these affine schemes this means
   exactly that $\phi$ is surjective.
   Uses: lem-a1-finite-monomorphism-closed-immersion.
   Uses: def-weil-finite-integral-morphism.
   Uses: def-weil-closed-immersion.
3. Apply the invariant-ring integrality and orbit lemmas to the groupoid just constructed. Thus
   $A$ is integral over $C$, $q$ is surjective, and the fibres of $|U|\to|M|$ are the $R$-orbits.
   These statements apply also to every affine groupoid obtained below after changing the
   invariant base.
   Uses: lem-a1-affine-groupoid-integral-invariants.
   Uses: lem-a1-affine-groupoid-orbit-fibres.
4. For a flat $C$-algebra $D$, tensor the exact sequence $0\to C\to A\xrightarrow{\tau-\sigma} B$
   with $D$. Flat tensor exactness identifies $D$ with the equalizer in $A_D=A\otimes_C D$ of
   $\sigma_D,\tau_D:A_D\to B_D=B\otimes_C D$. The operations base change because they are over $M$
   (the two maps to $M$ coincide); all groupoid equations remain equations after base change. Thus
   the new invariant ring is exactly $D$.
   Uses: lem-weil-pbc-flat-tensor-exact.
5. For each prime $\mathfrak p\subset C$, apply the flat local extension lemma to $C_{\mathfrak
   p}$ and the infinite field extension $\kappa(\mathfrak p)(z)$. It gives a flat local map
   $C_{\mathfrak p}\to D$ with infinite residue field. This local map is faithfully flat.
   Localization is flat, so apply the preceding equalizer argument first to $C\to C_{\mathfrak p}$
   and then to $C_{\mathfrak p}\to D$. We will prove $A_D$ finite free over $D$ and $\phi_D$ an
   isomorphism for each such choice.
   Uses: lem-weil-pbc-flat-local-extension-given-residue-field.
   Uses: lem-weil-pbc-flat-local-hom-faithfully-flat.
   Uses: lem-weil-pbc-localization-flat.
6. For $s:R\to U$, and likewise $t$, finite-flat-lfp pushforward is finite locally free. On affine
   schemes this supplies a cover by principal opens with $B$ finite free over $A$ via the chosen
   map; choose a finite such cover since $\operatorname{Spec}A$ is quasi-compact. Tensoring each
   displayed basis with $A_D$ gives the same kind of principal-open free cover for $B_D$ over
   $A_D$. The finite-free algebra spectrum lemma on each member proves $s_D,t_D$ finite locally
   free. In particular these maps have finite fibres. These affine basis descriptions will also be
   used when returning to $C$.
   Uses: lem-sc-finite-pushforward-locally-free.
   Uses: lem-weil-pbc-finite-free-algebra-spectrum.
7. Work now over the local invariant ring $(D,\mathfrak m)$ and abbreviate $A_D,B_D$ by $A,B$. By
   integrality, every maximal ideal of $A$ contracts to $\mathfrak m$, and every prime of $A$
   above $\mathfrak m$ is maximal. There is such a point $u_0$ by surjectivity of the orbit lemma.
   Every other maximal point lies in its $R$-orbit and is therefore in $t(s^{-1}(u_0))$. The fibre
   $s^{-1}(u_0)$ is finite, so $A$ is semilocal. Also $\mathfrak m A$ lies in every maximal ideal
   of $A$, hence in its Jacobson radical.
   Uses: lem-a1-affine-groupoid-integral-invariants.
   Uses: lem-a1-affine-groupoid-orbit-fibres.
   Uses: lem-weil-pbc-integral-maximal-contracts-maximal.
   Uses: lem-weil-pbc-integral-prime-over-maximal-maximal.
8. The degree function of $s$ is locally constant. Its values at $s(r)$ and $t(r)$ are equal:
   composition with the arrow $r$ and its inverse identifies the source fibres after extension to
   $\kappa(r)$, and fibre degree is unchanged by that extension. All maximal points of $A$ are in
   one orbit by the preceding step, hence have the same degree $r$. Every prime is contained in a
   maximal ideal, and a locally constant function takes equal values at two points in a
   specialization chain; therefore this degree is $r$ everywhere. The identity section makes $s$
   surjective, so $r\geq1$. The module $B$ via $\sigma$ is consequently finite locally free of
   constant rank $r$.
   Uses: lem-weil-pbc-finite-locally-free-degree-locally-constant.
   Uses: lem-weil-pbc-fibre-degree-base-change.
9. Apply the semilocal submodule basis lemma to $D\to A$, $P=B$ via $\sigma$, and $N=\tau(A)$.
   This is a $D$-submodule because $D$ consists of invariants. Surjectivity of $\phi$ says
   precisely that $N$ spans $B$ over $A$. The residue field is infinite, $A$ is semilocal,
   $\mathfrak m A\subseteq\operatorname{Jac}(A)$, and $B$ has the required constant positive rank
   by the preceding steps. We obtain $x_1,\ldots,x_r\in A$ such that $\tau(x_j)$ form an $A$-basis
   of $B$. The affine groupoid basis-descent lemma then gives $A=\bigoplus_j D x_j$ and identifies
   $\phi_D:A\otimes_D A\to B$ with an isomorphism.
   Uses: lem-a1-semilocal-submodule-basis.
   Uses: lem-a1-affine-groupoid-basis-descent.
10. Return to the original $C,A,B$. For each $\mathfrak p$, faithful flatness of $C_{\mathfrak
   p}\to D$ detects exactness, so $\phi_{\mathfrak p}$ is an isomorphism, since $\phi_D$ is. The
   flatness descent lemma likewise gives that $A_{\mathfrak p}$ is flat over $C_{\mathfrak p}$. A
   module vanishing at every prime is zero: a nonzero element has proper annihilator, contained in
   a maximal ideal where its localization is still nonzero. Apply this test to the kernel and
   cokernel of $\phi$ to conclude that $\phi$ is an isomorphism. For any injection $L\to L_2$,
   localization exactness makes $L_{\mathfrak p}\to L_2_{\mathfrak p}$ injective, and flatness of
   $A_{\mathfrak p}$ gives injectivity after tensoring. The same zero test on its kernel shows
   $L\otimes_C A\to L_2\otimes_C A$ injective. Thus $A$ is flat over $C$.
   Uses: def-weil-pbc-faithfully-flat-ring-map.
   Uses: lem-weil-pbc-flatness-descends-faithfully-flat.
   Uses: lem-weil-pbc-localization-module-exact.
11. Since $\operatorname{Spec}A\to\operatorname{Spec}C$ is surjective and flat, $C\to A$ is
   faithfully flat. The finite principal-open free cover of $B$ over $A$ from step 6 shows that
   $B$ is a finitely presented $A$-module. Under $\phi$, this is $A\otimes_C A$ with the
   $A$-action on its first factor. Faithfully flat descent of finite presentation, applied to the
   $C$-module $A$, makes $A$ finitely presented over $C$.
   Uses: lem-weil-pbc-flat-surjective-spectrum-faithfully-flat.
   Uses: lem-sc-affine-standard-cover-finite-presentation-flat.
   Uses: lem-trf-finite-presentation-module-descent-flat-local.
12. By steps 10 and 11, $A$ is a flat and finitely presented $C$-module, so the finitely-presented
   flat projectivity lemma makes $A$ a finite projective $C$-module. A finite projective module
   has a finite principal-open free cover: there are $g_1,\ldots,g_m\in C$ generating the unit
   ideal with each $A_{g_i}$ finite free over $C_{g_i}$. By the affine fibre-product formula the
   preimage of $D(g_i)$ in $U$ is $\operatorname{Spec}A_{g_i}$, and the finite-free algebra
   spectrum lemma shows that $\operatorname{Spec}A_{g_i}\to\operatorname{Spec}C_{g_i}$ is finite,
   flat and locally of finite presentation. Flatness at a point is a condition on local rings, and
   finite presentation at a point asks for affine neighbourhoods of the point and of its image;
   every point of $U$ lies over some open $D(g_i)$, so $q$ is flat and locally of finite
   presentation. For finiteness, let $V=\operatorname{Spec}R\subseteq M$ be an affine open. The
   affine fibre-product formula gives $q^{-1}(V)=\operatorname{Spec}(A\otimes_CR)$, and the images
   of finitely many $C$-module generators of $A$ generate $A\otimes_CR$ as an $R$-module. Hence
   $q$ is finite locally free. Surjectivity was already proved in step 3, and the affine
   fibre-product formula together with $\phi$ gives $R\cong U\times_MU$ with exactly the original
   projections.
   Uses: lem-weil-pbc-finitely-presented-flat-module-projective.
   Uses: lem-weil-pbc-finite-projective-standard-free-cover.
   Uses: lem-weil-pbc-finite-free-algebra-spectrum.
   Uses: lem-weil-pbc-fibre-product-affine-spectra.
   Uses: def-pc-finite-locally-free.
   Uses: def-weil-finite-integral-morphism.
   Uses: def-weil-flat-morphism.
   Uses: def-sbc-locally-finite-presentation.
13. The finite locally free surjection $q$ is an fppf cover. It is also a singleton fpqc cover,
   since its inverse image of each affine open is affine, flat and surjective. The maps $U\to S$
   agree on $R=U\times_MU$, so fpqc descent of scheme morphisms gives a unique map $M\to S$ making
   $q$ an $S$-morphism. Every fppf covering is an fpqc covering: its maps are open by flat-lfp
   openness, and the images of affine opens inside the inverse image of an affine open $V$ form an
   open cover of $V$; quasi-compactness selects finitely many of them, as required in the fpqc
   definition. Thus representable fpqc descent makes $h_M$ an fppf sheaf. On the fppf site over
   $S$, every $H\to M$ lifts after the fppf covering $H\times_MU\to H$, by base-change stability
   of fppf coverings. If two elements of $U(H)$ have the same image in $M(H)$, their pair is an
   $H$-point of $U\times_MU=R$, so their quotient classes are equal. The quotient presheaf
   therefore maps injectively and locally surjectively to $h_M$. The local-bijection
   sheafification criterion identifies its associated sheaf with $h_M$.
   Uses: def-pc-fppf-site.
   Uses: def-weil-pbc-fpqc-covering.
   Uses: lem-weil-pbc-fpqc-representable-descent.
   Uses: lem-cbc-set-presheaf-sheafification-local-bijection.
   Uses: lem-weil-pbc-flat-lfp-open.
   Uses: lem-trf-fppf-covering-base-change.
-/
theorem finiteFlat_affineRelation_quotient
    {S : Scheme.{u}} {A B : CommRingCat.{u}}
    (a : Spec A ⟶ S) (b : Spec B ⟶ S)
    (s t : Over.mk b ⟶ Over.mk a) [Mono (prod.lift s t)]
    [s.left.IsFiniteLocallyFree] [t.left.IsFiniteLocallyFree]
    (hrel : ∀ H : Over S, Equivalence (fun x y : H ⟶ Over.mk a ↦
      ∃ r : H ⟶ Over.mk b, r ≫ s = x ∧ r ≫ t = y)) :
    (affineRelationQuotientMap s.left t.left).IsFiniteLocallyFree ∧
    Surjective (affineRelationQuotientMap s.left t.left) ∧
    (∃ e : Spec B ≅ pullback (affineRelationQuotientMap s.left t.left)
        (affineRelationQuotientMap s.left t.left),
      e.hom ≫ pullback.fst _ _ = s.left ∧ e.hom ≫ pullback.snd _ _ = t.left) ∧
    ∃ m : Spec (CommRingCat.of (affineRelationInvariants s.left t.left)) ⟶ S,
      ∃ hq : affineRelationQuotientMap s.left t.left ≫ m = a,
        (∀ m' : Spec (CommRingCat.of (affineRelationInvariants s.left t.left)) ⟶ S,
          affineRelationQuotientMap s.left t.left ≫ m' = a → m' = m) ∧
        Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj (Over.mk m)) ∧
        ∃ η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj (Over.mk m),
          coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η =
            yoneda.map (Over.homMk (affineRelationQuotientMap s.left t.left) hq) ∧
          ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
            Function.Bijective (fun k : yoneda.obj (Over.mk m) ⟶ G.obj ↦ η ≫ k) := by
  sorry

end AlgebraicGeometry
