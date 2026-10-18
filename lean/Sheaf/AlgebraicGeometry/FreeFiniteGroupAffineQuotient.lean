/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Yoneda

/-!
# Free finite-group quotients of schemes affine over their base

Source: Stacks Project, Spaces Properties, Tag 07S7, affine case; Groupoids, Tag 03BM.
(blueprint: lem-per-free-finite-group-affine-quotient)

The coproduct of copies of the terminal S-scheme is K_S. Its product with X is
K_S ×_S X. The component formula determines the action from the given automorphisms.
The coequalizer of the two Yoneda maps is the pointwise orbit presheaf, including
locally constant K-valued maps on disconnected tests. Its universal arrow to a sheaf
expresses sheafification without assuming a global small-valued sheafification instance.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A free action of a finite group on a scheme affine over S has its representable
fppf quotient, a finite locally free surjection with the prescribed kernel pair.
Every base change represents its own orbit sheaf and is categorical for invariant maps.
Source: Stacks Project Tags 07S7 and 03BM.
(blueprint: lem-per-free-finite-group-affine-quotient)

Proof, following the nine steps of the DAG node:
1. Representable functors are fppf sheaves. Indeed, for an fppf covering and any affine open $V$
   of its target, the images of affine opens in the inverse images of $V$ form an open cover of
   $V$: the covering maps are open by flat-lfp openness. Quasi-compactness of $V$ selects
   finitely many such images, so the covering is fpqc by its definition. Apply fpqc descent of
   morphisms; the descended morphism is over $S$ because that equality holds on the cover. Put
   $P(T)=X(T)/K_S(T)$ and $F=P^\#$. The unit $P\to F$ becomes an isomorphism on sheafification
   by the universal property and idempotence. The local-bijection criterion therefore says both
   that sections of $F$ locally lift to $P$ and that two sections of $P$ with equal images in
   $F$ become equal on a covering. These assertions may be used on the small universe-bounded
   site of the statement.
   Uses: lem-weil-pbc-flat-lfp-open, def-weil-pbc-fpqc-covering, lem-weil-pbc-fpqc-
   representable-descent, def-weil-pbc-sheafification, lem-cbc-set-presheaf-sheafification-
   local-bijection.
2. Choose an affine open cover $(U_i)$ of $S$. Write $X_i=p^{-1}(U_i)=\operatorname{Spec}A_i$,
   affine by the definition of an affine morphism. The action preserves $X_i$, and
   $R_i=K_{U_i}\times_{U_i}X_i$ is the finite disjoint union of copies of $X_i$, hence affine.
   Its projection to $X_i$ is locally, on an affine open $\operatorname{Spec}D$ of $X_i$, the
   spectrum of the diagonal map $D\to\prod_KD$. The standard coordinate vectors give this
   algebra a finite $D$-basis, so the finite-free algebra spectrum lemma makes this projection
   finite locally free there. Finiteness is local on the target, and flatness and local finite
   presentation are local directly from their local-ring and affine-neighbourhood definitions;
   thus the projection is finite locally free globally. The automorphism $(k,x)\mapsto(k,kx)$ of
   $R_i$, with inverse $(k,y)\mapsto(k,k^{-1}y)$, makes the action map another finite locally
   free projection. On every test scheme the image of $(a,\operatorname{pr}_2)$ is an
   equivalence relation: identity, inverse and multiplication give reflexivity, symmetry and
   transitivity. Freeness gives injectivity, so $R_i$ identifies with that relation, rather than
   merely mapping onto it.
   Uses: pqf-def-affine-morphism, lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-finite-
   free-algebra-spectrum, lem-weil-pbc-finite-local-on-target, def-weil-flat-morphism, def-sbc-
   locally-finite-presentation.
3. Apply the affine finite locally free relation quotient theorem to $X_i,R_i$ over $U_i$. With
   $s=\operatorname{pr}_2$ and $t=a$, its invariant ring is $C_i=\{b\in
   A_i:s^\sharp(b)=t^\sharp(b)\}$, equivalently $A_i^K$. It supplies
   $M_i=\operatorname{Spec}C_i$ over $U_i$, representing the fppf orbit sheaf, a finite locally
   free surjection $q_i:X_i\to M_i$, and the comparison isomorphism $R_i\simeq
   X_i\times_{M_i}X_i$ with its two prescribed projections. All its hypotheses were checked in
   the preceding step. The relation on test points is exactly the action of $K_{U_i}(T)$,
   including locally constant elements on disconnected $T$.
   Uses: lem-a1-finite-flat-affine-relation-quotient.
4. For each $i$ let $F_i\subset F$ be the subfunctor that equals $F(T)$ when the structure map
   $T\to S$ factors through $U_i$, and is empty otherwise. This is a sheaf: factorization
   through an open can be checked on any surjective covering. On schemes over $U_i$, the
   presheaf $P$ is precisely $T\mapsto X_i(T)/K_{U_i}(T)$. The unit into the restriction of $F$
   is locally bijective by step 1: all covers of such a $T$, and their refinements, are still
   schemes over $U_i$. Hence the local-bijection criterion and the sheafification universal
   property identify this restriction with the orbit sheaf represented by $M_i$ in step 3.
   Extending to $S$-schemes identifies $F_i$ with $h_{M_i}$, since neither has sections when
   $T\to S$ does not factor through $U_i$. For a section $z\in F(T)$, its pullback of $F_i$ is
   represented by the open subscheme $T\times_SU_i$: on every $T'$ over $T$, membership of
   $z|_{T'}$ in $F_i(T')$ means exactly that $T'\to S$ factors through $U_i$. Thus each
   inclusion is representable by open immersions. These opens cover $T$, so the $F_i$ cover $F$.
   No affineness of $U_i\cap U_j$ is used.
   Uses: lem-cbc-set-presheaf-sheafification-local-bijection, def-weil-pbc-sheafification, lem-
   galois-yoneda-fully-faithful.
5. The sheaf $F$ is in particular a Zariski sheaf. Step 4 verifies all three open-subfunctor
   conditions of the scheme representability criterion, so obtain an $S$-scheme $Q$ representing
   $F$. Yoneda turns the composite $h_X\to P\to F=h_Q$ into $q:X\to Q$ over $S$. It is invariant
   because its first map identifies orbits. Under the representation in step 4,
   $Q\times_SU_i=M_i$ and $q$ restricted over $U_i$ is the actual $q_i$, since both are induced
   by the same orbit map. These identities fix the comparison maps, not just their isomorphism
   classes.
   Uses: lem-pc-schemes-criterion, lem-galois-yoneda-fully-faithful.
6. The opens $M_i=Q\times_SU_i$ cover $Q$. On their inverse images $q$ is the finite locally
   free surjection $q_i$. Finiteness follows from the finite-local-on-target theorem; flatness
   follows on the same local rings, and at every point local finite presentation is witnessed by
   the affine neighbourhoods for $q_i$. Thus $q$ is finite locally free by definition, and it is
   surjective since each $q_i$ is. The comparison $K_S\times_SX\to X\times_QX$ restricts on this
   cover to the comparison isomorphisms of step 3. Their inverses agree on overlaps because they
   are inverses to the same map. They glue uniquely to a global inverse (glue the morphisms on
   this Zariski, hence fpqc, open cover). This proves the required kernel-pair isomorphism
   globally.
   Uses: lem-weil-pbc-finite-local-on-target, def-weil-flat-morphism, def-sbc-locally-finite-
   presentation, def-pc-finite-locally-free, lem-weil-pbc-fpqc-representable-descent.
7. Fix any $S'\to S$ and put $X'=X\times_SS'$, $Q'=Q\times_SS'$. The map $q$ is an fppf
   covering, since it is flat, locally of finite presentation and surjective. The fppf base-
   change lemma makes $q':X'\to Q'$ an fppf covering; the finite-morphism base-change lemma also
   makes it finite. Thus $q'$ is finite locally free and surjective. The fibre-product universal
   property base changes the already constructed kernel pair to $K_{S'}\times_{S'}X'\simeq
   X'\times_{Q'}X'$ with the same action and projection. Explicitly both sides parametrize, over
   a test $S'$-scheme $T$, pairs of lifts to $X$ with equal images in $Q$, with their fixed map
   to $S'$; the original comparison sends $(k,x)$ to $(kx,x)$.
   Uses: def-pc-fppf-site, lem-trf-fppf-covering-base-change, lem-weil-pbc-finite-morphism-
   permanence, def-pc-finite-locally-free, def-pc-fibre-product.
8. For a test $S'$-scheme $T$, invariant $q'$ gives a map $P'(T)=X'(T)/K_{S'}(T)\to Q'(T)$. If
   two representatives have the same image, the kernel-pair isomorphism in step 7 gives $k\in
   K_{S'}(T)$ carrying one to the other, so this map is injective. For any $z:T\to Q'$, the fppf
   covering $T\times_{Q'}X'\to T$ supplies a lift; hence the map is locally surjective. The
   local-bijection criterion identifies its sheafification with $h_{Q'}$, already an fppf sheaf
   by step 1. This proves that the particular base-changed $q'$ represents the orbit sheaf; it
   does not assert that arbitrary invariants commute with arbitrary scalar extension.
   Uses: lem-trf-fppf-covering-base-change, lem-cbc-set-presheaf-sheafification-local-bijection.
9. Let $Y$ be any $S'$-scheme and $f:X'\to Y$ invariant. For every $T$ it induces $P'(T)\to
   Y(T)$, sending an orbit to the composite with $f$. This is well defined also for locally
   constant $k$: on the clopen pieces where $k$ is constant invariance gives equality, and the
   morphisms agree globally by their sheaf property. Naturality is composition. Since $h_Y$ is
   an fppf sheaf, the universal property of sheafification extends this natural map uniquely to
   $h_{Q'}\to h_Y$. Yoneda yields a unique $S'$-morphism $Q'\to Y$ whose composite with $q'$ is
   $f$. For uniqueness, the same universal property identifies any two such natural
   transformations. This works for every $S'\to S$ and every $Y$, with no connectedness or
   etaleness assumption on $X\to S$.
   Uses: def-weil-pbc-sheafification, lem-galois-yoneda-fully-faithful.
-/
theorem freeFiniteGroup_affine_quotient (S : Scheme.{u}) (X : Over S)
    [IsAffineHom X.hom] (K : Type v) [Group K] [Finite K]
    (ρ : K →* Aut X)
    (a : ((∐ fun _ : K => Over.mk (𝟙 S)) ⨯ X) ⟶ X)
    (ha : ∀ k : K,
      prod.lift (Over.homMk X.hom ≫ Sigma.ι (fun _ : K => Over.mk (𝟙 S)) k)
        (𝟙 X) ≫ a = (ρ k).hom)
    [Mono (prod.lift a (prod.snd : ((∐ fun _ : K => Over.mk (𝟙 S)) ⨯ X) ⟶ X))] :
    ∃ (Q : Over S) (q : X ⟶ Q),
      a ≫ q = prod.snd ≫ q ∧
      q.left.IsFiniteLocallyFree ∧ Surjective q.left ∧
      (∃ e : ((∐ fun _ : K => Over.mk (𝟙 S)) ⨯ X) ≅ pullback q q,
        e.hom ≫ pullback.fst q q = a ∧
        e.hom ≫ pullback.snd q q = prod.snd) ∧
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj Q) ∧
      (∃ η : coequalizer (yoneda.map a) (yoneda.map (prod.snd : _ ⟶ X)) ⟶
          yoneda.obj Q,
        coequalizer.π (yoneda.map a) (yoneda.map (prod.snd : _ ⟶ X)) ≫ η =
          yoneda.map q ∧
        ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
          Function.Bijective (fun k : yoneda.obj Q ⟶ G.obj => η ≫ k)) ∧
      ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
        Presheaf.IsSheaf (Scheme.fppfTopology.over S')
          (yoneda.obj ((Over.pullback f).obj Q)) ∧
        (∃ η : coequalizer (yoneda.map ((Over.pullback f).map a))
            (yoneda.map ((Over.pullback f).map (prod.snd : _ ⟶ X))) ⟶
              yoneda.obj ((Over.pullback f).obj Q),
          coequalizer.π (yoneda.map ((Over.pullback f).map a))
              (yoneda.map ((Over.pullback f).map (prod.snd : _ ⟶ X))) ≫ η =
            yoneda.map ((Over.pullback f).map q) ∧
          ∀ G : Sheaf (Scheme.fppfTopology.over S') (Type u),
            Function.Bijective
              (fun k : yoneda.obj ((Over.pullback f).obj Q) ⟶ G.obj => η ≫ k)) ∧
        ∀ (Y : Over S') (g : (Over.pullback f).obj X ⟶ Y),
          (Over.pullback f).map a ≫ g =
            (Over.pullback f).map (prod.snd : _ ⟶ X) ≫ g →
          ∃! h : (Over.pullback f).obj Q ⟶ Y,
            (Over.pullback f).map q ≫ h = g := by
  sorry

end AlgebraicGeometry
