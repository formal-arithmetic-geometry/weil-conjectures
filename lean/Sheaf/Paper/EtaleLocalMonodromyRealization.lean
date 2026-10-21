/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.Paper.EtaleLocalMonodromyRealizationBase
import Sheaf.Paper.EtaleLocalMonodromyRealizationLocal

/-!
# Etale-local monodromy and exact rational realization

Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
and the integral-monodromy reduction in Corollary 6.8.5, pp. 59--60
(blueprint: lem-sfb-etale-local-monodromy-realization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Continuous finite-dimensional representations have fully faithful E-linear exact
realizations, normalized simultaneously on all invariant lattices by finite-level
monodromy and inverse limit followed by inversion of l. Every finite diagram of lisse
modules is etale locally a diagram in these same realizations. Restriction along an
etale map is written in its slice-site presentation; the coefficient comparison is
identity on continuous functions. Isomorphisms of these module presheaves are exactly
isomorphisms of the corresponding sheaf modules.

Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.4(1),(4),(6), and the proof
of Corollary 6.8.5, pp. 59--60
(blueprint: lem-sfb-etale-local-monodromy-realization).

Proof plan (the seven steps of the DAG node):

1. Integral monodromy, before rationalization. Apply
   [lem-sfb-integral-lisse-reduction-equivalence] and [det-pe-finite-local-systems-twist] to
   identify integral lisse $A_T$-modules with compatible towers of finite locally constant etale
   $A/\varpi^n$-modules, whose reductions are normalized. The finite-ring equivalence
   [cor-galois-lisse-representations](1), including its compatibility with scalar extension,
   identifies these with compatible towers of finite discrete continuous $\Pi_T$-modules $B_n$,
   free over $A/\varpi^n$ of a single rank $r$. Connectedness ensures a single rank. By
   [lem-pod-adic-limit-finite-modules](1),(2), $B=\varprojlim B_n$ is finite over $A$, has
   precisely these reductions, and its inverse-limit topology is adic. In fact it is free:
   choose a basis at level one and recursively lift it to a basis at level $n+1$; a lifted
   matrix is invertible because its determinant is a unit modulo $\varpi$. The resulting
   compatible bases identify $B$ with $\varprojlim(A/\varpi^n)^r=A^r$. The coordinate actions
   make $\Pi_T\times B\to B$ jointly continuous, because their composites with every finite
   discrete projection are continuous. Conversely a continuous action on finite free $B$ gives
   those discrete actions. The Hom bijection in the adic-limit lemma, restricted to equivariant
   maps at every level, proves full faithfulness. Thus there is an equivalence $K_T$ from
   continuous finite free $A$-representations to integral lisse modules, with
   $K_T(B)=\varprojlim_n\nu^*\mathcal L(B/\varpi^nB)$, naturally in maps. No use is made of part
   (2) of the Galois node, whose extra hypotheses are absent here.

2. Hom after inverting $\ell$. For integral lisse $M,N$ put $H=\mathcal Hom_{A_T}(M,N)$
   [def-pur-sheaf-hom]. On a common trivializing covering this is the sheaf of finite matrices,
   so $H$ is integral lisse, and the entrywise map gives $H[1/\ell]\cong\mathcal
   Hom_{E_T}(M[1/\ell],N[1/\ell])$. These local identifications are canonical (a matrix
   represents the same linear map under change of basis), so glue. Here $A_T[1/\ell]=E_T$ by the
   integral reduction lemma; for a finite free model, tensoring with this ring equals the
   colimit of repeated multiplication by $\ell$, and hence this equality holds for all these
   locally finite free modules. Apply [det-pe-bounded-continuity-sections] with the small
   filtered index $\mathbf N$, $U=T$, $q=0$, and the complexes $H[0]$ joined by multiplication
   by $\ell$: the common lower bound is zero and $T$ is qcqs. It gives
   $H[1/\ell](T)=H(T)[1/\ell]$. Therefore the actual ambient sheaf Hom is
   $\operatorname{Hom}_{A_T}(M,N)[1/\ell]$. This proves rational full faithfulness of integral
   lisse modules directly; finite-level full faithfulness alone would not suffice.

3. Construction of $J_T$ and its canonical normalization. By [lem-pod-profinite-stable-lattice],
   every finite dimensional continuous $E$-representation has an invariant finite free
   $A$-lattice $B$. For two such representations with lattices $B,C$, any $E$-linear map is a
   finite matrix in lattice bases. Multiplication by $\ell^m$ for a sufficiently large $m\geq0$
   puts every entry in $A$. Thus every equivariant $E$-map is $\ell^{-m}g$ for an equivariant
   $A$-map $g:B\to C$, and two presentations agree exactly when they agree after multiplying by
   a common power of $\ell$. This identifies representation Hom with
   $\operatorname{Hom}_{A,\Pi_T}(B,C)[1/\ell]$. Combine step 1 with step 2 to define
   $J_T(V)=K_T(B)[1/\ell]$ and $J_T(\ell^{-m}g)=\ell^{-m}K_T(g)[1/\ell]$. Independence of a
   fraction, addition, scalar multiplication and composition follow after a common
   multiplication by $\ell$, where they hold for $K_T$. For two lattices in the same $V$, their
   finite bases show $\ell^mB\subset C$ and $\ell^mC\subset B$ for some $m$. The identity on $V$
   therefore gives a canonical isomorphism of the two realizations by this Hom correspondence;
   the reverse identity is its inverse. For three choices the comparisons satisfy the cocycle
   equation because all represent the identity of $V$. They also commute with every equivariant
   map. Hence a choice of lattices defines an $E$-linear fully faithful functor independent up
   to these specified natural isomorphisms. Its values are lisse since $K_T(B)$ is locally
   $A_T^r$ and rationalization is locally $E_T^r$. Step 1 gives exactly the required
   inverse-limit normalization, including rank zero.

4. Compatible lattices for an exact sequence. Given $0\to V'\to V\to V''\to0$, choose an
   invariant finite free lattice $B\subset V$ by [lem-pod-profinite-stable-lattice]. Put
   $B'=B\cap V'$ and $B''=\operatorname{im}(B\to V'')$. The ring $A$ is a DVR, hence every ideal
   is principal and it is Noetherian [lem-weil-l-adic-extension-integers-dvr,
   def-sc-discrete-valuation-ring]. In the family of finitely generated submodules of $B'$ a
   maximal member exists by [lem-weil-pbc-noetherian-finite-module-acc]; adjoining any element
   of $B'$ shows that member is all of $B'$. Thus $B'$ is finite, and $B''$ is finite as a
   quotient of $B$. Both are torsion free as submodules of vector spaces, hence finite free by
   [lem-sc-dvr-fg-torsionfree-free]. Each spans the required vector space: multiply any vector
   of $V'$ by a sufficiently high power of $\ell$ to enter $B$, and lift any vector of $V''$ to
   $V$ and do the same. Both actions are continuous: choose an $A$-basis of each lattice and
   extend its $E$-basis to a basis of its containing vector space; the adic lattice topology is
   the subspace topology, and the restricted action is continuous. Lift a basis of $B''$ to $B$
   to split $0\to B'\to B\to B''\to0$ as $A$-modules; the splitting need not be equivariant.
   Therefore reduction modulo every $\varpi^n$ is a short exact sequence of finite continuous
   representations, with surjective transition maps on its kernel tower. Arbitrarily chosen
   lattices would not give this reduction exactness.

5. Exact inverse limits in the sheaf category. Apply the exact finite-coefficient equivalence
   [cor-galois-lisse-representations](1) to the reduced sequences from step 4, then apply the
   module inverse image $\nu^*$ of [sk-thm-pe-classical-sheaves]. It is exact into the ambient
   category $\operatorname{Mod}(T_{\mathrm{proét}},A_{n,T})$, not only into the classical
   subcategory: by [def-weil-pbc-site-comparison-morphism] it is, on sheaves of modules over the
   finite discrete ring $A/\varpi^n$, the left adjoint of $\nu_*$ (so it preserves cokernels)
   and it preserves finite limits (so it preserves kernels). This gives compatible short exact
   sequences $0\to F'_n\to F_n\to F''_n\to0$ of pro-etale $A_T$-modules, with epimorphic
   transitions on $F'_n$. Products of these sequences are exact by [det-pe-products-exact]. By
   [det-pe-milnor-epimorphic] applied to $(F'_n)$, $1-T$ on $\prod F'_n$ is epic. Limits are
   sectionwise by [lem-weil-pbc-module-sheaves-colimits-forgetful]. Given a section $c$ of
   $\varprojlim F''_n$, the product epimorphism locally lifts its tuple of coordinates to
   $b\in\prod F_n$; the defect $(1-T)b$ is a section of $\prod F'_n$. After a further covering
   it has the form $(1-T)a$ for $a\in\prod F'_n$. Then $b-a$ is compatible and lifts $c$. Both
   local lifting assertions, and the conclusion that the limit map is epic, use
   [lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective] and the exact forgetful functor of
   the module-colimits node. Sectionwise kernels prove left exactness. Hence the inverse-limit
   sequence is short exact. Finally localization is the filtered colimit of repeated
   multiplication by $\ell$; [lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact] and the
   same exact colimit-preserving forgetful functor show it preserves this short exact sequence.
   The normalization and naturality of steps 1–3 identify it with the image under $J_T$ of the
   original exact representation sequence.

6. Obtaining connected qcqs topologically Noetherian charts. For each of the finitely many given
   objects use [lem-weil-pbc-lisse-lattice-etale-local] to obtain an etale covering with
   integral lisse lattices. Iterating these coverings for the finitely many objects gives a
   common covering in the small etale site [def-weil-pbc-etale-site]; existing lattices restrict
   to later stages. On an etale slice the continuous-function coefficient rings are literally
   the coefficient rings of that slice, by [def-weil-pbc-lisse-lattice-coefficients], so
   restricting preserves the finite free local models and the rationalization isomorphisms.
   Refine each member by affine neighbourhoods mapping into affine opens $\operatorname{Spec}R$
   of $S$. Since an etale map is locally of finite presentation [def-weil-etale-morphism,
   def-sbc-locally-finite-presentation], these can be chosen $\operatorname{Spec}B$ with $B$ a
   finitely presented, in particular finitely generated, $R$-algebra. The open
   $\operatorname{Spec}R$ has Noetherian underlying space, so
   [lem-sfb-finite-type-noetherian-spectrum] gives the same property for $\operatorname{Spec}B$.
   By [lem-sc-noetherian-finite-irreducible-components] it has finitely many irreducible
   components. Form the finite graph joining two components when they meet. The union in each
   graph component is connected (a chain of intersecting connected irreducible sets), closed (a
   finite union of closed sets), and open (its complementary graph components also have closed
   union). These unions partition the chart and are precisely its connected components. Each is
   a connected open subscheme with Noetherian underlying space, hence qcqs: every open subset is
   quasi-compact. Indeed, finite unions from any open covering have a maximal member by the
   ascending chain condition; adjoining any remaining covering open shows this member covers the
   subset. This applies to the whole scheme and every intersection of two affine opens. They
   still form an etale covering of $S$. Discard empty members. Choose a point in each nonempty
   member and an algebraic closure of its residue field by [def-weil-algebraic-closure]; this
   gives the required geometric point [def-weil-geometric-point]. This step uses no
   ring-theoretic Noetherianity or separation of $S$.

7. Realizing the whole finite diagram. On a member $T_i$ of step 6 let $M_{a,i}$ be the integral
   lattice of each pulled-back object. The equivalence of step 1 writes it as
   $K_{T_i}(B_{a,i})$. Tensoring $B_{a,i}$ with $E$ gives $V_{a,i}$ with continuous action: its
   action matrix has continuous entries on the invariant lattice, hence on the same finite
   dimensional vector space. The normalization of step 3 identifies $J_{T_i}(V_{a,i})$ with
   $M_{a,i}[1/\ell]$ and with $u_i^{-1}L_a$. Write
   $\iota_{a,i}:J_{T_i}(V_{a,i})\xrightarrow{\sim}u_i^{-1}L_a$ for these isomorphisms. For an
   arrow $b:a\to c$, full faithfulness in step 3 gives a unique equivariant $E$-linear map
   $h_{b,i}$ satisfying $J_{T_i}(h_{b,i})=\iota_{c,i}^{-1}\circ u_i^{-1}f_b\circ\iota_{a,i}$.
   For two composable arrows the middle factors $\iota_{c,i}\circ\iota_{c,i}^{-1}$ cancel, so
   applying $J_{T_i}$ to their composite gives precisely the conjugate of the composite sheaf
   arrow. The identity arrow gives the identity map by the same formula. Faithfulness then
   reflects every stipulated equality of paths in the diagram. It is unnecessary to arrange
   integral preservation of all of the chosen lattices by all arrows: the Hom localization has
   already proved the assertion for rational maps. If there are no objects choose the same
   connected refinement of $S$ without invoking lattice covers; if $S$ is empty choose the empty
   covering. Thus the construction covers empty diagrams, rank zero, and the empty base. -/
theorem etale_local_monodromy_realization (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ R : ∀ (T : Scheme.{u}) (p : SfMonodromyPoint T), SfMonodromyRealization l E p,
      ∀ (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S]
        (A B : Type (u + 1)) [Finite A] [Finite B] (s t : B → A)
        (L : A → SfRationalModules l E S) (f : ∀ b : B, L (s b) ⟶ L (t b)),
        (∀ a : A, (L a).IsFiniteLocallyFree) →
          ∃ (I : Type (u + 1)) (Y : I → S.Etale),
            S.smallEtaleTopology.CoversTop Y ∧ (IsEmpty S → IsEmpty I) ∧
            ∃ (p : ∀ i : I, SfMonodromyPoint (Y i).left)
              (V : ∀ i : I, A → SfContinuousRepresentations l E (p i))
              (h : ∀ (i : I) (b : B), V i (s b) ⟶ V i (t b))
              (e : ∀ (i : I) (a : A),
                ((R (Y i).left (p i)).functor.obj (V i a)).val ≅
                  (PresheafOfModules.pushforward
                    (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Y i).hom)).obj
                      (L a).val),
              ∀ (i : I) (b : B),
                ((R (Y i).left (p i)).functor.map (h i b)).val ≫ (e i (t b)).hom =
                  (e i (s b)).hom ≫
                    (PresheafOfModules.pushforward
                      (ProEtale.lisseEtaleCoefficientIdentificationSized l E (Y i).hom)).map
                        (f b).val := by
  obtain ⟨R⟩ := exists_sf_monodromy_realization l E
  exact ⟨R, etale_local_monodromy_realization_local l E R⟩


end AlgebraicGeometry.Scheme
