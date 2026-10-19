/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Topology.Spectral.Basic
import Sheaf.Topology.SpectralDirectedLimit
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Separable Riemann--Zariski refinement over an integral qcqs base

Source: Temkin, *Stable modification of relative curves*, §3.2, Propositions 3.2.1
and 3.2.6, Lemma 3.2.2 and Corollaries 3.2.4--3.2.7, printed pp. 15--17;
relative covering as in Theorem 3.5.5, Steps 1 and 5
(blueprint: lem-trf-qcqs-separable-riemann-zariski-refinement).

The model, quasi-model, compatible-point space with its initial topology, and
centred valuation pairs are the existing `AlgebraicGeometry.RiemannZariski` notions.
The opens of the common model are represented by actual open immersions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory Topology

namespace AlgebraicGeometry.RiemannZariski

/-- The specified generic map induced by the field inclusion into `L`.
Source: Temkin §3.2, opening paragraph, printed p. 15
(blueprint: lem-trf-qcqs-separable-riemann-zariski-refinement). -/
def separableGenericMap (S : Scheme.{u}) [IsIntegral S]
    (L : Type u) [Field L] [Algebra S.functionField L] : Spec (.of L) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
    S.fromSpecStalk (genericPoint S)

/-- Separable Riemann--Zariski refinement without any Noetherian or height bound.
Source: Temkin §3.2, printed pp. 15--17; relative covering as in Theorem 3.5.5,
Steps 1 and 5 (blueprint: lem-trf-qcqs-separable-riemann-zariski-refinement).

Proof plan, with the exact dependencies and all fourteen steps of the DAG node:
1. For any model or quasi-model $X$, take a nonempty affine chart $\operatorname{Spec}B$ over an
affine chart $\operatorname{Spec}A$ of $S$ with $B$ finitely generated over $A$, as in
[def-weil-finite-type-morphism]. Integrality identifies $\operatorname{Frac}A=F$ and
$\operatorname{Frac}B=k(X)\subseteq L$. If $b_1,\ldots,b_n$ generate $B/A$, then
$k(X)=F(b_1,\ldots,b_n)$. Each $b_j$ is algebraic separable over $F$, so adjoining them
successively gives a finite separable extension. Thus all the asserted generic fields are finite
separable. The same argument shows that $L$ is a separable closure of each $k(X)$.

2. Every model and quasi-model is qcqs. Its structure morphism is quasi-compact by finite type
[def-weil-finite-type-morphism], and is separated (proper implies separated by
[def-weil-proper-morphism]), hence quasi-separated by [lem-pc-separated-quasi-separated]. Since
$S$ is qcqs, clause (2) of [lem-weil-pbc-qcqs-morphism-permanence] gives both assertions about its
source. No Noetherian hypothesis is used.

3. We use the following explicit construction repeatedly. If $P\to S$ is proper and has a
specified $L$-point over the generic map, take the closure of its image point with the reduced
induced structure of [lem-weil-pbc-reduced-induced-closed-subscheme]. It is nonempty, irreducible
and reduced, hence integral [def-pc-integral-scheme]. On a chart meeting the image point its
defining ideal is the kernel of the ring map to $L$, so the generic $L$-point factors through the
closure and embeds its function field in $L$. The closed subscheme is proper over $S$ by
[lem-weil-pbc-closed-immersion-proper], and is therefore an $L$-model. If an integral open
subscheme of $P$ contains that image point densely, the induced closure restricts to that whole
open, since the kernel on its affine domains is zero.

4. The models form a nonempty directed partially ordered set after taking representatives: $S$ is
a model; for two models take the reduced generic closure of their product, which is proper by
[lem-weil-pbc-proper-base-change] and [lem-weil-pbc-proper-composition], and apply Step 3. There
is at most one refinement map: the equalizer of two maps to the separated target is closed by its
diagonal and [lem-weil-pbc-closed-immersion-base-change]; its ideal vanishes generically, hence is
zero on the affine domains of the integral source. Thus mutual refinements are inverse. The
representatives form a set: a finite affine cover of $S$ is fixed; each finite-type source has a
finite cover by finitely generated algebras over those rings (quotients by ideals in finite
polynomial rings), and its gluing uses finitely many affine charts on each intersection, since it
is quasi-separated by Step 2. These ring presentations, gluing maps and embeddings into the fixed
set $L$ range over a set.

5. By Step 2 and [lem-weil-pbc-qcqs-scheme-spectral], each model has a spectral underlying space.
A refinement is proper by [lemma-nagata-proper-to-separated-target], since its source is proper
over $S$ and its target separated over $S$. It is consequently quasi-compact by
[def-weil-proper-morphism] and [def-weil-finite-type-morphism], so it is a spectral map. Apply
[lem-weil-pbc-spectral-directed-limit-spectral] to the small directed system of Step 4. Its limit
is exactly the compatible-point space with the topology in the statement. It is spectral, hence
quasi-compact by [def-weil-spectral-space].

6. For a compatible point $x=(x_X)$ form $R_x=\bigcup_X\mathcal O_{X,x_X}\subseteq L$. A
refinement is dominant because it respects the specified generic points, so these are injective
subring maps and the union is directed. They are local maps, hence the maximal ideals have a
directed union $\mathfrak m$: it is an ideal and any element outside it has its inverse in a local
ring already containing that element. Thus $R_x$ is local and dominates each $\mathcal O_{X,x_X}$.
In particular the inclusion from the coordinate on the model $S$ gives $\operatorname{Spec}R_x\to
S$ with the prescribed generic map as soon as $\operatorname{Frac}R_x=L$.

7. For $f\in L^\times$, use the map $\operatorname{Spec}L\to S\times_{\mathbf Z}\mathbf
P^1_{\mathbf Z}$ with projective coordinate $[1:f]$. The product is proper over $S$ by
[lemma-nagata-projective-space-base-change-proper]; take its reduced generic closure $X_f$ by Step
3. The two standard opens of $\mathbf P^1$ cover it by [def-nagata-affine-proj], and
[lemma-nagata-relative-affine-space-open-immersion] identifies their coordinates with $f$ and
$f^{-1}$ on the generic point. At $x_{X_f}$ one of these coordinates is regular; hence $f$ or
$f^{-1}$ belongs to $R_x$. This proves that $R_x$ is a valuation subring and that its fraction
field is all of $L$.

8. Conversely a pair $(V,c)$ lifts uniquely to every proper model by
[lemma-nagata-proper-separated-valuation-extension]. The closed-point images of these lifts are
compatible by uniqueness. Their local homomorphisms embed the corresponding local rings in $V$ and
make $V$ dominate $R_x$. Now Step 7 says $R_x$ has fraction field $L$, so
[lemma-nagata-valuation-intersection], with both fields equal to $L$, gives $V=R_x$. In the other
direction the local inclusions into $R_x$ give lifts with closed-point images $x_X$; uniqueness
recovers the original compatible family. Both constructions preserve the entire morphism to $S$,
not just its closed-point image. This proves the asserted valuation-pair bijection even when $S$
is not separated over $\mathbf Z$.

9. For a quasi-model $U\to S$, [thm-nagata-compactification] and [def-nagata-compactification]
give a quasi-compact open immersion into a proper $S$-scheme. Replace the latter by its reduced
generic closure as in Step 3, calling it $\overline U$. This retains all of $U$ as an open
subscheme. Steps 1--8 apply over the integral qcqs scheme $U$ as well. By
[lemma-nagata-separated-valuation-lift-unique], composition gives an injection of valuation pairs
into those on $S$. Its image equals $p_{\overline U}^{-1}(U)$: a lift to $U$ agrees with the
proper lift to $\overline U$ by [lemma-nagata-proper-separated-valuation-extension]; conversely a
proper lift whose closed point lands in $U$ factors through $U$, since every point of a local
spectrum generalizes its closed point. Thus the image is open as a subset.

10. We spell out the permanence needed to compare the topologies. For any proper $U$-model $A$,
its composite to $S$ is finite type by [lem-sfb-finite-type-composition-base-change] and
[def-weil-proper-morphism]. It is separated: its diagonal factors as $A\to A\times_U A\to
A\times_S A$; the first arrow is closed and the second is a base change of the closed diagonal of
$U/S$. By [lem-weil-pbc-closed-immersion-base-change] and [lem-weil-pbc-closed-immersion-comp]
their composite is closed. Hence [thm-nagata-compactification] applies to $A\to S$. Taking the
reduced generic closure in this compactification produces an $S$-model $\overline A$ containing
$A$ openly, exactly as in Step 9.

11. For an open $O\subseteq A$ in any proper $U$-model, its inverse image in $RZ_L(U)$
corresponds, under the injection of Step 9, to $p_{\overline A}^{-1}(O)$ in $RZ_L(S)$. Indeed the
proper lift over $U$, composed with $A\hookrightarrow\overline A$, is the unique proper lift over
$S$ by [lemma-nagata-proper-separated-valuation-extension]. These are all the generating opens of
the source topology, so the injection is open. It is also continuous: for any proper $S$-model
$B$, the reduced generic closure inside $B\times_SU$ is a proper $U$-model by
[lem-weil-pbc-proper-base-change] and [lem-weil-pbc-closed-immersion-proper], and its map to $B$
computes the restricted centre projection. Thus inverse images of all generating opens of the
target are open. This proves the homeomorphism onto the open in Step 9.

12. For a finite family $U_i$, form their integral compactifications $\overline U_i$ from Step 9
and take $T$ to be the reduced generic closure in $\prod_S\overline U_i$. The product is proper by
[lem-weil-pbc-proper-base-change] and [lem-weil-pbc-proper-composition], so Step 3 applies. Its
projections $q_i:T\to\overline U_i$ are proper by [lemma-nagata-proper-to-separated-target] and
dominant because they send the specified generic point to that of $U_i$. Set $W_i=q_i^{-1}(U_i)$.
Then $W_i\to U_i$ is proper by [lem-weil-pbc-proper-base-change], and dominant since $W_i$
contains the generic point of $T$. It is quasi-compact over the quasi-compact scheme $U_i$ by
[def-weil-proper-morphism], [def-weil-finite-type-morphism] and
[lem-weil-pbc-qcqs-morphism-permanence](2). In particular $W_i$ is a quasi-compact open in $T$.
All morphisms commute with $\operatorname{Spec}L$ by construction. For the empty family use $T=S$.

13. For any model $T\to S$, proper lifting gives a bijection $RZ_L(T)\to RZ_L(S)$ by
[lemma-nagata-proper-separated-valuation-extension]. It is a homeomorphism: a proper $T$-model is
already a proper $S$-model by [lem-weil-pbc-proper-composition]; conversely the reduced generic
closure in $B\times_ST$ of any $S$-model $B$ is a $T$-model by [lem-weil-pbc-proper-base-change]
and [lem-weil-pbc-closed-immersion-proper]. The respective centre projections compute both
topologies. The same argument applies to the proper map $W_i\to U_i$, with their compatible
generic maps from $L$, and gives $RZ_L(W_i)=RZ_L(U_i)$ as subspaces of $RZ_L(S)$: the existence
and uniqueness of the proper lift to $W_i$ identifies the valuation sets, and Step 11 identifies
their open embeddings. This proves exactly the open-image equality asserted for the constructed
$W_i$.

14. For any $y\in T$, [lemma-nagata-local-domain-valuation-dominates] supplies a valuation ring of
$k(T)$ dominating $\mathcal O_{T,y}$. Extend it to a valuation ring $V$ of $L$ with
[lemma-nagata-valuation-ring-extension]. The resulting local inclusion $\mathcal O_{T,y}\subseteq
V$ gives a morphism $\operatorname{Spec}V\to T$ with closed point $y$. If the $RZ_L(U_i)$ cover,
this pair over $S$ lifts to some $U_i$. Its composite into $\overline U_i$ and the composite
through $q_i$ agree by [lemma-nagata-proper-separated-valuation-extension]. Therefore $q_i(y)\in
U_i$, or $y\in W_i$, proving the covering assertion. For an arbitrary open $S_0\subseteq S$, the
relative valuation subspace consists of the pairs whose morphism factors through $S_0$;
equivalently their centre on $S$ is in $S_0$, so this is the open $p_S^{-1}(S_0)$ denoted
$RZ_L(S_0)$. If $y\in T\times_SS_0$, the constructed valuation morphism factors through this open
(its closed point does), and the selected subfamily supplies a lift to one of its $U_i$. The same
uniqueness argument puts $y$ in the corresponding $W_i$. Each such $W_i$ already factors through
$S_0$ via $U_i$. Hence these opens cover exactly $T\times_SS_0$, without imposing
quasi-compactness on $S_0$.
-/
theorem qcqs_separable_refinement
    (S : Scheme.{u}) [IsIntegral S] [CompactSpace S] [QuasiSeparatedSpace S]
    (L : Type u) [Field L] [Algebra S.functionField L] [IsSepClosure S.functionField L] :
    (∀ U : QuasiModel S L (separableGenericMap S L),
      U.toGenericScheme.IsFiniteSeparableOver (algebraMap S.functionField L)) ∧
    CompactSpace (Point S L (separableGenericMap S L)) ∧
    ∃ e : Point S L (separableGenericMap S L) ≃
        ValuationPoint S L (separableGenericMap S L),
      (∀ x, Corresponds x (e x)) ∧
      ∃ (eU : ∀ U : QuasiModel S L (separableGenericMap S L),
          Point U.X L U.generic ≃ ValuationPoint U.X L U.generic)
        (j : ∀ U : QuasiModel S L (separableGenericMap S L),
          Point U.X L U.generic → Point S L (separableGenericMap S L)),
        (∀ U x, Corresponds x (eU U x)) ∧
        (∀ U, IsOpenEmbedding (j U)) ∧
        (∀ U x, e (j U x) = ValuationPoint.push U (eU U x)) ∧
        (∀ U x, x ∈ Set.range (j U) ↔ (e x).LiftsTo U) ∧
        (∀ M : Model S L (separableGenericMap S L),
          ∃ h : Point M.X L M.generic ≃ₜ Point S L (separableGenericMap S L),
            ∀ x, h x = j M.toQuasiModel x) ∧
        (∀ (I : Type w) [Finite I] (U : I → QuasiModel S L (separableGenericMap S L)),
          ∃ (M : Model S L (separableGenericMap S L))
            (W : I → QuasiModel S L (separableGenericMap S L))
            (a : ∀ i : I, (W i).X ⟶ M.X)
            (q : ∀ i : I, (W i).X ⟶ (U i).X),
            (∀ i : I, IsOpenImmersion (a i) ∧ CompactSpace (W i).X ∧
              IsProper (q i) ∧ IsDominant (q i)) ∧
            (∀ i : I, a i ≫ M.map = (W i).map ∧ q i ≫ (U i).map = (W i).map) ∧
            (∀ i : I, (W i).generic ≫ a i = M.generic ∧
              (W i).generic ≫ q i = (U i).generic) ∧
            (∀ i : I, Set.range (j (W i)) = Set.range (j (U i))) ∧
            ((∀ x, ∃ i : I, x ∈ Set.range (j (U i))) →
              ∀ y : M.X, ∃ i : I, y ∈ Set.range (a i)) ∧
            (∀ (J : Set I) (S₀ : S.Opens),
              (∀ i : I, i ∈ J → ∃ g : (U i).X ⟶ S₀.toScheme, g ≫ S₀.ι = (U i).map) →
              (∀ v : ValuationPoint S L (separableGenericMap S L),
                (∃ c : Spec (.of v.V) ⟶ S₀.toScheme, c ≫ S₀.ι = v.centre) →
                  ∃ i : I, i ∈ J ∧ v.LiftsTo (U i)) →
              ∀ y : M.X, (∃ i : I, i ∈ J ∧ y ∈ Set.range (a i)) ↔ M.map y ∈ S₀)) := by
  sorry

end AlgebraicGeometry.RiemannZariski
