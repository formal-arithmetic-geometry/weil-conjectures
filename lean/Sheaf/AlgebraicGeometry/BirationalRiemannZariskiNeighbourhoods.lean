/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.AlgebraicGeometry.BirationalValuationNeighbourhoodData
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Topology.Spectral.Basic
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Topology.SpectralDirectedLimit
import Sheaf.Compactification.BoundaryRefinement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.Compactification.Dense

/-!
# Birational Riemann--Zariski compactness and affine valuation neighbourhoods

Source: Temkin, Stable modification of relative curves, §3.2, Proposition 3.2.1,
Lemma 3.2.2 and Corollaries 3.2.4--3.2.5 and 3.2.7, pp. 15--17
(blueprint: lem-trf-birational-riemann-zariski-neighbourhoods).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.RiemannZariski

/-- Source: Temkin, Stable modification, §3.2, pp. 15--17.
(blueprint: lem-trf-birational-riemann-zariski-neighbourhoods).

Proof, following the fourteen steps of the node:
1. We use reduced generic closures throughout. If a scheme $P$ proper over $Z$ has a specified
   $Z$-map $\operatorname{Spec}F\to P$, take the reduced induced closed subscheme $C$ of the
   closure of its image, using [lem-weil-pbc-reduced-induced-closed-subscheme]. It is nonempty,
   reduced and irreducible, hence integral. On any affine chart meeting that image its coordinate
   ring is the quotient by the kernel of the map to $F$. Thus the generic map factors through $C$.
   Its generic residue field is $F$: it embeds into $F$, while the map from $Z$ supplies the
   opposite inclusion $F\to k(C)$, whose composite into $F$ is the identity. So $C$ is a
   birational model. It is proper by [lem-weil-pbc-closed-immersion-proper]. This construction
   imposes no Noetherian or finite-presentation hypothesis.
2. The identity model $Z$ exists. Given models $X,Y$, their fibre product is proper over $Z$ by
   [lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition]. Apply Step 1 to the pair of
   generic maps into this product. The resulting integral model dominates both. Refinement maps
   are unique: for two maps from an integral model to $Y$, their equalizer is the pullback of the
   closed diagonal of $Y/Z$ [def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change].
   Its ideal vanishes at the generic point. The injection of every nonempty affine ring into the
   function field [lem-sc-integral-scheme-stalks-in-function-field] forces that ideal to be zero.
   Consequently the equalizer is the whole source. Choosing representatives makes the model system
   a directed partially ordered set, ordered with dominating models larger.
3. This directed set can be chosen small. By [def-weil-finite-type-morphism] every model has a
   finite affine cover over a fixed finite affine cover of $Z$. Each nonempty affine ring embeds
   into the set $F$ by [lem-sc-integral-scheme-stalks-in-function-field], so its possible rings
   form a subset of the power set of $F$. Finite lists of these spectra, choices of their overlap
   opens, gluing isomorphisms, and structure morphisms to the fixed scheme $Z$ are all sets of
   data. Every model is represented by such data. Hence representatives of their isomorphism
   classes, and their morphisms, form sets. The same argument applies when affine opens of the
   models and a prescribed valuation centre are included in the data.
4. Every proper model is qcqs: properness gives quasi-compactness and separatedness [def-weil-
   proper-morphism], so [lem-weil-pbc-qcqs-morphism-permanence](2), with the qcqs base $Z$, gives
   both properties of its source. Each refinement is proper by [lemma-nagata-proper-to-separated-
   target], hence quasi-compact. By [lem-weil-pbc-qcqs-scheme-spectral], the model spaces are
   spectral; refinements are spectral maps, since quasi-compactness says exactly that inverse
   images of quasi-compact opens are quasi-compact. Form the space $R$ of compatible points on
   these models with the initial topology of the projections. It is the topological inverse limit
   by the defining universal property of the product subspace topology. Apply [lem-weil-pbc-
   spectral-directed-limit-spectral] to the small directed system of Steps 2--3. It makes $R$
   spectral and therefore quasi-compact [def-weil-spectral-space].
5. Fix a compatible point $x=(x_X)$ of $R$. Inside $F$, take $R_x=\bigcup_X\mathcal O_{X,x_X}$.
   These inclusions are justified by [lem-sc-integral-scheme-stalks-in-function-field]; refinement
   maps induce their inclusions because they commute with the generic maps. Their stalk maps are
   local. Thus the union of their maximal ideals is an ideal: sums and products can be tested at a
   common refinement. An element outside this union is a unit already at a stage containing it,
   and a member cannot become a unit later because the transition maps are local. This proves that
   $R_x$ is local and every stage maps locally to it. The local maps $\mathcal O_{X,x_X}\to R_x$
   give morphisms $\operatorname{Spec}R_x\to X$ by [lem-weil-pbc-morphism-from-spec-local-ring],
   with centre $x_X$. They are compatible, since they have the same centre and the same map on the
   local ring of the target. In particular the identity model supplies the required morphism to
   $Z$.
6. For $a\in F^\times$, map $\operatorname{Spec}F$ to $Z\times\mathbf P^1_{\mathbf Z}$ with
   projective coordinate $[1:a]$. This product is proper over $Z$ by [lemma-nagata-projective-
   space-base-change-proper]. Step 1 gives its reduced generic closure $X_a$, a birational model.
   The two standard charts of $\mathbf P^1$ cover it by [def-nagata-affine-proj]; [lemma-nagata-
   relative-affine-space-open-immersion], also with the two homogeneous coordinates interchanged,
   identifies their coordinates as $t=T_1/T_0$ and $s=T_0/T_1$. At $x_{X_a}$ at least one chart
   applies. Its coordinate has generic value $a$ or $a^{-1}$, respectively, so one of these lies
   in $\mathcal O_{X_a,x_{X_a}}\subset R_x$. Hence $R_x$ is a valuation subring of $F$ by the
   definition in the statement. Its fraction field is $F$, since for every nonzero $a$ either $a$
   itself or its inverse lies in $R_x$.
7. Conversely a centred valuation $(O,v)$ lifts uniquely to every proper model by [lemma-nagata-
   proper-separated-valuation-extension]: the given generic-point map and $v$ give its required
   square, and the fraction field is exactly $F$. Uniqueness makes the lifted centres compatible.
   Their local rings map locally into $O$, and these maps are their inclusions in $F$. Thus $O$
   dominates their union $R_x$ of Step 5. Both are valuation rings of the same field by Step 6.
   Apply [lemma-nagata-valuation-intersection] with both fields $F$, $A=R_x$ and $B=O$, to get
   $O=R_x$. Conversely, the local maps of Step 5 give lifts with the originally prescribed
   centres, so uniqueness recovers $x$. The map back to $Z$ is recovered as well: at its centre
   both morphisms induce the same local inclusion into $O$, so [lem-weil-pbc-morphism-from-spec-
   local-ring] identifies them. We have a bijection $R\simeq\operatorname{Val}_F(Z)$ compatible
   with every centre projection. Both topologies are initial for those projections, hence this is
   a homeomorphism. Step 4 proves (i), and this step proves unique lifting.
8. For the topology argument we record explicitly how composition preserves the hypotheses needed
   for compactification. If $A\to U$ and $U\to Z$ are separated and of finite type, their
   composite is of finite type by [lem-sfb-finite-type-composition-base-change]. Its diagonal
   factors as $A\to A\times_U A\to A\times_Z A$. The first map is a closed immersion by
   separatedness; the second is the base change of the closed diagonal of $U/Z$, so is a closed
   immersion by [lem-weil-pbc-closed-immersion-base-change]. Their composite is a closed
   immersion: on affine charts the corresponding surjections of rings compose, using the affine
   characterization in [def-weil-closed-immersion]. This proves separatedness of the composite
   from [def-weil-proper-morphism].
9. Let $U\to Z$ be a birational quasi-model. Apply [sk-thm-nagata-compactification] over the qcqs
   scheme $Z$. Its compactification is an open immersion into a proper $Z$-scheme, by [sk-def-
   nagata-sketch-data]. Replace that proper scheme by the reduced closure of its generic point as
   in Step 1, denoted $\overline U$. It still contains $U$ as an open subscheme: restriction of
   the reduced closure to the reduced integral open $U$ has support all of $U$, and uniqueness in
   [lem-weil-pbc-reduced-induced-closed-subscheme] identifies it with $U$. Thus $\overline U$ is a
   birational model. The map on centred valuations induced by $U\to Z$ is injective by [lemma-
   nagata-separated-valuation-lift-unique]. Its image is exactly $p_{\overline U}^{-1}(U)$. Indeed
   a lift into $U$ composes to the unique proper lift into $\overline U$; conversely if the proper
   lift has closed centre in $U$, it factors through that open, because every point of a local
   spectrum generalizes its closed point. This image is open.
10. The set injection of Step 9 is continuous. For any birational $Z$-model $B$ and open
   $W\subseteq B$, take the reduced generic closure $B_U$ in $B\times_ZU$. It is integral with
   function field $F$ as in Step 1; it is proper over $U$ by [lem-weil-pbc-proper-base-change,
   lem-weil-pbc-closed-immersion-proper]. Thus it is a birational $U$-model. The centre projection
   to $B_U$, followed by its map to $B$, computes the restricted centre projection to $B$: both
   lifts into $B$ agree by [lemma-nagata-proper-separated-valuation-extension]. Therefore the
   inverse image of $p_B^{-1}(W)$ is the inverse image of the open $W$ in $B_U$, an open subset of
   $\operatorname{Val}_F(U)$. This verifies continuity on all the generating opens of the target
   topology.
11. For inverse continuity, let $A\to U$ be any birational model and $W\subseteq A$ open. Step 8
   shows $A\to Z$ is separated of finite type, so [sk-thm-nagata-compactification] compactifies
   it. Its reduced generic closure $\overline A$ is a birational $Z$-model containing $A$ as an
   open, by the argument of Step 9 and [lem-weil-pbc-reduced-induced-closed-subscheme]. Under the
   injection of Step 9 the generating open $p_A^{-1}(W)$ is precisely $p_{\overline A}^{-1}(W)$
   intersected with the image. To check the nontrivial direction, start with a valuation in that
   image, lift it to $U$, then lift to $A$ by [lemma-nagata-proper-separated-valuation-extension]
   for $A/U$. Its composite into $\overline A$ equals the proper $Z$-lift by the same uniqueness
   theorem. Thus its centre lies in $W$ exactly when its $A$-centre does. These opens generate the
   source topology, proving inverse continuity and hence (ii). The qcqs property required if
   constructing the source limit follows from finite type and separatedness of $U/Z$ and [lem-
   weil-pbc-qcqs-morphism-permanence].
12. Fix $(O,v)$ and let $c_X$ be its unique centre on every birational model. Index pairs $(X,V)$
   with $V$ an affine open containing $c_X$, and arrows the $Z$-morphisms $V'\to V$ commuting with
   the generic maps. Such arrows are unique by the closed-diagonal argument in Step 2, since $V\to
   Z$ is separated (its diagonal is the restriction of that of $X/Z$). Any such arrow respects the
   valuation lifts: composing $\operatorname{Spec}O\to V'$ into $X$ gives the unique lift there by
   [lemma-nagata-proper-separated-valuation-extension]. Any two pairs have a common refinement:
   use the common model $Y$ of Step 2 and take an affine neighbourhood of $c_Y$ inside the
   intersection of the inverse images of their two opens. It maps into both. The pair category is
   nonempty, small by Step 3, and cofiltered; parallel-arrow equalization is automatic from
   uniqueness.
13. For every pair $(X,V=\operatorname{Spec}A)$ the whole map $\operatorname{Spec}O\to X$ factors
   through $V$, because $V$ contains its closed centre. The ring map $A\to O$ is injective and is
   its generic embedding into $F$ by [lem-sc-integral-scheme-stalks-in-function-field]. The
   fraction field of $A$ is $F$: its localization at the centre is $\mathcal O_{X,c_X}$, whose
   fraction field is $F$ by that node, and localization does not change the fraction field of a
   domain. Every transition is consequently inclusion of subrings of $O\subseteq F$. Their
   filtered union is $O$. Namely Step 7 gives $O=\bigcup_X\mathcal O_{X,c_X}$; if $a$ belongs to
   such a local ring, choose an affine neighbourhood with ring $A$ and express $a=b/s$ in
   $A_{\mathfrak p}$, $s\notin\mathfrak p$. The smaller affine $D(s)$ has ring $A_s$ containing
   $a$. Finally a directed union of subrings is their colimit: any compatible maps to another ring
   agree on overlaps after passing to a common stage, and hence define the unique ring map on the
   union. This proves every ring-diagram assertion in (iii).
14. Given a prescribed birational model $X_0$ and a neighbourhood $N$ of its centre, repeat Step
   12 after restricting to models dominating $X_0$ and to affine opens contained in the inverse
   image of $N$. This restricted category is nonempty and cofiltered: a common refinement can
   first be taken with $X_0$, then one chooses an affine neighbourhood of its centre inside all
   the finitely many inverse-image opens. It is cofinal for the ring system, since the same
   procedure starts from any pair of the original category. Explicitly every element represented
   in a former affine ring stays represented after its inclusion into such a refined affine ring.
   Thus the directed union is still $O$ by Step 13, with the same injective transitions and
   fraction field. If a neighbourhood has been specified on a different model, first dominate that
   model as well. This establishes the final restriction assertion.
-/
theorem birational_riemann_zariski_neighbourhoods
    (Z : Scheme.{u}) [IsIntegral Z] [CompactSpace Z] [QuasiSeparatedSpace Z] :
    (∀ (v : ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
        (M : Model Z Z.functionField (Z.fromSpecStalk (genericPoint Z))),
      ∃! l : Spec (.of v.V) ⟶ M.X,
        l ≫ M.map = v.centre ∧
          Spec.map (CommRingCat.ofHom v.V.subtype) ≫ l = M.generic) ∧
    (∀ c : (v : ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z))) →
          (M : Model Z Z.functionField (Z.fromSpecStalk (genericPoint Z))) → M.X,
      (∀ (v : ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
          (M : Model Z Z.functionField (Z.fromSpecStalk (genericPoint Z))),
        ∃ l : Spec (.of v.V) ⟶ M.X,
        l ≫ M.map = v.centre ∧
          Spec.map (CommRingCat.ofHom v.V.subtype) ≫ l = M.generic ∧
          l (IsLocalRing.closedPoint v.V) = c v M) →
      valuationTopology Z Z.functionField (Z.fromSpecStalk (genericPoint Z)) =
        ⨅ M, TopologicalSpace.induced (fun v ↦ c v M) inferInstance) ∧
    @CompactSpace (ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
      (valuationTopology Z Z.functionField (Z.fromSpecStalk (genericPoint Z))) ∧
    (∀ U : QuasiModel Z Z.functionField (Z.fromSpecStalk (genericPoint Z)),
      @IsOpenEmbedding (ValuationPoint U.X Z.functionField U.generic)
        (ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
        (valuationTopology U.X Z.functionField U.generic)
        (valuationTopology Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
        (ValuationPoint.push U)) ∧
    (∀ v : ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)),
      Nonempty (AffineValuationColimit v (fun _ ↦ True))) ∧
    (∀ (v : ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
        (M : Model Z Z.functionField (Z.fromSpecStalk (genericPoint Z))),
      Nonempty (AffineValuationColimit v (fun N ↦ N.AboveWithin M ⊤))) ∧
    (∀ (v : ValuationPoint Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
        (M : Model Z Z.functionField (Z.fromSpecStalk (genericPoint Z)))
        (l : Spec (.of v.V) ⟶ M.X),
      l ≫ M.map = v.centre →
      Spec.map (CommRingCat.ofHom v.V.subtype) ≫ l = M.generic →
      ∀ W : M.X.Opens, l (IsLocalRing.closedPoint v.V) ∈ W →
        Nonempty (AffineValuationColimit v (fun N ↦ N.AboveWithin M W))) := by
  sorry

end AlgebraicGeometry.RiemannZariski
