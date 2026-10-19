/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.Morphisms.GenericFibreCoverDensity
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sober

/-!
# Integral finite models of a finite etale cover after shrinking

Source: Stacks Project, More on Morphisms, Tag 05K0, followed by reduced closures of the
finitely many generic-fibre points and removal of their intersections
(blueprint: lem-per-finite-etale-integral-models-after-shrinking).

The comparison uses the entire pullback of each finite model. Its compatibility with the
canonical second projections specifies an isomorphism over the shrunken open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite etale surjection over a nonempty affine open of an integral Noetherian scheme
is, after shrinking that open, the disjoint union of nonempty opens in integral finite models.

Source: Stacks Project, More on Morphisms, Tag 05K0, with the reduced-closure refinement
specified by the node (blueprint: lem-per-finite-etale-integral-models-after-shrinking).

Proof plan:
1. Put $i:U\hookrightarrow C$ and $f=i\circ g$. The scheme $C$ is quasi-compact by its finite
   affine cover and quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]. The open
   immersion $i$ is quasi-compact because its inverse images in Noetherian affine opens are quasi-
   compact; this is included in [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Thus $i$ has
   finite type by [lem-weil-pbc-qc-open-immersion-finite-type]. A finite algebra is generated as
   an algebra by any finite module generating set, so $g$ has finite type; [lem-sfb-finite-type-
   composition-base-change] gives finite type of $f$. The fibres of $f$ are either fibres of $g$
   or empty, hence finite by [lem-weil-pbc-finite-closed-map-finite-fibres]; [pqf-lem-qf-
   finitefibres] makes $f$ quasi-finite. Finally $g$ is separated by [lem-weil-pbc-finite-closed-
   map-finite-fibres]. Since $i$ is a monomorphism, $T\times_C T=T\times_U T$ by the pullback
   universal property, and the diagonal of $f$ is the closed diagonal of $g$. Therefore $f$ is
   separated.
2. Apply [thm-pqf-zmt-factorization] to $f$. Obtain $j:T\hookrightarrow P$ a quasi-compact open
   immersion and $p:P\to C$ finite with $p\circ j=f$. The open $U$ is integral: its nonempty
   affine opens are nonempty affine opens of $C$, hence have domain coordinate rings by [def-pc-
   integral-scheme]. Therefore $U$ is reduced, and [etale-proposition-etale-reduced] makes $T$
   reduced. Let $Z\hookrightarrow P$ be the scheme-theoretic image of $j$. By [lem-trf-reduced-
   scheme-image] it is the reduced induced closed subscheme on $\overline{j(T)}$, and by [lemma-
   nagata-immersion-open-in-scheme-image] the induced $T\hookrightarrow Z$ is a dense open
   immersion. The morphism $r:Z\to C$ is finite by [lem-weil-pbc-closed-immersion-finite] and
   [lem-weil-pbc-finite-composition].
3. In fact $Z\times_C U$ equals $T$ as a $U$-scheme. To check this, put $P_U=p^{-1}(U)$ and let
   $j_U:T\hookrightarrow P_U$ be the induced open immersion. The map $p_U:P_U\to U$ is finite
   directly from the affine definition of a finite morphism: over every affine open of $U$, its
   ring map is the same finite ring map as for $p$. It is separated by [lem-weil-pbc-finite-
   closed-map-finite-fibres]. Since $p_U\circ j_U=g$ is finite, [lem-weil-pbc-finite-permanence-
   over-separated] makes $j_U$ finite, hence a closed map. Thus $T$ is closed in $P_U$, and so
   also in $Z\cap P_U$. But $T$ is dense in $Z$ and contained in this open subset; consequently
   $Z\cap P_U=T$ topologically. The map $T\hookrightarrow Z\cap P_U$ is an open immersion onto the
   whole space and hence an isomorphism by [def-weil-open-immersion]. The pullback universal
   property identifies this open restriction with $Z\times_C U$.
4. Let $\eta$ be the generic point of $U$, also the generic point of $C$. It exists by [lem-sc-
   scheme-sober], since $U$ is nonempty and integral. Apply [lem-sbc-finite-etale-generic-fibre-
   cover-density] with base $S=U$, smooth map $c=\mathrm{id}_U:U\to U$, and the etale map $g:T\to
   U$. The identity is smooth directly from the lifting definition [def-sbc-smooth-morphisms]: it
   has finite presentation and every prescribed map over $U$ lifts by the structure map. The lemma
   gives density of $T_\eta\to T$. Its function-field generic fibre is the residue-field fibre
   [def-pc-scheme-fibre], since on any nonempty affine domain chart the stalk at the zero prime is
   its field of fractions. The underlying fibre is finite by [lem-weil-pbc-finite-closed-map-
   finite-fibres], discrete by [lem-weil-pbc-etale-fibre-discrete-separable-points], and
   identified with $g^{-1}(\eta)$ by [def-pc-scheme-fibre]. It is nonempty by surjectivity of $g$.
   Write its distinct points as $t_a$ for a nonempty finite index set $A$. Their image is dense in
   $T$, hence in $Z$.
5. For $a\in A$, let $H_a=\overline{\{t_a\}}\subset Z$. It is irreducible by [lem-weil-pbc-
   irreducible-closure]. Give $H_a$ its reduced induced closed subscheme structure
   $Y_a\hookrightarrow Z$ using [lem-weil-pbc-reduced-induced-closed-subscheme]. It is nonempty,
   reduced and irreducible, hence integral by [def-pc-integral-scheme]. The map $q_a:Y_a\to C$ is
   finite by [lem-weil-pbc-closed-immersion-finite] and [lem-weil-pbc-finite-composition]. The
   finite closed union $\bigcup_a H_a$ contains the dense set $\{t_a:a\in A\}$, so it equals $Z$.
   Each $H_a$ meets the fibre over $\eta$ in exactly $t_a$: any such point is a specialization of
   $t_a$, and specialization in the discrete subspace $r^{-1}(\eta)=g^{-1}(\eta)$ forces equality.
   In particular $H_a\cap H_b$ has no point over $\eta$ when $a\ne b$. This argument proves the
   needed component property directly; it assumes no normality of $C$ or disjointness of
   components before shrinking.
6. Set $B=\bigcup_{a\ne b}r(H_a\cap H_b)$. Every intersection is closed in $Z$ and $r$ is finite,
   so [lem-weil-pbc-finite-closed-map-finite-fibres] shows that $B$ is closed in $C$. It avoids
   $\eta$ by the preceding step. Choose an affine open $W$ with $\eta\in W\subseteq U\setminus B$
   using [lem-weil-pbc-affine-opens-basis]. The open restriction $Z_W=r^{-1}(W)$ is the open
   $T\times_U W$ by Step 3. The closed subsets $H_a\cap Z_W$ cover it and are pairwise disjoint.
   Since there are finitely many of them, each is also open, its complement being the union of the
   others. Each contains $t_a$ and is nonempty.
7. Put $V_a=Y_a\times_C W$. Pullback along an open inclusion is the inverse-image open subscheme:
   for any scheme mapping to $Y_a$ with image over $W$, the unique map into this open restriction
   has precisely the pullback universal property [def-pc-fibre-product, def-weil-open-immersion].
   Thus $V_a$ is open in $Y_a$ and nonempty because it contains $t_a$. Its closed immersion into
   $Z_W$ has support $H_a\cap Z_W$. This is a reduced induced closed subscheme: on each affine
   open it is defined by the same radical ideal as $Y_a\hookrightarrow Z$ restricted to that open,
   by the affine-local construction in [lem-weil-pbc-reduced-induced-closed-subscheme]. The open
   subscheme of the reduced scheme $Z_W$ on $H_a\cap Z_W$ is itself reduced and is a closed
   subscheme, since the support is clopen; on affine charts its local rings are localizations of
   the reduced ambient coordinate rings. Uniqueness in [lem-weil-pbc-reduced-induced-closed-
   subscheme] identifies this open subscheme with $V_a$. Hence the $V_a$ are disjoint open
   subschemes covering $Z_W$. Gluing their inclusion maps and the inverse restrictions gives
   mutually inverse maps $\coprod_a V_a\simeq Z_W\simeq T\times_U W$ over $W$, using the scheme
   coproduct universal property [lem-weil-pbc-scheme-coproduct-family]. The pullback universal
   property also identifies the inverse image of $W$ in $\coprod_aY_a$ with $\coprod_a V_a$; the
   comparison is on the entire inverse image.
The equality after the isomorphism is its compatibility with the maps to `W`. Since every
summand is the full pullback, it identifies the whole inverse image of `W` in the models. -/
theorem exists_finite_etale_integral_models_after_shrinking
    (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C]
    (U : C.Opens) (hU : IsAffineOpen U) (hUne : Nonempty U)
    {T : Scheme.{u}} (g : T ⟶ U.toScheme) [IsFinite g] [Etale g] [Surjective g] :
    ∃ W : U.toScheme.Opens, IsAffineOpen W ∧ Nonempty W ∧
      ∃ (A : Type u) (_ : Finite A) (_ : Nonempty A)
        (Y : A → Scheme.{u}) (q : ∀ a : A, Y a ⟶ C),
        (∀ a : A, IsIntegral (Y a) ∧ IsFinite (q a) ∧
          Nonempty ↥(pullback (q a) (W.ι ≫ U.ι)) ∧
          IsOpenImmersion (pullback.fst (q a) (W.ι ≫ U.ι))) ∧
        ∃ e : pullback g W.ι ≅ ∐ (fun a : A ↦ pullback (q a) (W.ι ≫ U.ι)),
          e.hom ≫ Sigma.desc (fun a : A ↦ pullback.snd (q a) (W.ι ≫ U.ι)) =
            pullback.snd g W.ι := by
  sorry

end AlgebraicGeometry
