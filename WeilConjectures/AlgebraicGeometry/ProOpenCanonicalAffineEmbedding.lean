/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSubspace
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import WeilConjectures.Topology.InverseImageStalk
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenIntersection
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Sheaves.Stalks

/-!
# Canonical affine embedding of a pro-open intersection

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`, including the final
assertion about opens (blueprint: lem-sfb-proopen-canonical-affine-embedding).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open LocallyRingedSpace

set_option autoImplicit false

/--
The canonical morphism from the inverse-image locally ringed space on a nonempty
intersection of quasi-compact opens into the spectrum of its sections identifies
that space with an intersection of quasi-compact opens.  Every ambient open inside
the intersection maps to an open subscheme.

Source: Stacks Project, Tag 0API, `lemma-sits-in-functions`.
(blueprint: lem-sfb-proopen-canonical-affine-embedding)

Proof:
1. The hypothesis on $Y$ is precisely the ind-quasi-affine condition of [lem-sfb-ind-quasi-affine-
   base-change]; hence $Y$ is quasi-separated. By [pqf-lem-qs-intersection-qc], each nonempty
   finite intersection of the given $U_i$ is quasi-compact. Replace the family by the set $J$ of
   its distinct nonempty-indexed finite intersections, ordered by reverse inclusion. The poset $J$
   is nonempty and directed (intersection gives an upper bound), its intersection remains $E$, and
   it is small since it is a subset of the set of opens of $Y$. Every member is quasi-affine by
   the original hypothesis. Empty open members are retained. Uses: lem-sfb-ind-quasi-affine-base-
   change, pqf-lem-qs-intersection-qc.

2. For $U\in J$ put $A_U=\Gamma(U,\mathcal O_U)$ and let $r_U:A_U\to C$ be restriction to $E$.
   Apply [lem-sfb-qc-open-intersection-sections-colimit] to the additive sheaf $\mathcal O_Y$ as a
   sheaf of $\mathbb Z$-modules, using the intersection condition from Step 1. Its conclusion
   concerns the inverse image of $\mathcal O_Y$ taken in abelian sheaves; this is the underlying
   abelian sheaf of the ring-valued $\mathcal O_Y|_E$: the abelian adjunction of [def-weil-pbc-
   topological-inverse-image] applied to the underlying additive unit of the ring-valued inverse
   image gives a comparison map of abelian sheaves on $E$, and by [lem-weil-pbc-topological-
   inverse-image-stalk] (in both its abelian and its ring form, with the germ formula) at every
   $e\in E$ both stalks are $\mathcal O_{Y,e}$ compatibly with this map, so it is bijective on
   stalks and hence an isomorphism by [lem-weil-pbc-sets-sheaf-iso-on-stalks]. In particular
   $\Gamma(E,\mathcal O_Y|_E)$ and the restriction maps are the same additive groups and maps in
   both readings. Thus every section on $E$ comes from a stage and equality is detected at a
   common refinement. These descriptions give the ring-colimit property of $C$: for compatible
   ring maps $A_U\to B$, send a section to the image of any representative; eventual equality
   makes this well-defined, and addition, multiplication and the unit are preserved after passing
   to a common stage. Uniqueness follows from representation of every section. By [lem-trf-quasi-
   affine-canonical-affine-embedding], each canonical $a_U:U\to\operatorname{Spec}A_U$ is an open
   immersion and $U$ is quasi-compact. Thus its open image is quasi-compact. Put
   $\pi_U=\operatorname{Spec}r_U$. Naturality in [lem-a1-locally-ringed-space-affine-adjunction]
   gives $\pi_Uj_E=a_U\iota_U$, including the sheaf maps, where $\iota_U:E\to U$ is restriction.
   It also gives the corresponding compatibility for every inclusion of charts. Uses: lem-sfb-qc-
   open-intersection-sections-colimit, lem-trf-quasi-affine-canonical-affine-embedding,
   lem-a1-locally-ringed-space-affine-adjunction, def-weil-pbc-topological-inverse-image, lem-
   weil-pbc-topological-inverse-image-stalk, lem-weil-pbc-sets-sheaf-iso-on-stalks.

3. Let $V_U=\pi_U^{-1}(a_U(U))$. By [lem-sfb-filtered-spectrum-topological-limit] each $V_U$ is
   quasi-compact open, and a point of $\operatorname{Spec}C$ is determined by its compatible
   coordinates in all $\operatorname{Spec}A_U$. The displayed compatibility gives
   $j_E(E)\subseteq\bigcap_UV_U$. Conversely, for $z$ in this intersection let $x_U\in U$ be the
   unique lift of $\pi_U(z)$ through the open embedding $a_U$. If $T\subseteq U$, naturality and
   injectivity of $a_U$ identify $x_T$ and $x_U$ as points of $Y$. A common refinement identifies
   any two lifts. Choosing one chart therefore gives a single $x\in\bigcap_UU=E$. All coordinates
   of $j_E(x)$ equal those of $z$, so $j_E(x)=z$. This also proves injectivity. Its inverse on the
   image is continuous: choose a fixed chart $U$, apply $\pi_U$, then the continuous inverse of
   $a_U$, then include into $Y$ and corestrict to $E$ with its subspace topology. Hence $j_E$ is a
   homeomorphism onto $E'=\bigcap_UV_U$. Uses: lem-sfb-filtered-spectrum-topological-limit, lem-
   trf-quasi-affine-canonical-affine-embedding, lem-a1-locally-ringed-space-affine-adjunction.

4. The inverse-image stalk isomorphism [lem-weil-pbc-topological-inverse-image-stalk] identifies
   $\mathcal O_{E,e}$ with $\mathcal O_{Y,e}$, compatibly with germs; in particular $E$ is locally
   ringed. Fix $e\in E$ and put $\mathfrak p=j_E(e)$ and $\mathfrak p_U=r_U^{-1}(\mathfrak p)$.
   The open immersion $a_U$ (by [def-weil-open-immersion] its sheaf map $a_U^{-1}\mathcal
   O_{\operatorname{Spec}A_U}\to\mathcal O_U$ is an isomorphism, so with [lem-weil-pbc-
   topological-inverse-image-stalk] its stalk map at $e$ is an isomorphism) and [lem-weil-pbc-
   spec-domain-stalks-function-field](1) identify $(A_U)_{\mathfrak p_U}$ with $\mathcal
   O_{U,e}=\mathcal O_{Y,e}$ by the germ map. All transition maps become the identity under these
   identifications. By [lem-weil-pbc-filtered-colimit-localization-at-prime], $C_{\mathfrak p}$ is
   their colimit. A nonempty directed diagram identified with one fixed ring by compatible
   isomorphisms has that ring as its colimit: a map out is fixed by its value on any stage, and a
   common upper stage makes that value independent of the choice. Thus $C_{\mathfrak p}\to\mathcal
   O_{Y,e}$ induced by the germ is an isomorphism. The same spectrum-stalk theorem identifies the
   source with $\mathcal O_{\operatorname{Spec}C,\mathfrak p}$; the commutative sheaf-map squares
   in Step 2 show this is exactly the stalk map of $j_E$. Uses: lem-weil-pbc-topological-inverse-
   image-stalk, lem-weil-pbc-spec-domain-stalks-function-field, lem-weil-pbc-filtered-colimit-
   localization-at-prime, lem-trf-quasi-affine-canonical-affine-embedding, def-weil-open-
   immersion.

5. Factor the sheaf map of $j_E$ through the inverse-image sheaf on $E'$ by the inverse-image
   adjunction [def-weil-pbc-topological-inverse-image], using the homeomorphism of Step 3. The
   unit equation says the factor composed with the canonical subspace inclusion is $j_E$. By [lem-
   weil-pbc-topological-inverse-image-stalk], that inclusion preserves stalks; Step 4 makes the
   factor bijective on stalks. Apply [lem-weil-pbc-sets-sheaf-iso-on-stalks] to the underlying
   sheaves of sets. The inverse is a ring-sheaf map, since a bijective ring homomorphism has a
   ring-homomorphic inverse on every open, compatible with restrictions by uniqueness. This proves
   the required locally ringed-space isomorphism onto $(E',\mathcal
   O_{\operatorname{Spec}C}|_{E'})$. Uses: def-weil-pbc-topological-inverse-image, lem-weil-pbc-
   topological-inverse-image-stalk, lem-weil-pbc-sets-sheaf-iso-on-stalks.

6. Now let $W\subseteq Y$ be any open contained in $E$, with no quasi-compactness assumption. Fix
   $U\in J$. We claim $j_E(W)=\pi_U^{-1}(a_U(W))$. The forward inclusion follows from Step 2. For
   $z$ on the right, let $w\in W$ lift $\pi_U(z)$. For any refinement $T\subseteq U$, $w$ lies in
   $T$ because $W\subseteq E$. Apply [lem-sfb-quasi-affine-open-affinization-square] to
   $T\hookrightarrow U$: the pullback of $a_U|_T:T\to\operatorname{Spec}A_U$ along
   $\operatorname{Spec}A_T\to\operatorname{Spec}A_U$ is $T$, via $a_T$ and its identity map. Since
   the spectrum of the restriction $A_U\to A_T$ sends $\pi_T(z)$ to $\pi_U(z)=a_U(w)$ (Step 2),
   [lem-weil-pbc-scheme-pullback-compatible-point] gives a point of this fibre product whose two
   projections are $w$ and $\pi_T(z)$. The fibre product is $T$ with first projection the identity
   and second projection $a_T$, so that point is $w$ itself and $\pi_T(z)=a_T(w)$. For any other
   chart choose a common refinement with $U$; compatibility then gives the same equation in that
   chart. Coordinate uniqueness from [lem-sfb-filtered-spectrum-topological-limit] gives
   $z=j_E(w)$, proving the claim. Since $a_U$ is an open immersion, $a_U(W)$ is open, so its
   inverse image is open in $\operatorname{Spec}C$. Uses: lem-sfb-quasi-affine-open-affinization-
   square, lem-sfb-filtered-spectrum-topological-limit, lem-trf-quasi-affine-canonical-affine-
   embedding, lem-a1-locally-ringed-space-affine-adjunction, lem-weil-pbc-scheme-pullback-
   compatible-point.

7. Restriction of the locally ringed-space isomorphism of Step 5 to $W$ identifies $W$ with the
   inverse-image ringed subspace on $j_E(W)$. Since this subset is open by Step 6, that subspace
   is its open subscheme. This is exactly the open-immersion criterion in [def-weil-open-
   immersion], and the morphism is $j_E|_W$ by the factorization equation of Step 5. Uses: def-
   weil-open-immersion.
-/
theorem proopen_canonical_affine_embedding
    (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → Scheme.IsQuasiAffine U.toScheme)
    (I : Type v) [Nonempty I] (U : I → Y.Opens)
    (hU : ∀ i : I, IsCompact (U i : Set Y))
    (E : Set Y) (hE : E = ⋂ i : I, (U i : Set Y)) :
    ∃ hlocal : ∀ x : E,
      IsLocalRing ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.stalk x),
    ∃ V : Set (Spec
        ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).Opens,
      V.Nonempty ∧
      (∀ W ∈ V, IsCompact (W : Set (Spec
        ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))))) ∧
      ∃ hF : ∀ x : (⋂₀ (SetLike.coe '' V) : Set (Spec
          ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)))),
        IsLocalRing ((ringedSubspace
          (Spec
            ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
          (⋂₀ (SetLike.coe '' V))).presheaf.stalk x),
      ∃ e : locallyRingedSubspace Y.toLocallyRingedSpace E hlocal ≅
          locallyRingedSubspace
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V)) hF,
        e.hom.toShHom ≫ ringedSubspaceι
            (Spec
              ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤))).toLocallyRingedSpace
            (⋂₀ (SetLike.coe '' V)) =
          ((locallyRingedSubspace Y.toLocallyRingedSpace E hlocal).toΓSpec).toShHom ∧
        (∀ (W : Y.Opens) (hW : (W : Set Y) ⊆ E),
          ∃ l : W.toScheme.toLocallyRingedSpace ⟶
              locallyRingedSubspace Y.toLocallyRingedSpace E hlocal,
            (∀ x : W, l.base x = ⟨x.val, hW x.property⟩) ∧
            (l.toShHom ≫ ringedSubspaceι Y.toLocallyRingedSpace E =
              W.ι.toLRSHom.toShHom) ∧
            IsOpen (Set.range ((l ≫
              (locallyRingedSubspace Y.toLocallyRingedSpace E hlocal).toΓSpec).base)) ∧
            IsOpenImmersion (Scheme.Hom.mk (X := W.toScheme)
              (Y := Spec ((ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)))
              (l ≫
              (locallyRingedSubspace Y.toLocallyRingedSpace E hlocal).toΓSpec))) := by
  sorry

end AlgebraicGeometry
