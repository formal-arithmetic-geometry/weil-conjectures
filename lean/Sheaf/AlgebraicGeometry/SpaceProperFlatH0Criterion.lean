/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # A field-fibre criterion for universal structure-sheaf pushforward

Source: Stacks Project, Derived Categories of Spaces, Tag 0E6B,
`lemma-proper-flat-h0`, hypothesis (2) and conclusion (a)
(blueprint: lem-sfb-space-proper-flat-h0-criterion).

The fibre hypothesis is only bijectivity on global sections of the canonical
structure map, not an isomorphism of sheaves on the field spectrum. Global sections
of the direct image identify with global functions on the fibre by its chart-limit
universal property. Global functions on the field spectrum identify with the field.
Finite presentation includes quasi-compactness and quasi-compactness of the diagonal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper flat finitely presented morphism whose every field-valued fibre has
only scalar global functions has invertible canonical structure-module map after
every algebraic-space base change, including the original map.
Source: Stacks Project, Tag 0E6B, `lemma-proper-flat-h0`, conclusion (a)
(blueprint: lem-sfb-space-proper-flat-h0-criterion).

A field-valued point includes its structure morphism `a : Spec k ⟶ S` and its
map `b` to `Y`. The projection `enlargedFibreProductFst b f` is the base change
to that point; its source is the actual sheaf fibre product, with factors reversed.
`SheafOfModules.sectionsMap` applies global sections to the uniquely normalized
`moduleStructureMap`. Under the canonical global-section identifications this is
exactly the unital scalar map `k → Γ(X_b, O)`, so bijectivity means the prescribed
ring map is an isomorphism. No arbitrary isomorphism or scalar map is supplied.

Proof:
1. Fix an arbitrary algebraic space $T\to Y$; the choice $T=Y$ includes the first assertion. For
   every etale scheme chart $v:U\to T$, put $Z=X\times_YU$ and $p:Z\to U$. By
   [lem-sfb-space-flat-proper-fp-locality], $p$ is proper, flat and finitely presented. For every
   field-valued $w:\operatorname{Spec}k\to U$, associativity of the sheaf fibre product identifies
   $Z_w$ with $X_{vw}$, including the projections to $\operatorname{Spec}k$, so its scalar map is
   the assumed isomorphism. By [lem-trf-space-etale-module-pushforward-restriction], restriction
   of $(f_T)_*\mathcal O_{X\times_YT}$ to $U$ is $p_*\mathcal O_Z$. This identifies the restricted
   structure map with $p^\sharp$: their projections to every etale chart $(W,a)$ are both
   $s\mapsto a^\sharp(s)$ by [def-sfb-space-module-structure-map]. It remains to prove $p^\sharp$
   invertible for each such scheme $U$.
2. Apply [lem-sfb-proper-flat-space-derived-base-change] to $p$ and $\mathcal F=\mathcal O_Z$.
   This coefficient is quasi-coherent and finitely presented, with its identity rank-one
   presentation, and is flat over $U$ precisely by flatness of $p$. Write
   $A=Rp_{\mathrm{et},*}\mathcal O_Z$, $K=R\epsilon_{U,*}A$, and $a:\mathcal O_U[0]\to K$ for the
   derived scalar unit. The cited statement gives that $K$ is perfect, an isomorphism
   $\epsilon_U^*K\to A$ given by the canonical counit, and arbitrary scheme base change for $K$
   preserving $a$. A perfect complex has quasi-coherent cohomology, so $K\in
   D_{\mathrm{QCoh}}(\mathcal O_U)$.
3. Record the degree-zero normalization, also for every base change of $p$ to a scheme $V$. The
   small ringed sites have enough injectives and K-injective resolutions by
   [prop-pur-kinjective-resolutions-exist]: its monomorphism from $M[0]$ into a degreewise
   injective complex gives an embedding of each module $M$ into its degree-zero injective term.
   The direct image $p_{V,*}$ is additive and left exact, being the right adjoint of tensor
   pullback in [def-trf-space-etale-module-functors]. By [lem-sbc-right-derived-single-zero-unit],
   the canonical augmentation $(p_{V,*}\mathcal O)[0]\to Rp_{V,*}\mathcal O$ induces the standard
   isomorphism $p_{V,*}\mathcal O\simeq H^0(Rp_{V,*}\mathcal O)$. The derived scalar unit is the
   single complex of $p_V^\sharp$ followed by this augmentation. The canonical counit
   $\epsilon_V^*K_V\to Rp_{V,*}\mathcal O$ takes $\epsilon_V^*a_V$ to that unit: this is the
   counit triangle identity for the composite scalar adjunction. Exactness of $\epsilon_V^*$ in
   [lem-sfb-derived-etale-zariski-equivalence] therefore identifies $\epsilon_V^*H^0(a_V)$ with
   the actual map $p_V^\sharp$, not merely with some isomorphism between its source and target.
4. For a point $u\in U$ let $i_u:\operatorname{Spec}\kappa(u)\to U$. By
   [lem-sfb-proper-flat-space-derived-base-change], $Li_u^*(K,a)$ is $(K_{p_u}(\mathcal
   O),a_{p_u})$. Choose a nonnegative injective resolution $\mathcal O_{Z_u}\to I^\bullet$ using
   [lem-weil-pbc-left-exact-injective-resolution-degree-zero]. By [lem-sp-kinjective-computes], it
   is K-injective and computes the unbounded direct image as $p_{u,*}I^\bullet$. This complex has
   zero terms below zero, hence zero negative cohomology. The counit identifies it with
   $\epsilon_{\kappa(u)}^*Li_u^*K$. Since this pullback is exact and faithful by
   [lem-sfb-derived-etale-zariski-equivalence], $H^j(Li_u^*K)=0$ for $j<0$. The small ringed-site
   hypotheses and enough injectives are those established in Step 3.
5. By Step 3 on $\operatorname{Spec}\kappa(u)$, the etale pullback of $H^0(Li_u^*a)$ identifies
   with $p_u^\sharp$. Both sides are quasi-coherent: the target is $H^0$ of the exact etale
   pullback of the perfect object $Li_u^*K$. Apply
   [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence]. Its inverse is restriction to
   Zariski opens, with comparisons the identity on open sections. Thus $H^0(Li_u^*a)$, evaluated
   on the unique nonempty Zariski open of $\operatorname{Spec}\kappa(u)$, is exactly
   $\kappa(u)\to\Gamma(Z_u,\mathcal O_{Z_u})$. The definition
   [def-trf-space-etale-module-functors] computes the right side as compatible functions on etale
   charts, and [def-sfb-space-module-structure-map] computes the arrow by scalar pullback. It is
   an isomorphism by Step 1. A map of modules on this one-point Zariski space is an isomorphism
   when its value there is bijective; hence $H^0(Li_u^*a)$ is an isomorphism.
6. The scheme $U$, the perfect object $K$ and the morphism $a$ now satisfy
   [lem-sc-perfect-degree-zero-fibre-criterion]: Step 4 gives all negative-fibre vanishings and
   Step 5 gives the scalar isomorphism at every residue field. That statement yields
   $H^0(a):\mathcal O_U\to H^0(K)$ invertible. Exact etale pullback preserves its inverse. By the
   normalized comparison of Step 3, this is precisely invertibility of $p^\sharp:\mathcal
   O_{U,\mathrm{et}}\to p_*\mathcal O_Z$.
7. By Step 1, $f_T^\sharp$ is an isomorphism on every etale scheme chart of $T$. These charts
   cover its small etale site. The local inverses agree on overlaps, since two inverses to the
   same map agree; the sheaf gluing axiom therefore glues them to an inverse to $f_T^\sharp$. This
   works for the arbitrary $T\to Y$ fixed in Step 1, including $T=Y$.
-/
theorem isIso_moduleStructureMap_of_proper_flat_field_fibres
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hfibre : ∀ (k : Type u) [Field k] (a : Spec (CommRingCat.of k) ⟶ S)
      (b : schemeSpace (Over.mk a) ⟶ Y),
      Function.Bijective (SheafOfModules.sectionsMap
        (moduleStructureMap (enlargedFibreProductFst b f)))) :
    IsIso (moduleStructureMap f) ∧
      ∀ (T : AlgebraicSpace S) (g : T ⟶ Y),
        IsIso (moduleStructureMap (enlargedFibreProductFst g f)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
