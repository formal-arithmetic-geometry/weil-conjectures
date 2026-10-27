/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidHypersurfaceSlice
import Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.FiniteStability

/-! # A maximal Cohen-Macaulay slice of a scheme groupoid

Source: Stacks Project, Tags 04MZ (lemma-max-slice) and 04MY (situation-slice),
more-groupoids.tex (blueprint: lem-sfb-cm-groupoid-maximal-slice).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine immersed slice has Cohen-Macaulay saturation with identity-fibre dimension
as small as the stabilizer dimension.
Source: Stacks Project, Tags 04MZ and 04MY
(blueprint: lem-sfb-cm-groupoid-maximal-slice).

The equations hs and ht make the groupoid relative to S; the remaining structure maps
are over S by the groupoid laws. Cohen-Macaulayness is flatness together with the
Noetherian depth-equals-dimension condition on every fibre stalk. The finite type point
condition is finite type of its canonical residue-field morphism. The final pullback
is G_u: associating the stabilizer pullback with its fibre gives precisely the pullback
of (s,t) along the diagonal residue-field point. It uses one residue-field factor.
The equations on x identify the point (b,e(u)) in the actual fibre of the saturation.
Since g is an immersion, this point is unique; the residue-field isomorphism identifies
this fibre with the restricted source fibre of Tag 04MY.

Proof (the eleven steps of the node):
1. Write $F_u=s^{-1}(u)$ and $d=\dim_{e(u)}F_u$. At $e(u)$ choose affine source and target
   neighbourhoods with a finite presentation, as in [def-sbc-locally-finite-presentation].
   Applying [lem-trf-affine-fibre-point-dimension] to $s$ and these neighbourhoods gives that $d$
   is a finite nonnegative integer. The same affine calculation, $\kappa(v)\otimes_A
   A[z]/(f)=\kappa(v)[z]/(\bar f)$, at each point of each fibre shows that every fibre of a
   locally finitely presented morphism is locally of finite type over its residue field. Uses:
   def-sbc-locally-finite-presentation, lem-trf-affine-fibre-point-dimension.
2. The finite-type-point characterization gives an affine open $V\subset U$ in which $u$ is
   closed. Thus $\operatorname{Spec}\kappa(u)\to U$ is a closed immersion into $V$ followed by an
   open immersion. Its base change by $t:F_u\to U$ identifies $G_u\to F_u$ as an immersion. By
   [lem-weil-pbc-immersion-base-change-lft] and composition of locally finite type maps, $G_u$ is
   locally of finite type over $\kappa(u)$. On test schemes its arrows are loops at $u$, so the
   groupoid laws give it a group structure. Regard it as its actual representable algebraic space.
   Etale charts are locally finitely presented, hence locally of finite type, so the chartwise
   hypothesis of [lem-sfb-field-groupoid-constant-local-dimension] holds. That node gives
   $\dim_{e(u)}G_u=\sup_{z\in G_u}\dim_zG_u$. The identity atlas and [lem-weil-pbc-dimension-
   supremum-local-dimensions] identify this supremum with the topological dimension $a=\dim G_u$
   used here. Uses: lem-sfb-finite-type-field-point-characterization, def-weil-closed-immersion,
   lem-weil-pbc-immersion-base-change-lft, lem-weil-pbc-proper-fp-permanence, def-a1-groupoid-
   scheme, def-trf-scheme-algebraic-space, def-weil-etale-morphism, lem-sfb-field-groupoid-
   constant-local-dimension, lem-weil-pbc-dimension-supremum-local-dimensions.
3. For completeness the immersion in step 2 implies $a\le d$ without a dimension theorem about
   local rings. Factor it as a closed subspace of an open $O\subset F_u$ containing $e(u)$. In any
   neighbourhood $N$ of $e(u)$ in $F_u$, a chain of irreducible closed subsets of $G_u\cap N$ is a
   chain of closed subsets of $O\cap N$. Hence $\dim(G_u\cap N)\le\dim(O\cap N)\le\dim N$, the
   last inequality being [lem-weil-pbc-open-subspace-dimension-monotone]. Taking a neighbourhood
   $N$ attaining $d$ gives $a=\dim_{e(u)}G_u\le d$ by the definition of local dimension. In
   particular $a$ is also a nonnegative integer, since the identity belongs to $G_u$. Uses: def-
   weil-closed-immersion, def-kun-topological-krull-dimension, def-kun-topological-dimension-at-
   point, lem-weil-pbc-open-subspace-dimension-monotone.
4. We will use the following direct consequence of the cited statements. Arbitrary base change
   preserves a Cohen--Macaulay locally finitely presented morphism: on affine charts finite
   presentation is preserved by tensoring, by [lem-weil-pbc-finite-presentation-base-change-
   composition] and [lem-weil-pbc-fibre-product-affine-spectra]; flatness is preserved by [lem-
   weil-pbc-flat-morphism-base-change]. Each new fibre is the old fibre extended along its
   residue-field map by [lem-weil-pbc-fibre-of-base-change]. The old fibres are locally finite
   type by step 1, so the FIRST paragraph of [lem-pur-cohen-macaulay-field-extension] shows their
   extended local rings are Cohen--Macaulay. This uses no Noetherian hypothesis on either base
   scheme. Uses: lem-weil-pbc-finite-presentation-base-change-composition, lem-weil-pbc-fibre-
   product-affine-spectra, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-fibre-of-base-
   change, lem-pur-cohen-macaulay-field-extension.
5. For any $g:B\to U$ put $H_g=B\times_{g,U,t}R$ and $R_B=H_g\times_{s\operatorname{pr}_R,U,g}B$.
   The source $s_B:R_B\to B$ (last projection) is the base change of
   $h_g=s\operatorname{pr}_R:H_g\to U$; the target is isomorphic to it by
   $(b_0,r,b_1)\mapsto(b_1,i(r),b_0)$. Thus when $h_g$ is Cohen--Macaulay and locally finitely
   presented so are both restricted projections, by step 4. On test schemes loops at $b\in B$ are
   exactly loops at $g(b)$ with the specified object $b$; consequently the restricted stabilizer
   is $B\times_U G$. In particular its fibre at $b$ is $G_{g(b)}\times_{\kappa(g(b))}\kappa(b)$.
   Also $s_B^{-1}(b)=h_g^{-1}(g(b))\times_{\kappa(g(b))}\kappa(b)$ by the fibre-of-base-change
   statement. These identifications send the restricted identity to $(b,e(g(b)))$. Uses: def-pc-
   fibre-product, def-a1-groupoid-scheme, lem-weil-pbc-fibre-of-base-change.
6. Use strong induction on the integer $d$ for all groupoids and finite type points in the
   statement, proving the stated conclusion together with the extra assertion that the two
   restricted projections are Cohen--Macaulay and locally finitely presented. Steps 1--3 apply to
   every such input. If $d=a$, choose any affine open neighbourhood $B$ of $u$, with $b=u$. Its
   inclusion is an immersion and identifies residue fields. Open immersions are locally finitely
   presented: on affine neighbourhoods a principal open is $\operatorname{Spec}A_f$ with
   $A_f=A[z]/(fz-1)$. The source $H_g$ is the open subscheme $t^{-1}(B)$ of $R$, so $h_g$ is the
   restriction of $s$, and its local rings and fibre local rings agree with those of $s$. Hence it
   is Cohen--Macaulay and locally finitely presented. Step 5 proves the extra assertion. Its fibre
   at $u$ is an open neighbourhood of $e(u)$ in $F_u$, so [lem-weil-pbc-dimension-at-point-open-
   subspace] gives the required dimension $d=a$. This includes $d=0$. Uses: lem-weil-pbc-affine-
   opens-basis, def-weil-closed-immersion, def-weil-open-immersion, def-sbc-locally-finite-
   presentation, lem-weil-pbc-dimension-at-point-open-subspace.
7. If $d>a$, apply [lem-sfb-cm-groupoid-hypersurface-slice] to the given groupoid and $u$. It
   supplies an affine $B_0$, a locally finitely presented immersion $g_0:B_0\to U$, and $b_0$ over
   $u$ with the same residue field. Its saturation $h_0$ is Cohen--Macaulay at $(b_0,e(u))$ and
   the restricted source fibre has dimension $d-1$ at its identity. Since $s,t$ are flat and
   locally finitely presented and $g_0$ is locally finitely presented, [lem-sfb-groupoid-cm-locus-
   descent] applies and gives an open $W\subset B_0$ containing $b_0$, with $h_0$ Cohen--Macaulay
   on the entire inverse image of $W$. Uses: lem-sfb-cm-groupoid-hypersurface-slice, lem-sfb-
   groupoid-cm-locus-descent.
8. Choose an affine open $B_1\subset W$ containing $b_0$ and put $b_1=b_0$. The immersion
   $g_1:B_1\to U$ is the composite of this open inclusion and $g_0$, so remains an immersion and
   locally finitely presented, by [lem-weil-pbc-proper-fp-permanence](e), the local presentation
   of an open inclusion from step 6, and [lem-sbc-locally-finite-presentation-composition]. The
   saturation $h_1$ is a source-open restriction of $h_0|_{p^{-1}(W)}$, so remains Cohen--Macaulay
   and locally finitely presented. Step 5 gives Cohen--Macaulay locally finitely presented
   restricted projections. The restricted source fibre is an open neighbourhood of the identity in
   the previous restricted fibre, so still has local dimension $d-1$. Finally $b_1$ is a finite
   type point: choose the affine $V\subset U$ of step 2; the immersion makes $b_1$ closed in
   $g_1^{-1}(V)$, and then in an affine neighbourhood inside this open. The finite-type-point
   characterization applies with the identity residue-field extension. Uses: lem-weil-pbc-affine-
   opens-basis, lem-weil-pbc-proper-fp-permanence, lem-sbc-locally-finite-presentation-
   composition, lem-weil-pbc-dimension-at-point-open-subspace, lem-sfb-finite-type-field-point-
   characterization, def-weil-closed-immersion.
9. The restricted groupoid over $B_1$ and $b_1$ now meets every hypothesis of the induction claim,
   with parameter $d-1<d$. Apply it to obtain an affine $C$, a locally finitely presented
   immersion $j:C\to B_1$, and $c\in C$ over $b_1$ with identical residue field. The saturation
   $h_{C/B_1}$ is Cohen--Macaulay and locally finitely presented; the twice restricted source
   fibre at its identity has dimension equal to the stabilizer fibre of the groupoid over $B_1$ at
   $b_1$. By step 5 and $\kappa(b_1)=\kappa(u)$ that stabilizer fibre is canonically $G_u$. The
   twice restricted projections also satisfy the extra assertion of the induction claim. Uses:
   def-pc-fibre-product, def-a1-groupoid-scheme.
10. Set $g=g_1\circ j:C\to U$. Composition of immersions and of locally finitely presented
   morphisms gives the required type of $g$; its residue-field map at $c$ is the composite of two
   isomorphisms. The two saturation maps $h_1$ and $h_{C/B_1}$ are Cohen--Macaulay and locally
   finitely presented. Applying [lem-sfb-cm-groupoid-double-restriction] gives that
   $h_C=s\operatorname{pr}_R:C\times_{g,U,t}R\to U$ has these properties as well. This application
   requires no global surjectivity for $h_1$. Step 5 gives the extra assertion for the restriction
   directly to $C$. Uses: lem-weil-pbc-proper-fp-permanence, lem-sbc-locally-finite-presentation-
   composition, lem-sfb-cm-groupoid-double-restriction.
11. Associating fibre products identifies the twice restricted arrow scheme with
   $C\times_{g,U,t}R\times_{s,U,g}C$: on test schemes both consist of $(c_0,r,c_1)$ with
   $t(r)=g(c_0)$ and $s(r)=g(c_1)$; the intermediate objects are forced to be $j(c_0),j(c_1)$.
   This isomorphism preserves source, target and identity. By step 5 its source fibre at $c$ is
   $h_C^{-1}(u)\times_{\kappa(u)}\kappa(c)$. The map $\kappa(u)\to\kappa(c)$ is an isomorphism, so
   projection identifies this fibre with $h_C^{-1}(u)$, taking its identity to $x=(c,e(u))$. Step
   9 therefore gives $\dim_x h_C^{-1}(u)=\dim G_u$. Taking $B=C$ and $b=c$ completes the induction
   and the proof. Uses: def-pc-fibre-product, def-a1-groupoid-scheme, lem-weil-pbc-fibre-of-base-
   change.
-/
theorem exists_cm_groupoid_maximal_slice
    {S U R : Scheme.{u}} (p : U ⟶ S) (q : R ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c)
    (hs : s ≫ p = q) (ht : t ≫ p = q)
    [Flat s] [Flat t] [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]
    (hcm : ∀ (f : R ⟶ U), f = s ∨ f = t → ∀ (v : U) (r : f.fiber v),
      IsNoetherianRing ((f.fiber v).presheaf.stalk r) ∧
      (IsLocalRing.depth (R := (f.fiber v).presheaf.stalk r)
        ((f.fiber v).presheaf.stalk r) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber v).presheaf.stalk r))
    (u : U) [LocallyOfFiniteType (U.fromSpecResidueField u)]
    [QuasiCompact (U.fromSpecResidueField u)] :
    ∃ (B : Scheme.{u}) (g : B ⟶ U) (b : B),
      IsAffine B ∧ IsImmersion g ∧ LocallyOfFinitePresentation g ∧
      g b = u ∧ IsIso (g.residueFieldMap b) ∧
      Flat (pullback.snd g t ≫ s) ∧ LocallyOfFinitePresentation (pullback.snd g t ≫ s) ∧
      (∀ (v : U) (y : (pullback.snd g t ≫ s).fiber v),
        IsNoetherianRing (((pullback.snd g t ≫ s).fiber v).presheaf.stalk y) ∧
        (IsLocalRing.depth (R := ((pullback.snd g t ≫ s).fiber v).presheaf.stalk y)
          (((pullback.snd g t ≫ s).fiber v).presheaf.stalk y) : WithBot ℕ∞) =
            ringKrullDim (((pullback.snd g t ≫ s).fiber v).presheaf.stalk y)) ∧
      ∃ x : (pullback.snd g t ≫ s).fiber u,
        pullback.fst g t ((pullback.snd g t ≫ s).fiberι u x) = b ∧
        pullback.snd g t ((pullback.snd g t ≫ s).fiberι u x) = e u ∧
        topologicalKrullDimAt x = topologicalKrullDim
          (pullback (pullback.lift s t (hs.trans ht.symm))
            (pullback.lift (U.fromSpecResidueField u) (U.fromSpecResidueField u) rfl) :
              Scheme.{u}) := by
  sorry

end AlgebraicGeometry
