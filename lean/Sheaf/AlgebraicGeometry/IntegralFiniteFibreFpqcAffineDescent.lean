/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.IntegralExtensionDimension
import Sheaf.AlgebraicGeometry.FpqcRepresentabilityDescent
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete

/-!
# Integral fpqc descent with finite fibres and affine neighbourhoods

Source: Anantharaman, Schémas en groupes, Propositions 4.1.1 and 4.1.3,
printed pp.54-55 (the scan OCR reads the latter as 4.1.5); Stacks Tags 02KU, 02L0, 02L2.
(blueprint: lem-sfb-integral-finite-fibre-fpqc-affine-descent)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- An fpqc sheaf with a locally finitely presented fpqc model descends to a scheme
with affine neighbourhoods of every finite set if it has a locally Noetherian model
with that property over an integral fpqc cover with finite underlying fibres.
Flatness, separatedness and finite presentation descend as well.

Source: Anantharaman, Propositions 4.1.1 and 4.1.3, pp.54-55; Raynaud,
Critère d'effectivité de descente, Theorem 4.1 and Corollary 3.8; Stacks 02KU, 02L0, 02L2.
(blueprint: lem-sfb-integral-finite-fibre-fpqc-affine-descent)

Proof:
1. Choose representing identifications $h_P\simeq F_{S'}$ and $h_Y\simeq F_T$. On double overlaps
   both pullbacks represent the same restriction of $F$. By [lem-pc-representable-unique], the
   unique comparison respecting these identifications gives descent data on $P$ and $Y$. On triple
   overlaps both composites respect the same identification, which proves the cocycle. The base
   change $T\times_SS'\to T$ is fpqc. Over it, $Y$ is the base change of $P$ and hence locally of
   finite presentation. Descent of that property shows that $Y\to T$ is locally of finite
   presentation. This use of property descent is between existing schemes and makes no
   representability assumption about $F$ on $S$. Dependencies: def-pc-representable-functor, def-
   pd-descent-datum, lem-galois-fpqc-covering-base-change, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-fpqc-descend-locally-finite-presentation, lem-pc-representable-unique.
2. Apply [lem-sfb-integral-descent-finite-point-orbits] to $q$, $Y\to T$ and its canonical datum:
   the cover has finite underlying fibres by hypothesis, and $Y$ is locally Noetherian by
   hypothesis. Thus for every $y\in Y$, the orbit $O_y=r_1(r_0^{-1}(y))$ is a finite subset of
   $Y$. Property (FA) supplies an affine open containing $O_y$. We use finiteness of this image,
   not the generally false assertion that finite underlying fibres of $q$ stay finite after every
   base change. Dependencies: lem-sfb-integral-descent-finite-point-orbits.
3. The preceding orbit neighbourhoods meet precisely the hypothesis of [lem-sfb-integral-descent-
   invariant-quasiaffine-charts]. Its other hypotheses are the original fpqc sheaf $F$, the given
   locally finitely presented model $P$, the integral surjective cover $T\to S$, and the
   representing scheme $Y$. Obtain a covering $(U_i)$ of $P$ by opens whose maps to $S'$ are
   quasi-affine and whose pullbacks agree under the canonical datum. Restrict that datum to each
   open. The equality of inverse-image opens makes inclusion into $P$ compatible with transport;
   the identity and cocycle equations are restrictions of those on $P$. Dependencies: lem-sfb-
   integral-descent-invariant-quasiaffine-charts, def-pd-descent-datum.
4. Each restricted datum is effective by [lem-trf-quasi-affine-fpqc-effective-descent], since $p$
   is fpqc and $U_i\to S'$ is quasi-affine. The opens cover $P$ and their inclusions intertwine
   the canonical transport, exactly as required by [lem-pd-effective-invariant-open-cover]. That
   lemma glues their effective models to a scheme $X\to S$ and an isomorphism $P\simeq
   X\times_SS'$ inducing the canonical datum. This is where the local charts are assembled into
   the descended scheme. Dependencies: lem-trf-quasi-affine-fpqc-effective-descent, lem-pd-
   effective-invariant-open-cover.
5. The cartesian projection $P\to X$ is invariant under its canonical datum. Therefore [lem-pd-
   fpqc-representability-descent] identifies $h_X$ with $F$. In particular $Y\simeq X\times_ST$.
   Descent along $p$ also makes $X\to S$ locally of finite presentation. On each affine
   presentation, a finitely presented algebra is generated by its finitely many displayed
   variables, so this morphism is locally of finite type. Since $S$ is locally Noetherian, [pqf-
   lem-locnoeth-lft] gives that $X$ is locally Noetherian. Dependencies: lem-pd-fpqc-
   representability-descent, lem-weil-pbc-fpqc-descend-locally-finite-presentation, def-sbc-
   locally-finite-presentation, pqf-lem-locnoeth-lft.
6. Let $u:Y\to X$ be the projection. It is integral by base change of $q$ and is an fpqc cover by
   base change, hence surjective. Its underlying fibres are finite for a separate reason. For an
   affine open $W=\operatorname{Spec}A$ of $X$, integrality makes $u^{-1}W=\operatorname{Spec}B$
   an affine open of $Y$; $B$ is Noetherian because $Y$ is locally Noetherian. For $x\in W$
   corresponding to $\mathfrak p\subset A$, the fibre is
   $\operatorname{Spec}(B\otimes_A\kappa(\mathfrak p))$. Its ring is Noetherian by [lem-weil-pbc-
   fibre-ring-noetherian], and integral over the field $\kappa(\mathfrak p)$ by integrality under
   base change. The integral-extension dimension inequality makes its dimension at most zero. The
   zero-dimensional Noetherian scheme lemma now makes its point set finite (also for a zero fibre
   ring). Thus $u$ satisfies the finite-fibre condition without inferring it directly from base-
   change stability of finite underlying fibres. Dependencies: lem-sbc-integral-morphism-base-
   change, lem-galois-fpqc-covering-base-change, def-weil-finite-integral-morphism, pqf-lem-
   affine-open-locnoeth, lem-weil-pbc-fibre-ring-noetherian, lem-weil-pbc-integral-extension-
   dimension, lem-sc-zero-dim-noetherian-finite-discrete.
7. For any finite subset $E\subseteq|X|$, Step 6 makes $E'=u^{-1}(E)$ finite. Property (FA) for
   $Y$ puts $E'$ in an affine open of $Y$. Apply [lem-sfb-integral-finite-fibre-affine-
   neighbourhood-transfer] to $u$ and $E$: $X$ is locally Noetherian by Step 5, and $u$ is
   integral, surjective and has finite underlying fibres by Step 6. Its reverse implication
   supplies an affine open of $X$ containing $E$. This proves property (FA) for $X$. For
   $E=\varnothing$ the empty affine open is allowed. Dependencies: lem-sfb-integral-finite-fibre-
   affine-neighbourhood-transfer.
8. Assume additionally that $Y\to T$ is flat, separated and of finite presentation. Apply fpqc
   descent along the original cover $q:T\to S$ to the now existing scheme morphism $X\to S$. The
   cited flatness, separatedness, local finite-presentation and quasi-compactness descent
   statements give each of those four properties. Separatedness makes the diagonal a closed
   immersion; on an affine target chart its inverse image is a closed subscheme of an affine
   scheme and is affine, hence quasi-compact. Thus $X\to S$ is quasi-separated. By the definition
   of finite presentation (local finite presentation, quasi-compactness and quasi-separatedness),
   it is of finite presentation. All three requested properties therefore descend. Dependencies:
   lem-weil-pbc-fpqc-descend-flat, lem-weil-pbc-fpqc-descend-separated, lem-weil-pbc-fpqc-descend-
   locally-finite-presentation, lem-weil-pbc-fpqc-descend-quasi-compact, def-sbc-locally-finite-
   presentation, def-weil-closed-immersion. -/
theorem exists_representableBy_affine_neighbourhoods_of_integral_fpqc
    {S S' T : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F)
    (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    (P : Over S') [LocallyOfFinitePresentation P.hom]
    (hP : Nonempty (((Over.map p).op ⋙ F).RepresentableBy P))
    (q : T ⟶ S) [IsIntegralHom q] [Surjective q] [Flat q] [QuasiCompact q]
    (hq : ∀ s : S, (q ⁻¹' {s}).Finite)
    (Y : Over T) [IsLocallyNoetherian Y.left]
    (hY : Nonempty (((Over.map q).op ⋙ F).RepresentableBy Y))
    (hFA : ∀ E : Set Y.left, E.Finite →
      ∃ U : Y.left.Opens, IsAffineOpen U ∧ E ⊆ (U : Set Y.left)) :
    ∃ X : Over S, Nonempty (F.RepresentableBy X) ∧
      (∀ E : Set X.left, E.Finite →
        ∃ U : X.left.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X.left)) ∧
      ((Flat Y.hom ∧ IsSeparated Y.hom ∧
          LocallyOfFinitePresentation Y.hom ∧ QuasiCompact Y.hom ∧ QuasiSeparated Y.hom) →
        Flat X.hom ∧ IsSeparated X.hom ∧
          LocallyOfFinitePresentation X.hom ∧ QuasiCompact X.hom ∧ QuasiSeparated X.hom) := by
  sorry

end AlgebraicGeometry
