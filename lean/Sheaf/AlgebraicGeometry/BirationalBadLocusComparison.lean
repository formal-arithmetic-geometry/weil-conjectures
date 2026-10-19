/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.SixFunctors.ProperBaseChangeModules
import Sheaf.Paper.EtaleDerivedDirectImageCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.Morphisms.PointedSectionStageDescent
import Sheaf.TraceFormula.LocalDimensionFormula
import Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.Paper.RingedDerivedSliceLocalization
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.ProperFiniteCoefficientBoundedPreservation

/-!
# Birational comparison along the bad locus

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XIII 3.2.2,
Proposition 3.4.2 and 3.5.1 (blueprint: lem-per-birational-bad-locus-comparison).

The auxiliary predicates spell out the good complement and the finite disjoint bad locus.
The comparison is the adjunction mate of exchange restricted to that closed locus.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Bounded constructibility away from the image of a closed immersion: the open `O`
is exactly the complement, including the case of an empty closed subscheme.
Source: ILO XIII 3.2.2 (blueprint: lem-per-birational-bad-locus-comparison). -/
def boundedConstructibleOff (B : Type (u + 1)) [CommRing B] [Finite B]
    {T X : Scheme.{u}} (i : T ⟶ X) (M : DerivedCategoryModule B X) : Prop :=
  ∃ O : X.Opens, (O : Set X) = (Set.range i)ᶜ ∧
    DerivedCategory.isBoundedConstructible B O.toScheme
      (D(upperStar (ModuleCat.{u + 1} B) O.ι).obj M)

/-- The specified base-change unit followed by restriction to the bad locus.
First exchange for the Cartesian square defining `U'`, then restrict to `T'`, and take
its mate under `q^* ⊣ Rq_*`. This uses no choices of maps or isomorphisms.
Source: ILO XIII 3.3.2 and Proposition 3.4.2
(blueprint: lem-per-birational-bad-locus-comparison). -/
noncomputable def birationalBadLocusComparison (B : Type (u + 1)) [CommRing B]
    {U X X' T T' : Scheme.{u}} (j : U ⟶ X) (p : X' ⟶ X)
    (i : T ⟶ X) (a : T' ⟶ X') (q : T' ⟶ T) (w : CommSq a q p i)
    (K : DerivedCategoryModule B U) :
    D(upperStar (ModuleCat.{u + 1} B) i).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} B) j).obj K) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) q).obj
        (D(upperStar (ModuleCat.{u + 1} B) a).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) (pullback.snd j p)).obj
            (D(upperStar (ModuleCat.{u + 1} B) (pullback.fst j p)).obj K))) :=
  (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) q).homEquiv _ _
    ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) w).hom.app
        ((rightDerivedLowerStar (ModuleCat.{u + 1} B) j).obj K) ≫
      D(upperStar (ModuleCat.{u + 1} B) a).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} B)
          (CommSq.mk (pullback.condition (f := j) (g := p)))).app K))

/-- The conclusion after shrinking, with `T'` represented by a finite scheme coproduct.
The closed immersion makes this the disjoint reduced union of its integral components.
The last clause is a distinguished cone triangle for the canonical comparison above.
Source: ILO XIII 3.2.2, Proposition 3.4.2 and 3.5.1
(blueprint: lem-per-birational-bad-locus-comparison). -/
def BirationalBadLocusConclusion (B : Type (u + 1)) [CommRing B] [Finite B]
    {U X X' T : Scheme.{u}} (j : U ⟶ X) (p : X' ⟶ X) (i : T ⟶ X)
    {n : ℕ} (E : Fin n → Scheme.{u}) (e : ∀ k, E k ⟶ X')
    (K : DerivedCategoryModule B U) : Prop :=
  ∃ (m : ℕ) (D : Fin m → Scheme.{u}) (a : ∀ k, D k ⟶ X')
      (q : ∀ k, D k ⟶ T)
      (w : CommSq (Sigma.desc a) (Sigma.desc q) p i),
    IsClosedImmersion (Sigma.desc a) ∧
    (∀ k, IsIntegral (D k) ∧ IsFinite (q k) ∧ Surjective (q k) ∧
      ∃ (b : Fin n) (s : D k ⟶ E b), s ≫ e b = a k) ∧
    boundedConstructibleOff B (Sigma.desc a)
      ((rightDerivedLowerStar (ModuleCat.{u + 1} B) (pullback.snd j p)).obj
        (D(upperStar (ModuleCat.{u + 1} B) (pullback.fst j p)).obj K)) ∧
    ∃ (C : DerivedCategoryModule B T)
      (f : (rightDerivedLowerStar (ModuleCat.{u + 1} B) (Sigma.desc q)).obj
        (D(upperStar (ModuleCat.{u + 1} B) (Sigma.desc a)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) (pullback.snd j p)).obj
            (D(upperStar (ModuleCat.{u + 1} B) (pullback.fst j p)).obj K))) ⟶ C)
      (g : C ⟶ (D(upperStar (ModuleCat.{u + 1} B) i).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} B) j).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk (birationalBadLocusComparison B j p i (Sigma.desc a)
        (Sigma.desc q) w K) f g ∈ distTriang (DerivedCategoryModule B T) ∧
      DerivedCategory.isBoundedConstructible B T C

/-- Birational comparison along the height-`c` bad locus, assuming codimension-`c`
finiteness simultaneously for all Noetherian quasi-excellent schemes.

Source: ILO XIII 3.2.2, Proposition 3.4.2 and 3.5.1
(blueprint: lem-per-birational-bad-locus-comparison).

Proof plan (the ten steps of the DAG):
1. We work throughout on ordinary small etale sites with constant coefficients $B$. Exact inverse
   image [prop-weil-pbc-inverse-image-modules-exact] and constructible pullback [lem-weil-pbc-
   constructible-etale-set-pullback] show that pullback preserves $D^b_c$: cohomology commutes
   with the exact functor, and its cohomological interval is unchanged. For the finite field $B$,
   the underlying sets of finite modules are finite, so the set-sheaf constructibility criterion
   is equivalent to the module criterion. The long exact cohomology sequence and [thm-
   constructible-serre] show that $D^b_c$ is closed under shifts and distinguished triangles;
   retracts are handled by the same kernel/image criterion. Derived direct image carries triangles
   to triangles by [lem-pc-right-derived-functor-triangulated]. A finite map has exact direct
   image on abelian sheaves by [lemma-weil-pbc-finite-direct-image-exact]; [lem-sbc-higher-direct-
   image-forget-comparison] gives exactness and vanishing also for $B$-module direct images.
   Extension by zero is exact by [lem-weil-pbc-extension-by-zero-exact]. Thus the open-closed
   short exact sequence [lem-weil-pbc-open-closed-short-exact], applied to complexes, gives its
   usual distinguished triangle, with underived closed direct image.
2. Because $p$ is proper, it is finite type and quasi-compact. The stability statement [lem-per-
   quasi-excellent-finite-type-stability] makes $X'$, its open subschemes and its closed
   subschemes Noetherian quasi-excellent; the same applies to closed subschemes and opens of $X$.
   The prime $\ell$ stays invertible under these restrictions and base changes. Step 1 gives
   $K'=p_U^*K\in D^b_c(U',B)$. Apply the assumed induction hypothesis, with its same integer $c$,
   to $(X',j',K')$, obtaining a reduced closed subset $C\subset X'$ all of whose points have
   height at least $c$, with $M:=Rj'_*K'$ bounded constructible on $X'\setminus C$. Open
   restriction of all direct images and units is valid by [lem-weil-pbc-ringed-derived-slice-
   localization].
3. Let $D$ be an irreducible component of $C$, with generic point $y$, and put $s=p(y)$.
   Properness makes $p(D)=\overline{\{s\}}$ closed. Since $p$ is an isomorphism over a dense open,
   its map on function fields is an isomorphism. The inequality of [lem-trf-local-dimension-
   formula], applied to $p$ at $y$, therefore gives $\operatorname{ht}_{X'}(y)+\operatorname{trdeg
   }_{\kappa(s)}\kappa(y)\leq\operatorname{ht}_X(s)$. If $t\in p(D)$, then $s$ generalizes $t$, so
   $\operatorname{ht}_X(s)\leq c$. Together with $\operatorname{ht}_{X'}(y)\geq c$ this forces
   equality throughout and $s=t$: a strict specialization increases height by at least one, by
   appending a prime to a chain. It also forces $\kappa(y)/\kappa(t)$ algebraic. Remove the
   finitely many closed sets $p(D)$ for components not meeting the fibre over $t$. Every remaining
   component consequently maps onto $T$; the factorization through its reduced scheme structure
   follows on affine charts because an equation vanishing at every point of a reduced scheme is
   zero.
4. For each remaining integral component $D\to T$, the generic fibre is integral with algebraic
   function field over $\kappa(t)$. Each nonempty affine chart of that fibre has coordinate domain
   a finitely generated $\kappa(t)$-subalgebra of this algebraic field. Finitely many algebraic
   generators span a finite-dimensional algebra (bound each exponent by a polynomial relation),
   and a finite-dimensional domain over a field is a field: multiplication by a nonzero element is
   an injective, hence surjective, linear endomorphism. Each such chart therefore consists of one
   point. Irreducibility makes these the same point, so the generic fibre has one point. Apply
   [lem-weil-pbc-generic-finite-morphism-open-neighborhood] to each $D\to T$; these maps are
   finite type, quasi-compact and separated, and $T$ is Noetherian. After shrinking $T$ about $t$,
   all are finite surjective. This is achieved by an open restriction of $X$, since every open of
   $T$ is induced from $X$. Distinct components have distinct generic points over $t$, so their
   intersections have closed proper images in $T$. Remove those images as well. With reduced
   structures the surviving closed set is now $T'=\coprod_\alpha T'_\alpha$, a disjoint union of
   integral schemes finite surjective over $T$. The complement of $T'$ is the good complement of
   the restricted $C$ from Step 2. The construction also works when no component survives.
5. For the generic point $y_\alpha$ of each $T'_\alpha$, complete decomposition gives an
   $i_\alpha$ and a $\kappa(y_\alpha)$-point of $E_{i_\alpha}$ above it, hence a section of
   $E_{i_\alpha}\times_{X'}T'_\alpha$ at that generic point. The affine open neighbourhoods of
   $y_\alpha$ form a small cofiltered system of qcqs schemes with affine transitions whose limit
   is $\operatorname{Spec}\mathcal O_{T'_\alpha,y_\alpha}=\operatorname{Spec}\kappa(y_\alpha)$, by
   [lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods]. Its etale target is locally
   finitely presented. Thus [lem-sbc-pointed-section-stage-descent] extends the section to some
   open neighbourhood $V_\alpha$ of $y_\alpha$ in $T'_\alpha$, still over $T'_\alpha$. The closed
   set $T'_\alpha\setminus V_\alpha$ has closed image under its finite map to $T$, missing $t$.
   Remove these finitely many images by an open restriction of $X$. The sections are then defined
   on every surviving $T'_\alpha$. All previous properties persist under this restriction.
6. Choose a dense open $W\subset U$ over which $p$ is an isomorphism, and let $a:Z=U\setminus
   W\hookrightarrow U$ be the reduced closed inclusion. The proper-finiteness statement [lem-per-
   proper-finite-coefficient-bounded-preservation] applies to the proper base change $p_U:U'\to
   U$, with the Noetherian schemes of Step 2. Both $K$ and $Rp_{U*}p_U^*K$ are bounded
   constructible. Complete the unit to a triangle $K\to Rp_{U*}p_U^*K\to C_U\to K[1]$. Step 1
   gives $C_U\in D^b_c(U,B)$. By open localization its restriction to $W$ is zero: there the unit
   is the unit of an isomorphism. Apply the open-closed triangle of Step 1 to $C_U$. Its open-
   extension term is zero, so $C_U\simeq a_*H$ for $H=a^*C_U\in D^b_c(Z,B)$.
7. Let $\bar Z$ be the reduced closure of $Z$ in $X$, $b:\bar Z\hookrightarrow X$ its closed
   inclusion and $v:Z\hookrightarrow\bar Z$ the open inclusion. Since $W$ is dense in the integral
   scheme $X$, every component of $\bar Z$ has positive height in $X$. Apply the induction
   hypothesis on the Noetherian quasi-excellent scheme $\bar Z$ to $(v,H)$. It gives a closed
   $A\subset\bar Z$ with every point of height at least $c$ in $\bar Z$, such that $Rv_*H$ is
   bounded constructible off $A$. Every point of $A$ has height at least $c+1$ in $X$: a chain of
   length $c$ in $\bar Z$ can be prefixed by the generic point of $X$, which is outside $\bar Z$.
   In particular $t\notin A$. As $A$ is closed in $X$, remove $A$ from $X$. After this restriction
   $Rv_*H$ is bounded constructible on all of $\bar Z$. Since $b$ is proper, [lem-per-proper-
   finite-coefficient-bounded-preservation] gives $Rb_*Rv_*H\in D^b_c(X,B)$. The canonical
   composition isomorphisms of [lem-cbc-etale-derived-direct-image-coherence] identify
   $Rj_*a_*H=Rb_*Rv_*H$, since $ja=bv$ and closed direct image is exact (Step 1). Thus
   $i^*Rj_*a_*H\in D^b_c(T,B)$. The case $Z=\varnothing$ has $H=0$ and needs no induction.
8. Apply $i^*Rj_*$ to the triangle in Step 6. The last term is bounded constructible by Step 7.
   Write $F=X'\times_XT$, $k:F\hookrightarrow X'$ and $q:F\to T$. Derived direct-image composition
   [lem-cbc-etale-derived-direct-image-coherence] identifies the middle term before restriction
   with $Rp_*M$. Proper base change [det-properbasechange-modules] for $p$ identifies its
   restriction with $Rq_*k^*M$. This is applicable in $D^+$ because $M$ is bounded below, and
   every cohomology sheaf is killed by $\ell$. It follows that the canonical map $i^*Rj_*K\to
   Rq_*k^*M$ has bounded constructible cone. This is the first part of the specified comparison:
   if $\varepsilon_j$ is the counit for $j^*\dashv Rj_*$, the transpose under $p^*\dashv Rp_*$ of
   $Rj_*\eta_{p_U,K}$, using the composition isomorphisms, is the exchange $p^*Rj_*K\to
   Rj'_*p_U^*K$. Indeed transposing once more under $j'{}^*\dashv Rj'_*$ gives
   $p_U^*\varepsilon_{j,K}$; the other factors cancel by the two adjunction triangle identities.
   Transposing for $q$ after restricting gives exactly the proper base-change map followed by that
   unit.
9. Let $d:T'\hookrightarrow F$ be the closed inclusion and $h:F\setminus T'\hookrightarrow F$ its
   complementary open. Put $L=k^*M$. Its restriction to $F\setminus T'$ is bounded constructible,
   because $M$ is so on $X'\setminus T'$ and pullback preserves this property (Steps 1--4). The
   open-closed triangle of Step 1 gives $h_!h^*L\to L\to d_*d^*L\to h_!h^*L[1]$. By [lem-weil-pbc-
   extension-by-zero-exact], cohomology of the first term is extension by zero of that of $h^*L$.
   Adding the complementary closed stratum with zero module to each finite stratification proves
   constructibility, with the same bounded interval. Therefore $h_!h^*L\in D^b_c(F,B)$. Apply the
   proper-finiteness input [lem-per-proper-finite-coefficient-bounded-preservation] to $q$. Its
   direct image of the first term is bounded constructible, so $Rq_*L\to R(qd)_*d^*L$ has bounded
   constructible cone. The target is $R(p_T)_*i'{}^*M$ by direct-image composition, and the map is
   the direct image of the restriction unit. This argument permits $T'=\varnothing$, in which case
   $d_*d^*L=0$.
10. The arrow of the statement is the composite of the two arrows of Steps 8 and 9, with their
   stated adjunction units and restriction. The octahedral axiom of [def-weil-triangulated-
   category] gives a distinguished triangle from the cone of the first arrow to a cone of the
   composite to the cone of the second arrow. Both outer terms are in $D^b_c(T,B)$; closure under
   distinguished triangles, proved in Step 1 from [thm-constructible-serre], places the middle
   term there too. The finite surjectivity, disjointness, reduced structures and sections were
   obtained in Steps 4 and 5. Only finitely many open restrictions have been made, each containing
   $t$, so their intersection is the required open neighbourhood.
-/
theorem birational_bad_locus_comparison
    (ell : ℕ) [Fact ell.Prime] (B : Type (u + 1)) [Field B] [Finite B] [CharP B ell]
    (c : ℕ) (hc : 1 ≤ c)
    (ih : ∀ (Z : Scheme.{u}) [IsNoetherian Z],
      (∀ V : Z.affineOpens, IsQuasiExcellent Γ(Z, V.1)) →
      (∀ z : Z, IsUnit (ell : Z.presheaf.stalk z)) →
      ∀ (V : Scheme.{u}) (v : V ⟶ Z) [IsOpenImmersion v]
        (L : DerivedCategoryModule B V), DerivedCategory.isBoundedConstructible B V L →
        ∃ O : Z.Opens,
          (∀ z : Z, z ∉ O → (c : WithBot ℕ∞) ≤ ringKrullDim (Z.presheaf.stalk z)) ∧
          DerivedCategory.isBoundedConstructible B O.toScheme
            (D(upperStar (ModuleCat.{u + 1} B) O.ι).obj
              ((rightDerivedLowerStar (ModuleCat.{u + 1} B) v).obj L)))
    {U X X' T : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsIntegral X']
    (hX : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V.1))
    (hinv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (j : U ⟶ X) [IsOpenImmersion j] (hdense : Dense (Set.range j))
    (K : DerivedCategoryModule B U) (hK : DerivedCategory.isBoundedConstructible B U K)
    (i : T ⟶ X) [IsClosedImmersion i] [IsIntegral T]
    (t : T) (ht : IsGenericPoint t (Set.univ : Set T))
    (hheight : ringKrullDim (X.presheaf.stalk (i t)) = (c : WithBot ℕ∞))
    (hgood : boundedConstructibleOff B i
      ((rightDerivedLowerStar (ModuleCat.{u + 1} B) j).obj K))
    (p : X' ⟶ X) [IsProper p]
    (hbir : ∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (p ∣_ V))
    (n : ℕ) (E : Fin n → Scheme.{u}) (e : ∀ k, E k ⟶ X')
    (he : ∀ k, IsSeparated (e k) ∧ LocallyOfFiniteType (e k) ∧
      QuasiCompact (e k) ∧ Etale (e k))
    (hcover : ∀ x' : X', ∃ (k : Fin n) (z : E k),
      e k z = x' ∧ IsIso ((e k).residueFieldMap z)) :
    ∃ W : X.Opens, i t ∈ W ∧
      BirationalBadLocusConclusion B (j ∣_ W) (p ∣_ W) (i ∣_ W)
        (fun k ↦ ((e k) ⁻¹ᵁ (p ⁻¹ᵁ W)).toScheme)
        (fun k ↦ e k ∣_ (p ⁻¹ᵁ W))
        (D(upperStar (ModuleCat.{u + 1} B) (j ⁻¹ᵁ W).ι).obj K) := by
  sorry

end AlgebraicGeometry.Etale
