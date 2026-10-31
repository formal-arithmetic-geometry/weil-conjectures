/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Compactification.Over
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperationPreservation
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparisonSupplement
public import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.ModuleDirectImageOpenPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.CategoryTheory.ExactDerivedComposition
import WeilConjectures.SixFunctors.CompactSupportOpenRefinementPasting
import WeilConjectures.SixFunctors.CompactSupportProperTriangle
import WeilConjectures.SixFunctors.PodCondensedCompactificationSquareTransport
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-! # Concrete geometric-Frobenius compact-support exchange

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius/
prop-weil-operations.proof.md, sentence 2, and sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, paragraphs 1--3.
(blueprint: lem-pod-condensed-automorphism-compact-exchange).

All categories below are ordinary condensed module derived categories, or their full
bounded constructible subcategories. In particular the exceptional adjunction is only
on constructibles. No ambient exceptional adjoint or Weil datum is a hypothesis.


## Main definitions and statement

* `podGeometricBaseChange` and `podGeometricCompactification` give the actual scalar extension.
* `podAutomorphismPullbackInverse` is the canonical inverse-pullback comparison.
* `PodFixedPairAdjunctionNormalization` states the mate, Hom, unit and counit formulas.
* `PodCompactAutomorphismData` packages the concrete recipe and all its coherences.
* `pod_condensed_automorphism_compact_exchange` asserts these properties for geometric Frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u uC uD vC vD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory DerivedCategory.monoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Scalar extension to the fixed algebraic closure, on models and their maps.
Source: geometric-fibre paragraph of the node
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podGeometricBaseChange (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Base change of the chosen model compactification, with its actual two factors.
Source: compactification recipe, proof step 2
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
def podGeometricCompactification (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y} (c : Compactification f.left) :
    Compactification (((podGeometricBaseChange D).map f).left) where
  Z := ((podGeometricBaseChange D).obj c.overObj).left
  i := ((podGeometricBaseChange D).map c.overI).left
  g := ((podGeometricBaseChange D).map c.overG).left
  comm := by
    change ((podGeometricBaseChange D).map f).left =
      (((podGeometricBaseChange D).map c.overI) ≫
        ((podGeometricBaseChange D).map c.overG)).left
    rw [← Functor.map_comp]
    rw [c.overI_overG]
  isOpenImmersion := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    _ c.overI c.isOpenImmersion
  isProper := MorphismProperty.overPullbackMap (P := @IsProper)
    _ c.overG c.isProper

/-- The complete normalization of a constructible adjunction, including the action on every
Hom element and the actual unit and counit. `a` is diagrammatically PF -> FQ; `b` is QR -> RP.
The existential isomorphism is pinned to the mate bijection, not chosen independently.
Source: displayed b and the fixed-pair paragraph, proof steps 10--12
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
def PodFixedPairAdjunctionNormalization
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {F : C ⥤ D} {R : D ⥤ C} {Q : C ⥤ C} {P : D ⥤ D}
    (adj : F ⊣ R) (a : F ⋙ P ≅ Q ⋙ F) : Prop :=
  ∃ b : R ⋙ Q ≅ P ⋙ R,
    (mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans = b.hom ∧
    (∀ L : D, b.hom.app L = adj.unit.app (Q.obj (R.obj L)) ≫
      R.map (a.inv.app (R.obj L)) ≫ R.map (P.map (adj.counit.app L))) ∧
    (∀ (K : C) (θK : Q.obj K ≅ K) (L : D) (θL : P.obj L ≅ L)
      (t : F.obj K ⟶ L),
      adj.homEquiv K L (F.map θK.inv ≫ a.inv.app K ≫ P.map t ≫ θL.hom) =
        θK.inv ≫ Q.map (adj.homEquiv K L t) ≫ b.hom.app L ≫ R.map θL.hom) ∧
    (∀ (K : C) (θK : Q.obj K ≅ K),
      Q.map (adj.unit.app K) ≫ b.hom.app (F.obj K) ≫
          R.map (a.hom.app K ≫ F.map θK.hom) = θK.hom ≫ adj.unit.app K) ∧
    (∀ (L : D) (θL : P.obj L ≅ L),
      P.map (adj.counit.app L) ≫ θL.hom =
        a.hom.app (R.obj L) ≫ F.map (b.hom.app L ≫ R.map θL.hom) ≫ adj.counit.app L)

/-- Quasi-compactness of the geometric morphism, by stability under base change.
Source: geometric-fibre convention of the node
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
instance podGeometricMap_quasiCompact (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y) [QuasiCompact f.left] :
    QuasiCompact (((podGeometricBaseChange D).map f).left) :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f inferInstance

open CompactificationReindexing

/-- The published inverse-pullback comparison, transported to a bundled automorphism's
specified inverse. The inverse-uniqueness equality reconciles the unbundled `inv` in `pInverse`
with the actual inverse scheme map; these are propositionally, not definitionally, equal.
Source: the inverse-square comparison in proof step 9
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
def podAutomorphismPullbackInverse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} (g : T ≅ T) : P Λ g.hom ⋙ P Λ g.inv ≅ 𝟭 (D Λ T) :=
  Functor.isoWhiskerLeft (P Λ g.hom)
    (eqToIso (congrArg (P Λ) (IsIso.eq_inv_of_hom_inv_id g.hom_inv_id))) ≪≫ pInverse Λ g.hom


set_option maxHeartbeats 1600000 in
-- The proposition compares several large native derived-functor endpoints.
/-- The concrete exchange assertion, keeping the actual geometric compactifications,
normalized proper/open exchanges, boundary refinements and constructible adjunctions.
The two geometric squares have fixed maps; their proof witnesses add no choices of exchange.
Every inverse equation uses the published pullback composition/identity comparisons.
Source: all clauses of the node, proof steps 1--12
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
def PodCompactAutomorphismData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y) [QuasiCompact f.left] : Prop :=
  /- The Frobenius realization of the geometric compactification square. -/
  ∃ (square : ∀ (c : Compactification f.left),
    Square (podGeometricCompactification D c) (podGeometricCompactification D c)
      (StrictWeil.modelFrobenius D X).hom (StrictWeil.modelFrobenius D Y).hom),
  /- Its middle map is geometric Frobenius, rather than an arbitrary lift. -/
  ∃ (_middle : ∀ (c : Compactification f.left),
    (square c).middle = (StrictWeil.modelFrobenius D c.overObj).hom),
  /- The inverse-Frobenius realization on the same compactification. -/
  ∃ (inverseSquare : ∀ (c : Compactification f.left),
    Square (podGeometricCompactification D c) (podGeometricCompactification D c)
      (StrictWeil.modelFrobenius D X).inv (StrictWeil.modelFrobenius D Y).inv),
  /- Its middle map is the inverse of the specified geometric Frobenius. -/
  ∃ (_inverseMiddle : ∀ (c : Compactification f.left),
    (inverseSquare c).middle =
      (StrictWeil.modelFrobenius D c.overObj).inv),
  /- Frobenius pullback preserves the full bounded constructible domain on X. -/
  ∃ (source_mem : ∀ (K : BoundedConstructible
      (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)),
    boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)
      ((P Λ (StrictWeil.modelFrobenius D X).hom).obj K.obj)),
  /- Frobenius pullback preserves the full bounded constructible domain on Y. -/
  ∃ (target_mem : ∀ (K : BoundedConstructible
      (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)),
    boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)
      ((P Λ (StrictWeil.modelFrobenius D Y).hom).obj K.obj)),
  /- Compact support restricts to the same full categories. -/
  ∃ (support_mem : ∀ (c : Compactification f.left)
      (K : BoundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)),
    boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)
      ((F Λ (podGeometricCompactification D c)).obj K.obj)),
  /- The exceptional inverse image is a functor only between constructible categories. -/
  ∃ (exceptional : ∀ (_c : Compactification f.left),
    BoundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left) ⥤
      BoundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)),
  /- This is the chosen constructible adjoint pair, with its own actual unit and counit. -/
  ∃ (_adj : ∀ (c : Compactification f.left),
    (boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
      ((boundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
          F Λ (podGeometricCompactification D c)) (support_mem c) ⊣ exceptional c),
  /- PF is naturally isomorphic to FQ on all constructibles, without a Weil datum. -/
  ∃ (exchange : ∀ (c : Compactification f.left),
    (boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
      ((boundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
          F Λ (podGeometricCompactification D c)) (support_mem c) ⋙
      (boundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
        ((boundedConstructible
          (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).ι ⋙
            P Λ (StrictWeil.modelFrobenius D Y).hom) target_mem ≅
    (boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).lift
      ((boundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
          P Λ (StrictWeil.modelFrobenius D X).hom) source_mem ⋙
      (boundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
        ((boundedConstructible
          (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
            F Λ (podGeometricCompactification D c)) (support_mem c)),
  /- The forward map is exactly proper direct-image exchange followed by open exchange. -/
  ∃ (_exchange_hom : ∀ (c : Compactification f.left)
      (K : BoundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)),
    ((exchange c).hom.app K).hom = (squareExchange Λ (square c)).app K.obj),
  /- Inverse square followed by forward square, in canonical pullback coordinates. -/
  ∃ (_inverse_forward : ∀ (c : Compactification f.left)
      (K : BoundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)),
    (P Λ (StrictWeil.modelFrobenius D Y).inv).map
        ((squareExchange Λ (square c)).app K.obj) ≫
      (squareExchange Λ (inverseSquare c)).app
        ((P Λ (StrictWeil.modelFrobenius D X).hom).obj K.obj) ≫
      (F Λ (podGeometricCompactification D c)).map
        ((podAutomorphismPullbackInverse Λ (StrictWeil.modelFrobenius D X)).hom.app K.obj) =
      (podAutomorphismPullbackInverse Λ (StrictWeil.modelFrobenius D Y)).hom.app
        ((F Λ (podGeometricCompactification D c)).obj K.obj)),
  /- Forward square followed by inverse square, giving the other inverse identity. -/
  ∃ (_forward_inverse : ∀ (c : Compactification f.left)
      (K : BoundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)),
    (P Λ (StrictWeil.modelFrobenius D Y).hom).map
        ((squareExchange Λ (inverseSquare c)).app K.obj) ≫
      (squareExchange Λ (square c)).app
        ((P Λ (StrictWeil.modelFrobenius D X).inv).obj K.obj) ≫
      (F Λ (podGeometricCompactification D c)).map
        ((podAutomorphismPullbackInverse Λ (StrictWeil.modelFrobenius D X).symm).hom.app K.obj) =
      (podAutomorphismPullbackInverse Λ (StrictWeil.modelFrobenius D Y).symm).hom.app
        ((F Λ (podGeometricCompactification D c)).obj K.obj)),
  /- Boundary refinements over the finite base give the canonical compatible comparisons.
  The middle-map equality specifies the geometric base change of this very refinement. -/
  ∃ (_refinement : ∀ (c d : Compactification f.left)
      (h₀ : detSfBoundaryCompactification d ⟶ detSfBoundaryCompactification c),
    ∃ h : detSfBoundaryCompactification (podGeometricCompactification D d) ⟶
        detSfBoundaryCompactification (podGeometricCompactification D c),
      h.hom.hom.hom = ((podGeometricBaseChange D).map
        (Over.homMk h₀.hom.hom.hom
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z ↦ z ≫ Y.hom) h₀.hom.hom.hom_g)) :
          d.overObj ⟶ c.overObj)).left ∧
      ∀ K : BoundedConstructible
          (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left),
        (P Λ (StrictWeil.modelFrobenius D Y).hom).map
            (compactificationRefinementComponent Λ h K.obj) ≫
          (squareExchange Λ (square d)).app K.obj =
        (squareExchange Λ (square c)).app K.obj ≫
          compactificationRefinementComponent Λ h
            ((P Λ (StrictWeil.modelFrobenius D X).hom).obj K.obj)),
  /- The mate, all Hom elements, and the original unit and counit are equivariant. -/
  ∀ (c : Compactification f.left)
      (G : BoundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left) ⥤
        BoundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left))
      (adjG : (boundedConstructible
        (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
          ((boundedConstructible
            (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
              F Λ (podGeometricCompactification D c)) (support_mem c) ⊣ G),
    PodFixedPairAdjunctionNormalization adjG (exchange c)

/-- Concrete geometric-Frobenius compact-support exchange, refinement independence,
inverse-square normalization and equivariance of the constructible adjunction.

Source: latest blueprint prop-weil-operations.proof.md, sentence 2, and
lem-fix-weil-operations.proof.md, paragraphs 1--3
(blueprint: lem-pod-condensed-automorphism-compact-exchange).

Natural-language proof (the node's twelve steps):

1. Work throughout in ordinary derived categories of the pulled-back condensed module objects. In
   the preservation statement choose as its chosen compactification exactly $c$, the geometric
   base change of the compactification of $f_0$ selected in step 2. Thus from the outset
   $F=F_c=Rr_*D(j_!)$, and $R$, $\eta$, $\varepsilon$ are the restricted right adjoint, unit and
   counit supplied for this very composite. The preservation statement requires finite
   $\operatorname{cd}_\ell(k)$; since $k=\overline{\mathbf F}_q$ is algebraically closed, sk-lem-
   base-field-cd gives $\operatorname{cd}_\ell(k)=0$. Preservation therefore applies, also when
   $X_0,Y_0$ are not separated. The Frobenius-square lemma applies to every $k_0$-morphism and
   gives the commuting Cartesian scheme square and its inverse. The exact inverse equivalences
   $P_T$ in the condensed Weil-complex definition apply to every $T_0$ (its smooth morphism is
   explicitly only context). They preserve constructibility and Tor intervals. Consequently $P,Q$
   are equivalences on the full constructible categories since there $\Dbc=\Dctf$. These are not
   rationalized completed-module functors.
   Uses: lem-pod-condensed-six-operation-preservation, lem-weil-frobenius-square-cartesian, sk-
   def-sf-weil-complexes, sk-lem-base-field-cd.

2. Choose a compactification $X_0\xrightarrow{j_0}Z_0\xrightarrow{r_0}Y_0$. Nagata applies because
   a finite-type scheme over a field is qcqs; the finite-type-over-Noetherian lemma verifies this
   without separatedness. The compactification-base-change lemma says that the constructed base-
   changed factorization is a compactification; apply it along
   $\operatorname{Spec}k\to\operatorname{Spec}k_0$ to obtain $c=(j,r)$. This is the chosen
   compactification in step 1. Write $H=Lg_Z^*$. The Frobenius-square lemma for $r_0$ and $j_0$
   gives $r g_Z=g_Yr$ and $j g_X=g_Zj$. All three horizontal pullbacks $P,H,Q$ are the exact
   equivalences of the preceding step. These are squares of schemes, so no assertion that $g_T$ is
   a $k$-morphism enters the argument.
   Uses: thm-nagata-compactification, lem-weil-pbc-finite-type-over-noetherian, lem-weil-
   frobenius-square-cartesian, sk-def-sf-weil-complexes, lemma-nagata-compactification-base-
   change.

3. Let $U=Lr^*$ and $V=Rr_*$. The module-derived adjunction supplies $U\dashv V$. The pullback
   composition comparison gives $UP\simeq HU$. Take its mate $e_r:PV\to VH$ under that adjunction,
   using the specified unit-insertion/counit-contraction convention. This is exactly the ordinary
   exchange, by the ambient ringed-exchange formula, in internal-module coordinates. The mate-
   isomorphism lemma applies with intervening functors $P,H$, both equivalences, hence $e_r$ is
   invertible. This proof uses an automorphism square and applies to arbitrary ambient inputs; it
   does not invoke proper base change at field coefficients.
   Uses: det-def-sfb-module-derived-pushpull, prop-sfb-module-left-derived-upper-star-comp, def-
   weil-pbc-adjunction-mate, def-weil-pbc-ambient-ringed-exchange, lem-weil-mate-iso-along-
   equivalences.

4. Put $J=D(j_!)$ and $W=Lj^*$. Extension by zero is exact by the module lower-shriek statement,
   and $j^*$ is additive exact by the module-pullback-exactness statement. Thus both functors meet
   the exact-derived-adjunction hypotheses; localizing their specified open adjunction gives
   $J\dashv W$ with its actual unit and counit. The pullback compositor identifies $WH\simeq QW$.
   Its inverse mate gives $t:JQ\to HJ$. Apply normalized equivalence-square inverse-mate coherence
   (1), with $E_A=Q$, $E_B=H$ and the same open adjunction on each side: $t$ is invertible and
   identifies its units and counits. Thus $o=t^{-1}:HJ\simeq JQ$ is precisely the normalized open
   exchange. For $F_c=VJ$, form $a_c=V(o)\circ(e_r J):PF_c\to F_cQ$. The compactification recipe
   specifies exactly this order of factors. Both factors are natural isomorphisms, so $a_c$ is
   one, on arbitrary inputs and hence on constructibles.
   Uses: det-def-sfb-module-lower-shriek, def-weil-exact-derived-adjunction, prop-sfb-module-left-
   derived-upper-star-comp, lem-sfb-equivalence-square-inverse-mate-coherence, def-sfb-compact-
   support-base-change-maps, det-prop-sfb-module-pullback-exact-main.

5. Record the coherence needed for inverse squares. Write $C_{g,f}:(gf)^*\cong f^*g^*$ for the
   underived module compositor and $c_{g,f}:(gf)_*\cong g_*f_*$ for its right-adjoint comparison.
   The module-direct-image-open-pasting statement gives the associativity equation for $c$ and its
   identity comparisons, including coefficient actions; its coefficient-isomorphism hypothesis is
   supplied by $\alpha$-iso. The definition of $C$ says it is the adjoint conjugate of $c^{-1}$.
   Apply mate-pasting to the two sides of the direct-image associativity equation: their
   conjugates are the two paths from $(hgf)^*$ to $f^*g^*h^*$. Since the mate assignment is a
   bijection these paths are equal. The same argument on the stated direct-image identity
   equations gives both pullback unit equations, with the pullback identity comparison defined as
   the conjugate of the direct-image identity comparison. This is an equation between the
   specified comparisons, not merely existence of isomorphic functors.
   Uses: lem-sfb-module-direct-image-open-pasting, lem-sfb-alpha-iso, def-sfb-module-upper-star-
   comp, lem-weil-pbc-mate-pasting, def-weil-pbc-adjunction-mate.

6. All module pullbacks are additive exact by module-pullback-exactness. Therefore their derived
   functors are the exact termwise descents. Under the normalized exact-derived composition and
   natural-isomorphism factorizations, either derived associativity path, after precomposition by
   the localization on complexes, is the localization of the corresponding termwise path in the
   preceding step: the intermediate factorization isomorphisms cancel in adjacent inverse pairs.
   Those paths agree in every degree. Uniqueness in the exact-derived-natural-isomorphism
   statement now makes the two derived natural isomorphisms equal. The identical cancellation for
   an identity functor proves the two derived unit equations. The derived pullback composition
   statement specifies that its compositor is induced by precisely this underived $C$, so these
   are the compositors used in the exchange. In particular a square comparison written as
   $C_2^{-1}C_1$ pastes with a neighboring square by cancellation of the middle $C$; associativity
   permits reassociation, and an identity outer square reduces by the unit equations to the
   identity.
   Uses: det-prop-sfb-module-pullback-exact-main, lem-sfb-exact-derived-composition, lem-sfb-
   exact-derived-natural-iso, prop-sfb-module-left-derived-upper-star-comp.

7. First establish refinement in literal coordinates. Let $h_0:d_0\to c_0$ be a boundary-
   preserving refinement of the compactifications of $f_0$, and let $h:d\to c$ be its geometric
   base change. The refinement triangles pull back, and the boundary condition pulls back as the
   equality of the inverse-image open subschemes, so $h$ is again a boundary-preserving
   refinement. Write $c',d',h'$ for the literal pullbacks along $g_Y$, and $U=L u^*$ for
   $u:X'=X\times_{Y,g_Y}Y\to X$. Denote the literal exchanges by $B_c:PF_c\to F_{c'}U$ and
   $B_d:PF_d\to F_{d'}U$. Apply open-refinement-pasting with $w=d'$, $h_d=\mathrm{id}$, $h_c=h'$
   and its literal open mates. The required triangle is $\mathrm{id};h'=h'$. Apply $Rp_{c'*}$ to
   its equality; proper-triangle, with $a=h$ and $p=p_c$, combines the direct-image factors.
   Substitution of the specified definition of $\rho$ gives the literal, correctly typed equation
   $$B_d\circ P(\rho_h)=(\rho_{h'}U)\circ B_c.$$ These two pasting statements allow arbitrary
   condensed rings and base maps and do not require density. All refinements here and below are
   base changes of refinements over $k_0$, as are the compactifications chosen by the recipe.
   Uses: lem-sfb-compact-support-open-refinement-pasting, lem-sfb-compact-support-proper-triangle,
   def-sfb-compactification-refinement-component.

8. Now change from literal to Frobenius coordinates using compactification-square-transport. Take
   $e_X=(g_X,f):X\cong X'$ and $e_c=(g_{Z_c},p_c):Z_c\cong Z_c'$ (and $e_d$). These are
   isomorphisms by the Frobenius-square lemma. The realized open is $e_c^{-1}j_c'e_X=j_c$, the
   realized proper map is $p_c'e_c=p_c$, and the horizontal maps are $g_X,g_{Z_c}$. Indeed the two
   projections of each claimed equality agree, so the pullback universal property gives it. The
   realized refinement is $$\widetilde h=e_c^{-1}h'e_d=g_{Z_c}^{-1}h g_{Z_d}.$$ The square lemma
   applies to $h_0$, hence $h g_{Z_d}=g_{Z_c}h$ and $\widetilde h=h$. Without this $k_0$-origin
   the equality would not be justified. The transport lemma identifies the proper and open factors
   with the actual mates of steps 3–4, so $\widetilde B_c=a_c$ and $\widetilde B_d=a_d$. Its
   refinement identity identifies $\rho_{h'}$ with $\rho_h$ under $\chi_c,\chi_d$; its compositor
   identifies $P_{e_X}U$ with $Q$. Conjugating the preceding literal equation by these specified
   comparisons and using their naturality gives $$a_d\circ P(\rho_h)=(\rho_h Q)\circ a_c.$$ This
   proves agreement under the canonical refinement comparisons for the compactifications over
   $k_0$ used in the recipe, including their inverses wherever the canonical comparisons are
   isomorphisms.
   Uses: lem-pod-condensed-compactification-square-transport, lem-weil-frobenius-square-cartesian,
   def-sfb-compactification-refinement-component.

9. Let $\bar P,\bar H,\bar Q$ be inverse-Frobenius pullbacks. For $e_r$ the mate-pasting identity
   identifies the pasted forward and inverse comparisons with the mate of the identity pullback
   square, hence with the identity. For $t$ use the same identity for inverse mates of the open
   adjunction: the inverse-paste has identity restriction, so uniqueness of the mate makes it the
   identity. The two coherence steps above prove that the pasted pullback comparisons reduce to
   the identity: reassociate the compositors, cancel the middle comparison, and use
   $g_T^{-1}g_T=g_Tg_T^{-1}=\mathrm{id}_T$ followed by the unit equations. Thus the identity-mate
   assertion applies to the actual squares. Whisker these two equalities and use naturality of
   $e_r$ to combine the proper and open factors. If $\bar a:\bar P F\to F\bar Q$ is the inverse-
   Frobenius compactification composite, the two resulting equations are $$\bar a_{QK}\circ\bar
   P(a_K)=\mathrm{id}_{FK},\qquad a_{\bar QK}\circ P(\bar a_K)=\mathrm{id}_{FK}.$$ Here the
   sources and targets are identified using $\bar PP\simeq1$, $P\bar P\simeq1$, $\bar QQ\simeq1$,
   $Q\bar Q\simeq1$. In particular $a_K^{-1}$ is $P(\bar a_{QK}):FQK\to PFK$ under these
   identifications. The refinement equation of the preceding step preserves these identities.
   Uses: lem-weil-pbc-mate-pasting, prop-sfb-module-left-derived-upper-star-comp, def-weil-pbc-
   adjunction-mate, sk-def-sf-weil-complexes.

10. Now work only in $\mathcal C_X,\mathcal C_Y$, with $F=F_c$ and $F_c\dashv R$ supplied by
   preservation for our selected $c$, as fixed in step 1. The base-field hypothesis needed by
   preservation is already verified in step 1 using sk-lem-base-field-cd. Its unit and counit are
   the $\eta,\varepsilon$ of the statement, so the $a_c$ just constructed is the $a$ whose inverse
   is being transposed. Substitute $L_1=L_2=F$, $R_1=R_2=R$, $G=Q$, $H=P$, $\alpha=a^{-1}:FQ\to
   PF$ into the mate formula. It gives exactly $$b_L=R(P\varepsilon_L)\circ
   R(a_{RL}^{-1})\circ\eta_{QRL}:QRL\to RPL.$$ The mate-isomorphism lemma applies because $Q$ is
   an equivalence and $P$ is fully faithful. Therefore $b$ is a natural isomorphism on the
   constructible category. No adjunction on the ambient pro-etale category is used.
   Uses: lem-pod-condensed-six-operation-preservation, def-weil-pbc-adjunction-mate, lem-weil-
   mate-iso-along-equivalences, sk-lem-base-field-cd.

11. Apply the fixed-pair adjunction lemma with its left functor $L=F$, right functor $R=R$, and
   its endofunctors $F_{\mathrm{there}}=Q$, $G_{\mathrm{there}}=P$. Its $e$ is $a:PF\simeq FQ$ in
   functional notation and its $b$ is precisely the mate just computed. Thus the structures are
   $\Theta_{FK}=F(\theta_K)a_K$ and $\Theta_{RL}=R(\theta_L)b_L$. They are invertible and natural,
   and the lifted adjunction has exactly the original carrier unit $\eta_K$ and counit
   $\varepsilon_L$. In particular both are morphisms of fixed pairs.
   Uses: lem-sf-fixed-pair-adjunction-lift.

12. For completeness verify equivariance on all Hom elements, beyond restriction to fixed arrows.
   On $\operatorname{Hom}(FK,L)$ let $T(u)=\theta_L P(u)\Theta_{FK}^{-1}$; on
   $\operatorname{Hom}(K,RL)$ let $S(v)=\Theta_{RL}Q(v)\theta_K^{-1}$. Write $A(u)=R(u)\eta_K$ for
   the adjunction transpose. Naturality of $b$ and the mate unit equation
   $b_{FK}Q(\eta_K)=R(a_K^{-1})\eta_{QK}$ give $$\begin{aligned} S(A(u))&=R(\theta_L)b_L
   Q(R(u))Q(\eta_K)\theta_K^{-1}\\ &=R(\theta_L P(u)a_K^{-1})\eta_{QK}\theta_K^{-1}\\ &=R(\theta_L
   P(u)a_K^{-1}F(\theta_K^{-1}))\eta_K=A(T(u)). \end{aligned}$$ The last equality is naturality of
   $\eta$ and $\Theta_{FK}^{-1}=a_K^{-1}F(\theta_K^{-1})$. To verify the mate unit equation
   directly, expand $b_{FK}Q\eta_K$ as
   $RP\varepsilon_{FK}\,R(a_{RFK}^{-1})\,\eta_{QRFK}\,Q\eta_K$. Naturality of $\eta$ replaces its
   last two factors by $RFQ\eta_K\,\eta_{QK}$. Naturality of $a^{-1}$ replaces
   $a_{RFK}^{-1}FQ\eta_K$ by $PF\eta_K\,a_K^{-1}$. The triangle $\varepsilon_{FK}F\eta_K=1$ leaves
   $R(a_K^{-1})\eta_{QK}$, as claimed. Since $A$ is a bijection, its inverse also intertwines
   $S,T$. This is equivariance of the entire constructible Hom bijection.
   Uses: def-weil-pbc-adjunction-mate, lem-sf-fixed-pair-adjunction-lift.
-/
theorem pod_condensed_automorphism_compact_exchange
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (X Y : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] [QuasiCompact f.left] [IsSeparated f.left] :
    Nonempty (Compactification f.left) ∧ PodCompactAutomorphismData Λ D f := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
