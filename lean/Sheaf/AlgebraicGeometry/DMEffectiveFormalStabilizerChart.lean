/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.FormalModuliQuotient
public import Sheaf.AlgebraicGeometry.AdicFormalCompletion
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.EtaleCompletedLocalRingIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale

/-! # The effective completed groupoid of a finite-diagonal DM stack

Source: Stacks Project, stacks-geometry.tex, Tag 0DR3, remark-groupoid-defo;
etale.tex, Tag 039M, lemma-characterize-etale-completions, and its following remark
(blueprint: lem-sfb-dm-effective-formal-stabilizer-chart).

Formal schemes are their diagrams of nilpotent thickenings. The relation is specified
by its universal isomorphism and its full, natural functor-of-points description.
Thus its groupoid operations are composition, identity and inverse of actual stack
isomorphisms. The presentation uses local lifts and all arrows, retaining nontrivial
torsors after stackification. The stabilizer is a small model of the actual group
of vertical automorphisms, with a specified multiplicative equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace DMFormalChart

/-- The existing nilpotent-thickening diagram, viewed over the ground scheme.
Index `n` means the positive power `n + 1`.
Source: Stacks 0DR3, completion by infinitesimal neighbourhoods
(blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
def tower {S : Scheme.{u}} (U : Over S) (I : U.left.IdealSheafData) : ℕ ⥤ Over S :=
  (AdicFormalCompletion.mk U.left I).thickenings ⊥ ⋙ Over.map U.hom

/-- The canonical maps of the thickenings to their ambient scheme.
Source: Stacks 0DR3 (blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
def towerι {S : Scheme.{u}} (U : Over S) (I : U.left.IdealSheafData) :
    tower U I ⟶ (Functor.const ℕ).obj U where
  app n := Over.homMk (((AdicFormalCompletion.mk U.left I).thickenings ⊥).obj n).hom
  naturality _ _ a := by
    ext
    exact Over.w (((AdicFormalCompletion.mk U.left I).thickenings ⊥).map a)

/-- Restriction of a vertical isomorphism along a scheme map, without choosing a
cleavage of the fibred category. Source: Stacks 003T and 0DR3
(blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
def restrictIso {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {V U : Over S} (a : V ⟶ U)
    {f g : BasedFunctor (discreteModuli (yoneda.obj U)) F} (η : f ≅ g) :
    moduliChartMap a f ≅ moduliChartMap a g :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft (discreteModuliMap (yoneda.map a)).toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso η))
    (BasedCategory.whiskerLeft (discreteModuliMap (yoneda.map a)) η.hom).isHomLift'

/-- The effective spectrum of the actual completed stalk, over the ground scheme.
Its map is the spectrum of the completion algebra map followed by `fromSpecStalk`.
Source: Stacks 0DR3 (blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
def completedAtlas {S : Scheme.{u}} (U : Over S) (z : U.left) : Over S :=
  Over.mk ((Spec.map (CommRingCat.ofHom
    (algebraMap (U.left.presheaf.stalk z)
      (AdicCompletion (IsLocalRing.maximalIdeal (U.left.presheaf.stalk z))
        (U.left.presheaf.stalk z)))) ≫ U.left.fromSpecStalk z) ≫ U.hom)

/-- The effective morphism to the original atlas.
Source: Stacks 0DR3 (blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
def completedAtlasMap {S : Scheme.{u}} (U : Over S) (z : U.left) :
    completedAtlas U z ⟶ U :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (algebraMap (U.left.presheaf.stalk z)
      (AdicCompletion (IsLocalRing.maximalIdeal (U.left.presheaf.stalk z))
        (U.left.presheaf.stalk z)))) ≫ U.left.fromSpecStalk z)

/-- The extended maximal ideal on the spectrum of the completed local ring.
Source: Stacks 039M and Algebra, 05GG, 05GI
(blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
def completedIdeal {S : Scheme.{u}} (U : Over S) (z : U.left) :
    (completedAtlas U z).left.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (((IsLocalRing.maximalIdeal (U.left.presheaf.stalk z)).map
      (algebraMap (U.left.presheaf.stalk z)
        (AdicCompletion (IsLocalRing.maximalIdeal (U.left.presheaf.stalk z))
          (U.left.presheaf.stalk z)))).map
      (Scheme.ΓSpecIso (.of
        (AdicCompletion (IsLocalRing.maximalIdeal (U.left.presheaf.stalk z))
          (U.left.presheaf.stalk z)))).inv.hom)

/-- All data and clauses of the completed atlas. The universal-arrow clause says
exactly that `R` represents the two-fibre product, with both projections. It determines
identity, inverse and composition uniquely from those in the stack, including on
nonreduced tests. `label` identifies the reduced arrows with the actual stabilizer,
so these operations reduce to its group operations. The natural isomorphisms
`source` and `target` give the completed projections on every thickening. `pieces`
is the disjoint-union decomposition of the entire completed arrow system.

`objects` and `arrows` are the local essentially-surjective and fully-faithful
presentation criteria for stackification. Every arrow is the restriction of `η`;
there is no separately chosen comparison map or formal object. `effectiveComparison`
identifies the formal atlas with the restrictions of the displayed effective map.
Source: Stacks 0DR3 and 039M, finite-diagonal étale specialization
(blueprint: lem-sfb-dm-effective-formal-stabilizer-chart). -/
structure Chart {k : Type u} [Field k] [IsAlgClosed k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (𝟙 (Spec (.of k)))))) F) where
  U : Over (Spec (.of k))
  p : BasedFunctor (discreteModuli (yoneda.obj U)) F
  atlas : ∀ (V : Over (Spec (.of k)))
    (a : BasedFunctor (discreteModuli (yoneda.obj V)) F),
    ∃ (Z : AlgebraicSpace (Spec (.of k))) (q : Z.obj.obj ⟶ yoneda.obj V),
      HasSpaceBaseChange p V a Z q ∧ SpaceMapIsEtale Z V q ∧ SpaceMapIsSurjective Z V q
  u : Over.mk (𝟙 (Spec (.of k))) ⟶ U
  pointIso : moduliChartMap u p ≅ x
  R : Over (Spec (.of k))
  s : R ⟶ U
  t : R ⟶ U
  etale : Etale s.left ∧ Etale t.left
  finite : IsFinite (prod.lift s t).left
  η : moduliChartMap s p ≅ moduliChartMap t p
  universal : ∀ (V : Over (Spec (.of k))) (a b : V ⟶ U),
    ∀ θ : moduliChartMap a p ≅ moduliChartMap b p,
      ∃! r : V ⟶ R, r ≫ s = a ∧ r ≫ t = b ∧ HEq (restrictIso r η) θ
  H : Type u
  [group : Group H]
  stabilizer : H ≃* Aut x
  finiteStabilizer : Finite H
  D : Over (Spec (.of k))
  d : D ⟶ R
  q : D ⟶ Over.mk (𝟙 (Spec (.of k)))
  point : H → (Over.mk (𝟙 (Spec (.of k))) ⟶ D)
  reducedFiber : IsColimit (Cofan.mk D point)
  fiber : IsPullback d q (prod.lift s t) (prod.lift u u)
  label : ∀ h : H, HEq (restrictIso (point h ≫ d) η)
    (pointIso ≪≫ stabilizer h ≪≫ pointIso.symm)
  effectiveComparison :
    tower U u.left.ker ≅
      tower (completedAtlas U (u.left (IsLocalRing.closedPoint k)))
        (completedIdeal U (u.left (IsLocalRing.closedPoint k)))
  effectiveComparison_map :
    effectiveComparison.hom ≫
      towerι (completedAtlas U (u.left (IsLocalRing.closedPoint k)))
        (completedIdeal U (u.left (IsLocalRing.closedPoint k))) ≫
      (Functor.const ℕ).map (completedAtlasMap U (u.left (IsLocalRing.closedPoint k))) =
        towerι U u.left.ker
  source : ∀ h : H, tower R (point h ≫ d).left.ker ≅ tower U u.left.ker
  target : ∀ h : H, tower R (point h ≫ d).left.ker ≅ tower U u.left.ker
  source_map : ∀ h : H,
    (source h).hom ≫ towerι U u.left.ker =
      towerι R (point h ≫ d).left.ker ≫ (Functor.const ℕ).map s
  target_map : ∀ h : H,
    (target h).hom ≫ towerι U u.left.ker =
      towerι R (point h ≫ d).left.ker ≫ (Functor.const ℕ).map t
  piece : ∀ h : H, tower R (point h ≫ d).left.ker ⟶ tower R d.left.ker
  piece_map : ∀ h : H,
    piece h ≫ towerι R d.left.ker = towerι R (point h ≫ d).left.ker
  pieces : ∀ n : ℕ,
    IsColimit (Cofan.mk ((tower R d.left.ker).obj n) (fun h ↦ (piece h).app n))
  mapsIntoCompletion : ∀ (V : Over (Spec (.of k))) (n : ℕ)
    (a : V ⟶ (tower U u.left.ker).obj n),
    ModuliCompletionAt x (moduliChartMap (a ≫ (towerι U u.left.ker).app n) p)
  objects : ∀ (V : Over (Spec (.of k)))
    (a : BasedFunctor (discreteModuli (yoneda.obj V)) F), ModuliCompletionAt x a →
    ∃ C : Sieve V, C ∈ (Scheme.etaleTopology.over (Spec (.of k))) V ∧
      ∀ (W : Over (Spec (.of k))) (b : W ⟶ V), C b →
        ∃ (n : ℕ) (z : W ⟶ (tower U u.left.ker).obj n),
          Nonempty (moduliChartMap (z ≫ (towerι U u.left.ker).app n) p ≅
            moduliChartMap b a)
  arrows : ∀ (V : Over (Spec (.of k))) (n m : ℕ)
    (a : V ⟶ (tower U u.left.ker).obj n) (b : V ⟶ (tower U u.left.ker).obj m),
    ∀ θ : moduliChartMap (a ≫ (towerι U u.left.ker).app n) p ≅
      moduliChartMap (b ≫ (towerι U u.left.ker).app m) p,
      ∃ (N : ℕ) (r : V ⟶ (tower R d.left.ker).obj N),
        (r ≫ (towerι R d.left.ker).app N) ≫ s = a ≫ (towerι U u.left.ker).app n ∧
        (r ≫ (towerι R d.left.ker).app N) ≫ t = b ≫ (towerι U u.left.ker).app m ∧
        HEq (restrictIso (r ≫ (towerι R d.left.ker).app N) η) θ

end DMFormalChart

/-- An effective completed stabilizer chart exists for every rational point of a
finite-type DM stack with finite diagonal over an algebraically closed field.
Source: Stacks 0DR3, remark-groupoid-defo, and 039M with the residue-degree remark
(blueprint: lem-sfb-dm-effective-formal-stabilizer-chart).

Proof (the ten steps of the DAG):
1. Choose a finite-type surjective étale atlas. Its base change by `x` is a nonempty
   étale scheme over `k`. Its separable residue extensions are `k`, giving `u` and
   `pointIso` (def-sfb-finite-stack-scheme-tests and
   lem-weil-pbc-etale-fibre-discrete-separable-points).
2. Finite diagonal represents the relation and its projections. Its fibre at `(u,u)`
   represents the automorphisms of `x`. It is finite and unramified over `k`, hence
   the disjoint union of copies of `Spec k` indexed by that group
   (lem-sfb-dm-isom-space-unramified and
   lem-weil-pbc-unramified-algebra-over-field-product).
3. Finite type over the field gives Noetherian affine neighbourhoods of `u` and
   the arrow points. Their localizations are Noetherian. Completion modulo every
   positive power is the original local quotient, and its extended maximal ideal
   is the maximal ideal (pqf-def-locnoeth; the finite-type, localization,
   completion-mod-power and local-completion-local-ring nodes).
4. The rational points are closed. Every infinitesimal neighbourhood of the finite
   reduced fibre is the disjoint union of its singleton open-and-closed pieces.
   Their stalk rings are the quotients by powers of the corresponding maximal
   ideals; the identifications commute with reduction (039M and 0DR3).
5. Apply lem-trf-etale-completed-local-ring-iso to both projections at each arrow.
   Both completed local maps are isomorphisms, preserving all maximal-ideal powers.
   This gives `source`, `target`, and their ambient-map equations.
6. Restrict the original relation's operations. In each component a source uniquely
   specifies an arrow. Thus the composite of the arrows labelled `g` and `h` has
   label `h*g`, and its target is the composite of their targets. Identity and
   inverse give `1` and inversion. These equations commute with every reduction.
   The universal arrow and `label` retain exactly these operations.
7. The canonical completion map gives `Spec A → T → F`. Pulling back the universal
   arrow to every completed arrow thickening gives compatible isomorphisms of its
   two restrictions. Identity and cocycle equations are inherited from the relation.
8. On a nilpotent test, lift an étale cover trivializing the special-fibre object
   by thickening invariance. Refine by affine opens. The base-changed atlas is an
   étale scheme; successive square-zero lifting uniquely lifts the specified section
   (sbc-lem-thickening-etale-site and
   lem-weil-pbc-flat-unramified-formally-etale).
9. Functions vanishing at `u` map into the nilpotent ideal; nonvanishing functions
   become units. Thus each local lift factors through a finite atlas thickening.
   Isomorphisms are exactly maps into the relation and factor through a finite
   thickening of the fibre. This gives `objects` and `arrows`, with full faithfulness
   supplied by `universal`. Geometric support gives the same criterion locally,
   since the point ideal is finitely generated on the Noetherian atlas.
10. Stack descent glues these local objects and all their arrows. Local essential
    surjectivity and the full isomorphism-sheaf identification give the equivalence
    from the completed groupoid's stackification to the residual-gerbe completion.
    Every construction restricts compatibly in the thickening index. -/
theorem exists_effectiveFormalStabilizerChart
    {k : Type u} [Field k] [IsAlgClosed k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (_hDM : IsDeligneMumfordModuliStack F)
    (_hfin : HasFiniteModuliDiagonal F) (_hft : HasFiniteTypeEtaleModuliAtlas F)
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (𝟙 (Spec (.of k)))))) F) :
    Nonempty (DMFormalChart.Chart F x) := by
  sorry

end CategoryTheory
