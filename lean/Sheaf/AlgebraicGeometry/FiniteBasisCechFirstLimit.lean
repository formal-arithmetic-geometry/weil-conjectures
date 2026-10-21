/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.FiniteIntersectionLimitCompatibility
public import Sheaf.AlgebraicGeometry.CoverCech
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-! # The first finite-cover Čech limit

Source: Stacks Project, Tag 099U (`lemma-affine-vanishing`), first Čech-colimit
calculation, and Tag 099S (`lemma-limit-pullback`)
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit).

The stage families are precisely the coordinate-reindexed presentations over `U`.
Their objects need only be ind-étale over `X`. The maps below are characterized by
restriction on every ordered tuple, including repeated indices. Colimit comparisons
are stated using `colimit.desc`, so their directions and their legs are specified.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The underlying abelian presheaf of the actual module inverse image `ν_X^* F`,
restricted to the affine ind-étale basis. Source: Stacks 099U, first-limit calculation
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
noncomputable def firstLimitClassicalPresheaf (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    X.AffineProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (toProEt X).op ⋙ ((ProEtale.finiteCoefficientComparison X Λ).obj F).val.presheaf

/-- Bundle the simultaneous first-limit stage as an object of the original basis.
Source: Stacks 099U, the family indexed by the product of directed sets
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisStage {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (j : ∀ a, J a) (a : Fin m) : X.AffineProEt :=
  mk (((firstLimitCoordinate D a).obj (op j)).hom ≫ U.hom) (hD a (op (j a)))

/-- The stage covering arrow is its given structure map to `U`.
Source: Stacks 099U, first-limit stage covering
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisArrow {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (j : ∀ a, J a) (a : Fin m) : firstLimitBasisStage U D hD j a ⟶ U :=
  MorphismProperty.Over.homMk ((firstLimitCoordinate D a).obj (op j)).hom rfl trivial

/-- The transition is the coordinate transition of the given inverse system.
Source: Stacks 099U, first-limit directed system
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisTransition {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    {i j : ∀ a, J a} (h : i ⟶ j) (a : Fin m) :
    firstLimitBasisStage U D hD j a ⟶ firstLimitBasisStage U D hD i a :=
  MorphismProperty.Over.homMk ((firstLimitCoordinate D a).map h.op).left
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ U.hom) (Over.w ((firstLimitCoordinate D a).map h.op))))
    trivial

/-- The original member maps to its chosen stage by the supplied presentation cone.
Source: Stacks 099U, first-limit restriction maps
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisProjection {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    (V : Fin m → X.AffineProEt) (f : ∀ a, V a ⟶ U)
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (q : ∀ a, (Functor.const (J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶ D a)
    (j : ∀ a, J a) (a : Fin m) : V a ⟶ firstLimitBasisStage U D hD j a :=
  MorphismProperty.Over.homMk ((q a).app (op (j a))).left
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ U.hom) (Over.w ((q a).app (op (j a)))))).trans
        (MorphismProperty.Over.w (f a))) trivial

/-- The canonical restriction comparisons for the first finite-cover limit are
isomorphisms, both on integer-indexed complexes and in every nonnegative cohomological
degree. `e` only identifies the objects of the diagram with the chosen ordered Čech
complexes. The two coordinate formulas fix its transitions and cocone legs as the
actual restrictions along the unique projection-compatible intersection maps.
Source: Stacks Project, Tags 099U and 099S, first Čech-colimit calculation
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit).

Proof:
1. Use lem-weil-pbc-finite-intersection-limit-compatibility. The product of the
   nonempty directed coordinate sets is small, nonempty and directed. Every ordered
   intersection is the scheme limit of the corresponding affine ind-étale stages,
   with affine transitions and face-compatible projections.
2. Apply lem-weil-pbc-proetale-classical-continuity-sets to the underlying set sheaf
   of F on each intersection. The module comparison uses the same underlying inverse
   image by def-weil-pbc-site-comparison-morphism. Restriction maps are additive.
   The representative and eventual-equality criterion of
   lem-weil-pbc-filtered-colimit-modules-elementwise, for integers, identifies these
   section bijections with the canonical abelian-group colimit maps.
3. For each degree separately the ordered tuple set is finite. Use
   lem-weil-pbc-filtered-colimits-commute-finite-limits to commute its finite product
   with the filtered colimit. No product over all degrees is interchanged.
4. The face-compatible projections give equality of restriction before and after
   deleting any factor. Additivity and the signed finite sum in def-weil-pbc-cover-cech
   give commutation with the differential, for both transitions and cocone legs.
5. Form the diagram C with its specified restrictions. Its cocone is colimiting
   degreewise by step 3, hence in complexes. Extend by zero to negative degrees.
   The unique comparison colimit.desc is consequently an isomorphism.
6. Filtered abelian-group colimits are exact by
   lem-weil-pbc-filtered-colimit-abelian-groups-exact. Apply
   src-weil-homology-preserves-exact-colimits to C and its cocone. Thus every displayed
   cohomology comparison is an isomorphism with the original restriction maps as legs.
   At q=0 there is no incoming differential. No injectivity of F is used. -/
theorem finite_basis_cech_first_limit (X : Scheme.{u}) [IsAffine X]
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.AffineProEt) {m : ℕ} (hm : 0 < m)
    (V : Fin m → X.AffineProEt) (f : ∀ a, V a ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ topology X U)
    (J : Fin m → Type u) [∀ a, Preorder (J a)] [∀ a, Nonempty (J a)]
    [∀ a, IsDirected (J a) (· ≤ ·)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (q : ∀ a, (Functor.const (J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶ D a)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (hstage : ∀ a i, IsAffine ((D a).obj i).left ∧ Etale ((D a).obj i).hom ∧
      LocallyOfFinitePresentation ((D a).obj i).hom ∧ QuasiCompact ((D a).obj i).hom)
    (hlimit : ∀ a, Nonempty (IsLimit ((Over.forget U.left).mapCone
      (Cone.mk (Over.mk (f a).left) (q a)))))
    (htransition : ∀ a (i j : (J a)ᵒᵖ) (h : i ⟶ j), IsAffineHom ((D a).map h).left)
    (hprojection : ∀ a i, IsAffineHom ((q a).app i).left)
    (hstagecover : ∀ j : ∀ a, J a,
      Sieve.ofArrows (fun a ↦ ((D a).obj (op (j a))).left)
        (fun a ↦ ((D a).obj (op (j a))).hom) ∈ etaleTopology U.left)
    (S : SiteCechComplex V f)
    (Sj : ∀ j : ∀ a, J a,
      SiteCechComplex (firstLimitBasisStage U D hD j) (firstLimitBasisArrow U D hD j)) :
    ∃ (C : (∀ a, J a) ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (e : ∀ j, C.obj j ≅ (Sj j).complex (firstLimitClassicalPresheaf X Λ F))
      (ι : C ⟶ (Functor.const (∀ a, J a)).obj
        (S.complex (firstLimitClassicalPresheaf X Λ F))),
      (∀ (i j : ∀ a, J a) (h : i ⟶ j) (p : ℕ)
        (s : (Sj i).cochains (firstLimitClassicalPresheaf X Λ F) p)
        (α : Fin (p + 1) → Fin m) (b : (Sj j).W p α ⟶ (Sj i).W p α),
        (∀ r, b ≫ (Sj i).pr p α r =
          (Sj j).pr p α r ≫ firstLimitBasisTransition U D hD h (α r)) →
        (((e i).inv ≫ C.map h ≫ (e j).hom).f p) s α =
          (firstLimitClassicalPresheaf X Λ F).map b.op (s α)) ∧
      (∀ (j : ∀ a, J a) (p : ℕ)
        (s : (Sj j).cochains (firstLimitClassicalPresheaf X Λ F) p)
        (α : Fin (p + 1) → Fin m) (b : S.W p α ⟶ (Sj j).W p α),
        (∀ r, b ≫ (Sj j).pr p α r =
          S.pr p α r ≫ firstLimitBasisProjection U V f D hD q j (α r)) →
        (((e j).inv ≫ ι.app j).f p) s α =
          (firstLimitClassicalPresheaf X Λ F).map b.op (s α)) ∧
      IsIso (colimit.desc
        (C ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).mapCocone
          (Cocone.mk (S.complex (firstLimitClassicalPresheaf X Λ F)) ι))) ∧
      ∀ q : ℕ, IsIso (colimit.desc
        (C ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q)
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapCocone
          (Cocone.mk (S.complex (firstLimitClassicalPresheaf X Λ F)) ι))) := by
  sorry

end AlgebraicGeometry.Scheme.AffineProEt
