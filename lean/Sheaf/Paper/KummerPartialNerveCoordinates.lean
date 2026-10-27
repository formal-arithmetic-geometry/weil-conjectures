/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.Paper.KummerNerveCoordinates
public import Sheaf.Paper.KummerBarResolution

/-! # Actual successive-root algebra and double-nerve coordinates
Source: direct-image stability proof paragraph (3), agent-expanded successive roots;
exact all-continuous geometric reference WANTED.
(blueprint: def-sfb-kummer-partial-nerve-coordinates).

## Main definitions

* `SuccessiveRoots`: the specified equivalence on coefficients and every named root.
* `DoubleNerve`: actual faces, degeneracies and diagonal coordinates.
* `Environment`: normalized full and successive bar comparisons.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.KummerPartialNerve
open Profinite.CondensedAction

/-- The specified coordinate reordering of the full root deck group.
Source: direct-image proof (3), G_J = G_o times G_i
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
structure DeckSplit (p : ℕ) {A : Type u} (Jo Ji J : Finset A) where
  equiv : ParameterRootDeckGroup p {a : A // a ∈ J} ≃ₜ*
    (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji})
  outer : ∀ g (a : A) (ho : a ∈ Jo) (h : a ∈ J),
    (equiv g).1.toAdd ⟨a, ho⟩ = g.toAdd ⟨a, h⟩
  inner : ∀ g (a : A) (hi : a ∈ Ji) (h : a ∈ J),
    (equiv g).2.toAdd ⟨a, hi⟩ = g.toAdd ⟨a, h⟩

/-- The real inner root algebra, with no chosen substitute for its data.
Source: direct-image proof (3), adjoining inner roots first
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
abbrev InnerAlgebra (p : ℕ) {A : Type u} [Finite A] [DecidableEq A] {R : Type u} [CommRing R]
    (J : Finset A) (t : {a : A // a ∈ J} → R) (Ji : Finset A) :=
  FullParameterRootAlgebra p (fun a : {a : {a : A // a ∈ J} // a.val ∈ Ji} ↦ t a.val)

/-- The real successive root algebra; its outer parameters are the images in the
inner root algebra. Source: direct-image proof (3), disjoint root equations
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
abbrev SuccessiveAlgebra (p : ℕ) {A : Type u} [Finite A] [DecidableEq A] {R : Type u} [CommRing R]
    (J : Finset A) (t : {a : A // a ∈ J} → R) (Ji : Finset A) :=
  FullParameterRootAlgebra p
    (fun a : {a : {a : A // a ∈ J} // a.val ∉ Ji} ↦
      algebraMap R (InnerAlgebra p J t Ji) (t a.val))

/-- The canonical base-coefficient map into the actual successive root algebra.
Source: direct-image proof (3), adjoining the two disjoint root lists
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def successiveCoefficient (p : ℕ) {A : Type u} [Finite A] [DecidableEq A]
    {R : Type u} [CommRing R] (J : Finset A) (t : {a : A // a ∈ J} → R)
    (Ji : Finset A) : R →+* SuccessiveAlgebra p J t Ji :=
  (algebraMap (InnerAlgebra p J t Ji) (SuccessiveAlgebra p J t Ji)).comp
    (algebraMap R (InnerAlgebra p J t Ji))

/-- The specified inner root viewed in the successive algebra.
Source: direct-image proof (3), named inner roots
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def successiveInnerRoot (p : ℕ) {A : Type u} [Finite A] [DecidableEq A]
    {R : Type u} [CommRing R] (J : Finset A) (t : {a : A // a ∈ J} → R)
    (Ji : Finset A) (n : TameRootOrder p) (a : {a : A // a ∈ J}) (h : a.val ∈ Ji) :
    SuccessiveAlgebra p J t Ji :=
  algebraMap (InnerAlgebra p J t Ji) (SuccessiveAlgebra p J t Ji)
    (fullParameterRoot p (fun b : {b : {a : A // a ∈ J} // b.val ∈ Ji} ↦ t b.val)
      n ⟨a, h⟩)

/-- The specified outer root in the successive algebra.
Source: direct-image proof (3), named outer roots
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def successiveOuterRoot (p : ℕ) {A : Type u} [Finite A] [DecidableEq A]
    {R : Type u} [CommRing R] (J : Finset A) (t : {a : A // a ∈ J} → R)
    (Ji : Finset A) (n : TameRootOrder p) (a : {a : A // a ∈ J}) (h : a.val ∉ Ji) :
    SuccessiveAlgebra p J t Ji :=
  fullParameterRoot p
    (fun b : {b : {a : A // a ∈ J} // b.val ∉ Ji} ↦
      algebraMap R (InnerAlgebra p J t Ji) (t b.val)) n ⟨a, h⟩

/-- Canonical successive-root identification, fixed on every named root and every
base coefficient. This also fixes all power transitions.
Source: direct-image proof (3), disjoint root algebra calculation
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
structure SuccessiveRoots (p : ℕ) {A : Type u} [Finite A] [DecidableEq A] {R : Type u} [CommRing R]
    (J : Finset A) (t : {a : A // a ∈ J} → R) (Ji : Finset A) where
  equiv : FullParameterRootAlgebra p t ≃+* SuccessiveAlgebra p J t Ji
  base : equiv.toRingHom.comp (algebraMap R (FullParameterRootAlgebra p t)) =
    successiveCoefficient p J t Ji
  inner : ∀ (n : TameRootOrder p) (a : {a : A // a ∈ J}) (h : a.val ∈ Ji),
    equiv (fullParameterRoot p t n a) = successiveInnerRoot p J t Ji n a h
  outer : ∀ (n : TameRootOrder p) (a : {a : A // a ∈ J}) (h : a.val ∉ Ji),
    equiv (fullParameterRoot p t n a) = successiveOuterRoot p J t Ji n a h

/-- The canonical identification of the nonnegative single complex, extended by
zero, with the ordinary derived degree-zero object.
Source: direct-image proof (3), compatible nonnegative resolutions
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def degreeZeroIso {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 2} C] (M : C) :
    productBarQ.obj ((CochainComplex.single₀ C).obj M) ≅
      (DerivedCategory.singleFunctor C 0).obj M :=
  DerivedCategory.Q.mapIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl)

section Environments
variable (R : CategoryTheory.CondensedBar.Ring.{u})
  (G H : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- A shared normalized full bar and the successive bar. All structural existence
is in the conclusion of the theorem, rather than an assumption on its geometric input.
The two unit normalizations and the comparison equation are those of the existing
ProductBarResolutionComparison; they fix gamma and its augmentation arrow in D(Mod).
Source: direct-image proof (3), ordinary composite inflation adjunction
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
class Environment where
  [abelian : CategoryTheory.CondensedBar.ActionAbelian R (G × H)]
  [productGroth : IsGrothendieckAbelian.{u + 1} (ActionModule R.toMon (G × H))]
  [modulesDerived : HasDerivedCategory.{u + 2} (Modules R.toMon)]
  [outerDerived : HasDerivedCategory.{u + 2} (ActionModule R.toMon G)]
  [productDerived : HasDerivedCategory.{u + 2} (ActionModule R.toMon (G × H))]
  full : CategoryTheory.CondensedBar.Model R (G × H)
  outer : Invariants R.toMon G
  inner : ProductInvariants R.toMon G H
  inflation : trivial (R := R.toMon) (P := G × H) =
    trivial (R := R.toMon) (P := G) ⋙ inflate (R := R.toMon) (ContinuousMonoidHom.fst G H)
  bar : ProductBar R.toMon G H
  comparison : ∀ (M : ActionModule R.toMon (G × H)) (I : InjectiveResolution M),
    ProductBarResolutionComparison bar outer inner full.invariants inflation M I
  naturality : ∀ (M N : ActionModule R.toMon (G × H)) (m : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (f : I.cocomplex ⟶ J.cocomplex),
    I.ι ≫ f = (CochainComplex.single₀ _).map m ≫ J.ι →
    full.invariants.functor.rightDerivedFunctor.map
        (productBarQ.map ((CochainComplex.single₀ _).map m)) ≫
        (comparison N J).diagonalIso.hom =
      (comparison M I).diagonalIso.hom ≫ productBarQ.map (bar.diagonalMap f) ∧
    (inner.functor.rightDerivedFunctor ⋙ outer.functor.rightDerivedFunctor).map
        (productBarQ.map ((CochainComplex.single₀ _).map m)) ≫
        (comparison N J).iteratedIso.hom =
      (comparison M I).iteratedIso.hom ≫ productBarQ.map (bar.iteratedMap f) ∧
    productBarQ.map (bar.diagonalMap f) ≫ (comparison N J).augmentations.comparison inflation =
      (comparison M I).augmentations.comparison inflation ≫
        productBarQ.map (bar.iteratedMap f)

attribute [instance_reducible] Environment.modulesDerived Environment.outerDerived
  Environment.productDerived
attribute [instance] Environment.productGroth Environment.abelian Environment.modulesDerived
  Environment.outerDerived
  Environment.productDerived

/-- The normalized identification of the iterated total with successive invariants.
Its source is the signed inner-first finite total, with the ordinary K-injective
successive invariants as its target.
Source: direct-image proof (3), displayed gamma_F
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def Environment.iteratedInvariantIso [e : Environment R G H] (T : Scheme.{u})
    (M : ActionModule R.toMon (G × H)) (I : InjectiveResolution M) :=
  (CondensedRing.kummerPointPullBig R T).mapIso ((e.comparison M I).iteratedIso.symm ≪≫
    (e.inner.functor.rightDerivedFunctor ⋙ e.outer.functor.rightDerivedFunctor).mapIso
      (degreeZeroIso M))
end Environments

section DoubleNerves
variable (G H : Profinite.{u}) [CommGroup G] [IsTopologicalGroup G]
  [CommGroup H] [IsTopologicalGroup H]

/-- Profinite parameters of the successive geometric nerve.
Source: direct-image proof (3), G_o^a times G_i^b
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def parameters (a b : ℕ) : Profinite.{u} :=
  Profinite.of ((Fin a → G) × (Fin b → H))

/-- Parameter maps for either direction of the successive nerve.
Source: direct-image proof (3), multiplication, deletion and identity insertion
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def parameterMap {a b c d : ℕ} (f : C((Fin c → G), (Fin a → G)))
    (g : C((Fin d → H), (Fin b → H))) : parameters G H c d ⟶ parameters G H a b :=
  CompHausLike.ofHom _ (f.prodMap g)

/-- The operator on root points as well as their labels. The first face moves the
root point by the first group label; other faces have identity label here.
Source: direct-image proof (3), actual two-direction action nerve
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
def nerveOperator {X : Scheme.{u}}
    (a : ProfiniteCoefficientAction X (Profinite.of (G × H)))
    {P Q : Profinite.{u}} (f : Q ⟶ P) (g : C(Q, G × H)) :
    coefficientParameter X Q ⟶ coefficientParameter X P :=
  coefficientActionLift a.act Q g ≫ ((profiniteToProEtOf X).map f).left

/-- The actual double geometric action nerve, specified on the whole profinite
parameter schemes, with its diagonal identified with the actual full Cech nerve.
All four operator equations are equations of scheme maps, before point evaluation.
Source: direct-image proof (3), successive root nerves and diagonal
(blueprint: def-sfb-kummer-partial-nerve-coordinates). -/
structure DoubleNerve {X W : Scheme.{u}}
    (a : ProfiniteCoefficientAction X (Profinite.of (G × H)))
    (v : X ⟶ W) (hv : a.act ≫ v = coefficientParameterProjection _ _ ≫ v) where
  diagram : SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Over W
  coordinates : ∀ n m : ℕ, (diagram.obj (op (.mk n))).obj (op (.mk m)) ≅
    Over.mk (coefficientParameterProjection X (parameters G H n m) ≫ v)
  faceG : ∀ (n m : ℕ) (i : Fin (n + 2)),
    (coordinates (n + 1) m).inv.left ≫
        ((diagram.map (SimplexCategory.δ i).op).app (op (.mk m))).left ≫
        (coordinates n m).hom.left =
      nerveOperator G H a
        (parameterMap G H (productBarFace n i) (ContinuousMap.id _))
        (if i.val = 0 then
          ((ContinuousMap.eval 0).comp ContinuousMap.fst).prodMk (ContinuousMap.const _ 1)
        else ContinuousMap.const _ 1)
  faceH : ∀ (n m : ℕ) (i : Fin (m + 2)),
    (coordinates n (m + 1)).inv.left ≫
        ((diagram.obj (op (.mk n))).map (SimplexCategory.δ i).op).left ≫
        (coordinates n m).hom.left =
      nerveOperator G H a
        (parameterMap G H (ContinuousMap.id _) (productBarFace m i))
        (if i.val = 0 then
          (ContinuousMap.const _ 1).prodMk ((ContinuousMap.eval 0).comp ContinuousMap.snd)
        else ContinuousMap.const _ 1)
  degeneracyG : ∀ (n m : ℕ) (i : Fin (n + 1)),
    (coordinates n m).inv.left ≫
        ((diagram.map (SimplexCategory.σ i).op).app (op (.mk m))).left ≫
        (coordinates (n + 1) m).hom.left =
      nerveOperator G H a
        (parameterMap G H (productBarDegeneracy n i) (ContinuousMap.id _))
        (ContinuousMap.const _ 1)
  degeneracyH : ∀ (n m : ℕ) (i : Fin (m + 1)),
    (coordinates n m).inv.left ≫
        ((diagram.obj (op (.mk n))).map (SimplexCategory.σ i).op).left ≫
        (coordinates n (m + 1)).hom.left =
      nerveOperator G H a
        (parameterMap G H (ContinuousMap.id _) (productBarDegeneracy m i))
        (ContinuousMap.const _ 1)
  diagonal : Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj diagram ≅
    CondensedRing.cechOver v
  diagonal_coordinates : ∀ n : ℕ,
    (coordinates n n).inv.left ≫ (diagonal.hom.app (op (.mk n))).left =
      ((profiniteToProEtOf X).map
        (CompHausLike.ofHom _
          (ContinuousMap.pi (fun i : Fin n ↦
            (((ContinuousMap.eval i : C((Fin n → G), G))).comp ContinuousMap.fst).prodMk
              ((ContinuousMap.eval i : C((Fin n → H), H)).comp ContinuousMap.snd))))).left ≫
        kummerNerveCoordinateMap a v hv n
end DoubleNerves

end AlgebraicGeometry.ProEtale.KummerPartialNerve
