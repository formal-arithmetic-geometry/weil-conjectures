/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeDerivedInvariants



/-! # RelativeCyclicTotal

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-cyclic-total)

## Main definitions and statements

The primary declaration is `TotalModel`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}
/-- Coordinates specifying the relative two-column total, including its actual maps and
row augmentation. Its data is determined up to coordinate-preserving natural isomorphism.
Source: paragraph (3), steps 7--8
(blueprint: def-sfb-relative-cyclic-total). -/
structure TotalModel where
  functor : CochainComplex (Equivariant A (G × Z.{u})) ℤ ⥤
    CochainComplex (Equivariant A G) ℤ
  coordinates : ∀ N n, (functor.obj N).X n ≅
    (retainResidual A G Z).obj (N.X n) ⊞ (retainResidual A G Z).obj (N.X (n - 1))
  differential : ∀ N n,
    (coordinates N n).inv ≫ (functor.obj N).d n (n + 1) ≫
        (coordinates N (n + 1)).hom =
      biprod.lift
        (biprod.fst ≫ (retainResidual A G Z).map (N.d n (n + 1)))
        (biprod.fst ≫ (generatorEnd (N.X n) - 𝟙 _) ≫
            (retainResidual A G Z).map (eqToHom (congrArg N.X (by omega))) -
          biprod.snd ≫ (retainResidual A G Z).map (N.d (n - 1) ((n + 1) - 1)))
  maps : ∀ {N P} (f : N ⟶ P) n,
    (functor.map f).f n ≫ (coordinates P n).hom =
      (coordinates N n).hom ≫ biprod.map
        ((retainResidual A G Z).map (f.f n)) ((retainResidual A G Z).map (f.f (n - 1)))
  bounded : ∀ N, CochainComplex.plus _ N → CochainComplex.plus _ (functor.obj N)
  shift : functor.CommShift ℤ
  augmentation : (invariants A G Z).functor.mapHomologicalComplex (.up ℤ) ⟶ functor
  augmentation_coordinates : ∀ N n,
    (augmentation.app N).f n ≫ (coordinates N n).hom =
      biprod.lift (invariantInclusion (N.X n)) 0



attribute [instance] TotalModel.shift

/-- Localization of bounded-below complexes in the bounded-below derived category.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def plusQ : CochainComplex.Plus (Equivariant A G) ⥤
    DerivedCategory.Plus (Equivariant A G) :=
  HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh

/-- The explicit localization comparison for bounded-below complexes. Keeping this
comparison named avoids unfolding the bounded-below full-subcategory construction.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def plusQιIso : plusQ A G ⋙ DerivedCategory.Plus.ι ≅
    CochainComplex.Plus.ι (Equivariant A G) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient (Equivariant A G))
      (DerivedCategory.Plus.QhCompιIsoιCompQh (Equivariant A G)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso (Equivariant A G))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι (Equivariant A G))
      (DerivedCategory.quotientCompQhIso (Equivariant A G))

/-- The canonical derived descent: relative ordinary derived invariants on D+.
The comparison states that the explicit cyclic total represents this functor.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def descent : DerivedCategory.Plus (Equivariant A (G × Z.{u})) ⥤
    DerivedCategory.{u + 1} (Equivariant A G) :=
  DerivedCategory.Plus.ι ⋙ derived A G Z

/-- The descent carries the canonical signed shifts.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
instance descentShift : (descent A G).CommShift ℤ :=
  inferInstanceAs ((DerivedCategory.Plus.ι ⋙ derived A G Z).CommShift ℤ)

/-- The canonical descent preserves distinguished triangles.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
instance descentTriangulated : (descent A G).IsTriangulated :=
  inferInstanceAs ((DerivedCategory.Plus.ι ⋙ derived A G Z).IsTriangulated)

/-- Localization of bounded-below complexes carries its canonical shifts.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
instance plusQShift : (plusQ A G).CommShift ℤ :=
  Functor.CommShift.ofComp (plusQιIso A G) ℤ

/-- The explicit cyclic total represents the canonical triangulated descent, with
comparison pinned on EVERY bounded-below complex by theta alpha = Qb.
Source: paragraph (3), steps 7--12
(blueprint: def-sfb-relative-cyclic-total). -/
def HasComparison (K : TotalModel A G) : Prop :=
  ∃ e : CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q ≅
      plusQ A (G × Z) ⋙ descent A G,
    NatTrans.CommShift e.hom ℤ ∧
    (∀ (N : CochainComplex (Equivariant A (G × Z.{u})) ℤ) (s n : ℤ),
      ((K.functor.commShiftIso s).hom.app N).f n ≫
          ((K.functor.obj N).shiftFunctorObjXIso s n (n + s) rfl).hom ≫
          (K.coordinates N (n + s)).hom =
        (K.coordinates ((shiftFunctor _ s).obj N) n).hom ≫
          biprod.map
            ((retainResidual A G Z).map (N.shiftFunctorObjXIso s n (n + s) rfl).hom)
            (s.negOnePow • (retainResidual A G Z).map
              (N.shiftFunctorObjXIso s (n - 1) ((n + s) - 1) (by omega)).hom)) ∧
    (∀ N : CochainComplex.Plus (Equivariant A (G × Z.{u})),
      (unit A G Z) N.obj ≫
          (derived A G Z).map ((plusQιIso A (G × Z)).inv.app N) ≫
          e.inv.app N = DerivedCategory.Q.map (K.augmentation.app N.obj))

/-- The invariant-normalized comparison selected from its universal characterization.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def HasComparison.iso {K : TotalModel A G} (C : HasComparison A G K) :
    CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q ≅
      plusQ A (G × Z) ⋙ descent A G := Classical.choose C

/-- The actual localized cyclic comparison on bounded-below complexes.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def lambda {K : TotalModel A G} (C : HasComparison A G K)
    (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    DerivedCategory.Q.obj (K.functor.obj N.obj) ≅
      (derived A G Z).obj (DerivedCategory.Q.obj N.obj) :=
  C.iso.app N ≪≫
    (derived A G Z).mapIso
      ((plusQιIso A (G × Z)).app N)

/-- A module, viewed as a bounded-below integer-indexed complex.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def single (N : Equivariant A G) : CochainComplex.Plus (Equivariant A G) :=
  ⟨(HomologicalComplex.single _ (.up ℤ) 0).obj N, ⟨0, inferInstance⟩⟩

/-- The specified comparison c = lambda inverse after beta, on a module in degree zero.
Source: paragraph (3) (blueprint: def-sfb-relative-cyclic-total). -/
def cyclicMap {K : TotalModel A G} (C : HasComparison A G K)
    (v : Z.{u} →ₜ* H) (N : Equivariant A (G × H)) :
    (derived A G H).obj ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
      DerivedCategory.Q.obj (K.functor.obj
        (single A (G × Z) ((inflate (productMap (G := G) v)).obj N)).obj) :=
  (beta (A := A) (G := G) v).app ((DerivedCategory.singleFunctor _ 0).obj N) ≫
    (derived A G Z).map
      (((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategorySingleFunctor
        0).hom.app N) ≫
    (lambda A G C (single A (G × Z) ((inflate (productMap (G := G) v)).obj N))).inv




end CategoryTheory.RelativeCyclic
