/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitNbhdSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection
public import WeilConjectures.SixFunctors.UpperLowerStar.Stalk

/-!

# The stalks of a pushforward along a finite morphism

For a finite morphism `f : X ⟶ Y` and a geometric point `y : Spec Ω ⟶ Y` with `Ω`
algebraically closed, the stalk of `f_* G` at `y` is the product of the stalks of `G` at the
finitely many geometric points `t` of `X` over `y`:
`(f_* G)_y ≅ ∏_{t ↦ y} G_t` (`AlgebraicGeometry.Etale.lowerStarCompSheafFiberIsoPi`).

The stalk `(f_* G)_y` is the colimit of the sections `G (U ×_Y X)` over the pointed étale
neighbourhoods `(U, u)` of `y`. The split neighbourhoods
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd`) are cofinal among them, and over a split
neighbourhood `U ×_Y X` decomposes into pairwise disjoint clopen pieces indexed by the `t`,
so that `G (U ×_Y X) = ∏_t G (piece_t)`. Finite products commute with the filtered colimit
(`A` satisfies AB5), and the colimit of `G (piece_t)` over the split neighbourhoods is the
stalk `G_t`, the pieces being cofinal among the pointed étale neighbourhoods of `t`
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd.initial_pieceFunctor`).

## Main definitions

- `AlgebraicGeometry.Etale.stalkRestrict`: the map `(f_* G)_y ⟶ G_t` for a geometric point
  `t` of `X` over `y`, restricting a germ at `y` to the point `(u, t)` of `U ×_Y X`.
- `AlgebraicGeometry.Etale.lowerStarCompSheafFiberIsoPi`: the natural isomorphism
  `(f)_*[A] ⋙ (pointSmallEtale y).sheafFiber ≅ ∏ᶜ fun t ↦ (pointSmallEtale t.1).sheafFiber`,
  whose components are the `stalkRestrict`.

## Implementation notes

The map `AlgebraicGeometry.Etale.stalkRestrict` is defined as a `colimit.pre`; what pins it
down is its effect on germs, `AlgebraicGeometry.Etale.toPresheafFiber_stalkRestrict`, and the
resulting uniqueness statement `AlgebraicGeometry.Etale.eq_stalkRestrict`. Identifying it with
the composite `(f_* G)_y ≅ (f^* f_* G)_t ⟶ G_t` of
`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso` and the counit of
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction` would need a germ-level description of
that comparison isomorphism, which is not available yet.

Throughout, *stalk* means the fibre functor
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` of the point
`AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site attached to a geometric
point; the declarations naming the functor-level isomorphisms use `sheafFiber` accordingly.

The formula is stated for an *algebraically* closed `Ω`, whereas the rest of the étale-stalk
API is set up for a separably closed `Ω`: the product is indexed by
`AlgebraicGeometry.GeometricFiber f y`, which is the set-theoretic fibre only over an
algebraically closed field, since `AlgebraicGeometry.GeometricFiber.exists_apply_default_eq`
needs a root of a purely inseparable residue extension in `Ω`. The reduction of a separably
closed geometric point to its algebraic closure is done downstream.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom Scheme.Hom.SplitNbhd

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

section Instances

/-- Colimits over the split neighbourhoods of `y` exist: the category is essentially small
and `A` is cocomplete. -/
instance hasColimitsOfShape_splitNbhd_op : HasColimitsOfShape (SplitNbhd f y)ᵒᵖ A :=
  hasColimitsOfShape_of_essentiallySmall.{u + 1} _ _

/-- Colimits over the split neighbourhoods of `y` are exact: the category is filtered and
finally small, and `A` satisfies AB5. -/
instance hasExactColimitsOfShape_splitNbhd_op :
    HasExactColimitsOfShape (SplitNbhd f y)ᵒᵖ A :=
  hasExactColimitsOfShape_of_final _ (FinallySmall.fromFilteredFinalModel.{u + 1} (SplitNbhd f y)ᵒᵖ)

end Instances

section StalkRestrict

variable (t : GeometricFiber f y) (G : Sheaf X.smallEtaleTopology A)

/-- The restriction of germs at `y` of `f_* G` to germs at a geometric point `t` of `X` over
`y`: a section of `G` over `U ×_Y X` is a section over the pointed étale neighbourhood
`(U ×_Y X, (u, t))` of `t`. -/
def Etale.stalkRestrict :
    (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) ⟶
      (pointSmallEtale t.1).sheafFiber.obj G :=
  colimit.pre ((CategoryOfElements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)
    (baseChangeNbhd f t).op

omit [IsFinite f] in
/-- `stalkRestrict` on the germ of a section over `(U, u)`: it is the germ of the same section
at the pointed étale neighbourhood `(U ×_Y X, (u, t))` of `t`.

```
   (f_* G) U ─toPresheafFiber (U, u)─→ (f_* G)_y
       ‖                                   │
       ‖                                   │ stalkRestrict
       ‖                                   ↓
   G (U ×_Y X) ─toPresheafFiber (U ×_Y X, (u, t))─→ G_t
```
-/
@[reassoc (attr := simp)]
lemma Etale.toPresheafFiber_stalkRestrict (U : Y.Etale) (u : (pointSmallEtale y).fiber.obj U) :
    (pointSmallEtale y).toPresheafFiber U u ((f)_*[A].obj G).obj ≫
        Etale.stalkRestrict A f y t G =
      (pointSmallEtale t.1).toPresheafFiber (f.Etale.obj U)
        ((baseChangeNbhd f t).obj ⟨U, u⟩).2 G.obj :=
  colimit.ι_pre ((CategoryOfElements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)
    (baseChangeNbhd f t).op (op ⟨U, u⟩)

omit [IsFinite f] in
/-- `stalkRestrict` is the unique map `(f_* G)_y ⟶ G_t` sending the germ at `(U, u)` of a
section of `f_* G` to the germ of the same section at `(U ×_Y X, (u, t))`. -/
lemma Etale.eq_stalkRestrict
    (ψ : (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) ⟶
      (pointSmallEtale t.1).sheafFiber.obj G)
    (hψ : ∀ (U : Y.Etale) (u : (pointSmallEtale y).fiber.obj U),
      (pointSmallEtale y).toPresheafFiber U u ((f)_*[A].obj G).obj ≫ ψ =
        (pointSmallEtale t.1).toPresheafFiber (f.Etale.obj U)
          ((baseChangeNbhd f t).obj ⟨U, u⟩).2 G.obj) :
    ψ = Etale.stalkRestrict A f y t G := by
  apply (pointSmallEtale y).presheafFiber_hom_ext (P := ((f)_*[A].obj G).obj)
  intro U u
  rw [hψ, Etale.toPresheafFiber_stalkRestrict]

omit [IsFinite f] in
/-- `stalkRestrict` is natural in the sheaf:

```
   (f_* G)_y ──stalkRestrict──→ G_t
       │                         │
       │ (f_* φ)_y               │ φ_t
       ↓                         ↓
   (f_* G')_y ─stalkRestrict──→ G'_t
```
-/
@[reassoc]
lemma Etale.stalkRestrict_naturality {G G' : Sheaf X.smallEtaleTopology A} (φ : G ⟶ G') :
    Etale.stalkRestrict A f y t G ≫ (pointSmallEtale t.1).sheafFiber.map φ =
      (pointSmallEtale y).sheafFiber.map ((f)_*[A].map φ) ≫ Etale.stalkRestrict A f y t G' := by
  apply (pointSmallEtale y).presheafFiber_hom_ext (P := ((f)_*[A].obj G).obj)
  intro U u
  rw [GrothendieckTopology.Point.sheafFiber_map, GrothendieckTopology.Point.sheafFiber_map,
    ← Category.assoc, ← Category.assoc, Etale.toPresheafFiber_stalkRestrict,
    GrothendieckTopology.Point.toPresheafFiber_naturality,
    GrothendieckTopology.Point.toPresheafFiber_naturality, Category.assoc,
    Etale.toPresheafFiber_stalkRestrict]
  -- `f_* φ` on sections over `U` is `φ` on sections over `U ×_Y X`
  rfl

end StalkRestrict

section StalkFormula

variable (G : Sheaf X.smallEtaleTopology A)

/-- The comparison of the colimit of the sections of `G` over `U ×_Y X`, for `U` running over
the split neighbourhoods of `y`, with the stalk of `f_* G` at `y`. -/
def Etale.colimitSectionsIsoStalk :
    colimit (sectionsFunctor f y G) ≅ (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) :=
  Functor.Final.colimitIso (forget f y).op
    ((CategoryOfElements.π (pointSmallEtale y).fiber).op ⋙ ((f)_*[A].obj G).obj)

@[reassoc (attr := simp)]
lemma Etale.ι_colimitSectionsIsoStalk_hom (s : (SplitNbhd f y)ᵒᵖ) :
    colimit.ι (sectionsFunctor f y G) s ≫ (Etale.colimitSectionsIsoStalk A f y G).hom =
      (pointSmallEtale y).toPresheafFiber s.unop.obj.1 s.unop.obj.2 ((f)_*[A].obj G).obj :=
  Functor.Final.ι_colimitIso_hom _ _ _

/-- The comparison of the colimit of the sections of `G` over the `t`-th pieces of the split
neighbourhoods of `y` with the stalk of `G` at `t`. -/
def Etale.colimitPieceSectionsIsoStalk (t : GeometricFiber f y) :
    colimit (pieceSectionsFunctor f y G t) ≅ (pointSmallEtale t.1).sheafFiber.obj G :=
  Functor.Final.colimitIso (pieceFunctor t).op
    ((CategoryOfElements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)

@[reassoc (attr := simp)]
lemma Etale.ι_colimitPieceSectionsIsoStalk_hom (t : GeometricFiber f y)
    (s : (SplitNbhd f y)ᵒᵖ) :
    colimit.ι (pieceSectionsFunctor f y G t) s ≫
        (Etale.colimitPieceSectionsIsoStalk A f y G t).hom =
      (pointSmallEtale t.1).toPresheafFiber (s.unop.pieceObj t) (s.unop.piecePt t) G.obj :=
  Functor.Final.ι_colimitIso_hom _ _ _

/-- The components `stalkRestrict` assemble, through the split neighbourhoods, to the
composite of the product decomposition of the sections and the commutation of the colimit
with finite products:

```
   colim_s G (U_s ×_Y X) ──────≅──────→ (f_* G)_y
            │                                │
            │ colim (sectionsIsoPi)          │ Pi.lift stalkRestrict
            ↓                                ↓
   colim_s ∏_t G (piece_t s) ───≅────→ ∏_t G_t
```
-/
lemma Etale.colimitSectionsIsoStalk_hom_comp_piLift_stalkRestrict :
    (Etale.colimitSectionsIsoStalk A f y G).hom ≫
        Pi.lift (fun t ↦ Etale.stalkRestrict A f y t G) =
      colim.map (sectionsIsoPi f y G).hom ≫
        (PreservesProduct.iso colim (pieceSectionsFunctor f y G)).hom ≫
        Limits.Pi.map fun t ↦ (Etale.colimitPieceSectionsIsoStalk A f y G t).hom := by
  apply colimit.hom_ext
  intro s
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.lift_π, Limits.Pi.map_π, PreservesProduct.iso_hom, colim_map]
  rw [Etale.ι_colimitSectionsIsoStalk_hom_assoc, Etale.toPresheafFiber_stalkRestrict,
    piComparison_comp_π_assoc, ι_colimMap_assoc, colim_map, ι_colimMap_assoc, sectionsIsoPi_hom,
    ← NatTrans.comp_app_assoc, Pi.lift_π, Etale.ι_colimitPieceSectionsIsoStalk_hom]
  exact (colimit.w ((CategoryOfElements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj)
    (CategoryOfElements.homMk ⟨s.unop.pieceObj t, s.unop.piecePt t⟩
      ((baseChangeNbhd f t).obj s.unop.obj) (s.unop.pieceIncl t)
      (CategoryTheory.Over.OverMorphism.ext (s.unop.piecePt_comp_pieceIncl t))).op).symm

/-- The stalk of `f_* G` at `y` is the product of the stalks of `G` at the geometric points
over `y`, through the restriction maps `stalkRestrict`. -/
instance Etale.isIso_piLift_stalkRestrict :
    IsIso (Pi.lift fun t ↦ Etale.stalkRestrict A f y t G) := by
  have h := Etale.colimitSectionsIsoStalk_hom_comp_piLift_stalkRestrict A f y G
  rw [← Iso.eq_inv_comp] at h
  rw [h]
  infer_instance

/-- The stalk of `f_* G` at `y` as the product of the stalks of `G` at the geometric points
over `y`, for a single sheaf `G`. -/
def Etale.stalkIsoPi :
    (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) ≅
      ∏ᶜ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber.obj G :=
  asIso (Pi.lift fun t ↦ Etale.stalkRestrict A f y t G)

@[simp]
lemma Etale.stalkIsoPi_hom :
    (Etale.stalkIsoPi A f y G).hom = Pi.lift fun t ↦ Etale.stalkRestrict A f y t G := rfl

/-- **The geometric stalk formula for a finite direct image.** For a finite morphism
`f : X ⟶ Y` and a geometric point `y` of `Y` with algebraically closed residue field, the
stalk of `f_* G` at `y` is the finite product of the stalks of `G` at the geometric points of
`X` over `y`, naturally in the sheaf `G`. -/
def Etale.lowerStarCompSheafFiberIsoPi :
    (f)_*[A] ⋙ (pointSmallEtale y).sheafFiber ≅
      ∏ᶜ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber :=
  NatIso.ofComponents
    (fun G ↦ Etale.stalkIsoPi A f y G ≪≫
      (piObjIso (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) G).symm)
    (fun {G G'} φ ↦ by
      rw [← cancel_mono
        (piObjIso (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) G').hom]
      apply Pi.hom_ext
      intro t
      simp only [Functor.comp_map, Iso.trans_hom, Etale.stalkIsoPi_hom, Iso.symm_hom,
        Category.assoc, piObjIso_hom_comp_π]
      rw [NatTrans.naturality, piObjIso_inv_comp_π_assoc, piObjIso_inv_comp_π, Pi.lift_π,
        Pi.lift_π_assoc, Etale.stalkRestrict_naturality])

@[simp]
lemma Etale.lowerStarCompSheafFiberIsoPi_hom_app :
    (Etale.lowerStarCompSheafFiberIsoPi A f y).hom.app G =
      (Etale.stalkIsoPi A f y G).hom ≫
        (piObjIso (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) G).inv :=
  rfl

/-- The components of the geometric stalk formula are the restriction maps `stalkRestrict`. -/
@[reassoc (attr := simp)]
lemma Etale.lowerStarCompSheafFiberIsoPi_hom_app_comp_π (t : GeometricFiber f y) :
    (Etale.lowerStarCompSheafFiberIsoPi A f y).hom.app G ≫
        (piObjIso (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) G).hom ≫
        Pi.π _ t =
      Etale.stalkRestrict A f y t G := by
  rw [Etale.lowerStarCompSheafFiberIsoPi_hom_app, Category.assoc, Iso.inv_hom_id_assoc,
    Etale.stalkIsoPi_hom, Pi.lift_π]

end StalkFormula

end AlgebraicGeometry

end
