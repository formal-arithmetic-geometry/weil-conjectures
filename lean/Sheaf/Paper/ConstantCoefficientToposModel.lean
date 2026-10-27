/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Sheaf.CategoryTheory.SystemScalarModel
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses

/-! # Scalar and site pasting for compact-support factorizations

Source: blueprint main-20261015, sk-thm-purity-transport, Steps 1 and 3.
(blueprint: def-pur-constant-coefficient-topos-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Bundled presentations retain independent object and morphism universes.
set_option linter.checkUnivs false


universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CompactScalarSite

/-- A fixed small-site presentation, with the usual coefficient size.
Source: Stacks 00XA and 00VI
(blueprint: def-pur-constant-coefficient-topos-model). -/
structure Presentation where
  C : Type u
  [category : Category.{v} C]
  J : GrothendieckTopology C
  [small : EssentiallySmall.{max u v} C]
  [ringSheafify : HasSheafify J CommRingCat.{max u v}]
  [abSheafify : HasSheafify J AddCommGrpCat.{max u v}]
  [abLocal : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [ringForget : J.PreservesSheafification (forget CommRingCat.{max u v})]

attribute [instance] Presentation.category Presentation.small Presentation.abSheafify
  Presentation.abLocal Presentation.ringSheafify Presentation.ringForget

/-- Constant commutative coefficients on the fixed site.
Source: Stacks 093J (blueprint: def-pur-constant-coefficient-topos-model). -/
def coefficients (W : Presentation.{u, v}) (R : Type (max u v)) [CommRing R] :=
  (constantSheaf W.J CommRingCat.{max u v}).obj (CommRingCat.of R)

/-- The recorded module-sheaf category over these coefficients.
Source: Stacks 03DA (blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev modules (W : Presentation.{u, v}) (R : Type (max u v)) [CommRing R] :=
  ringedSiteModules.{max u v}
    ((sheafCompose W.J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (coefficients W R))

/-- The ordinary unbounded derived category, with the recorded standard localization.
Source: Stacks 05RU (blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev derived (W : Presentation.{u, v}) (R : Type (max u v)) [CommRing R] :=
  DerivedCategory (modules W R)

/-- Underlying sheaves of sets, retaining all generalized sections.
Source: Stacks 03D2 (blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev underlying (W : Presentation.{u, v}) (R : Type (max u v)) [CommRing R] :=
  SheafOfModules.toSheaf
    ((sheafCompose W.J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (coefficients W R)) ⋙ sheafCompose W.J (forget AddCommGrpCat.{max u v})

variable {A B : Type (max u v)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The actual constant-ring coefficient map.
Source: Stacks 093J (blueprint: def-pur-constant-coefficient-topos-model). -/
def coefficientMap (W : Presentation.{u, v}) : coefficients W A ⟶ coefficients W B :=
  (constantSheaf W.J CommRingCat.{max u v}).map (CommRingCat.ofHom φ)

/-- The existing scalar-extension model, including insertion-of-one normalization.
Source: Stacks 03D7, 06YY, 0FND and 09T5
(blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev Scalar (W : Presentation.{u, v}) :=
  SheafOfModules.SystemScalarModel.{u, v, max u v}
    (R := coefficients W A) (S := coefficients W B) (coefficientMap φ W)

/-- Exact restriction of scalars on module sheaves.
Source: Stacks 03DA (blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev restrict (W : Presentation.{u, v}) : modules W B ⥤ modules W A :=
  SheafOfModules.restrictScalars
    ((sheafCompose W.J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      (coefficientMap φ W))

/-- Exact restriction of scalars on unbounded derived categories.
Source: Stacks 03DA and 015F
(blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev derivedRestrict (W : Presentation.{u, v}) : derived W B ⥤ derived W A :=
  (restrict φ W).mapDerivedCategory

/-- Geometric inverse image with its transported constant-ring module structure.
Both site universes remain independent. The coefficient and module universes coincide
because the node uses ordinary sheaves of modules in the universe containing the site.
Source: Stacks 00YV and 03D2
(blueprint: def-pur-constant-coefficient-topos-model). -/
structure InverseModel (T W : Presentation.{u, v}) (R : Type (max u v)) [CommRing R]
    (g : GeometricMorphism (Sheaf T.J (Type (max u v)))
      (Sheaf W.J (Type (max u v)))) where
  lift : SheafOfModules.AlgebraicInverseImage g.inverse (coefficients W R) (coefficients T R)
  [additive : lift.modules.Additive]
  [limits : PreservesFiniteLimits lift.modules]
  [colimits : PreservesFiniteColimits lift.modules]
  point : g.inverse.obj ((constantSheaf W.J (Type (max u v))).obj PUnit.{max u v + 1}) ≅
    (constantSheaf T.J (Type (max u v))).obj PUnit.{max u v + 1}
  constants : ∀ r : R,
    g.inverse.map ((constantSheaf W.J (Type (max u v))).map
      (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ r))) ≫
      g.inverse.map ((constantCommuteCompose W.J (forget CommRingCat.{max u v})).inv.app
        (CommRingCat.of R)) ≫ lift.ringUnderlying.hom =
      point.hom ≫ (constantSheaf T.J (Type (max u v))).map
        (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ r)) ≫
      (constantCommuteCompose T.J (forget CommRingCat.{max u v})).inv.app (CommRingCat.of R)

attribute [instance] InverseModel.additive InverseModel.limits InverseModel.colimits

/-- The exact induced inverse image on derived module sheaves.
Source: Stacks 015F (blueprint: def-pur-constant-coefficient-topos-model). -/
abbrev inverse {T W : Presentation.{u, v}} {R : Type (max u v)} [CommRing R]
    {g : GeometricMorphism (Sheaf T.J (Type (max u v)))
      (Sheaf W.J (Type (max u v)))} (L : InverseModel T W R g) :
    derived W R ⥤ derived T R := L.lift.modules.mapDerivedCategory

/-- The derived right adjoint of the actual exact inverse image. The adjunction
characterizes ordinary derived direct image up to its unique counit-compatible iso.
Source: Stacks 09T5 (blueprint: def-pur-constant-coefficient-topos-model). -/
structure DirectModel {T W : Presentation.{u, v}} {R : Type (max u v)} [CommRing R]
    {g : GeometricMorphism (Sheaf T.J (Type (max u v)))
      (Sheaf W.J (Type (max u v)))} (L : InverseModel T W R g) where
  functor : derived T R ⥤ derived W R
  adj : inverse L ⊣ functor


/-- The canonical scalar/pullback isomorphism, characterized as the left mate
of the identity on restricted underlying sections. Its direction is lambda_v.
The normalization uses exact scalar restriction and exact geometric inverse image,
so it applies on the unbounded derived categories. No cube equation is assumed.
Source: Stacks 03EL, 07A4 and 09T5
(blueprint: def-pur-constant-coefficient-topos-model). -/
structure ScalarPullback {T W : Presentation.{u, v}}
    {g : GeometricMorphism (Sheaf T.J (Type (max u v)))
      (Sheaf W.J (Type (max u v)))}
    (LA : InverseModel T W A g) (LB : InverseModel T W B g)
    (SW : Scalar φ W) (ST : Scalar φ T) where
  restriction : restrict φ W ⋙ LA.lift.modules ≅ LB.lift.modules ⋙ restrict φ T
  underlying_normalized : ∀ N : modules W B,
    (underlying T A).map (restriction.hom.app N) ≫ LB.lift.moduleUnderlying.hom.app N =
      LA.lift.moduleUnderlying.hom.app ((restrict φ W).obj N)
  comparison : SW.model.T ⋙ inverse LB ≅ inverse LA ⋙ ST.model.T
  mate_normalized :
    (mateEquiv SW.adjunction ST.adjunction
      (TwoSquare.mk _ _ _ _ comparison.inv)).natTrans =
        (Functor.mapDerivedCategorySquareIso restriction).hom

/-- One of the three vertical comparison morphisms, with both coefficients and
its canonical scalar/pullback comparison. The inverse comparison is delta_W.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-constant-coefficient-topos-model). -/
structure Vertex where
  W : Presentation.{u, v}
  tildeW : Presentation.{u, v}
  scalar : Scalar φ W
  tildeScalar : Scalar φ tildeW
  ν : GeometricMorphism (Sheaf tildeW.J (Type (max u v)))
    (Sheaf W.J (Type (max u v)))
  NA : InverseModel tildeW W A ν
  NB : InverseModel tildeW W B ν
  scalarPullback : ScalarPullback φ NA NB scalar tildeScalar

end CategoryTheory.CompactScalarSite
