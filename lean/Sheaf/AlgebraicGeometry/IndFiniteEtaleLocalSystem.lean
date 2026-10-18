/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Ind-finite étale local systems

Source: ILO, Travaux de Gabber, Exposé XVII, Definition 7.2.1 and the module paragraph
following Proposition 7.2.3, pp. 301–302 (blueprint: def-per-ind-finite-etale-local-system).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A set local system is an actual filtered colimit of finite étale representable sheaves.
The index lives in the universe of the sets, allowing arbitrary stalks in that universe.
Source: ILO XVII, Definition 7.2.1 (blueprint: def-per-ind-finite-etale-local-system). -/
def IsIndFiniteEtaleSheaf {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
    (D : I ⥤ S.FiniteEtale)
    (c : Cocone (D ⋙ ObjectProperty.ι _ ⋙ S.smallEtaleTopology.uliftYoneda.{u + 1})),
    Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ F)

/-- A module local system is defined by its underlying set sheaf, with no finite-generation
or finite-ring condition. We use the established ModuleCat-valued encoding of modules over
constant coefficients, retaining the original sheaf maps and scalar operations.
Source: ILO XVII, paragraph after Proposition 7.2.3
(blueprint: def-per-ind-finite-etale-local-system). -/
def IsIndFiniteEtaleModule {S : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)) : Prop :=
  IsIndFiniteEtaleSheaf ((sheafCompose S.smallEtaleTopology
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F)

/-- The full category of ind-finite étale module sheaves: its arrows are precisely the
ambient module sheaf morphisms. Source: ILO XVII, Definition 7.2.1 and the paragraph after
Proposition 7.2.3 (blueprint: def-per-ind-finite-etale-local-system). -/
abbrev IndFiniteEtaleModules (S : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  ObjectProperty.FullSubcategory (IsIndFiniteEtaleModule (S := S) (R := R))

end AlgebraicGeometry.Scheme
