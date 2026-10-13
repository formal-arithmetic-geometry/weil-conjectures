/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Internal Hom under the open-subscheme equivalence

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Mathlib AlgebraicGeometry/Modules/Sheaf.lean, `overEquiv`.
(blueprint: lem-sc-internal-hom-over-equiv). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The equivalence from the over-open site to the open subscheme preserves internal
Hom, naturally in both module arguments.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Mathlib AlgebraicGeometry/Modules/Sheaf.lean, `overEquiv`.
(blueprint: lem-sc-internal-hom-over-equiv).

Proof: An open V of U corresponds to its image open in Y equipped with the inclusion
into U. The slice over V is equivalent to the slice over that image object in the
over-U site: both describe the smaller opens contained in V, and the functors send
an inclusion to that same inclusion. A section of internal Hom is a compatible
family of local linear maps on this slice. Transport each map along this slice
equivalence and the structure-sheaf isomorphisms defining `overEquiv U`. These
isomorphisms transport scalars as well as the source and target modules, so the
transported maps are linear. The inverse transports them back. The two composites
are identities by cancellation of the scalar and module isomorphisms. Transport
commutes with restriction to a smaller open by naturality of these isomorphisms,
and with addition and scalar multiplication pointwise. Thus it defines an
isomorphism of sheaves of modules. Precomposition by f and postcomposition by g
commute with transport: in the expression for the three transported maps, the
intermediate module isomorphisms cancel. This is exactly the displayed naturality
equation. Empty opens and zero modules cause no exceptions: the same compatible
families and the same inverse constructions apply. This statement concerns only
module sheaves; it asserts neither product nor differential compatibility. -/
theorem internalHom_overEquiv {Y : Scheme.{u}} (U : Y.Opens) :
    let F := (Scheme.Modules.overEquiv U).functor
    ∃ e : ∀ (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U)),
      F.obj (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf) (F.obj A) (F.obj B),
      ∀ (A A' B B' : SheafOfModules.{u} (Y.ringCatSheaf.over U))
        (f : A' ⟶ A) (g : B ⟶ B'),
        F.map (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf.over U) f g) ≫
            (e A' B').hom =
          (e A B).hom ≫
            SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
              (F.map f) (F.map g) := by sorry

end AlgebraicGeometry
