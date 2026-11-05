/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedGlobalSections
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedFlatBaseChange.BaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedFlatBaseChange.ExtendScalars
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedFlatBaseChange.Pullback
public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Cohomology and flat base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `RΓ(X, ℱ) ⊗_A B ≅ RΓ(Y, g'^* ℱ)` in `D(B)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_derivedGlobalSectionsOver_baseChange_iso`), and
taking cohomology, `H^q(X, ℱ) ⊗_A B ≅ H^q(Y, g'^* ℱ)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_H_baseChange_linearEquiv`) (Stacks 02KH). The
degreewise statement is deduced from the derived one: the cohomology of `RΓ` is sheaf cohomology
(`AlgebraicGeometry.Scheme.Modules.homologyDerivedGlobalSectionsOverLinearEquiv`), and `- ⊗_A B`
commutes with cohomology since `B` is flat over `A`.
-/

@[expose] public section

universe w wA u

open CategoryTheory Limits TopologicalSpace TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {X : Scheme.{u}}

section BaseChange

variable {Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
  [Flat g] [QuasiSeparated f] [QuasiCompact f]

section Derived

variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
  [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
  [∀ U : X.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

end Derived

end BaseChange

end AlgebraicGeometry.Scheme.Modules
