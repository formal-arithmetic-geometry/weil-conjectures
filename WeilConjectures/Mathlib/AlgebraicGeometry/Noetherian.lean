/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Algebra.Colimit.Finiteness
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Noetherian approximations of a scheme

A *Noetherian approximation* of a scheme `S` is a cofiltered system of schemes of finite
type over `ℤ` with affine transition morphisms, together with a limit cone over the system
with point `S` (`AlgebraicGeometry.Scheme.NoetherianApproximation`). The stages of such a
system are Noetherian schemes
(`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`).

Here we set up the definition and treat the affine case: for an affine scheme `S`, the
spectra of the finitely generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a Noetherian
approximation (`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The key
algebraic input is that `Γ(S, ⊤)` is the filtered colimit of its finitely generated
`ℤ`-subalgebras (`CommRingCat.isColimitFGSubalgebraCocone`), and the geometric translation
is that `Spec`, being a right adjoint, preserves limits.

That *every* quasi-compact quasi-separated scheme admits a Noetherian approximation is
absolute Noetherian approximation, Stacks Project Tag 01ZA; it is proved in
`WeilConjectures/AlgebraicGeometry/NoetherianApproximation/Extension.lean` as
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`.

Throughout, "of finite type over `ℤ`" is spelled out as `LocallyOfFiniteType` of the
structure morphism `specULiftZIsTerminal.from X : X ⟶ Spec ℤ` together with
`CompactSpace X`.

## Main declarations

* `AlgebraicGeometry.Scheme.NoetherianApproximation`: the data of a Noetherian
  approximation of a scheme (blueprint:
  `def:nagata-absolute-noetherian-approximation-datum`).
* `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`: the affine case of
  absolute Noetherian approximation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- `Spec ℤ` is a locally Noetherian scheme. -/
instance isLocallyNoetherian_spec_uliftInt :
    IsLocallyNoetherian (Spec <| .of <| ULift.{u} ℤ) :=
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  inferInstance

/-- A **Noetherian approximation** of a scheme `S`: a cofiltered system of schemes of finite
type over `ℤ` with affine transition morphisms, exhibiting `S` as the limit of the system.
The stages are automatically Noetherian, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`.

```
              S
    π.app i  ↙         ↘  π.app j
  D.obj i  ─────────⟶  D.obj j
                D.map f
```

By absolute Noetherian approximation (Stacks Project Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`), every quasi-compact
quasi-separated scheme admits one.
(Blueprint: `def:nagata-absolute-noetherian-approximation-datum`; the blueprint indexes
the system by a directed preorder, while here the index category is any small cofiltered
category.) -/
structure Scheme.NoetherianApproximation (S : Scheme.{u}) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of stages. -/
  D : I ⥤ Scheme.{u}
  /-- Every stage is locally of finite type over `ℤ`. -/
  locallyOfFiniteType_obj (i : I) : LocallyOfFiniteType (specULiftZIsTerminal.from (D.obj i))
  /-- Every stage is quasi-compact; together with `locallyOfFiniteType_obj` this says that
  every stage is of finite type over `ℤ`. -/
  compactSpace_obj (i : I) : CompactSpace (D.obj i)
  /-- The transition morphisms of the system are affine. -/
  isAffineHom_map {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f)
  /-- The projections from `S` to the stages. -/
  π : (Functor.const I).obj S ⟶ D
  /-- `S` is the limit of its stages. -/
  isLimit : IsLimit (Cone.mk S π)

namespace Scheme.NoetherianApproximation

-- These are scoped: the heads of `compactSpace_obj` and `isAffineHom_map` are
-- metavariables, so as global instances they would be tried on every `CompactSpace` and
-- `IsAffineHom` goal.
attribute [instance] smallCategory isCofiltered
attribute [scoped instance] locallyOfFiniteType_obj compactSpace_obj isAffineHom_map

variable {S : Scheme.{u}}

/-- The stages of a Noetherian approximation are Noetherian schemes: they are of finite type
over the Noetherian ring `ℤ`. -/
scoped instance isNoetherian_obj (N : S.NoetherianApproximation) (i : N.I) :
    IsNoetherian (N.D.obj i) :=
  have := LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from (N.D.obj i))
  ⟨⟩

/-- Transport a Noetherian approximation along an isomorphism of schemes. -/
noncomputable def ofIso {S' : Scheme.{u}} (e : S ≅ S') (N : S.NoetherianApproximation) :
    S'.NoetherianApproximation where
  I := N.I
  D := N.D
  locallyOfFiniteType_obj := N.locallyOfFiniteType_obj
  compactSpace_obj := N.compactSpace_obj
  isAffineHom_map := N.isAffineHom_map
  π := (Functor.const N.I).map e.inv ≫ N.π
  isLimit := N.isLimit.ofIsoLimit <| Cone.ext e fun i ↦ by simp

variable (S : Scheme.{u}) [IsAffine S]

/-- **Noetherian approximation of an affine scheme**: the spectra of the finitely
generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a cofiltered system of schemes of finite type
over `ℤ` with affine transition maps whose limit is `S`. This is the affine case of Stacks
Project Tag 01ZA (blueprint:
`lemma:nagata-absolute-noetherian-approximation-exists`, affine case).

For `A ≤ B` the transition morphism `Spec ↥B ⟶ Spec ↥A` is `Spec.map` of the inclusion:

```
              S
    π.app B  ↙         ↘  π.app A
  Spec ↥B  ─────────⟶  Spec ↥A
```
-/
noncomputable def ofIsAffine : S.NoetherianApproximation where
  I := {A : Subalgebra ℤ Γ(S, ⊤) // A.FG}ᵒᵖ
  D := (CommRingCat.fgSubalgebraDiagram Γ(S, ⊤)).op ⋙ Scheme.Spec
  locallyOfFiniteType_obj i :=
    have : Algebra.FiniteType ℤ i.unop.1 := (Subalgebra.fg_iff_finiteType _).mp i.unop.2
    inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of i.unop.1))))
  compactSpace_obj i := inferInstanceAs (CompactSpace (Spec (CommRingCat.of i.unop.1)))
  isAffineHom_map f := inferInstanceAs (IsAffineHom (Spec.map _))
  π := (Functor.const _).map S.isoSpec.hom ≫
    (Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCocone Γ(S, ⊤)).op).π
  isLimit :=
    (isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFGSubalgebraCocone Γ(S, ⊤)).op).ofIsoLimit
      (Cone.ext S.isoSpec.symm fun A ↦ by simp)

end Scheme.NoetherianApproximation

end AlgebraicGeometry
