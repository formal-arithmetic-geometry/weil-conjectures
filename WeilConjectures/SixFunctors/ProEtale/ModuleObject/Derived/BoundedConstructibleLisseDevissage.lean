/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization

/-!
# Dévissage of bounded constructible complexes to lisse sheaves on locally closed subschemes

Let `Λ` be a commutative condensed ring and `T` a scheme with noetherian underlying space. A
triangulated functor `Φ : D(Mod_{Λ_T}) ⥤ D(Mod_{Λ_Y})`, where the bounded constructible
complexes on `Y` form a triangulated subcategory, carries `Dᵇc(T)` into `Dᵇc(Y)` as soon as it
does so for the extensions by zero `Rc_* j_! Rc'_* L` of the pro-étale locally finitely presented
(lisse) sheaves `L` along the locally closed immersions `E ⟶ W ⊆ D ⟶ T` (with `c` and `c'` closed
immersions and `W` open in `D`)
(`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse`). Given an open `U` of `T`, it
suffices to treat surjective `c'` and opens `W` lying inside `c⁻¹ U` or inside its complement
(`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse_along`).

The proof is a noetherian induction on the closed subset of `T` containing the image of a closed
immersion `c : D ⟶ T`, for complexes of the form `Rc_* M` with `M` bounded constructible on `D`.
By dévissage along the truncation triangles, `M` is a constructible sheaf `G` placed in degree
`0`. Some stratum of a stratification of `D` adapted to `G` contains a nonempty open `V` of `D`
(`ProEtale.CondensedRing.exists_nonempty_opens_subset_stratum`), and the open–closed triangle
`j_! Lj^* G ⟶ G ⟶ Ri_* Li^* G ⟶` for `V` and its closed complement splits `G` into the extension
by zero of a sheaf which is lisse on (a surjective closed immersion onto) `V`, and a complex
supported on the smaller closed subset `c(D ∖ V)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Devissage

variable {T Y : Scheme.{u}} [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated]
  (Φ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
  [Φ.CommShift ℤ] [Φ.IsTriangulated]

variable {Λ Φ}

end Devissage

end AlgebraicGeometry.ProEtale.CondensedRing
