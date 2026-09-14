/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!

# Compactifications of morphisms of schemes

A compactification of a morphism of schemes `f : X ⟶ Y` is a factorization `f = i ≫ g`
where `g : Z ⟶ Y` is proper and `i : X ⟶ Z` is an open immersion. We record
the data of a compactification of `f` in the class
`AlgebraicGeometry.Compactification f`.

We derive the properties of the morphisms involved in a compactification:

- `Compactification.isSeparated`: `f` is separated;
- `Compactification.locallyOfFiniteType`: `f` is locally of finite type;
- `Compactification.quasiCompact_openImmersion_iff`: `i` is quasi-compact if and only
  if `f` is;
- `Compactification.isProper_openImmersion`, `Compactification.isClosedImmersion_openImmersion`
  and `Compactification.isClopen_range_openImmersion`: if `f` is proper, then `i` is proper,
  hence a closed immersion with clopen range;
- `Compactification.isNoetherian_Z`: the ambient scheme of a compactification of a morphism
  to a Noetherian scheme is Noetherian;
- `Compactification.ofIsProper`: a proper morphism is a compactification of itself.

Finally, we define the class `AlgebraicGeometry.HasCompactification f`, asserting
`Nonempty (Compactification f)`. Nagata's compactification theorem asserts
`HasCompactification f` whenever `f` is separated and of finite type (and `Y` is
quasi-compact and quasi-separated). Any `f` satisfying `HasCompactification f` is
separated and locally of finite type; these are instances.
A choice of compactification is extracted from `HasCompactification f` by
`HasCompactification.compactification f`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The data of a compactification of `f : X ⟶ Y`: a scheme `Z` together with a proper
morphism `g : Z ⟶ Y` and an open immersion `i : X ⟶ Z` such that `f = i ≫ g`. -/
structure Compactification {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The scheme in which `X` is compactified. -/
  Z : Scheme.{u}
  /-- The structure morphism of the compactification, which is proper. -/
  g : Z ⟶ Y
  /-- The open immersion of `X` into the compactification. -/
  i : X ⟶ Z
  comm : f = i ≫ g
  isProper : IsProper g
  isOpenImmersion : IsOpenImmersion i

attribute [instance] Compactification.isProper Compactification.isOpenImmersion

namespace Compactification

variable {X Y : Scheme.{u}}

/-- A proper morphism is a compactification of itself. -/
def ofIsProper (f : X ⟶ Y) [IsProper f] : Compactification f where
  Z := X
  g := f
  i := 𝟙 X
  comm := (Category.id_comp f).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable {f : X ⟶ Y} (c : Compactification f)
include c

/-- A morphism admitting a compactification is separated. -/
theorem isSeparated : IsSeparated f := by
  rw [c.comm]
  infer_instance

/-- A morphism admitting a compactification is locally of finite type. -/
theorem locallyOfFiniteType : LocallyOfFiniteType f := by
  rw [c.comm]
  infer_instance

/-- If the open immersion into a compactification is quasi-compact, the compactified
morphism is quasi-compact. -/
theorem quasiCompact (hi : QuasiCompact c.i) : QuasiCompact f := by
  rw [c.comm]
  infer_instance

/-- The open immersion into a compactification of a quasi-compact morphism is
quasi-compact. -/
theorem quasiCompact_openImmersion (hf : QuasiCompact f) : QuasiCompact c.i := by
  have : QuasiCompact (c.i ≫ c.g) := c.comm ▸ hf
  exact .of_comp c.i c.g

/-- The open immersion into a compactification is quasi-compact if and only if the
compactified morphism is. -/
theorem quasiCompact_openImmersion_iff : QuasiCompact c.i ↔ QuasiCompact f :=
  ⟨c.quasiCompact, c.quasiCompact_openImmersion⟩

/-- The ambient scheme of a compactification of a morphism to a Noetherian scheme is
Noetherian, its structure morphism being proper. -/
theorem isNoetherian_Z [IsNoetherian Y] : IsNoetherian c.Z :=
  LocallyOfFiniteType.isNoetherian c.g

/-- The open immersion into a compactification of a **proper** morphism is itself proper:
`c.i` is proper as soon as `c.i ≫ c.g` is, because `c.g` is separated. -/
theorem isProper_openImmersion (hf : IsProper f) : IsProper c.i :=
  have : IsProper (c.i ≫ c.g) := c.comm ▸ hf
  .of_comp c.i c.g

/-- The open immersion into a compactification of a proper morphism is also a **closed**
immersion. -/
theorem isClosedImmersion_openImmersion (hf : IsProper f) : IsClosedImmersion c.i :=
  have := c.isProper_openImmersion hf
  .of_isOpenImmersion_of_universallyClosed c.i

/-- The open immersion into a compactification of a proper morphism identifies `X` with a
**clopen** subscheme of the compactification: its range is open, being an open immersion,
and closed, being universally closed. -/
theorem isClopen_range_openImmersion (hf : IsProper f) : IsClopen (Set.range c.i) :=
  have := c.isProper_openImmersion hf
  Scheme.Hom.isClopen_range c.i

end Compactification

variable {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` has a compactification if it factors as an open
immersion followed by a proper morphism. -/
class HasCompactification (f : X ⟶ Y) : Prop where
  nonempty_compactification : Nonempty (Compactification f)

attribute [instance low] HasCompactification.nonempty_compactification

lemma Compactification.hasCompactification {f : X ⟶ Y} (c : Compactification f) :
    HasCompactification f := ⟨⟨c⟩⟩

/-- A choice of compactification of `f`, extracted from a `HasCompactification f`
instance using choice. -/
@[no_expose]
noncomputable def HasCompactification.compactification (f : X ⟶ Y) [hf : HasCompactification f] :
    AlgebraicGeometry.Compactification f :=
  Classical.arbitrary _

namespace HasCompactification

/-- A proper morphism has a compactification, namely itself. -/
instance (priority := 100) of_isProper (f : X ⟶ Y) [IsProper f] : HasCompactification f :=
  ⟨⟨.ofIsProper f⟩⟩

variable (f : X ⟶ Y) [hf : HasCompactification f]

/-- A morphism admitting a compactification is separated. -/
instance isSeparated : IsSeparated f := hf.compactification.isSeparated

/-- A morphism admitting a compactification is locally of finite type. -/
instance locallyOfFiniteType : LocallyOfFiniteType f := hf.compactification.locallyOfFiniteType

end HasCompactification

end AlgebraicGeometry
