/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Preservation of exactness by ringed-slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8G
(blueprint: lem-weil-pbc-ringed-slice-extension-exactness).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The sheafified direct-sum extension preserves exactness at the middle term.

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8G
(blueprint: lem-weil-pbc-ringed-slice-extension-preserves-exact).

Proof: Write L for the displayed extension and T for restriction to the slice.
A map from the direct-sum presheaf of G to a module sheaf F is specified by
its maps on each summand. Naturality identifies these maps with a morphism
G → T(F); conversely such a morphism extends by the direct-sum universal
property. Module sheafification extends this bijection uniquely to maps
L(G) → F, giving L ⊣ T. Thus L preserves colimits and is right exact.
A monomorphism of module sheaves is injective on sections. Its direct-sum
extension is injective on every summand and hence on the whole direct sum.
Exact module sheafification preserves this injection, so L preserves monos.
An additive right exact functor between abelian categories that preserves
monos is exact: factor the first arrow through its image, then use the
short exact sequence from that image to the middle and final image.
Consequently L sends S.Exact to exactness of S.map L, which is the displayed
image-kernel equality. This argument uses arbitrary covering sieves and
requires neither pullbacks in C nor equality of its two universes. -/
theorem ringedSliceExtension_preserves_exact
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max u v}) (U : C)
    (S : ShortComplex (ringedSiteModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).over U)))
    (hS : S.Exact) :
    let R := (sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
    let L := extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
    imageSubobject (L.map S.f) = kernelSubobject (L.map S.g) := by
  sorry

end SheafOfModules
