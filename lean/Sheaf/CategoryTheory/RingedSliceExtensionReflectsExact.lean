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
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.CategoryTheory.RingedSliceExtensionPreservesExact

/-!
# Reflection of exactness by ringed-slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8G
(blueprint: lem-weil-pbc-ringed-slice-extension-exactness).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Exactness after the sheafified direct-sum extension detects exactness on the slice.

Source: Stacks Project, Modules on Sites, Tag 0E8G
(blueprint: lem-weil-pbc-ringed-slice-extension-reflects-exact).

Proof: At (V, φ), inject a section of G into the φ summand of its direct-sum
extension and then sheafify. These maps commute with restrictions. If the
image is zero, the module and underlying-set sheafification comparisons and
local injectivity of the sheafification unit give a covering sieve on V
where the restricted direct-sum section is zero. Projecting to the φ-coordinate
after restriction shows that the original section vanishes on the corresponding
cover in the slice. Sheaf separatedness makes it zero. An empty covering sieve
also works: a sheaf has just one section there. Thus this natural unit is monic,
and L(G) = 0 implies G = 0.
The preservation theorem makes L exact. Factor S.f through ker S.g and let H
be the cokernel of this factorization. Exactness of L identifies L(H) with
the analogous quotient for the extended complex. The hypothesis makes that
quotient zero, so H = 0 by the monic unit. The factorization is therefore epic,
which is precisely S.Exact. Equivalently the monic natural unit makes L faithful,
and Mathlib's Functor.reflects_exact_of_faithful supplies the last step. -/
theorem ringedSliceExtension_reflects_exact
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max u v}) (U : C)
    (S : ShortComplex (ringedSiteModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).over U)))
    (hS : let R := (sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
      let L := extensionByZeroPresheaf.{max u v} R U ⋙
        PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
      imageSubobject (L.map S.f) = kernelSubobject (L.map S.g)) :
    S.Exact := by
  sorry

end SheafOfModules
