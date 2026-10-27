/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.RingTheory.Flat.Basic

import Sheaf.Algebra.Homology.RingedSitePointFlat
import Sheaf.Algebra.Homology.RingedSitePointExact
import Sheaf.Algebra.Homology.RingedSitePointTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Conservative points detect flatness over a ring sheaf

Source: Stacks Project, Modules on Sites, Tag 05VC, lemma-check-flat-stalks
(blueprint: lem-sfb-ringed-site-conservative-flatness).

The normalized presentations specify the induced ring and module operations, and exist
for every point. The statement applies to every such presentation, an arbitrary ring
sheaf, and a family of points indexed by a type in any universe.
-/

@[expose] public section
set_option autoImplicit false

universe u v w t

open CategoryTheory

namespace CategoryTheory.RingedSitePoint

/-- A module sheaf is flat exactly when its modules at a conservative family of points
are flat over the induced stalk rings. The ring sheaf need not be constant; there is
no finiteness or quasi-coherence hypothesis. Normalized presentations encode precisely
transport of the operations along the inverse finite-product comparisons.

Source: Stacks Project, Modules on Sites, Tag 05VC, lemma-check-flat-stalks
(blueprint: lem-sfb-ringed-site-conservative-flatness).

Proof:
1. The normalized presentation in def-sfb-ringed-site-point identifies its module
   functor with inverse image on underlying sets, with the induced operations.
   Theorem lem-sfb-ringed-site-point-flat gives flatness of each stalk of a flat sheaf.
2. Conversely, take any three-term exact complex A → B → C, in degrees 0, 1, 2,
   and the complex M[0]. By lem-sfb-ringed-site-point-exact, every stalk of the
   first complex is exact. Flatness of the stalk of M and
   lem-weil-pbc-flat-tensor-exact make its tensor triple exact at the middle term.
   The signed-total construction def-pc-tensor-complex-sheaves and the isomorphism
   lem-sfb-ringed-site-point-tensor identify this with degree-one exactness of the
   stalk of the sheaf tensor triple.
3. Stalks reflect exactness: exactness of the module inverse-image functors identifies
   the stalk of ker(b)/im(a) with its stalkwise kernel quotient. If these all vanish,
   the map from its underlying set sheaf to the underlying set sheaf of zero becomes
   an isomorphism at every point. Joint reflection makes this map an isomorphism
   before taking stalks, so the kernel quotient vanishes. This also handles an empty
   conservative family.
4. Apply step 3 to the tensor triple. The total formula leaves only the degree-zero
   factor from M[0], hence gives A ⊗ M → B ⊗ M → C ⊗ M. This works also with a
   zero endpoint. Tensoring is additive by bilinearity and sheafification
   (def-pur-sheaf-tensor-product), so preservation of these exact triples is exactness
   of tensoring with M. This is def-pc-flat-sheaf-modules. -/
theorem isFlatOnSite_iff
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    {I : Type t} (p : I → GeometricMorphism (Type w) (Sheaf J (Type w)))
    (s : ∀ i : I, RingedSitePoint R (p i))
    (hp : JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse))
    (M : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    SheafOfModules.IsFlatOnSite.{u, v, w, w} (J := J) (R := R) M ↔
      ∀ i : I, Module.Flat (s i).ring ((s i).modules.obj M) := by
  sorry

end CategoryTheory.RingedSitePoint
