/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange

import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import Sheaf.RingTheory.StrictHenselizationModuleFlatness
import Sheaf.Algebra.Homology.SubcategoryLeftResolution
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion

/-!
# Tor intervals over a local ring and its strict henselization

Source: Stacks Project, More on Flatness, Tag 0DK0,
`lemma-tor-amplitude-up-down-henselization`, equivalence (1) with (3), at the closed
point of Spec R (blueprint: lem-sfb-strict-henselization-tor-interval).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace DerivedCategory

/-- A complex over a strict henselization has Tor amplitude in the same interval
before and after restricting scalars to the local base ring. Here `torAmplitudeIn`
tests the K-flat derived tensor with every module placed in degree zero. The
complex is arbitrary in the unbounded derived category; it need not descend.

Source: Stacks Project, Tag 0DK0, equivalence (1) with (3)
(blueprint: lem-sfb-strict-henselization-tor-interval).

Proof:
1. Put B = R^sh. Starting with Tor amplitude over B, use
   lem-pc-module-tor-amplitude-flat-model to choose a flat B-complex E supported
   in [a,b]. By lem-sfb-strict-henselization-module-flatness its terms are R-flat.
   Restriction leaves underlying groups, differentials, kernels and images
   unchanged, so preserves quasi-isomorphisms. The same flat-model criterion over
   R gives Tor amplitude over R.
2. Conversely, tensoring with R in degree zero shows that L has cohomology only
   in [a,b]. For a representative K, replace its degree-b term by ker(d^b) and
   its terms above b by zero. The resulting bounded-above complex T maps
   quasi-isomorphically to K.
3. Apply lem-sfb-subcategory-left-resolution with the class of free B-modules
   and upper bound b to T. Zero is free, and every module M is a quotient of the
   free module with basis its elements, by e_x mapping to x. Obtain a free
   complex P, zero above b, representing L over B and after scalar restriction.
4. Free B-modules are B-flat, hence R-flat by
   lem-sfb-strict-henselization-module-flatness. By
   lem-pc-module-bounded-flat-kflat, P is K-flat over R. Tensoring P with every
   R-module is exact in degree a-1. By lem-pc-module-flat-opcycles-tor-criterion,
   Q = P^a / im(d^(a-1)) is R-flat; it is a B-module, so
   lem-sfb-strict-henselization-module-flatness makes it B-flat as well.
5. Replace P below a by zero and its degree-a term by Q. The induced
   differential is well-defined since successive differentials compose to zero.
   This good truncation E is quasi-isomorphic to P: above a the cohomology is
   unchanged, at a it is ker(Q to P^(a+1)), and below a both cohomologies vanish.
   It is flat over B and supported in [a,b]. Apply
   lem-pc-module-tor-amplitude-flat-model over B to finish. -/
theorem torAmplitudeIn_iff_strictHenselization (R K B : Type u)
    [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing B] [Algebra R B]
    (_presentation : Algebra.StrictHenselizationPresentationIn.{u, u} R K B)
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} B)) (a b : ℤ) (_hab : a ≤ b) :
    torAmplitudeIn (ModuleCat.{u} R) a b
      ((ModuleCat.restrictScalars.{u} (algebraMap R B)).mapDerivedCategory.obj L) ↔
    torAmplitudeIn (ModuleCat.{u} B) a b L := by
  sorry

end DerivedCategory
