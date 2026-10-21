/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # Proper pushforward and ambient coproducts over a qcqs base

Source: blueprint main-20261015, sec-six-functors-basics,
`det-sf-comp-coherence-refinement.proof.md`, (2), first paragraph.
(blueprint: lem-sfb-qcqs-proper-localizing-coproducts)

`PreservesColimit (Discrete.functor L)` expresses invertibility of the canonical
ambient coproduct comparison induced by the images of the coprojections. Ambient
coproducts exist by the Grothendieck derived-coproduct theorem, including for the
empty family. This formulation is independent of the choices of coproduct objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper pushforward preserves ambient small coproducts of objects in the localizing
hull of bounded constructible finite-Tor complexes, over an arbitrary qcqs base.

Source: blueprint main-20261015, `det-sf-comp-coherence-refinement.proof.md`, (2),
first paragraph (blueprint: lem-sfb-qcqs-proper-localizing-coproducts).

Proof plan:
1. The closed monoidal Grothendieck theorem for sheaves and the module-object theorem
   `lem-sfb-modobj-grothendieck` make the source and target module categories
   Grothendieck abelian. `lem-kun-grothendieck-derived-coproducts` gives ordinary
   ambient coproducts of unbounded complexes, with their specified coprojections.
2. Exactness of coproducts gives their commutation with cohomology and good lower
   truncations (`def-kun-truncations`), including the natural truncation maps.
3. Properness implies finite type and quasi-compactness, and separatedness implies
   quasi-separatedness (`lem-pc-separated-quasi-separated`). Apply
   `lem-sfb-adic-proper-bounded-below-coproducts` to the family truncated below a
   single integer a. This gives the invertible comparison for that family.
4. Choose c from `lem-sfb-qcqs-proper-hull-tail-bound`. In output degree n put
   a = n - c. The standard truncation triangle and the triangulated total right
   derived functor (`lem-pc-right-derived-functor-triangulated`) show that the map
   from K to its lower truncation induces an isomorphism on H^n after pushforward:
   the lower tail has vanishing H^n and H^(n+1). Use the long exact sequence
   `lem-sf-derived-homology-long-exact`. Apply this to each L_t and to their sum,
   which lies in the hull. The truncations need not themselves lie in the hull.
5. The square comparing the original family with its lower truncations commutes,
   by naturality of the truncation map, tested on every coprojection. On H^n both
   vertical maps are invertible by steps 2 and 4, and the bottom map by step 3.
   Thus the original comparison is invertible on every cohomology object.
   `lem-weil-pbc-unbounded-derived-iso-cohomology` detects its invertibility.
6. For the empty family both sums are zero and triangulated pushforward preserves
   zero. The cutoff depends on n, so no common bound on the original family and
   no completeness property of its ordinary ambient sum have been assumed. -/
theorem qcqs_proper_localizing_preservesCoproduct
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S X Y : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f]
    (I : Type (u + 1))
    (L : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hL : ∀ t : I, localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K) (L t)) :
    PreservesColimit (Discrete.functor L) (moduleObjectDerivedPushforward Λ f) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
