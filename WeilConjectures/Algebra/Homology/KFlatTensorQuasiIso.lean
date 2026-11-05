/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Tensoring a K-flat quasi-isomorphism with an arbitrary complex

Source: Stacks Project, Lemma 15.60.12, Tag 064L
(blueprint: lem-pc-kflat-tensor-quasi-iso).

The ring is regarded as a constant sheaf on the one-point site with the bottom topology.
K-flatness is the existing `CochainComplex.IsKFlatTensor` for sheaves of modules on this site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- (blueprint: lem-pc-kflat-tensor-quasi-iso) The commutative ring `R` regarded as a
sheaf on the one-point site, as in the node's interpretation of Stacks, Tag 064L.
The bottom topology imposes no additional sheaf condition; the constant presheaf
has value `R` at the unique object. -/
def onePointRingSheaf (R : Type u) [CommRing R] :
    Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{u+1})) CommRingCat.{u} :=
  ⟨(Functor.const _).obj (CommRingCat.of R), Presheaf.isSheaf_bot _⟩

end CochainComplex
