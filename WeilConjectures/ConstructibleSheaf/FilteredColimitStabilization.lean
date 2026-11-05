/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Noetherian

/-!
# Constructible sheaves are not unions of strictly increasing families of subsheaves

Let `X` be a Noetherian scheme and `Λ` a finite ring. A constructible étale sheaf `F` of
`Λ`-modules on `X` which is the colimit of a filtered diagram of subsheaves is equal to one of
them (`AlgebraicGeometry.Etale.exists_epi_ι_app_of_isConstructibleSheaf`): its stalks are finite,
hence each is attained at some stage, the locus where a stage is attained is a constructible
neighbourhood of the point (`AlgebraicGeometry.Etale.exists_isConstructible_sheafFiber_map_eq_zero`
applied to the cokernels), and a Noetherian induction makes one stage work at all points.

This is the finiteness input of Deligne's approximation of a sheaf by a constructible subsheaf
on the geometric generic fibres of coordinates (SGA 4½, [Th. finitude], proof of 3.2).
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

end Etale

end AlgebraicGeometry
