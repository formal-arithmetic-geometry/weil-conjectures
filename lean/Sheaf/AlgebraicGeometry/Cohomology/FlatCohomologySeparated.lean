/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-! # The separated case of flat cohomology base change

Source: Stacks Project, Cohomology of Schemes, Lemma 30.5.2 (Tag 02KH),
the separated-case paragraph (blueprint: lem-pc-flat-cohomology-separated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison is bijective for a quasi-compact separated scheme over
an arbitrary commutative ring and an arbitrary flat commutative algebra.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), separated-case paragraph.
(blueprint: lem-pc-flat-cohomology-separated)

Proof: Choose a finite affine open cover of X. Separatedness over the affine base
makes every nonempty finite intersection affine. Their inverse images in X_S are
again affine and form a cover. Leray's theorem identifies both sheaf cohomologies
with the cohomologies of these ordered Cech complexes. On each intersection the
quasi-coherent affine pullback section formula identifies the sections after base
change with S tensor_R the original sections. The identifications are the maps
induced by the adjunction unit, hence commute with restriction and alternating
Cech differentials. Finite products commute with tensor, giving a chain isomorphism
from the tensored original Cech complex to the new complex. Flatness makes tensor
exact, so its homology comparison is invertible (Mathlib's mapHomologyIso).
Naturality of the Cech-to-sheaf comparison identifies the resulting map with
H.baseChange, not just an unspecified isomorphism. Its bijectivity follows.
This argument includes the empty scheme and all degrees, and requires neither
properness nor finite-dimensionality. The base algebra need not be a field. -/
theorem H.baseChange_bijective_of_isSeparated
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Function.Bijective (H.baseChange (S := S) f M q) := by sorry

end AlgebraicGeometry.Scheme.Modules
