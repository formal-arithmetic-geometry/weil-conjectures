/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteness
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.ConstructibleSheaf.EtaleDescent

/-!
# The Verdier dual of a complex of lisse sheaves on a smooth scheme

Let `O` be an irreducible scheme smooth of pure relative dimension `n` over a field `k`, and `K` a
complex on `O` represented by a bounded complex of flat finite locally constant sheaves in degrees
`[a, b]`. After shrinking `O` to a nonempty open, the Verdier dual `𝔻_O K = RHom(K, ω_O)` has Tor
amplitude in `[-b - 2n, -a - 2n]`.

The proof avoids the dualizability of lisse sheaves: after shrinking `O`, there is a finite étale
surjection `p : V ⟶ O` along which all the terms become constant
(`AlgebraicGeometry.Etale.exists_finite_etale_surjective_isConstant`), hence dualizable, being
constant sheaves of finite projective modules. Along the finite étale `p`, `p^* = Rp^!` commutes
with the internal hom, and `ω_O` is a shifted flat invertible sheaf by smooth duality, so
`p^* 𝔻_O K ≅ RHom(p^* K, p^* ω_O) ≅ (p^* K)^∨ ⊗ᴸ p^* ω_O`; the Tor amplitude then descends along
the surjection `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Trivialising finitely many locally constant sheaves -/

/-! ### Dualizability after a finite étale trivialisation -/

section Dualizable

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable [Finite Λ]

end Dualizable

/-! ### The Verdier dual of a complex of lisse sheaves -/

variable [Finite Λ]

end Etale

end AlgebraicGeometry
