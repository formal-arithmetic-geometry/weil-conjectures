/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.PoincareDuality.ProjectionFormulaShiftBoundedConstructible

/-!
# The Künneth–Verdier map is a morphism of triangulated functors

Fix `N ∈ Dᵇc(Y)⟦ℚ̄_ℓ⟧`. Both sides of the Künneth–Verdier map
```
κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)
```
are triangulated functors of `M ∈ Dᵇc(X)⟦ℚ̄_ℓ⟧`, and `κ_{-,N}` is a natural transformation
compatible with the shifts (`ProEtale.CondensedRing.kunnethVerdierNatTrans`). Hence the objects `M`
for which `κ_{M,N}` is an isomorphism form a triangulated subcategory, closed under direct
summands: this is the two-out-of-three property on which the dévissage in `M` of the proof of the
Künneth–Verdier theorem rests (blueprint `prop-trf-exceptional-kunneth`,
`lem-sf-triangle-two-out-of-three`).

The compatibility with the shifts is obtained by writing `κ_{-,N}` as a composite of natural
transformations which commute with the shifts: `κ_{-,N}` is the transpose along
`Lp_Y^* N ⊗ᴸ - ⊣ RHom(Lp_Y^* N, -)` of the pairing
(`ProEtale.CondensedRing.kunnethVerdierPairingNatTrans`), a rearrangement of the tensor factors
followed by the exceptional Künneth map `α`
(`ProEtale.CondensedRing.exceptionalKunnethMapNatTrans`),
itself the transpose along `Rp_X! ⊣ Rp_X^!` of a composite of the braiding, the inverse of the
exceptional projection formula, compact-support base change, a counit and the left unitor
(`ProEtale.CondensedRing.exceptionalKunnethAdjointNatTrans_eq`).

## Main statements

- `ProEtale.CondensedRing.commShift_kunnethVerdierNatTrans`: `κ_{-,N}` commutes with the shifts.
- `ProEtale.CondensedRing.isIso_kunnethVerdierMap_of_triangEnvelope`: if `κ_{M,N}` is an
  isomorphism for `M` in a class `P`, it is one for `M` in the triangulated envelope of `P`.
- `ProEtale.CondensedRing.isIso_kunnethVerdierMap_of_distinguished`,
  `ProEtale.CondensedRing.isIso_kunnethVerdierMap_shift_iff`: two out of three and shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

end AlgebraicGeometry.ProEtale.CondensedRing
