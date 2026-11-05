/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Iso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperShriekFieldExtension
public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TateTwist.Pullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials

/-!

# Base change of dualizing complexes along field extensions, embedded case

Let `L/F` be a field extension, `X` a proper `F`-scheme with base change `X' = X ×_F L` and
`φ : π^* ω_X ⟶ ω_{X'}` the comparison of the dualizing complexes
(`ProEtale.CondensedRing.dualizingComplexBaseChange`). If `X` admits a closed immersion
`i : X ⟶ P` into an `F`-scheme `P` smooth of pure relative dimension `d` (for instance a
projective space, `AlgebraicGeometry.ProjectiveSpace.smoothOfRelativeDimension`), then `φ` is an
isomorphism
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_isClosedImmersion_of_tateTwistIso`),
given the pullback of the Tate twists `π_P^* ℚ̄_ℓ(d)[2d] ≅ ℚ̄_ℓ(d)[2d]`.

By `ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_iso` it suffices to find some
isomorphism `π^* ω_X ≅ ω_{X'}`. It is the composite
```
π^* ω_X ≅ π^* Ri^! ω_P ≅ π^* Ri^! ℚ̄_ℓ(d)[2d] ≅ Ri'^! π_P^* ℚ̄_ℓ(d)[2d] ≅ Ri'^! ℚ̄_ℓ(d)[2d]
  ≅ Ri'^! ω_{P'} ≅ ω_{X'}
```
of the composition isomorphisms of the exceptional inverse images
(`ProEtale.CondensedRing.upperShriekDualizingComplexIso`), smooth purity on `P` and on `P'`
(`ProEtale.CondensedRing.isIso_smoothPurityMap`, an input of the smooth purity section), the
commutation of `Ri^!` with the field extension
(`ProEtale.CondensedRing.nonempty_iso_upperShriek_closedImmersion_of_fieldExtension`) and the
pullback of the Tate twists.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  {X P : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {X' P' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {i : X ⟶ P} {i' : X' ⟶ P'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
  {πP : P'.left ⟶ P.left} {π : X'.left ⟶ X.left}

section Projective

variable {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] {π : X'.left ⟶ X.left}

end Projective

end AlgebraicGeometry.ProEtale.CondensedRing
