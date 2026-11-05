/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!

# Base change of exceptional inverse images and composition

Let `f : Z ⟶ Y` and `g : Y ⟶ P` be proper morphisms of separated schemes of finite type over a
field `k₁`, with base changes `f' : Z' ⟶ Y'` and `g' : Y' ⟶ P'` (over a field `k₂`) in stacked
cartesian squares
```
Z' --πZ--> Z
 |f'       |f
 v         v
Y' --πY--> Y
 |g'       |g
 v         v
P' --πP--> P
```
This file proves that the base change maps of the exceptional inverse image
`β : πZ^* Rf^! ⟶ Rf'^! πP^*` (`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) are compatible
with composition.

## Main results

- `ProEtale.CondensedRing.upperShriekBaseChangeOfMap_comp_app`: through the composition
  isomorphisms `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`), `β_{f ≫ g}(M)` is
  `β_f(Rg^! M)` followed by `Rf'^!(β_g(M))`.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app_iff`: if `β_f` is invertible
  at `Rg^! M`, then `β_{f ≫ g}(M)` is invertible if and only if `Rf'^!(β_g(M))` is.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app`: `β_{f ≫ g}(M)` is invertible
  if `β_f(Rg^! M)` and `β_g(M)` are; in particular, for a closed immersion `f`, if `β_g(M)` is,
  along weakly étale base change
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app_of_weaklyEtale`) or a field
  extension (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app_of_fieldExtension`).

## Proof

The adjunctions `Rf_* ⊣ Rf^!` (`ProEtale.CondensedRing.lowerStarUpperShriekAdjunction`) compose,
and the inverse proper base change isomorphisms paste
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_app_comp_lowerStarCompOfEq_inv_app`),
so the mates paste through the isomorphisms of right adjoints induced by `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`CategoryTheory.Adjunction.mateEquiv_inv_comp_rightAdjointUniq`). These isomorphisms are the
composition isomorphisms of the exceptional inverse image, since `Rf_! ≅ Rf_*` is compatible with
composition (`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp`);
this is the abstract
`CategoryTheory.Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_eq_conjugateIsoEquiv`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Composition isomorphisms of exceptional inverse images -/

section CompIso

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y P : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

end CompIso

/-! ### Base change maps and composition -/

section Comp

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z Y P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' Y' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ Y} {g : Y ⟶ P} {f' : Z' ⟶ Y'} {g' : Y' ⟶ P'} [IsProper f.left] [IsProper g.left]
  [IsProper f'.left] [IsProper g'.left] [IsProper (f ≫ g).left] [IsProper (f' ≫ g').left]
  {πZ : Z'.left ⟶ Z.left} {πY : Y'.left ⟶ Y.left} {πP : P'.left ⟶ P.left}

end Comp

/-! ### Field extensions -/

section FieldExtension

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  {Z Y P : Over (Spec (.of F))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' Y' P' : Over (Spec (.of L))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {i : Z ⟶ Y} {g : Y ⟶ P} {i' : Z' ⟶ Y'} {g' : Y' ⟶ P'} [IsClosedImmersion i.left]
  [IsClosedImmersion i'.left] [IsProper g.left] [IsProper g'.left] [IsProper (i ≫ g).left]
  [IsProper (i' ≫ g').left]
  {πZ : Z'.left ⟶ Z.left} {πY : Y'.left ⟶ Y.left} {πP : P'.left ⟶ P.left}

end FieldExtension

end AlgebraicGeometry.ProEtale.CondensedRing
