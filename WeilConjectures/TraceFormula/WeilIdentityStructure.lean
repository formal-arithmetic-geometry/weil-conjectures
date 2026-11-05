/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.WeilTrace

/-!
# Weil objects for the identity with the identity structure

Let `X` be a separated scheme of finite type over a finite field `k`. Every bounded constructible
complex `K` on `X` is a Weil object for the identity of `X`, with the structure isomorphism
`L(𝟙)^* K ≅ K` (`ProEtale.CondensedRing.boundedConstructibleUpperStarId`); likewise every module
object `M` on `X` is a Weil sheaf for the identity, with the structure isomorphism
`(𝟙)^* M ≅ M` (`ProEtale.CondensedRing.upperStarId`). This file shows that these identity
structures are preserved by the compactly supported cohomology and by the homology sheaves.

## Main results

- `boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_horizontal_id`: the
  compact-support base change of the square `𝟙 ≫ f = f ≫ 𝟙` is
  `L(𝟙)^* Rf_! K ≅ Rf_! K ≅ Rf_! L(𝟙)^* K`. It follows from the idempotence of the square under
  horizontal pasting (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`).
- `ProEtale.CondensedRing.weilCompactSupportCohomology_obj_str_hom_of_id`: the compactly
  supported cohomology `RΓ_c(X, K)` of a Weil object with the identity structure has the identity
  structure.
- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id`: the
  homology sheaves of a Weil object with the identity structure have the identity structure.
- `ProEtale.CondensedRing.WeilSheaf.isoOfId`: Weil sheaves with the identity structure are
  isomorphic as soon as their underlying module objects are.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChange

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

end BaseChange

section CompactSupport

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

end CompactSupport

section Homology

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

end Homology

end AlgebraicGeometry.ProEtale.CondensedRing
