/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.FiniteBiproductUnit
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-!

# Stalks of homology sheaves of bounded constructible complexes are dualizable

Let `K` be a bounded constructible complex of `ℚ̄_ℓ`-sheaves on a separated scheme `X` of finite
type over a field `k`, and `x̄ : Spec Ω ⟶ X` a geometric point, `Ω` algebraically closed. The
stalk `x̄^* Hʲ(K)` of each homology sheaf is a dualizable object of the symmetric monoidal
category `Mod_{Spec Ω}` of `ℚ̲̄_ℓ`-modules on the pro-étale site of `Spec Ω`
(`ProEtale.CondensedRing.nonempty_hasRightDual_upperStar_homology`): `Hʲ(K)` is constructible,
so its restriction to the stratum through `x̄` is pro-étale locally finitely presented, and a
finitely presented module over the field `ℚ̄_ℓ` on the point `Spec Ω` is free of finite rank
(`ProEtale.CondensedRing.isFiniteFree_upperStar_homology`), hence dualizable.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Stalks of homology sheaves of bounded constructible complexes are dualizable**: for a
bounded constructible complex `K` of `ℚ̄_ℓ`-sheaves on `X` and a geometric point
`x̄ : Spec Ω ⟶ X`, `Ω` algebraically closed, the stalk `x̄^* Hʲ(K)` has a right dual in
`Mod_{Spec Ω}`. -/
theorem nonempty_hasRightDual_upperStar_homology
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (j : ℤ) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.left) :
    Nonempty (HasRightDual ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
      ((DerivedCategory.homologyFunctor _ j).obj K.obj))) :=
  letI := Abelian.hasFiniteBiproducts (C := CategoryTheory.Mod
    (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))
  have ⟨n, ⟨e⟩⟩ := isFiniteFree_upperStar_homology ℓ (Field.toIsField Ω)
    IsField.isSepClosed_toField K j x
  Limits.IsFiniteBiproductOf.nonempty_hasRightDual ⟨Fin n, inferInstance, ⟨e⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
