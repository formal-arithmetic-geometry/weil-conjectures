/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-!
# Finite compactifications of quasi-finite morphisms

By Zariski's main theorem, a separated quasi-compact morphism `f : X ⟶ Y` which is locally
quasi-finite and locally of finite type, with `Y` quasi-compact and quasi-separated, factors as a
quasi-compact open immersion followed by a finite morphism. Since finite morphisms are proper,
this factorization is a compactification of `f`
(`AlgebraicGeometry.Compactification.exists_isFinite_of_locallyQuasiFinite`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A separated quasi-compact morphism, locally quasi-finite and locally of finite type, into a
quasi-compact quasi-separated scheme has a compactification `X ⟶[i] Z ⟶[g] Y` with `i`
quasi-compact and `g` finite (Zariski's main theorem, blueprint: `thm-pqf-zmt-factorization`). -/
theorem Compactification.exists_isFinite_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ c : Compactification f, IsFinite c.g ∧ QuasiCompact c.i := by
  obtain ⟨T, j, p, hj, hjc, hp, hjp⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  exact ⟨⟨T, p, j, hjp.symm, inferInstance, hj⟩, hp, hjc⟩

end AlgebraicGeometry
