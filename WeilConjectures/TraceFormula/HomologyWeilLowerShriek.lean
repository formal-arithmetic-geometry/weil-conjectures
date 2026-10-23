/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.WeilSheafLowerStar
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Homology sheaves of the lower shriek of Weil objects along a finite morphism

Let `f : X ⟶ Y` be a finite morphism with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`. For a Weil object `K` for `e_X`, the homology sheaves of the lower shriek
`Rf_!^Weil K` are the pushforwards of the homology sheaves of `K`, as Weil sheaves for `e_Y`:
```
Hʲ(Rf_!^Weil K) ≅ f_* Hʲ(K)
```
(`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerShriek_iso`). It is the composite of

- `Rf_!^Weil K ≅ Rf_*^Weil K` for proper `f`
  (`ProEtale.CondensedRing.nonempty_weilLowerShriek_iso_weilLowerStar`), through
  `Rf_! ≅ Rf_*` and the identification of the compact-support base change with the direct-image
  base change for proper vertical maps
  (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`, blueprint
  `def-exchange-projection`);
- `Hʲ(Rf_*^Weil K) ≅ f_* Hʲ(K)` for finite `f`
  (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerStar_iso`): the pushforward along a
  finite morphism is exact, so `Rf_*` is computed levelwise and commutes with homology, and the
  derived base-change morphism of the Frobenius square induces the underived one on homology.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- **`Rf_! ≅ Rf_*` for Weil objects** along a proper morphism `f`: the isomorphism
`Rf_! ≅ Rf_*` (`boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`) is compatible with the
Frobenius structures, the compact-support base change of the Frobenius square being the
direct-image base change for proper vertical maps
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`). -/
theorem nonempty_weilLowerShriek_iso_weilLowerStar [IsProper f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) :
    Nonempty ((weilLowerShriek ℓ eX eY hf).obj K ≅ (weilLowerStar ℓ eX eY f hf).obj K) :=
  sorry

/-- **Homology of the pushforward of Weil objects along a finite morphism**: for finite `f`, the
Weil sheaf `Hʲ(Rf_*^Weil K)` for `e_Y` is the pushforward `f_* Hʲ(K)` of the Weil sheaf `Hʲ(K)`.
The pushforward along a finite morphism is exact, so `Rf_*` is computed levelwise and commutes
with homology, and on homology the derived base-change morphism of the Frobenius square is the
base-change morphism of module objects. -/
theorem nonempty_homologyFunctor_weilLowerStar_iso [IsFinite f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj
        ((weilLowerStar ℓ eX eY f hf).obj K) ≅
      (weilSheafLowerStar ℓ eX eY hf).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) :=
  sorry

/-- **Homology of the lower shriek of Weil objects along a finite morphism**:
`Hʲ(Rf_!^Weil K) ≅ f_* Hʲ(K)` as Weil sheaves for `e_Y`. -/
theorem nonempty_homologyFunctor_weilLowerShriek_iso [IsFinite f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj
        ((weilLowerShriek ℓ eX eY hf).obj K) ≅
      (weilSheafLowerStar ℓ eX eY hf).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) := by
  obtain ⟨i⟩ := nonempty_weilLowerShriek_iso_weilLowerStar ℓ eX eY hf K
  obtain ⟨i'⟩ := nonempty_homologyFunctor_weilLowerStar_iso ℓ eX eY hf K j
  exact ⟨(WeilBoundedConstructible.homologyFunctor ℓ eY j).mapIso i ≪≫ i'⟩

end AlgebraicGeometry.ProEtale.CondensedRing
