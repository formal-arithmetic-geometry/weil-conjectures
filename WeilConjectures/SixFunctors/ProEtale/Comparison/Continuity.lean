/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Pro.HypercoverColimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-!
# Continuity of the comparison pullback

Let `S` be a scheme and `F` an étale sheaf on `S` with values in a Grothendieck abelian category.
If `Y = limᵢ Dᵢ` is a cofiltered limit of quasi-compact quasi-separated étale `S`-schemes with
affine transition maps, then the sections of the comparison pullback `ν^* F` over `Y` are the
filtered colimit of the sections over the `Dᵢ`
(`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Continuity of the comparison pullback.** For a cofiltered diagram `K` of quasi-compact
quasi-separated étale `S`-schemes with affine transition maps and a cone `c` over it in the
pro-étale site whose underlying cone of schemes is a limit, the sections of `ν^* F` over the
cone point are the filtered colimit of the sections over the `Kᵢ`. -/
theorem isColimit_comparisonUpperStar_mapCocone {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (K : I ⥤ S.Etale)
    [∀ i, CompactSpace (K.obj i).left] [∀ i, QuasiSeparatedSpace (K.obj i).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (K.map g).left]
    (c : Cone (K ⋙ toProEt S))
    (hc : IsLimit ((ProEt.forget S ⋙ CategoryTheory.Over.forget S).mapCone c)) :
    Nonempty (IsColimit (((comparisonUpperStar A S).obj F).obj.mapCocone c.op)) :=
  sorry

end AlgebraicGeometry.ProEtale
