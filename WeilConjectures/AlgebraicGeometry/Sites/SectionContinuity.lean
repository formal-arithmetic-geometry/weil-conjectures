/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsLimit

/-!
# Continuity of sections of étale sheaves at inverse limits

Let `h₁ : T ⟶ S` and `h₂ : S ⟶ R` be morphisms of schemes. For an abelian étale sheaf `G` on
`R`, the unit of `h₁^* ⊣ h₁_*` induces a comparison map
`h₂_* h₂^* G ⟶ (h₁ ≫ h₂)_* (h₁ ≫ h₂)^* G`
(`AlgebraicGeometry.Etale.unitComparison`), compatible with the units of `h₂` and `h₁ ≫ h₂`.
On sections over an étale `R`-scheme `W` it is the pullback of sections of `G|_{W ×_R S}` to
`W ×_R T`.

For a cofiltered system `(Dⱼ)` of quasi-compact quasi-separated schemes over `R` with affine
transition maps and limit `X`, the comparison maps exhibit the sections of the pullback of `G`
over `W ×_R X` as the colimit of the sections over the `W ×_R Dⱼ`, for `W` quasi-compact and
quasi-separated (`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`). This is
blueprint `lem-weil-pbc-etale-section-continuity`, which belongs to the subsection
`sk-prop-h2`; its proof is not formalised here.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

variable {R : Scheme.{u}} {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
  (π : D ⟶ (Functor.const J).obj R) (c : Cone D) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

/-- **Continuity of sections at an inverse limit.** Let `(Dⱼ)` be a cofiltered system of
quasi-compact quasi-separated schemes over `R` with affine transition maps, with limit `X`, let
`G` be an abelian étale sheaf on `R` and `W` a quasi-compact quasi-separated étale `R`-scheme,
where `R` is quasi-separated, so that all the `W ×_R Dⱼ` are quasi-compact and quasi-separated
(as for the étale objects of finite presentation of the blueprint; without it the statement
fails).
Then the sections of the pullback of `G` over `W ×_R X` are the filtered colimit of the sections
of the pullbacks of `G` over the `W ×_R Dⱼ`: every section over `W ×_R X` comes from some
`W ×_R Dⱼ`, and a section over `W ×_R Dⱼ` which vanishes on `W ×_R X` already vanishes on some
`W ×_R Dⱼ'`, `j' ⟶ j`. The sections of the pullback of `G` over `W ×_R Dⱼ` are written as the
sections of `πⱼ_* πⱼ^* G` over `W`, and the transition maps are
`AlgebraicGeometry.Etale.unitComparison`.
(blueprint: `lem-weil-pbc-etale-section-continuity`) -/
theorem unitComparison_app_isColimit_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    (∀ t : ((P)_*[AddCommGrpCat.{u + 1}].obj
        ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W),
      ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
        (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t) ∧
    ∀ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0 →
        ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
          (by simp) G).hom.app (op W) s = 0 :=
  sorry

/-- **Continuity of sections at an inverse limit, surjectivity**: the first half of
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`. -/
theorem unitComparison_app_surjective_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (t : ((P)_*[AddCommGrpCat.{u + 1}].obj ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)) :
    ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t :=
  (unitComparison_app_isColimit_of_isLimit D π c P hP hc G W).1 t

/-- **Continuity of sections at an inverse limit, injectivity**: the second half of
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`. -/
theorem exists_unitComparison_app_eq_zero_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (j : J)
    (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W))
    (hs : (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0) :
    ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
      (by simp) G).hom.app (op W) s = 0 :=
  (unitComparison_app_isColimit_of_isLimit D π c P hP hc G W).2 j s hs

end Etale

end AlgebraicGeometry
