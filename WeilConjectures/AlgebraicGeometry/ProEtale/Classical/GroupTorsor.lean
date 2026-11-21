/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import WeilConjectures.CategoryTheory.Sites.GroupTorsor
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Pro-étale torsors under classical groups

Let `G` be a sheaf of groups on the small pro-étale site of a scheme `X` whose underlying sheaf
of sets is classical, i.e. isomorphic to the comparison pullback `ν_X^*` of an étale sheaf. We
show that every `G`-torsor is classical and has sections on an étale covering of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.isProEtaleClassical_groupTorsor`: a torsor under a classical sheaf
  of groups is classical.
- `AlgebraicGeometry.Scheme.exists_etale_coversTop_groupTorsor`: a torsor under a classical
  sheaf of groups has sections over the members of an étale covering of `X`.

## Implementation details

A section `s` of the torsor `P` over `V` identifies the restrictions of `P` and of `G` to `V`,
by `g ↦ g • s`. The restriction of the classical sheaf `G` to `V` is classical, so `P` is
locally classical, hence classical by
`AlgebraicGeometry.Scheme.proEtale_locallyClassical_etaleCover`, which also gives the étale
covering.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {G : Sheaf (ProEt.topology X) GrpCat.{u + 1}}

/-- A torsor under a sheaf of groups with classical underlying sheaf of sets is locally
classical. -/
theorem isProEtaleLocallyClassical_groupTorsor
    (hG : IsProEtaleClassical X
      ((sheafCompose _ (CategoryTheory.forget GrpCat.{u + 1})).obj G))
    (P : Sheaf.GroupTorsor G) : IsProEtaleLocallyClassical X P.sheaf := by
  refine ⟨Σ V : X.ProEt, P.sheaf.obj.obj (op V), Sigma.fst, fun W ↦ ?_,
    fun ⟨V, s⟩ ↦ ?_⟩
  · refine (ProEt.topology X).superset_covering ?_ (P.nonemptySieve_mem W)
    rintro Z f ⟨t⟩
    exact ⟨⟨Z, t⟩, ⟨𝟙 Z⟩⟩
  · obtain ⟨F, ⟨e⟩⟩ := hG.restriction V
    let r : (proEtaleSetRestriction X V).obj
          ((sheafCompose _ (CategoryTheory.forget GrpCat.{u + 1})).obj G) ≅
        (proEtaleSetRestriction X V).obj P.sheaf :=
      (fullyFaithfulSheafToPresheaf _ _).preimageIso
        (P.isoOfSection (ProEt.sliceFrom X V ⋙ Over.forget V)
          (Functor.whiskerLeft (ProEt.sliceFrom X V) (Over.forgetCocone V).ι) s)
    exact ⟨F, ⟨r.symm ≪≫ e⟩⟩

/-- A torsor under a sheaf of groups on the small pro-étale site of `X` whose underlying sheaf
of sets is classical is itself classical. -/
theorem isProEtaleClassical_groupTorsor
    (hG : IsProEtaleClassical X
      ((sheafCompose _ (CategoryTheory.forget GrpCat.{u + 1})).obj G))
    (P : Sheaf.GroupTorsor G) : IsProEtaleClassical X P.sheaf :=
  (proEtale_locallyClassical_etaleCover X P.sheaf).1
    (isProEtaleLocallyClassical_groupTorsor hG P)

/-- A torsor under a sheaf of groups on the small pro-étale site of `X` whose underlying sheaf
of sets is classical has sections over the members of an étale covering of `X`. -/
theorem exists_etale_coversTop_groupTorsor
    (hG : IsProEtaleClassical X
      ((sheafCompose _ (CategoryTheory.forget GrpCat.{u + 1})).obj G))
    (P : Sheaf.GroupTorsor G) :
    ∃ (I : Type (u + 1)) (Y : I → X.Etale), X.smallEtaleTopology.CoversTop Y ∧
      ∀ i, Nonempty (P.sheaf.obj.obj (op ((toProEt X).obj (Y i)))) := by
  refine (proEtale_locallyClassical_etaleCover X P.sheaf).2.2
    (isProEtaleLocallyClassical_groupTorsor hG P)
    ⟨Σ V : X.ProEt, P.sheaf.obj.obj (op V), Sigma.fst, fun W ↦ ?_, fun i ↦ ⟨i.2⟩⟩
  refine (ProEt.topology X).superset_covering ?_ (P.nonemptySieve_mem W)
  rintro Z f ⟨t⟩
  exact ⟨⟨Z, t⟩, ⟨𝟙 Z⟩⟩

end AlgebraicGeometry.Scheme
