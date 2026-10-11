module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Étale and Zariski cohomology over strictly henselian schemes

Source: literature/stacks-project/etale-cohomology.tex, Lemma 09AX
(blueprint: lem-weil-pbc-gabber-strict-henselian-zariski-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- The comparison from Zariski to étale cohomology is an isomorphism when all
local rings of the scheme are strictly henselian.
Source: literature/stacks-project/etale-cohomology.tex, Lemma 09AX
(blueprint: lem-weil-pbc-gabber-strict-henselian-zariski-comparison).
The functor `i` is the inclusion of the small Zariski site into the small étale
site. Its continuous direct image is `ε_* F`; `c` is the pullback followed by
its counit, and is the identity in degree zero. -/
theorem strictHenselian_zariski_etale_comparison
    {X : Scheme.{u + 1}}
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : ∀ q : ℕ,
      Sheaf.H'
          ((i.sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F)
          q ⊤ ⟶
        Sheaf.H' F q (i.obj ⊤)) :
    ∀ q : ℕ, IsIso (c q) := by
  sorry
