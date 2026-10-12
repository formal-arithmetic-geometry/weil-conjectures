module

public import Sheaf.CategoryTheory.SiteMorphismComposition
public import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf
import Sheaf.CategoryTheory.SiteEquivalenceMorphismOfSites
import Sheaf.Paper.SiteCoveringIsomorphicFamily

/-!
# Transport of morphisms of sites across equivalences

Source: literature/stacks-project/sites.tex, Definitions 00VH, 00WV, 00X1 and
Lemma 03CB (blueprint: lem-weil-pbc-site-equivalence-morphism-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: literature/stacks-project/sites.tex, Definitions 00VH, 00WV, 00X1
and Lemma 03CB (blueprint: lem-weil-pbc-site-equivalence-morphism-transport).

The proof transports continuity and exactness through the two equivalences, using
site-equivalence-is-morphism, site-morphism-composition, and invariance under
isomorphic covering families.  The natural isomorphism identifies the two
functors and hence identifies their sheaf pullbacks; exactness is invariant under
that identification.
-/
theorem site_equivalence_morphism_transport
    {A B C D : Type u}
    [SmallCategory A] [SmallCategory B] [SmallCategory C] [SmallCategory D]
    (JA : Precoverage A) (JB : Precoverage B)
    (JC : Precoverage C) (JD : Precoverage D)
    [JA.HasIsos] [JA.IsStableUnderComposition] [JA.IsStableUnderBaseChange]
    [JA.HasPullbacks]
    [JB.HasIsos] [JB.IsStableUnderComposition] [JB.IsStableUnderBaseChange]
    [JB.HasPullbacks]
    [JC.HasIsos] [JC.IsStableUnderComposition] [JC.IsStableUnderBaseChange]
    [JC.HasPullbacks]
    [JD.HasIsos] [JD.IsStableUnderComposition] [JD.IsStableUnderBaseChange]
    [JD.HasPullbacks]
    (p : A ⥤ C) (q : B ⥤ D)
    [p.IsEquivalence] [q.IsEquivalence]
    (hpcover : ∀ (X : A) (R : Presieve X),
      R ∈ JA X ↔ R.map p ∈ JC (p.obj X))
    (hqcover : ∀ (X : B) (R : Presieve X),
      R ∈ JB X ↔ R.map q ∈ JD (q.obj X))
    (u : C ⥤ D)
    (hucover : ∀ (X : C) (R : Presieve X),
      R ∈ JC X → R.map u ∈ JD (u.obj X))
    (hupullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ JC X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous JC.toGrothendieck JD.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u)
      JC.toGrothendieck JD.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u)
      JC.toGrothendieck JD.toGrothendieck)]
    (u' : A ⥤ B)
    (α : u' ⋙ q ≅ p ⋙ u) :
    (∀ (X : A) (R : Presieve X), R ∈ JA X →
      R.map u' ∈ JB (u'.obj X)) ∧
    (∀ (X Y Z : A) (R : Presieve X), R ∈ JA X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) u') ∧
    ∃ (_ : u'.IsContinuous JA.toGrothendieck JB.toGrothendieck),
      PreservesFiniteLimits (sheafPullback u' (Type u)
        JA.toGrothendieck JB.toGrothendieck) ∧
      PreservesFiniteColimits (sheafPullback u' (Type u)
        JA.toGrothendieck JB.toGrothendieck) := by
  sorry

end CategoryTheory
