module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
/-- Then every member of every Q-cover has a pullback along every arrow into its target.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-colimit-site-covering-axioms-haspullbacks)

Proof: Fix a Q-cover R, a member f of R, and an arbitrary arrow g into
its target. Represent R by a stage covering S using hQ and f by a member of S
using the definition of Presieve.map. Represent g in the arrow colimit, move
its representative and S to a common stage, and enforce their common target
using eventual equality in the object colimit. The image of S remains covering
by hcover, and the representative of f is a member of that image. Thus stage
HasPullbacks supplies a pullback of the represented f and g. Every subsequent
transition preserves it by hpullback. Its image in the cocone category is a
pullback: represent a test cone's vertex and legs at a common later stage and
make its endpoint and cone equations hold there by eventual equality in the
object and arrow colimits. Preservation of the stage pullback gives a mediating
arrow whose cocone image factors the cone. For uniqueness represent any two
mediating arrows and make their factorization equations hold at a common later
stage; the preserved pullback there equates them. Their cocone images therefore
agree. This establishes a pullback of f and g after the endpoint transports.
Applying this argument to every R, g, and member f gives Q.HasPullbacks. There
is nothing to construct for an empty covering. -/
theorem colimit_site_covering_axioms_HasPullbacks
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)) :
        Q.HasPullbacks := by sorry

end CategoryTheory
