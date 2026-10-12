module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.CategoryTheory.FilteredColimitPreservesPullback

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- A finite family of prescribed covering pullback squares admits a common stage presentation.
The conclusion supplies a stage cover and pullback squares, without asserting that their first
projections cover. In particular no stage base-change or composition axiom is assumed.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram and pullback paragraphs.
(blueprint: lem-weil-pbc-colimit-site-covering-pullback-stage-presentation)

Proof: The equality himage represents the indexed family by the finite stage presieve R₀.
For each f i choose a representing arrow in R₀, including its endpoint equalities. Conversely,
for each arrow of R₀ choose an index whose image is that arrow's image. There are finitely many
choices in both directions by Finite ι and hfinite. Lift the objects, g and these equalities
using surjectivity and eventual equality of the object and arrow colimits. Move everything
above j₀ to a common stage and impose the finitely many equalities. The resulting indexed
presieve equals the transition image of R₀, so is covering by hcover; its cocone image is f.
Form its stage pullbacks along the lifted g. Each covering arrow belongs to this stage presieve,
so hpullback preserves its pullback under every further transition. The limiting-cone argument
of filteredColimit_preservesPullback makes its cocone image a pullback. Uniqueness of pullbacks
gives an isomorphism from each prescribed vertex P' i to the corresponding image pullback,
commuting with both projections. Lift the vertices, these isomorphisms and their inverses,
and enforce both inverse equations and both leg equations at one later stage by eventual
equality. Transport the preserved stage pullbacks along these stage isomorphisms. Their first
projections now have precisely the prescribed cocone images. Mapping the indexed presieve
and transporting its target equality gives the final presieve equality. The transitioned
source family remains covering by hcover. For an empty index, himage forces R₀ to be empty;
lift only g and its endpoints, so all square and leg conditions are vacuous. No covering
property of the first projections is used in this construction. -/
theorem colimit_site_covering_pullback_stage_presentation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasPullbacks]
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
    (j₀ : J) (T₀ : F.obj j₀) (R₀ : Presieve T₀) (hR₀ : R₀ ∈ P j₀ T₀)
    {ι : Type (max u u)} [Finite ι] {S : V.pt} {X : ι → V.pt}
    (e₀ : (V.ι.app j₀).toFunctor.obj T₀ = S) (f : ∀ i, X i ⟶ S)
    (himage : e₀ ▸ R₀.map (V.ι.app j₀).toFunctor = Presieve.ofArrows X f)
    {Y : V.pt} (g : Y ⟶ S) {P' : ι → V.pt}
    (p₁ : ∀ i, P' i ⟶ Y) (p₂ : ∀ i, P' i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    ∃ (j : J) (T : F.obj j) (A : ι → F.obj j) (a : ∀ i, A i ⟶ T)
      (B : F.obj j) (b : B ⟶ T) (D : ι → F.obj j)
      (q₁ : ∀ i, D i ⟶ B) (q₂ : ∀ i, D i ⟶ A i)
      (e : (V.ι.app j).toFunctor.obj B = Y),
      Presieve.ofArrows A a ∈ P j T ∧
      (∀ i, IsPullback (q₁ i) (q₂ i) b (a i)) ∧
      e ▸ (Presieve.ofArrows D q₁).map (V.ι.app j).toFunctor =
        Presieve.ofArrows P' p₁ := by
  sorry

end CategoryTheory
