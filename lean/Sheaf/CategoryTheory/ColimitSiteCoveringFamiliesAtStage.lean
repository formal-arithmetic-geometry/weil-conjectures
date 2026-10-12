module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Precoverage

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- One finite layer of covering families lifts over targets already fixed at a stage.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram observation.
(blueprint: lem-weil-pbc-colimit-site-covering-families-at-stage)

Proof: For each family use hQ to choose a finite covering stage presieve with the
specified image. For every requested indexed arrow choose a member of that presieve
mapping to it, with its source equality. Conversely choose an index for each member
of the stage presieve with the same image. Both collections are finite, including
when indices repeat. Filteredness gives a common stage above these stages and j₀.
Eventual equality in the object colimit aligns each presieve target with the
transition image of T₀ i. Eventual equality in the arrow colimit identifies every
presieve member with its selected indexed representative, including the endpoint
objects. Move to a common successor where all these finitely many equalities hold.
Transport along the endpoint equalities to obtain a i t into the transition of
T₀ i. The comparisons in both directions show that this indexed presieve equals
the transition image of the original covering presieve; hcover makes it covering.
Cocone naturality gives each prescribed image-arrow equality. If a family's index
is empty, its representing presieve is empty because its image is empty, so only
its target must be aligned. If the family of targets is empty, take j₀ and its
identity transition. This construction has only one layer of arrows, and does not
involve composing or simultaneously lifting nested coverings. -/
theorem colimit_site_covering_families_at_stage
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X → Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V)) (Q : Precoverage V.pt)
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X)
        (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    {κ : Type u} [Finite κ] (j₀ : J) (T₀ : κ → F.obj j₀)
    {S : κ → V.pt} (hT₀ : ∀ i, (V.ι.app j₀).toFunctor.obj (T₀ i) = S i)
    {τ : κ → Type u} [∀ i, Finite (τ i)] {X : ∀ i, τ i → V.pt}
    (f : ∀ i t, X i t ⟶ S i)
    (hf : ∀ i, Presieve.ofArrows (X i) (f i) ∈ Q (S i)) :
    ∃ (j : J) (e : j₀ ⟶ j) (A : ∀ i, τ i → F.obj j)
      (a : ∀ i t, A i t ⟶ (F.map e).toFunctor.obj (T₀ i)),
      (∀ i, Presieve.ofArrows (A i) (a i) ∈ P j ((F.map e).toFunctor.obj (T₀ i))) ∧
      (∀ i t, Arrow.mk ((V.ι.app j).toFunctor.map (a i t)) = Arrow.mk (f i t)) := by
  sorry

end CategoryTheory
