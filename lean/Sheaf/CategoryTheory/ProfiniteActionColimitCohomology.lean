module

public import Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.CategoryTheory.GrothendieckSheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Filtered colimits and cohomology on the profinite action site

Source: Stacks Project, Cohomology on Sites, Tag 09YP, lemma-colimit;
blueprint direct-image stability, paragraph (3), filtered passage
(blueprint: lem-sfb-profinite-action-colimit-cohomology).

The comparison is the actual map from the pointwise colimit of cohomology presheaves,
induced by the given cocone. In particular its components have the original stage legs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction.CoherentPresentation

variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]
  (P : SetPresentation J) (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
  (Φ : ModulePresentation J P R)

/-- Transport through the normalized action-site equivalence and forget scalars.
Source: Tag 09YP, coefficient transport through the coherent presentation
(blueprint: lem-sfb-profinite-action-colimit-cohomology). -/
def abelianCoefficients : ActionModule R J ⥤
    Sheaf (coverage J).toGrothendieck AddCommGrpCat.{u + 1} :=
  Φ.data.equivalence.functor ⋙ SheafOfModules.toSheaf _

variable [HasExt.{u + 1} (Sheaf (coverage J).toGrothendieck AddCommGrpCat.{u + 1})]

/-- Object cohomology, retaining its restriction maps and coefficient functoriality.
Source: Tag 09YP, object cohomology, using the recorded sites-and-cohomology convention
(blueprint: lem-sfb-profinite-action-colimit-cohomology). -/
def actionCohomology (q : ℕ) : ActionModule R J ⥤ (Space J)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  abelianCoefficients J P R Φ ⋙ Sheaf.cohomologyPresheafFunctor _ q

variable {I : Type (u + 1)} [SmallCategory I]
  {N : I ⥤ ActionModule R J}

/-- The coprojection-induced comparison, with an actual pointwise colimit as source.
No equivalence, cocone, or comparison arrow is chosen from an existence theorem.
Source: Tag 09YP, canonical comparison and its original legs
(blueprint: lem-sfb-profinite-action-colimit-cohomology). -/
def actionCohomologyColimitComparison (c : Cocone N) (q : ℕ) :
    (pointwiseCocone (N ⋙ actionCohomology J P R Φ q)).pt ⟶
      (actionCohomology J P R Φ q).obj c.pt :=
  (pointwiseIsColimit (N ⋙ actionCohomology J P R Φ q)).desc
    ((actionCohomology J P R Φ q).mapCocone c)

/-- Transported filtered colimits commute with object cohomology, with the specified
legs, restrictions, diagram maps, and restriction to trivial-action parameters.
Source: Stacks Project, Cohomology on Sites, Tag 09YP, lemma-colimit; blueprint
paragraph (3), filtered passage
(blueprint: lem-sfb-profinite-action-colimit-cohomology).

Proof:
1. The coherent-presentation theorem gives the small finite-cover action site, finite
   limits, singleton isomorphism covers, and stability under pullback and composition.
   Its normalized module equivalence preserves the given colimit cocone (Tag 0038).
2. Abelian groups are Z-modules, hence Grothendieck by the ring-modules theorem.
   The Grothendieck sheafification theorem supplies abelian sheafification on this site.
3. Apply clause (3) of moduleSheaves_colimits_forgetful (Tag 03DB) to the ring sheaf
   supplied by the presentation: forgetting scalars preserves precisely these legs.
4. Apply lem-sfb-finite-cover-derived-presheaf-continuity to that abelian cocone.
   Homology and evaluation of its derived comparison give the displayed pointwise
   comparison, an isomorphism in each degree, with the original coprojections.
5. Restriction and coefficient naturality commute on every stage leg. The universal
   property of the colimit gives both naturality squares. Restrict the resulting
   presheaf isomorphism along the trivial-action functor; its inverse also restricts.
-/
theorem profiniteAction_colimit_cohomology [IsFiltered I]
    (c : Cocone N) (hc : IsColimit c) :
    Nonempty (IsColimit (Φ.data.equivalence.functor.mapCocone c)) ∧
    Nonempty (IsColimit ((abelianCoefficients J P R Φ).mapCocone c)) ∧
    ∀ q : ℕ,
      IsIso (actionCohomologyColimitComparison J P R Φ c q) ∧
      (∀ T : Space J, IsIso ((actionCohomologyColimitComparison J P R Φ c q).app (op T))) ∧
      (∀ (i : I) (T : Space J),
        colimit.ι ((N ⋙ actionCohomology J P R Φ q).flip.obj (op T)) i ≫
          (actionCohomologyColimitComparison J P R Φ c q).app (op T) =
            ((actionCohomology J P R Φ q).map (c.ι.app i)).app (op T)) ∧
      (∀ (T T' : Space J) (f : T' ⟶ T),
        (pointwiseCocone (N ⋙ actionCohomology J P R Φ q)).pt.map f.op ≫
            (actionCohomologyColimitComparison J P R Φ c q).app (op T') =
          (actionCohomologyColimitComparison J P R Φ c q).app (op T) ≫
            ((actionCohomology J P R Φ q).obj c.pt).map f.op) ∧
      (∀ (N' : I ⥤ ActionModule R J) (c' : Cocone N') (_hc' : IsColimit c')
          (a : N ⟶ N') (b : c.pt ⟶ c'.pt),
        (∀ i : I, c.ι.app i ≫ b = a.app i ≫ c'.ι.app i) →
        ∀ T : Space J,
          colim.map ((Functor.whiskerRight a (actionCohomology J P R Φ q)).flipApp (op T)) ≫
              (actionCohomologyColimitComparison J P R Φ c' q).app (op T) =
            (actionCohomologyColimitComparison J P R Φ c q).app (op T) ≫
              ((actionCohomology J P R Φ q).map b).app (op T)) ∧
      IsIso (Functor.whiskerLeft ((AsSmall.up ⋙ trivialParameter J).op)
        (actionCohomologyColimitComparison J P R Φ c q)) := by
  sorry

end Profinite.CondensedAction.CoherentPresentation
