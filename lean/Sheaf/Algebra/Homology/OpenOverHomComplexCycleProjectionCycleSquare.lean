module
public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions
/-! Cycle projection comparison square.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square). -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonCategoryCycle
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonPreadditiveCycle
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000)
    openOverHomComplexCycleProjectionComparisonAbelianCycle
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf
/-- Restriction of a Hom complex has a chain isomorphism compatible with its projection.
Source: Stacks Project, Tags 0A8X and 08DL, product construction of the Hom complex.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square).
Proof: Restriction to an open preserves products, computed sectionwise, and passing
through the open-site equivalence preserves limits. Apply the universal properties
of the limiting product fans of the fixed Hom projections to the isomorphisms e.
This constructs mutually inverse degreewise maps, carrying every product projection
to its e comparison. To check the chain-map equation, compose with every projection:
the signed differential formula for Hom complexes reduces it to the two naturality
equations he and additivity of restriction. Thus the maps form a chain isomorphism.
Its projection identity at p = -n and q = 0 is the displayed equation. The same
argument applies to empty opens and unbounded complexes. -/
theorem openOver_homComplex_chain_projection_iso (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens)
    (e : ∀ M N : X.Modules,
      (Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
        V.toScheme.ringCatSheaf W).obj (SheafOfModules.homObj (R := X.sheaf) M N) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
          V.toScheme.ringCatSheaf W).obj M)
        ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
          V.toScheme.ringCatSheaf W).obj N))
    (he : ∀ (M M' N N' : X.Modules) (f : M' ⟶ M) (g : N ⟶ N'),
      (Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
        V.toScheme.ringCatSheaf W).map (SheafOfModules.homObjMap
          (R := X.sheaf) f g) ≫ (e M' N').hom =
        (e M N).hom ≫ SheafOfModules.homObjMap
          (R := V.toScheme.sheaf.over W)
          ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
            V.toScheme.ringCatSheaf W).map f)
          ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
            V.toScheme.ringCatSheaf W).map g))
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let P := homComplex (R := X.sheaf) T J
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let Q := homComplex (R := V.toScheme.sheaf.over W) A K
    let π := (Classical.choose (homComplex_projections_exists
      (R := V.toScheme.sheaf.over W))) A K n (-n) 0 (by omega)
    ∃ h : (moduleOpenOverComplexFunctor X V W).obj P ≅ Q,
      h.hom.f n ≫ π = F.map (homologyEvaluationProjection X T J n) ≫
        (e (T.X (-n)) (J.X 0)).hom := by sorry
end CategoryTheory
