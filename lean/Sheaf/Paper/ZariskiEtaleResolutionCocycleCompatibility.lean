module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Intermediate cocycle-comparison component for the Zariski–étale resolution comparison.

The existence of the displayed additive equivalences is the termwise sheafification,
free-abelian, and Yoneda calculation from Stacks Project, Section 01FT.

STATEMENT-DISPUTED: the theorem quantifies over arbitrary additive equivalences e₁ and e₂;
composing either with negation generally changes one side only, so the claimed equality is false
without coherence hypotheses.
(blueprint: lem-weil-pbc-zariski-etale-resolution-cocycle-compatibility) -/
theorem zariski_etale_resolution_cocycle_compatibility
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (q : ℕ) (V : X.Opens) :
    ∀ (e₁ : Sheaf.H' ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) q V ≃+
        ↑(HomologicalComplex.homology
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).obj R.cocomplex) q))
      (e₂ : Sheaf.H' F q (i.obj V) ≃+
        ↑(HomologicalComplex.homology
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).obj
                (((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                  (Opens.grothendieckTopology X.carrier)
                    X.smallEtaleTopology).mapHomologicalComplex
                       (ComplexShape.up ℕ)).obj I.cocomplex)) q)),
      ∀ (a : (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ R.cocomplex.X q)
        (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
        (c : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q)
        (hc : c ≫ I.cocomplex.d q (q + 1) = 0),
        (b.f q).hom.app (op V) ((a.hom.app (op V)).hom
          (((toSheafify (Opens.grothendieckTopology X.carrier)
            (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
              (FreeAbelianGroup.of (𝟙 V)))) =
        ((c.hom.app (op (i.obj V))).hom
          (((toSheafify X.smallEtaleTopology
            (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
              (FreeAbelianGroup.of (𝟙 (i.obj V))))) →
        e₂ (I.extMk c (q + 1) rfl hc) =
        (HomologicalComplex.homologyMap
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).map b) q).hom (e₁ (R.extMk a (q + 1) rfl ha))  := by sorry
