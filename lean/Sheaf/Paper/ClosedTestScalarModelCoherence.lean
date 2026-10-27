module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams
import Sheaf.Paper.ClosedTestScalarUniversalCoherence
import Sheaf.Paper.ClosedTestScalarSectionCoherence
import Sheaf.Paper.ClosedTestScalarModelSquares
import Sheaf.Paper.ClosedTestModelMapNaturality

/-! # Universal coefficient coherence for closed-test section models

Source: Stacks Project, derived.tex, Tags 070I, 070Y and 09T5;
sites-cohomology.tex, Tags 07A6, 0D6D--0D6F and 0FPI; proetale.tex, Tag 09BL
(blueprint: lem-sfb-closed-test-scalar-model-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj S] [IsCommMonObj S]
  (c : Λ ⟶ S) [IsMonHom c]
private theorem map_coherence_of_sections (hs : SectionCoherence c)
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (α : K ⟶ (restrict c X).obj N) : MapCoherence c A a f h fZ w V K N α := by
  constructor
  · exact (derivedSectionArrow Λ h (testFibre f (liftedTest A a V))
      (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V)).naturality α
  · exact hs.2.2.1 h (testFibre f (liftedTest A a V))
      (testFibre fZ (closedTest A a V)) (fibreSectionArrow A a w V) N

/-- Universal scalar coherence for closed-test models.
Source: Stacks derived.tex, Tags 070I, 070Y and 09T5; sites-cohomology.tex,
Tags 07A6, 0D6D--0D6F, 0FPI; proetale.tex, Tag 09BL
(blueprint: lem-sfb-closed-test-scalar-model-coherence).

Proof plan (the nine steps of the node):
1. Use sk-def-sfb-coefficient-morphisms for the commuting coefficient squares.
   lem-sfb-internal-section-scalar-adjunction and
   lem-pd-section-derived-pushpull-normalization preserve the underlying sections,
   restriction of scalars, ordinary adjunctions, derived units and pullback compositors.
2. lem-sfb-exact-square-right-derived-unit applied to direct image and section evaluation
   gives delta and gamma in their forward directions. Their equations on every complex
   characterize them uniquely; re-resolve the restricted complex over the first ring.
3. lem-weil-pbc-ring-sheaf-change-adjunction identifies its forward comparison with delta
   by this uniqueness. Apply its adjunct equation to the identity and to the counit to
   obtain precisely the unit and counit clauses of UniversalCoherence.
4. Ordinary scalar restriction commutes with pullback composition and restriction to a
   slice on the underlying sheaves. Exact termwise descent gives the compositor clause.
   lem-sfb-unbounded-sections-localization and
   lem-weil-pbc-ringed-derived-slice-localization give the localized scalar squares,
   normalized by the literal section identity and these same universal units.
5. Expand exchange as the unit, canonical pullback square and counit. Naturality of delta and the
   preceding unit, compositor and counit equations give its displayed coefficient square.
6. lem-sfb-closed-test-unit-evaluation gives the actual closed unit section and its inverse
   at the two contractible tests. Restriction leaves the underlying section untouched,
   so the inverse also commutes. lem-sfb-closed-test-kinjective-section-models gives the
   source and target isomorphisms, with sourceModel in the forward unit direction and
   localizationModel normalized by the degreewise identity. Paste their scalar squares.
7. lem-sfb-closed-test-chain-mate-restriction identifies the exchange with chainRestriction,
   namely Q of the actual unit section followed by j(T0). Paste step 6 with step 5 to get
   its coefficient square. This inverts only model and closed-unit isomorphisms.
8. lem-sfb-closed-test-localized-model-coherence gives the left-hand cospan square for
   each actual map K to Res N. Paste it with step 7. The Hom bijection of
   lem-weil-pbc-kinjective-hom-derived shows the result is independent of representatives;
   modelMap depends only on the derived arrow, so homotopic maps give the same arrow.
9. The ordinary extension/restriction adjunction unit is m maps to 1 tensor m, as preserved
   by lem-sfb-internal-section-scalar-adjunction. Apply step 8 to scalarUnit in degree
   zero. Both complexes are bounded below without assuming the coefficient map flat.
   No preservation of K-injectives by restriction or invertibility of delta or gamma is used.
-/
theorem closed_test_scalar_model_coherence :
    UniversalCoherence c ∧ SectionCoherence c ∧
    ∀ (A : Type u) [CommRing A] (a : Ideal A)
      {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
      (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
      (w : IsPullback h fZ f (closedMap A a))
      (V : (Spec (.of (A ⧸ a))).AffineProEt)
      [IsWContractibleRing Γ(V.left, ⊤)]
      [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)],
      (∀ (N : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
          (M : TestModel S h N.obj)
          (P : TestModel Λ h ((restrict c X).obj N.obj)),
        ModelCoherence c A a f h fZ w V N.obj M P) ∧
      (∀ (K : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
          (N : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
          (α : K.obj ⟶ (restrict c X).obj N.obj)
          (M : TestModel Λ h K.obj)
          (P : TestModel Λ h ((restrict c X).obj N.obj)),
        MapCoherence c A a f h fZ w V K.obj N.obj α ∧
          ModelMapCoherence A a f h fZ w V α M P) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
        MapCoherence c A a f h fZ w V ((DerivedCategory.singleFunctor _ 0).obj M)
          ((DerivedCategory.singleFunctor _ 0).obj
            ((Mod.extendScalars (coefficientMap c X)).obj M)) (scalarUnit c X M) ∧
        ∀ (P : TestModel Λ h ((DerivedCategory.singleFunctor _ 0).obj M))
          (P' : TestModel Λ h ((restrict c X).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((Mod.extendScalars (coefficientMap c X)).obj M)))),
          ModelMapCoherence A a f h fZ w V (scalarUnit c X M) P P') := by
  have hc := closed_test_scalar_universal_coherence c
  have hs := closed_test_scalar_section_coherence c
  refine ⟨hc, hs, ?_⟩
  intro A _ a X XZ _ f h fZ w V _ _
  refine ⟨?_, ?_, ?_⟩
  · intro N M P
    exact closed_test_scalar_model_squares c hc hs A a f h fZ w V N M P
  · intro K N α M P
    exact ⟨map_coherence_of_sections c hs A a f h fZ w V K.obj N.obj α,
      closed_test_model_map_naturality A a f h fZ w V α M P⟩
  · intro M
    refine ⟨map_coherence_of_sections c hs A a f h fZ w V _ _ (scalarUnit c X M), ?_⟩
    intro P P'
    exact closed_test_model_map_naturality A a f h fZ w V (scalarUnit c X M) P P'

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
