# AlgebraicGeometry.Etale.StrictHenselizationRestriction retirement

## Reason

The queue and coord/retire-items.tsv assign retirement of the already sorry-free SHEAF
restriction twin. The prior return correctly ruled out redirecting its consumers to the
upstream strictLocalization API: those consumers use the actual small coordinate-ring
colimit scheme. The present packet retires all seven specialized declarations, retains
only the necessary geometric cone data, and obtains restriction from a new general
colimit-descent API. It does not copy the upstream restriction into a compatibility module.

The general API applies to every morphism T -> S and every initial pointed-neighbourhood
diagram with compatible sections of its pullbacks. The Leray construction is generalized
to every morphism Y -> T with exact global sections on T. The existing, independently
proved strictHenselizationScheme_globalSections_preservesFiniteColimits supplies exactness
for the small model. The unused specialized cohomology-comparison definition is removed.

## Old

The following signatures occur in namespace AlgebraicGeometry.Etale with
`{S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`.

```lean
noncomputable def strictHenselizationNeighbourhoodSection
    (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)) ⟶
      (Scheme.strictHenselizationStructuralMap s).Etale.obj
        ((Scheme.AffineEtale.Spec S).obj
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)

noncomputable def strictHenselizationSectionRestriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op ((Scheme.AffineEtale.Spec S).obj
        ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)) ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj F)

def IsStrictHenselizationStalkRestriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj F)) : Prop

theorem existsUnique_strictHenselizationStalkRestriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ∃! r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj F),
      IsStrictHenselizationStalkRestriction s F r

theorem strictHenselization_globalSections_preservesFiniteColimits :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1})

noncomputable def strictHenselizationLerayHomologyIso
    {X : Scheme.{v}} (f : X ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus
      (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        AddCommGrpCat.{v + 1})) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).obj K)) ≅
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) q).obj
      (DerivedCategory.Plus.ι.obj K)

noncomputable def strictHenselizationCohomologyComparison
    {X : Scheme.{v}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) (q : ℕ) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
      ((upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)).obj
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ⟶
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) (q : ℤ)).obj
      ((DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F)))
```

## New

The canonical node def-weil-pbc-strict-henselization-restriction is attached to the
unchanged adopted source module WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction.
The retired SHEAF module is listed in deleted.txt. All its direct live importers are
adapted in this packet. No source-tree declaration, signature, attribute, import, or proof
is changed or removed.

The new public interfaces are:

- PointedEtaleSectionCone g N: initiality and compatible sections of g's pullbacks.
- PointedEtaleSectionCone.restriction, IsRestriction, existsUnique_restriction:
  the unit-section restriction formula and its stalk-colimit universal property.
- strictLocalNeighbourhoodSection and strictLocalSectionCone: only the geometric
  pullback sections for the actual small-colimit scheme and their compatibility.
- exactGlobalSectionsLerayHomologyIso h t q K: the canonical exact-global-sections/Leray
  composite for an arbitrary base with exact global sections.

The generic restriction uses exactly the original section formula. Its specialization's
section maps and germ predicate are definitionally equal to the former ones. The generic
Leray specialization is definitionally equal to the former composite, including its
normalization. Although the colimit-descent proof is generalized, uniqueness of the
specified germ map proves equality of the maps selected with Classical.choose. Consequently
etaleStalkSpecialization, localAcyclicityAlpha, and the derived source germ construction
keep their mathematical maps. A temporary Lean comparison probe checks these facts against
the original interface and is removed from the delivered packet.

These data are not selected from an unproved existence theorem. Every construction and
proof in the new modules is complete. The existing small-model exactness instance is used
instead of duplicating that theorem or its local-ring proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationRestriction | M2 | Withdraw the seven-declaration twin and redirect its node to the existing source realization. |
| Sheaf.AlgebraicGeometry.EtaleStalkSpecialization | unclaimed | Construct specialization from the unique restriction supplied by strictLocalSectionCone; preserve its section and germ factors. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf | unclaimed | Construct localAcyclicityAlpha from the same unique germ restriction, with derived cohomology imported explicitly. |
| Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms | unclaimed | Choose the unique generic restriction for the source homology sheaf; preserve the source isomorphism and germ legs. |
| Sheaf.AlgebraicGeometry.StrictLocalConstantComparison | unclaimed | Use the generic restriction predicate in the existing constant-sheaf comparison proof. |
| Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso | unclaimed | Express its germ hypothesis using the definitionally equal generic predicate and adapt the component calculation. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Remove the retired import, import base-change definitions explicitly, and pin the adapted transitive proof dependencies. |
| Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData | unclaimed | Use the generic Leray composite with the existing small-model exactness instance; preserve the target isomorphism. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray | unclaimed | Use the existing small-model exactness instance and explicit derived-functor imports in place of the retired import. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | Use the existing small-model exactness instance in the cocycle restriction formulas and proofs. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeGlobalSections | unclaimed | Use the existing exactness instance and unfold the generalized Leray composite in the original coherence calculation. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | Use the existing small-model exactness instance in the derived exchange and Leray calculation. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | Use the existing small-model exactness instance in the factorization proof. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | Use generic component restrictions, their unique germ descent and the existing exactness instance; preserve the natural transformation. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalSectionsUnitLeray | unclaimed | Use the existing small-model exactness instance and explicit derived-functor imports in the original-model coherence calculation. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Unfold the generic component restriction and use the geometric section of the small-model cone in the mate calculation. |

| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit | unclaimed | Audited, unchanged: its colimit cocone uses strictLocalCohomologySourceIso and source legs, whose uniquely specified germ map is preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | Audited, unchanged: the complex restriction and target Leray comparison have the same component formulas after specialization. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Audited, unchanged: uses strictLocalBaseChangeTargetIso as the same canonical Leray composite; its mate calculation is preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | unclaimed | Audited, unchanged: uses the hom and inverse of the preserved target comparison, together with the same representative sections comparison. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | unclaimed | Audited, unchanged: the restriction formula contains the inverse of the preserved target comparison; no interface adaptation is needed. |

The table includes all direct importers and every live small-model textual consumer of
the retired API, found by reading the source graph and searching the seven names. It also
records the five unchanged downstream consumers of the adapted source and target
isomorphisms and complex section restriction. Their formulas use the preserved maps;
their statements and proof calculations require no edits. The
similarly named calls in SourceCocycleExactRestriction use the adopted canonical API and
are left untouched. Only the original-model StrictLocalSmallModel counterpart is adapted.
All adapted consumers are unclaimed at preparation time. No forced adaptation of a module
held by another group is included. Their declaration names, binders, scheme models, and
conclusions are preserved; references to the old germ predicate become its definitionally
equal general specialization.

The canonical target statements in Challenge.lean are untouched. The changed implementations
of specialization and local-acyclicity restriction require the normal independent definition
review, with the uniqueness comparison above as the reason their mathematical meanings do
not change. Existing docstrings on adapted declarations are preserved.

## Status

landed 20261021T022438-L-2847349 2026-10-21 (merge of deliver/M2/Sheaf.AlgebraicGeometry.StrictHenselizationRestriction)
