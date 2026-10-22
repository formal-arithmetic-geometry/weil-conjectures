# CategoryTheory.ringedHomComposition_existsUnique and ringedHomComposition_model

## Reason

Complete the remaining two proofs using the chain tensor–Hom equivalence,
pure-section tensor constraints, and the stipulated normalized derived models.
New namespace openings, local instance attributes and local irreducibility
attributes serve only the private proof helpers. Record their scope because
the interface checker conservatively checks such commands.

## Old

The existing module-level opening is:

```lean
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
```

The two original theorem declarations are:

```lean
theorem ringedHomComposition_existsUnique
    (E F G : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃! m : (coefficientTotalTensor.{u, c, v} J R).obj
      (homComplex (R := R) F G, homComplex (R := R) E F) ⟶ homComplex (R := R) E G,
      RingedHomCompositionFormula.{c, v, u} J R E F G m := by sorry

theorem ringedHomComposition_model
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (N : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (D : RingedDerivedTensorCoherence.{c, v, u, w} J R S N β)
    (E F G T : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    [F.IsKInjective] [G.IsKInjective]
    (t : T ⟶ homComplex (R := R) E F)
    (ht : CochainComplex.IsKFlatResolutionIndependentCoefficients (J := J) (R := R) t) :
    (D.tensorIso (homComplex (R := R) F G) T (Or.inr ht.2)).hom ≫
        S.tensor.map
          (ringedHomRepresentativeMap.{c, v, u, w} J R F G,
            DerivedCategory.Q.map t ≫ ringedHomRepresentativeMap.{c, v, u, w} J R E F) ≫
        S.composition (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj G) =
      DerivedCategory.Q.map
        ((coefficientTotalTensor.{u, c, v} J R).map
          (𝟙 (homComplex (R := R) F G), t) ≫ ringedHomComposition.{c, v, u} J R E F G) ≫
        ringedHomRepresentativeMap.{c, v, u, w} J R E G := by sorry
```

There is no `HomCompositionProof` namespace in the original module.

## New

The module-level opening, public signatures, public imports and public
definition bodies remain verbatim. Private complex helpers occur in the namespace
`HomCompositionProof`, where `MonoidalCategory`, `RingedDerivedNative` and
`WeilConjectures.ZeroClassAux` are opened locally. Local instance and irreducibility attributes in that namespace
select the existing native tensor structures and the existing chain
adjunction. The complex helpers take finite-limit and graded-tensor instances as explicit
private instance parameters, so those instances are available while elaborating
the signatures. The public theorem proofs supply the existing instances with
the coefficient universe explicit. These extra private parameters are propositions.
The existing transparent sheaf-compose cache has its original high priority. Local
opacity for the equivalence, the constructed chain maps and the closed structural
maps prevents repeated unfolding during elaboration. Additional generic private categorical lemmas sit beside the existing
closed-naturality calculation in `CategoryTheory`. All new helpers are private and proved. The new proof imports
are private imports, including `import all` for existing private proof helpers.

## Users

The downstream search for the item and its declarations lists its own module
and the following consumer. No public interface changes, so no adaptation is
required. The consumer's use of composition and the component formula has been
read against the unchanged signatures.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedHomCompositionModel | H3 | Complete private proofs. |
| Sheaf.Paper.RingedPullbackHomEvaluationComparison | unclaimed in local records | Unchanged public interface; no adaptation. |

No target statement or definition changes.

## Status

landed 20261022T020101-L-10806 2026-10-22 (merge of deliver/H3/Sheaf.Algebra.Homology.RingedHomCompositionModel)
