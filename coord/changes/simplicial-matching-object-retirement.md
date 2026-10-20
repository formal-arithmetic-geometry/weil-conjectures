# Simplicial matching-object wrapper retirement

## Reason

The human's retirement hand-off in `coord/changes/retire-sheaf-twins-20261020.md`
and `coord/retire-items.tsv` assigns this module for retirement. The copy is
already sorry-free. Its upstream twin contains the identical boundary definitions,
but lacks `matching_object_zero`, `matching_object_one`, and
`matching_object_succ_succ`. Three consumers use only existence of matching cones
and maps; the other five direct consumers need only the boundary definitions.

The three proof consumers now form the canonical finite product or multiequalizer
and lift the faces. Mathlib's simplicial face identity proves compatibility.
No result is replaced by sorry. No upstream file, definition, target statement,
or surviving declaration signature changes. Target meanings are unchanged:
the boundary definitions already came from this twin before retirement.
The unique-iso and tuple-bijection exports have no remaining consumers.

## Old

The withdrawn wrapper publicly imported
`WeilConjectures.CategoryTheory.SimplicialMatchingObject` and exported these three
already-proved signatures:

```lean
theorem matching_object_zero {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (e : C) (he : IsTerminal e) :
    (∃! μ : K _⦋0⦌ ⟶ e, True) ∧
      (∀ (M : C), IsTerminal M → ∃! α : e ≅ M, True)

theorem matching_object_one {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) :
    ∃ c : Fan (fun _ : Fin 2 => K _⦋0⦌),
      Nonempty (IsLimit c) ∧
      (∀ (c' : Fan (fun _ : Fin 2 => K _⦋0⦌)), Nonempty (IsLimit c') →
        ∃! α : c.pt ≅ c'.pt, ∀ i : Fin 2, α.hom ≫ c'.proj i = c.proj i) ∧
      (∃ E : ∀ W : C, (W ⟶ c.pt) ≃ (Fin 2 → (W ⟶ K _⦋0⦌)),
        (∀ (W : C) (g : W ⟶ c.pt) (i : Fin 2), E W g i = g ≫ c.proj i) ∧
        (∀ (W W' : C) (f : W' ⟶ W) (g : W ⟶ c.pt) (i : Fin 2),
          E W' (f ≫ g) i = f ≫ E W g i)) ∧
      (∃! μ : K _⦋1⦌ ⟶ c.pt, ∀ i : Fin 2, μ ≫ c.proj i = K.δ i)

theorem matching_object_succ_succ {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (n : ℕ) :
    ∃ c : Cone (matchingBoundaryIndex K n).multicospan,
      Nonempty (IsLimit c) ∧
      (∀ (c' : Cone (matchingBoundaryIndex K n).multicospan), Nonempty (IsLimit c') →
        ∃! α : c.pt ≅ c'.pt, ∀ j, α.hom ≫ c'.π.app j = c.π.app j) ∧
      (∃ E : ∀ W : C, (W ⟶ c.pt) ≃
        {x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌) //
          ∀ p : (matchingBoundaryShape n).R,
            x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
              x p.val.2 ≫ (matchingBoundaryIndex K n).snd p},
        (∀ (W : C) (g : W ⟶ c.pt) (i : Fin (n + 3)),
          (E W g).val i = g ≫ c.π.app (WalkingMulticospan.left i)) ∧
        (∀ (W W' : C) (f : W' ⟶ W) (g : W ⟶ c.pt) (i : Fin (n + 3)),
          (E W' (f ≫ g)).val i = f ≫ (E W g).val i)) ∧
      (∀ p : (matchingBoundaryShape n).R,
        K.δ p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
          K.δ p.val.2 ≫ (matchingBoundaryIndex K n).snd p) ∧
      (∃! μ : K _⦋n + 2⦌ ⟶ c.pt, ∀ i : Fin (n + 3),
        μ ≫ c.π.app (WalkingMulticospan.left i) = K.δ i)
```

Eight consumers imported `Sheaf.CategoryTheory.SimplicialMatchingObject`, publicly
except for the proof import in SRMatchingObjectOneMember.

## New

The wrapper is withdrawn through `deleted.txt`. All eight consumers import
`WeilConjectures.CategoryTheory.SimplicialMatchingObject` with the same visibility.
The upstream file is unchanged and still defines
`CategoryTheory.SimplicialObject.matchingBoundaryShape` and
`CategoryTheory.SimplicialObject.matchingBoundaryIndex`.

The private `exists_properFaceMatchingArrow` in SiteHypercoverDisjointUnion,
the private `etaleFaces` in SRMatchingObjectOneMember, and
`exists_affine_hypercover_geometry` in ProEtaleAffineAcyclicHypercoverGeometry
now use `limit.cone`, `Multiequalizer.multifork`, `Fan.IsLimit.lift`,
`Multifork.IsLimit.lift`, and `SimplicialObject.δ_comp_δ` directly. Their signatures
are unchanged. The five other consumers change only an import line.
No replacement public declaration or module is added.

The existing node attaches to the actual upstream boundary definitions only.
Its note explicitly says that the former three theorem exports are absent from
the twin and names the consumers proving the needed existence facts locally.
Its mathematical statement, proof dependencies, and unit route are unchanged.

## Users

The successful `tools/downstream.py` scan returned these 48 users, including all
eight adapted modules. The only uses of the removed theorem names were six calls
in the three adapted proof consumers. All eight adapted modules were unclaimed
at preparation; observed holders of other users are listed below. A subsequent union scan of all changed modules confirmed the same 48 users.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFiniteSimplexLifting | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOrdinalPathHypercover | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSimplicialMatching | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic | T6 | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercoverFreeAbelianPositive | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercoverFreeModulePositive | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercoverInjectiveAbelianPositive | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercoverInjectiveModulePositive | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.SingleAffineHypercover | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | unclaimed | Only the import switches to the twin; no use of removed theorem names; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry | unclaimed | Import switched to twin; needed matching cones/maps now constructed from Mathlib; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak | unclaimed | Only the import switches to the twin; no use of removed theorem names; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | Q5 | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember | unclaimed | Import switched to twin; needed matching cones/maps now constructed from Mathlib; signatures unchanged. |
| Sheaf.CategoryTheory.DerivedCategory.BoundedBelowSectionModel | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.CategoryTheory.MatchingObjectCoskeleton | unclaimed | Only the import switches to the twin; no use of removed theorem names; signatures unchanged. |
| Sheaf.CategoryTheory.SiteHypercoverDisjointUnion | unclaimed | Import switched to twin; needed matching cones/maps now constructed from Mathlib; signatures unchanged. |
| Sheaf.CategoryTheory.SiteHypercoverFreeResolution | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.CategoryTheory.SiteHypercoverInjectiveSections | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Only the import switches to the twin; no use of removed theorem names; signatures unchanged. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Only the import switches to the twin; no use of removed theorem names; signatures unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.CondensedUnderivedPushforwardContinuity | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.EtaleHypercoverHomotopyEqualizer | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | U9 | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.SemiRepresentableHypercoverEtale | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.Paper.SiteHypercoverDerivedDescent | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Transitive consumer; no use of removed theorem names; same boundary definitions; no adaptation. |

## Status

landed 20261020T145456-L-2399564 2026-10-20 (merge of deliver/C4/Sheaf.CategoryTheory.SimplicialMatchingObject)
