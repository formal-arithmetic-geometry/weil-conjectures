# ModuleCat.exists_localizedTensorComparison_derived_arrow

## Reason

Execute the explicit retirement assignment in coord/retire-items.tsv, row
retire:Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow. The Sheaf
module duplicates the complete upstream construction under the same theorem
name. The upstream theorem has exactly the same conclusion, with the same
ambient rings, algebra structures, derived-category instances and Q, N, t,
but omits the unused C-flatness assumption. It therefore supplies every use
of the old theorem by specialization. No upstream file is edited.

## Old

With the ambient parameters of the original module, verbatim signature:

```lean
theorem exists_localizedTensorComparison_derived_arrow
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) (i : ℤ) :
    ∃ H : DerivedCategory (ModuleCat.{u} A) ⥤ Arrow (ModuleCat.{u} C),
      ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
      ∀ mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C,
      let F := (extendScalars.{u, u, u}
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
          (.up ℤ)
      Nonempty (Arrow.mk (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≅
          H.obj (DerivedCategory.Q.obj U))
```

The sole direct consumer imported
`Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow` and called:

```lean
  obtain ⟨H, hH⟩ := exists_localizedTensorComparison_derived_arrow R A B C Q N t hC hQ i
```

## New

Withdraw the duplicate through deleted.txt. The unchanged upstream module
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonDerivedArrow provides:

```lean
theorem exists_localizedTensorComparison_derived_arrow
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) (i : ℤ) :
    ∃ H : DerivedCategory (ModuleCat.{u} A) ⥤ Arrow (ModuleCat.{u} C),
      ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
      ∀ mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C,
      let F := (extendScalars.{u, u, u}
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
          (.up ℤ)
      Nonempty (Arrow.mk (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≅
          H.obj (DerivedCategory.Q.obj U))
```

The consumer's proof-only import now names that upstream module. Its call is:

```lean
  obtain ⟨H, hH⟩ :=
    (fun (_ : Module.Flat (A ⊗[R] B) C) ↦
      exists_localizedTensorComparison_derived_arrow R A B C Q N t hQ i) hC
```

The lambda explicitly specializes the stronger theorem to the retained hC
binder and avoids an unused-variable warning. The consumer's existing public
signature, visibility, docstring, and all other proof steps stay verbatim.

Reattach lem-pc-localized-tensor-comparison-derived-arrow to the existing upstream
module and record its actual signature. The node's old mathematical statement
remains a valid specialization. No logical dependency is removed: its parent
still uses this same node and receives its witnesses from upstream. There is no
new construction, arbitrary witness, weakened conclusion, or postponed proof.

## Users

The downstream.py module and declaration searches give these downstream modules;
the item itself is the only other textual occurrence of the theorem name. The
shared snapshot has no claim file for either downstream module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow | B6 (assigned) | Withdraw duplicate; attach its node to the proved upstream theorem. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore | unclaimed | Migrate proof import and omit the upstream call's hC argument, retaining the consumer's interface. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract | unclaimed | Transitive consumer; interface unchanged; compile checked. |

Source and DAG searches find one current direct importer and one logical parent,
lem-pc-localized-tensor-comparison-closure-retracts-core. Other node references
are historical blueprint/created metadata. No rework quarantine entry names this
item. The unit sk-thm-picard-semicon has empty realized statement and step lists;
reattachment preserves the unit route and its mathematical dependency. All target
statements and definitions remain unchanged, so no target-meaning review reopens.

Repair validation after return C-997a7 (head 997a7a91ef): the current consumer
and node still have the original interfaces described above. Rechecked the live
and quarantined source consumers, the retirement assignment, claim and unit
route. Both direct and transitive consumers compile through lcompile.py against
the adapted sandbox. The unrelated KunnethMapAgrees quarantine archive and all
of its records are preserved.

## Status

landed 20261021T004815-L-1789876 2026-10-21 (merge of deliver/B6/Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow)
