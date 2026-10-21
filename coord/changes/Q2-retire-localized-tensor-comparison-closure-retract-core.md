# ModuleCat.localizedTensorComparisonProperty_retract_core

## Reason

Execute the listed retirement assignment
retire:Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore
in coord/retire-items.tsv. The local module duplicates the completely proved
upstream theorem under the same declaration name. The upstream theorem omits
only the unused hypothesis that C is flat over A tensor_R B. Its remaining
parameters and conclusion agree verbatim, so specialization supplies every
existing use. No upstream file is changed.

## Old

With the ambient parameters R, A, B, C, Q, N and t of the original module,
the old signature is:

```lean
theorem localizedTensorComparisonProperty_retract_core
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (hXY : Retract X Y)
    (hY : localizedTensorComparisonProperty R A B C Q N t Y) :
    ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
    Nonempty (DerivedCategory.Q.obj U ≅ X) →
    (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
    ∀ (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ),
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)
```

The sole consumer imported the Sheaf module and concluded:

```lean
  exact localizedTensorComparisonProperty_retract_core R A B C Q N t hC hQ hXY hY
```

## New

Withdraw the Sheaf duplicate through deleted.txt and attach its existing node
to the unchanged upstream module
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore.
The upstream signature, with the same ambient parameters, is:

```lean
theorem localizedTensorComparisonProperty_retract_core
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (hXY : Retract X Y)
    (hY : localizedTensorComparisonProperty R A B C Q N t Y) :
    ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
    Nonempty (DerivedCategory.Q.obj U ≅ X) →
    (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
    ∀ (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ),
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)
```

The consumer's proof-only import now names this upstream module. Its body ends:

```lean
  exact (fun (_ : Module.Flat (A ⊗[R] B) C) ↦
    localizedTensorComparisonProperty_retract_core R A B C Q N t hQ hXY hY) hC
```

This explicitly specializes the stronger upstream theorem to the consumer's
retained hC binder. The consumer's signature, visibility, docstring and public
imports remain verbatim. No statement or definition of a target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore | Q2 (assigned) | Retire duplicate; retain node with upstream attachment. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract | unclaimed | Migrate proof-only import and specialize the upstream theorem; signature unchanged. |

The downstream.py module/declaration searches and rg of live and quarantined
sources identify this sole direct consumer. No rework row names the item, and
no current claim file names the consumer in the inspected snapshot. A parsed
search of all node stmt_deps, proof_deps and proof-step uses finds no incoming
logical edge to the core node. The node itself and all of its dependencies stay;
only its Lean attachment changes. The unit sk-thm-picard-semicon has empty
realized statement/step lists, which are preserved. Its unit route is unchanged.
No archive is removed or restored.

Validation: the original local module compiled before withdrawal. Changing only
the consumer import produced an application type mismatch at its old line 56:
hC has type Module.Flat (A tensor_R B) C, but the upstream theorem expects the
acyclic-tensor hypothesis hQ in that argument position. The adapted consumer
compiled without warnings in 3.0 seconds through lcompile.py. An independent
probe of the upstream theorem's #print axioms reported exactly propext,
Classical.choice and Quot.sound. There are zero direct sorry holes before or
after this repair and no new statements or proof obligations.

## Status

landed 20261021T012424-L-2188387 2026-10-21 (merge of deliver/Q2/Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore)
