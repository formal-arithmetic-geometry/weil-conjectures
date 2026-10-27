# SheafOfModules.StrictScalarHom.exists_sliceScalarHomChainAdjunction

## Reason

Complete the normalized ordinary and slice scalar adjunction, reusing the independently
proved strict scalar-Hom chain theorem for the chain isomorphisms. Private constructions
supply the ordinary adjunction and the comparison of scalar extension with continuous
cocontinuous restriction at the independent universes of this interface.

## Old

```lean
theorem exists_sliceScalarHomChainAdjunction
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Nonempty (SliceScalarHomAdjunction.{c, v, u} φ) := by
  sorry
```

The public section sets
`backward.isDefEq.respectTransparency true`. There is no private ordinary-extension
additivity helper or associated local instance command.

## New

The theorem retains the exact signature quoted above and is now proved.
All three source-written public structures, every field, the theorem signature and the
public import remain verbatim. The theorem is proved from private constructions and
the canonical data underlying `exists_scalarHomChainIdentification`. These are independently
proved and their actual
Lean imports and current DAG proof dependencies do not depend on this item.

The ordinary-extension functor, its additivity proof, the scalar Hom equivalence,
and the ordinary adjunction are reused from the existing proved private helpers of
`StrictScalarHomChain`, via the private proof import:

```lean
import all Sheaf.Algebra.Homology.StrictScalarHomChain
```

The public import of that same module remains verbatim. The private import exposes
its proved private declarations to this file's proofs; no public signature or public
definition refers to a private helper. `ordinaryExtension_additive` is activated as
an instance locally. The additional private constructions supply normalization and
continuous/cocontinuous restriction comparisons. The comparison morphism has an explicit equation and a separate invertibility proof.
Its pure-tensor formula and naturality are proved before constructing its isomorphism.
Locally irreducible completed constructions and generator equations prevent repeated
unfolding of sheafification terms; the final assembly restores semireducibility where projections are needed.
The file sets `backward.isDefEq.respectTransparency false`, and the private proof block
sets `linter.unusedTactic false` and `linter.unusedSectionVars false`. These suppress
optional lint traversals over large proofs; elaboration and kernel checking remain
enabled. No global attribute or downstream scope changes. Profiling commands are
removed from the delivered file. All remaining private helpers are fully proved.
No target statement or definition changes meaning; no target review is reopened.

The two unused private proof imports of SliceModuleSheafification and
SheafRingCoefficientOrdinaryAdjunction are removed. Their interfaces respectively fix
one common small-site universe and use HasSheafify; the private proofs here work at the
independent site universes and HasWeakSheafify of the original item. Added private proof
imports supply the scalar generator API and preservation of local bijectivity.

## Users

The read-only downstream query found four modules below this item. All source-written
public interfaces and the public import remain identical; no consumer adaptation is
needed. Only ScalarHomChainEvaluation directly uses the proved existence theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence | A8 | Same interface. |
| Sheaf.Algebra.Homology.ScalarHomChainEvaluation | unclaimed | Same existence theorem. |
| Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison | unclaimed | Same interface. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Same interface. |

## Status

landed 20261023T135013-L-2823505 2026-10-23 (merge of deliver/G8/Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction)
