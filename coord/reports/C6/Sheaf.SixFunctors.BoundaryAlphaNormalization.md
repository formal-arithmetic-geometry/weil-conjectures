## What changed

Repair of the return at `de4c837830` (2026-10-21): the independent review passed;
landing failed while reading the absent source of
`Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction`. Its current rework row
preserves that module under `quarantine/`; this packet neither restores nor withdraws
it and preserves its attachment and dependencies. The retained reviewed proof has
been checked against current sources and recompiled on the project server: the item
compiled cleanly in 8.9 seconds, and the unchanged quarantined parent
`BoundaryDualityDischarge` compiled against it in 5.5 seconds. The temporary parent
source was removed from the packet after validation. `deliver3.py` constructs the
fresh delivery on current `sheaf-dag`, as requested by the return.

Proved `AlgebraicGeometry.Etale.boundaryAlphaNormalization` in
`Sheaf.SixFunctors.BoundaryAlphaNormalization`. Its original hypotheses and all three
conclusions are retained. The conclusion is now the explicit proposition
`boundaryNormalizationConclusions`: invertibility of the specified evaluation-normalized
alpha, the independent Hom-chain identity, and contravariant naturality with the original
admissibility assumptions on K'. This intermediate theorem is not a Challenge target.
No declaration of `Challenge.lean` or the adopted source library was changed.

The proof performs the seven adjunction/symmetry Hom bijections in arbitrary categories.
It proves naturality in the test object, identifies the identity value with the expanded
q/r/evaluation transpose, and proves parameter naturality using projection naturality.
The inverse of alpha is explicitly obtained from the Hom bijections at the two admissible
objects X=G(D_T K) and Y=D_Z(i^*K). No test on arbitrary objects is assumed.

`CategoryTheory.BoundaryData` and its real construction helpers retain the canonical
functors, adjunctions, projection map, signed symmetries, q, r, alpha and independent Hom
chain. Alpha is defined by the expanded evaluation formula, independently of the chain;
`BoundaryData.alpha_eq_transpose_r` verifies its normalization. `boundarySigma` now uses
the already constructed `derivedTensorSymmetry` directly. The two opposite signed
interchanges cancel by `derivedTensorSymmetry_involutive`.

Canonical sheafification and derived-inverse-image hypotheses are cached as proved
public theorems with local instance registrations. The native inverse-image expressions
are retained in the map interfaces. The shared conclusion proposition avoids the
expensive conversion between two expanded concrete derived-functor statements: the
cleaned file compiled without warnings in 9.4 seconds, and its actual module compiled
in 16.0 seconds during the consumer check. No heartbeat or time limit was raised.

The unchanged quarantined parent
`quarantine/Sheaf/SixFunctors/BoundaryDualityDischarge.lean` compiled against this module
in 7.9 seconds. It was copied into the sandbox only for that check and is not delivered.
`tools/downstream.py --uses` finds no current external textual users of any changed
declaration; the quarantined parent imports this module but mentions none of them.
The parent is unclaimed. Its Lean attachment and pending DAG dependencies are preserved.

Updated the item's existing node with the actual proof route, public implementation
attachments and the factored Lean statement. No new mathematical node or module was
introduced. Definition changes and the proposition factoring require renewed
statement-meaning review. Change records are:

- `coord/changes/C6-boundarySigma.md`
- `coord/changes/C6-boundaryEvaluation.md`
- `coord/changes/C6-boundaryG.md`
- `coord/changes/C6-boundaryProjection.md`
- `coord/changes/C6-boundaryAlphaQ.md`
- `coord/changes/C6-boundaryAlphaR.md`
- `coord/changes/C6-boundaryAlpha.md`
- `coord/changes/C6-boundaryAlphaHomChain.md`
- `coord/changes/C6-boundaryOmegaT.md`
- `coord/changes/C6-boundaryDT.md`
- `coord/changes/C6-boundaryDZ.md`
- `coord/changes/C6-boundaryAlphaNormalization.md`

## Proved and sorry left

Closed 1 existing hole: `AlgebraicGeometry.Etale.boundaryAlphaNormalization`, node
`lem-weil-boundary-alpha-normalization`. Added 0 holes; split off 0 holes. The item and
all delivered Lean code contain 0 sorries. All generic and native helpers are proved.
This is a proof from existing declarations, not a decomposition.

The axiom audit of the public theorem reports `propext`, `Classical.choice`, `Quot.sound`
and inherited `sorryAx` from existing imported dependencies. No axiom or local hole was
introduced. The generic evaluation-normalization identity
`BoundaryData.alpha_eq_transpose_r` uses only the three permitted standard axioms.

## No longer needed

Removed these direct imports:

```lean
public import Sheaf.Paper.DualityPairing
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Algebra.Homology.RhomGlobalSections
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
```

The canonical ordinary-etale `derivedTensorHomAdjunction₂` supplies currying and its
parameter naturality directly. Thus this proof does not need
`lem-weil-pbc-ringed-internal-hom-exact-restriction` or
`lem-pur-rhom-global-sections`. Removed those proof dependencies and their obsolete
top-level `tool_uses` entries. Historical split records and conceptual statement
dependencies are preserved.

The generic ringed-site and pro-etale presentations are replaced by
`WeilConjectures.SixFunctors.Etale.Derived.Hom`. The pairing import is replaced by the
canonical signed-symmetry construction in
`Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`.
`Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive` is public because the public canonical
data construction uses its identity. No module or declaration is withdrawn, and no claim
is made that the removed imports have no other library users. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction through generic ringed-site restriction and zeroth global
sections is unnecessary: the existing ordinary-etale parametrized tensor-Hom adjunction
already supplies the required argument. The HEq-characterized symmetry choice is also
unnecessary when the canonical descended signed symmetry is already constructed.

The original expanded coefficient specialization caused kernel conversion to expand
large derived constructions for more than 60 seconds. Factoring its exact conjunction
as a real proposition definition repairs that interface without weakening it. This
syntactic statement change and the definition changes are explicitly recorded for review.

The pending parent remains quarantined; its temporary compilation did not restore or
withdraw it. No mathematical statement was found false. The argument also applies to
the zero object, empty closed subscheme, identity immersion and zero coefficient ring:
it uses only the stated adjunctions, symmetry identities and projection isomorphisms.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
