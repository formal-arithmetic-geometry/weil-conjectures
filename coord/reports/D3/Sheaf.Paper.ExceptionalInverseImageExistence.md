## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.exceptionalInverseImage_exists` in
`Sheaf.Paper.ExceptionalInverseImageExistence`, preserving its complete signature and the
unit route. The proof assembles the existing Brown hypotheses, compactification exactness,
coproduct preservation, coherence, and finite/integral/rational restriction theorems.

The compact-generator family is an actual small skeleton, with essential surjectivity and
uniqueness of its representatives proved using the skeletal equivalence. Compactness is
transported from those representatives to every Dctf object.

All added helpers are private and fully proved. They construct the finite-ring universe-lift
isomorphism sectionwise, transport bounded constructibility termwise, preserve the recorded
ambient-intersection localizing closures under coefficient equivalences, and conjugate the
supplied adjunction along those equivalences. The integral comparison identifies the same
supplied general adjoint with the integral one before applying integral restriction. The
finite-subextension-valued algebraic closure uses the existing rational restriction-glue
result; the all-continuous algebraic closure uses rational exceptional restriction and its
separate finite-Tor theorem. No coefficient models are identified without an isomorphism.

Added private proof imports for coefficient transport, base-coefficient identification,
continuous algebraic-closure finite Tor, rational restriction glue, constant-model Tor
invariance, localizing-closure existence, and categorical preservation of colimits by
adjoints. The two coefficient-transport imports use `import all` to reuse their existing
proved private constructibility and inverse-comparison helpers. Public imports are unchanged.
The node copy records the dependencies actually used, including the separate continuous
algebraic-closure result. No definitions, public signatures, or consumers were changed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.CondensedRing.exceptionalInverseImage_exists`
(node `sk-thm-existence`). The item originally had one hole and now has zero. Added zero
holes and zero split-off statements. Every new private helper has a complete proof.

The proof uses the existing named dependency declarations as authorized by stage 3; it does
not claim that their transitive proofs are free of sorry. In particular the previously
recorded arbitrary-field dispute on `CategoryTheory.brownHypotheses` remains a dependency
issue and is not resolved by this assembly.

Validation: `lcompile.py` compiled the complete module without errors or warnings in 33.8 s.
The theorem signature was compared verbatim with the original and is identical. Checks of
the construction include the zero finite ring, empty schemes, arbitrary finite coefficient
rings without regularity, and the distinction between the two algebraic-closure rings.

## No longer needed

Removed the direct private import `WeilConjectures.Compactification.Dense`. The theorem uses
the already constructed `compactificationOverField f`; it does not choose another dense
compactification. The quasi-compactness of its open leg comes from the existing
`Compactification.quasiCompact_openImmersion` API. Nagata remains part of the chosen
compactification construction and the unit route.

The separate node `lem-sp-fully-faithful-adjunction-restriction` is not needed directly by
the current Lean conclusion: clause (4) encodes preservation by the supplied adjoint, and
requests no separate adjunction on restricted functors. The full Hom equivalences are still
those of the original adjunction. Its unused dependency was removed from the parent node.
No Lean module is withdrawn, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The existing coefficient-transport API uses `ObjectProperty.localizingClosure`, whereas the
item uses `CategoryTheory.localizingClosure` through `localizingClosureProEtale`. These are
different definitions with different coproduct-index conventions; they are not definitionally
equal. The proof therefore reuses the ambient coefficient equivalence and compactification
comparison, and proves preservation/reflection of the item's actual closures by minimality.
It does not silently replace either closure.

The older `localizingClosure_ctf_equals_bc` theorem covers the finite-subextension-valued
algebraic closure, while the item's final coefficient clause uses all continuous maps into
`PadicAlgCl`. The latter equality is obtained from the existing separate theorem
`continuousAlgCl_bounded_finiteTor` on the noetherian schemes in this setting.

The original Brown-hypotheses dependency already carries `STATEMENT-DISPUTED` for its
arbitrary positive-characteristic base-field compactness claim. Its statement is unchanged;
this delivery proves the assigned assembly from that existing declaration and records the
limitation for the independent reader.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
