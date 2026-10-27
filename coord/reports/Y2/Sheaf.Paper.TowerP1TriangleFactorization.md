## What changed

Reduced `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1TriangleFactorization` to four
strict internal steps, with a complete combining proof of the unchanged six-clause
statement. The main proof factors eta, applies diagonal-free trace rearrangements,
transports its initial insertion, cancels the inverse outside projection, and combines
tensor maps to obtain the actual scalar contraction. In particular neither an abstract
F/G adjunction nor c_i=1 is assumed or used.

Moved the original sixteen definitions, with names, types and bodies preserved, to
`Sheaf.Paper.TowerP1TriangleWords`, publicly re-exported by the original module.
This prevents a dependency cycle between the word definitions and the internal lemmas.
The new concrete words `unitInsertion`, `unitTail`, `contractionTail`, `pushSwap` and
`rightPullComparison` name the respective parts of the calculation. They contain no
proof holes or choice of arbitrary existence witnesses. Change record:
`coord/changes/Y2-tower-p1-triangle-words.md`.

The four new statement modules each contain one genuine step, with the source and
full argument in the docstring and matching DAG node. The first two have no supported
diagonal in their conclusions; the transport theorem has no trace or triangle composite;
the section-specialization theorem has no eta, epsilon, or scalar normalization.

## Proved and sorry left

This is a decomposition, not a net proof gain. The original module's one direct hole
in `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1TriangleFactorization` is closed by a
complete proof from named intermediate statements. Four new holes are added:

- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1FirstTraceReordering`
  (`lem-sp-tower-p1-first-trace-reordering`).
- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1SecondTraceReordering`
  (`lem-sp-tower-p1-second-trace-reordering`).
- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1DiagonalTransport`
  (`lem-sp-tower-p1-diagonal-transport`).
- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1DiagonalProjectionFactor`
  (`lem-sp-tower-p1-diagonal-projection-factor`).

No direct sorry remains in the item or the word module. Proved private helpers are
`eta_factor`, `cancel_projection_word`, `outside_projection_cancel`,
`expanded_eq_scalar`, `first_expanded`,
and `second_expanded`. The new holes are strictly parts of the argument, not the
original six-clause theorem with repackaged hypotheses. Net direct holes: 1 closed,
4 added, hence -3. Existing dependency holes are unchanged.

## No longer needed

Removed the old unused direct proof imports from the original module:
`Sheaf.Paper.TowerClassTwisting`, `Sheaf.Paper.RingedProjectionTensorComposition`,
`Sheaf.Paper.RingedExchangeTensorCoherence`, `Sheaf.Paper.ProjectionMateExact`,
`Sheaf.Paper.ProEtaleTateTwistsOfUniverses`, `Mathlib.Algebra.Homology.BifunctorShift`,
and `Mathlib.CategoryTheory.Adjunction.Mates`. The specialized internal statements
now carry the mathematical uses of these generic tools in their nodes. All original
public imports are retained transitively through the publicly re-exported word module.

The parent proof does not use `lem-sp-tower-p1-kernel-scalar-normalization`:
its projection traces are already defined by inverse exchange and pullback of the
q trace, so their trace-base-change equation is formal. In particular constructing
an independent splitting for p_i, and proving its c_i=1, are unnecessary for this
factorization. The independent normalization theorem remains intact for its other
users. No module is withdrawn, and no adopted source declaration is changed.
No globally unreachable module is claimed on the basis of the zero-importer result.
The parent node's four old direct tool-use entries (semilinear sections, projection
tensor composition, exchange/tensor coherence and projection-mate exactness) are
removed because those direct proof dependencies belong to the new internal lemmas.

## Where the brief, the DAG or earlier work was wrong

The nine-step proof was a valid mathematical plan but its generic ringed-topos
coherence declarations do not directly state the equalities for the normalized tower
words. The delivery isolates that specialization and its source comparisons explicitly.
It also records the actual conjugate pushSwap and the explicit comparison p1*GK=p2*GK,
instead of treating the corresponding objects as definitionally equal.

The plan's trace-base-change use of the kernel-normalization node is redundant for
these projectionTrace definitions: they are the inverse-exchange trace words already.
No target statement, definition meaning, or unit route is changed.

Validation: the extracted word module and all four new statement modules compile
through lcompile.py. The main proof uses a generic proved categorical cancellation lemma and local
irreducibility annotations to avoid expanding derived localization representatives
during composition rewriting. Profiling identified kernel conversion of the first
expanded equation as the main cost; the revised full file ran within 60 seconds
before the final small proof and linter cleanups. The final main module then compiled
cleanly with exit code 0 and no warnings in 49.7 seconds through lcompile.py.

Edge checks: no finite-Tor condition is introduced; S may be empty and M or K may be
zero; both Bool projection cases retain alpha_i. The even shift contributes identity
sign, including at ell=2. The argument never uses faithfulness of evaluation on
general derived maps. A no-importer check is only a consumer inventory, not a reason
for withdrawing the item; its DAG parent attachments stay intact.

## New nodes

`def-sp-tower-p1-triangle-words` records the relocated definitions and the five new
explicit canonical compositions. It contains no sorry.

`lem-sp-tower-p1-first-trace-reordering` is steps 2--4 before inserting delta: transpose
the two forward words, use their common tensor of counits, and cancel the invertible
second word. It states an equality out of R Rp2*(p1*M tensor T_W), not out of FM.

`lem-sp-tower-p1-second-trace-reordering` is steps 6--8 before inserting delta: invert
the exchange/tensor square at (K,T), extract the last line factor, check its even-shift
symmetry, and cancel the projection against G(epsilon).

`lem-sp-tower-p1-diagonal-transport` isolates the two source-comparison pastings used
in steps 5 and 9. It only transports the supported insertion and has no trace.

`lem-sp-tower-p1-diagonal-projection-factor` is section specialization and projection
naturality for either p_i, with alpha_i on the source; tensor algebra in the original
module then gives expanded contraction equals scalar contraction.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
