## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_classical_stalk` with its signature and
public imports unchanged. The proof constructs the canonical marked strict-local
neighbourhood from `strictHenselizationResidue`, proves its weak etaleness using the
stated affine-chart ind-etale theorem, and constructs pointed sections using Olivier.
All auxiliary results are proved private helpers in the assigned module; there are
no new public declarations or modules.

Pointed uniqueness uses the weakly etale diagonal and the same lifting construction.
The opposite initial neighbourhood is terminal, so Mathlib makes precisely the
canonical natural transformations in the statement invertible. Covering sieves at
this object contain the identity. Thus evaluation commutes with abelian
sheafification, and the existing reflective-adjunction lemma gives preservation of
finite colimits. Sectionwise limits and the canonical natural isomorphism finish
the proof. The DAG proof and dependencies now describe this argument.

The section construction adapts the proved private etale helper in
`WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk` to weakly
etale morphisms. The sheafification argument follows the proved field-evaluation
calculation in `Sheaf.Paper.GeometricFieldProEtaleEvaluation`, generalized here to
any strictly henselian local spectrum. Neither module is imported or duplicated as
public API.

Validation: single-file server compilation through `lcompile.py` passes cleanly
(the final compile took 4.8 seconds). The
statement was compared verbatim with the repository version. The delivery tool
also checks compilation and declaration axioms. The section helper only needs a
field-valued marked point, so the cover-splitting proof can use the selected
point's residue field without imposing an extra geometric lifting hypothesis.
An empty covering cannot cover the nonempty local spectrum; arbitrary base schemes
and arbitrary nonreduced affine chart rings are allowed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtale_classical_stalk`
(node `lem-cbc-proetale-classical-stalk`).

Holes closed: 1. Holes added: 0. Sorries left in the assigned module: 0.
No split-off obligations. All seven private helpers are complete.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.StrictHenselization`: already available through the
  retained public structural-map interface.
- `Sheaf.RingTheory.IndPrincipalZariski`: the retained stability interface supplies
  the affine weak-etale criterion; its principal-Zariski construction is unused.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: no derived-category argument.
- `Mathlib.AlgebraicGeometry.Scheme`: the retained public interfaces supply schemes.
- `Mathlib.CategoryTheory.Sites.EpiMono`: replaced by the narrower
  `Mathlib.CategoryTheory.Sites.LocallyBijective`; no epi/local-surjectivity theorem.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: the required open-immersion instances
  are available from the retained geometry interfaces.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: weak etaleness of an open
  immersion follows from Mathlib directly; no comparison morphism is needed.
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`: the retained functoriality
  clause supplies the canonical residue lift and its factorization together.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the concrete Mathlib pro-etale
  precoverage and its covering-family criterion suffice.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`: already
  supplied by the unchanged public structural-map import.

Removed proof dependencies `def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, and
`lem-weil-pbc-weakly-etale-source-locality`. No comparison construction or
sheaf-epimorphism criterion is used. Restricting the source to the chosen chart
uses composition with its weakly etale open immersion directly; the separate
source-locality theorem is unnecessary. Removed the obsolete epi-criterion and
source-locality entries from `tool_uses`.
The original image-factorization/cokernel proof of finite-colimit preservation is
unnecessary. No unit statement or unit step is bypassed. These are removals from
this proof and its direct imports, not a claim that all listed modules are absent
from the entire targets' import closure.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original proof plan works, but uniqueness is
shorter using the weakly etale diagonal, and exactness is shorter by commuting
evaluation with sheafification and applying the existing reflective-adjunction
colimit lemma. Existing Mathlib leaves for weakly etale composition/base change,
between-objects permanence, and local bijectivity after sheafification record the
additional APIs used. No new node or statement/definition repair is required.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
