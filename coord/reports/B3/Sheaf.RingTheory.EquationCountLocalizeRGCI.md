## What changed

Proved `Algebra.localized_presentation_is_relativeGlobalCompleteIntersection` in
`Sheaf.RingTheory.EquationCountLocalizeRGCI` without changing its statement or visibility.
The three public imports and the existing theorem docstring are preserved.

The proof uses `Algebra.exists_away_fibre_dimension_le` for the upper bound, lifts its
chosen element by quotient surjectivity, and uses the existing inverse-variable
presentation isomorphism. It constructs the Option-to-Fin quotient equivalence and
residue-field base-change equivalence directly from Mathlib. Applying the global
polynomial-quotient lower bound to the enlarged quotient gives the reverse inequality;
antisymmetry closes the dimension equality. The reindexed presentation witnesses the
intrinsic relative-global-complete-intersection predicate, with fibre dimensions
transported by tensor-product equivalences and homeomorphisms of spectra.

Added proof imports: `Sheaf.RingTheory.FibreDimensionNeighborhood`,
`Sheaf.RingTheory.PolynomialQuotientDimensionLowerBound`, and
`Mathlib.RingTheory.Extension.Presentation.Basic`.
Two private noncomputable definitions construct explicit algebra equivalences from
proved Mathlib constructions; neither chooses data from an unproved existence result.
The DAG copy records this route. No interface changes or adaptations.

Checked the source at https://stacks.math.columbia.edu/tag/00ST, part (3), including
its proof's choice of g and lift h. The local literature .tex is absent in this clone;
the source was read on the Stacks site. The original unit sk-thm-p1 is preserved:
this node realizes none of its fixed statement or proof steps. Both dimension lemmas
are generic tools within the same unit.

## Proved and sorry left

Closed 1 original hole:
`Algebra.localized_presentation_is_relativeGlobalCompleteIntersection`
(node `new-equation-count-localize-rgci`).

No sorry remains in the item; no holes or new nodes were added (0 split off).
This is a proof from existing project lemmas, not a claim that every transitive
proof dependency is already free of sorry. In particular the upper-bound route
still reaches the existing localized-fibre-dimension bound.

The file compiled without errors or warnings using lcompile.py. Edge cases require
no extra hypotheses: n=c gives dimension zero, n=c=0 reindexes to one variable and
one inverse relation, repeated equations cause no problem for the lower bound,
and zero fibres are excluded only where the original statement excludes them.
No chosen localization element is used to define a public data object.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`.
- `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`.
- `Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference`.
- `Sheaf.Topology.DimensionSupremumLocalDimensions`.
- `Mathlib.RingTheory.TensorProduct.MvPolynomial`.
- `Mathlib.RingTheory.TensorProduct.Quotient`.
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.
- `Mathlib.RingTheory.Localization.BaseChange`.

The direct point-height-difference argument is replaced by the global lower bound
on the enlarged presentation. The following original direct DAG dependencies are
removed from this node (some are still needed transitively by the existing upper
or lower bound, or in the statement; no claim that all become globally unreachable):
- `def-weil-pbc-mv-polynomial-ring`.
- `def-weil-pbc-finite-type-algebra`.
- `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`.
- `lem-weil-pbc-spec-localization-away-basic-open`.
- `def-weil-pbc-localization-at-prime`.
- `lem-weil-pbc-polynomial-scalar-extension`.
- `lem-weil-pbc-tensor-quotient-base-change`.
- `lem-weil-pbc-finite-type-algebra-noetherian`.
- `def-weil-pbc-noetherian-ring`.
- `lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference`.
- `lem-weil-pbc-noetherian-height-quotient-bound`.
- `def-kun-topological-dimension-at-point`.
- `lem-weil-pbc-localization-away-tensor-iso`.
- `def-weil-pbc-module-localization-away`.
- `def-weil-ring-localization-away`.
- `def-weil-affine-spectrum`.
- `lem-weil-pbc-dimension-at-point-open-subspace`.
- `lem-weil-pbc-fibre-ring-primes-bijection`.
- `lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`.
- `lem-weil-pbc-dimension-supremum-local-dimensions`.

Retained direct proof dependency `new-equation-count-localize-presentation`.
`Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference` is no longer
needed by this proof even indirectly through its lower-bound route. The specified
presentation predicate is not used; the intrinsic predicate is witnessed directly.
Global pruning from the targets is for the maintainer to measure.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable signature was found. The DAG's pointwise lower-bound
route is unnecessarily strong: a global lower bound on the enlarged polynomial
quotient suffices after the upper bound has already been established. The existing
`FibreDimensionNeighborhood` module packages the first two steps and the localized
upper-bound comparison, so there is no need to redo them in this module.
The preserved old docstring describes the longer valid pointwise argument; the
updated node and this report describe the actual shorter Lean proof.


## Second reading by B3

1. Interface: compared the complete module with the repository version and checked
   the theorem signature byte for byte, including its let-bound fibre, nontriviality
   hypotheses, visibility and both conclusions. It is identical. The three public
   imports are unchanged; all added imports are proof-only. There are no changed
   definitions used by callers, change records, or adapted modules. Verdict: pass.

2. Proof: independently compiled the delivered file with lcompile.py (7.6 seconds,
   no warnings or errors), inspected every proof and both private constructions,
   and compiled a scratch copy with #print axioms for all three declarations.
   reindex_quotient and polynomialQuotient_baseChange use only propext,
   Classical.choice and Quot.sound. The main theorem additionally uses sorryAx
   through existing imported results, as already disclosed above. There is no
   sorry, axiom, unsafe, opaque, implemented_by or extern in the delivered source.
   The helpers construct equivalences by renameEquiv, quotient equivalences and
   Presentation.baseChange; they do not select arbitrary unproved data. The chosen
   localization element and the presentation equivalence are used inside a theorem
   proof, not to define a public object. Verdict: pass.

3. Split statements: none were added, so there is no shifted hole or restatement
   to review. Read the exact signatures of exists_away_fibre_dimension_le,
   exists_localization_presentation and
   sub_le_topologicalKrullDim_spec_mvPolynomial_quotient. The first applies to the
   finite-type quotient S with hdim.2; the second identifies precisely the displayed
   inverse-variable quotient; the third applies over p.ResidueField with hc and
   nontriviality transported from the original fibre. The zero-variable case and
   c=n still have one added variable and one added relation and give dimension zero;
   repeated relations are permitted, and empty fibres are never passed to the lower
   bound. Verdict: pass.

4. Route and pruning: checked the tensor equivalences in both directions and the
   spectrum homeomorphism equalities. The upper bound is transported from S_g to T;
   the lower bound is transported from the residue-field quotient to U and then T.
   Antisymmetry gives exactly the requested dimension, and E.symm witnesses the
   intrinsic RGCI predicate. Independent LeanFinder and Loogle searches and local
   rg searches found Presentation.reindex and generic quotient equivalences, but no
   shorter theorem proving this item. The existing short explicit reindexing helper
   is correct and was retained. All four proof imports are used, and the public
   imports supply the signature. Compared old and new proof_deps: every one of the
   twenty removed entries is listed under No longer needed. Read sk-thm-p1.json:
   this node realizes none of its fixed statement or steps; the generic dimension
   tools do not replace a unit-level step. Verdict: pass.

5. DAG: compared the node JSON with the repository. Only proof, proof_deps and
   proof_origin differ. The four steps follow the Lean argument; their uses have
   union exactly proof_deps. The statement, stmt_deps, source, Lean record, chapter,
   unit and blueprint placement remain unchanged. No new nodes need auditing.
   Verdict: pass.

Second reading changes: appended this independent review only. No Lean or DAG repair
was needed. The preserved theorem docstring describes the older, longer valid route;
the proof record and report correctly describe the implemented global lower bound.
