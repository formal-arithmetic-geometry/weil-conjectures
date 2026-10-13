## What changed

The signature and docstring of
`AlgebraicGeometry.exists_open_generic_hypersurface_geometric_irreducibility` are unchanged.
Its proof now handles `P = 0` directly. For `P ≠ 0` it proves injectivity of global evaluation
at the generic point, obtains absolute irreducibility from the generic fibre hypotheses,
uses polynomial specialization, and constructs `S.basicOpen a`. Genericity gives membership
of eta; nonvanishing under residue-field embeddings gives primality in every extended fibre.

Added `Sheaf.AlgebraicGeometry.HypersurfaceGeometricFibrePrimeCriterion`, fully proved from
Mathlib. Its private ring equivalence commutes tensoring with the principal quotient and
polynomial scalar extension. Pullback pasting and the affine spectrum tensor isomorphism
identify the extended fibre. The public theorem converts geometric integrality into
primality under all residue-field extensions, including properness and nonemptiness.

Added `Sheaf.RingTheory.AbsoluteIrreducibilitySpecialization`, the remaining purely algebraic
part of Stacks Tag 0557. Its injective coefficient embedding formulation lets the caller use
the generic residue field without needing a separate fraction-field identification.
All new imports in the original module are proof imports. No existing signature, public
import, definition or target changes. Each of the three modules compiles without warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_open_generic_hypersurface_geometric_irreducibility`
(node `lem-sbc-generic-hypersurface-geometric-irreducibility-spread`).

Fully proved the new
`AlgebraicGeometry.hypersurface_geometric_fibre_prime_criterion`
(node `lem-sbc-hypersurface-geometric-fibre-prime-criterion`), and all its private helpers.

The sole added and remaining hole is
`MvPolynomial.exists_nonzero_irreducible_specializations`
(node `lem-sbc-absolute-irreducibility-specialization`). It has a complete source-based
natural-language proof and its entire proof is `by sorry`. This is a decomposition with
one original hole closed and one strictly algebraic hole added, net zero holes; the
pointwise scheme/algebra identification and the final scheme assembly are actual proofs.
The original module and fibre criterion have no remaining sorry.

Edge cases checked in the argument: P = 0 works on the whole base; a nonzero constant cannot
satisfy generic primality (its ideal is the whole ring); n = 0 therefore falls in the zero
case. The obstruction product for degree one is empty. No arbitrary witness is used to
construct any definition; the private tensor quotient equivalence is explicitly constructed.

## No longer needed

Removed the first worker's redundant proof import `Mathlib.RingTheory.MvPolynomial`;
the reduced import set compiles. No original proof-dependency imports or named proof
dependencies existed to prune. Its three public Mathlib imports are retained. The proof does not need a separate
scheme-theoretic identification of the generic residue field with a fraction field, nor
any higher generic geometric-irreducibility shrinking theorem. No existing DAG module
becomes unreachable through a removed import.

## Where the brief, the DAG or earlier work was wrong

The original node contained one long non-elementary step with `uses: []` and no declared
proof dependencies, so there was no already-stated lemma making its plan executable. This
delivery makes the algebra/scheme boundary explicit and proves it; the source's polynomial
specialization argument is now a separate item. No statement was found false.

LeanSearch returned Internal Server Error for both new statements; these failed searches
are recorded as unavailable. Loogle/LeanFinder and source grep supplied the Mathlib APIs,
but no existing exact polynomial specialization theorem. Searches of the full blueprint
for hypersurfaces and Tag 0557 found no existing matching blueprint statement. The unit
`sk-prop-normal-form` and its realized route are unchanged.

## New nodes

`lem-sbc-hypersurface-geometric-fibre-prime-criterion`: the pointwise prime-ideal criterion,
fully proved from Mathlib, in its own module. It needs neither an integral base nor a
nonzero polynomial, and says nothing about spreading or choosing a base open.

`lem-sbc-absolute-irreducibility-specialization`: Stacks Tag 0557 for a domain embedded in
a field, in its own module. This remaining hole concerns only ring maps and polynomial
irreducibility; it has no schemes, fibres, generic points, geometric morphism properties
or opens. Its source-based proof includes descent to the fraction field, triangular
normalization, finite factor coefficient algebras and the Nullstellensatz obstruction.
No change record is necessary: no existing interface changes.

## Second reading by P3

1. Interface preservation: compared the original module with the repository using diff,
   and checked the existing theorem signature byte for byte. It is identical, including
   the two generic-fibre hypotheses and the open-neighbourhood conclusion. The original
   docstring, definitions and public imports are unchanged. Both other modules are new;
   no change record or forced adaptation is needed. Verdict: pass.
2. Proof and trust: compiled all three delivered files in dependency order with lcompile.py.
   Each compiles cleanly. Inspected every proof and the explicitly constructed private
   tensor quotient equivalence. There is no forbidden declaration or hollow definition;
   the only sorry is the entire public named specialization theorem. The separate axiom
   probe confirms that the fibre criterion uses only propext, Classical.choice and
   Quot.sound; the original theorem additionally uses sorryAx through specialization.
   Verdict: a valid one-for-one decomposition, not a completed proof of the import closure.
3. Split statements: read Stacks Tags 0557, 01JQ and 05DY directly. The new fibre criterion
   matches affine tensor base change and geometric integrality, with proper prime ideals
   accounting for nonemptiness. The remaining ring theorem is the polynomial part of
   0557, with descent from an arbitrary containing field to the fraction field. Injective
   coefficient maps preserve nonconstant factors, so this descent is valid. After the
   triangular substitution the degree bounds are those of the transformed polynomial.
   Monic factors of degree zero in the last variable are 1, so only positive degree
   pairs represent nontrivial factorizations. The product of their nonzero annihilators
   remains nonzero in the domain. Checked zero polynomials, nonzero constants, n = 0,
   degree one, and arbitrary field specializations (including positive characteristic).
   New LeanFinder and grep queries using localization, base change and factorization,
   and rg searches in Sheaf and WeilConjectures, found no matching existing theorem.
   The new statements isolate strictly smaller algebraic and pointwise geometric parts,
   rather than restating the original existence of a scheme open. The remaining general
   specialization theorem requires substantial polynomial factor-parameter machinery;
   it cannot be closed by a few-minute application of the located APIs. Verdict: pass.
4. Route and pruning: followed the proof downward through generic evaluation injectivity,
   primality, absolute irreducibility, polynomial specialization and the principal open.
   The fully proved fibre criterion uses Mathlib directly. Removed the redundant newly
   added Mathlib.RingTheory.MvPolynomial import and recompiled successfully. All retained
   new proof imports are plain imports. No old proof dependency is omitted from the
   pruning report: there were none. The sk-prop-normal-form unit record has empty realized
   statement/step lists; it is untouched and no realized unit step is bypassed. Verdict: pass.
5. DAG agreement: read all three nodes and their recorded dependencies. The original
   proof uses the two new nodes in exactly its three recorded steps. The criterion uses
   the existing Mathlib scalar-extension leaf, whose declaration is
   MvPolynomial.algebraTensorAlgEquiv. The specialization node records its complete
   source-based unfinished argument. New nodes carry the required source, creation,
   blueprint, chapter, unit and Lean records. Made both new Lean statement records
   verbatim multiline signatures and marked failed LeanSearch entries unavailable.
   Verdict: pass.

Changes in this reading: removed one redundant proof import, normalized the two new
node signature records, corrected unavailable-search verdicts, and added this review.
No proof body or mathematical statement needed repair. One original hole is closed,
one lower hole is added, and no existing module is pruned: net zero holes.
