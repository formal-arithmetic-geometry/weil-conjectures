## What changed

Replaced the direct sorry in `Algebra.exists_smooth_reduction_factorization` in
`Sheaf.RingTheory.PopescuLiftOnceCore` by a complete Lean combination of the existing
`Algebra.ind_isStandardSmooth_of_ind_smooth` and two new presentation constructions.
The first constructs the finitely presented factor algebra with standard smooth reduction;
the second lifts a standard smooth quotient algebra to a standard smooth algebra over the
original base. The proof installs the existential ring and algebra structures, applies the
second construction to the first reduction, uses the Mathlib standard smooth implies smooth
instance, and restricts the quotient-algebra equivalence to an R-algebra equivalence.
All original signatures and visibility are unchanged. Added proof-only imports of
`Sheaf.RingTheory.PopescuStandardReductionFactor`,
`Sheaf.RingTheory.StandardSmoothQuotientLift`, and
`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`. Updated the original node's proof and
proof dependencies to this combination. Each new module has one public theorem with its
source, full argument in words, and matching node.

## Proved and sorry left

Closed one direct hole: `Algebra.exists_smooth_reduction_factorization`
(node `lem-weil-pbc-popescu-lift-once-core`). No sorry remains in the item's module.
Added two direct holes:

- `Algebra.exists_standardSmooth_reduction_factorization`, node
  `lem-weil-pbc-popescu-standard-reduction-factor`, module
  `Sheaf.RingTheory.PopescuStandardReductionFactor`.
- `Algebra.exists_standardSmooth_quotient_lift`, node
  `lem-weil-pbc-standard-smooth-quotient-lift`, module
  `Sheaf.RingTheory.StandardSmoothQuotientLift`.

This is a decomposition, not a sorry-free proof or positive net hole reduction. Both new
statements are strictly parts of the original argument: the factor construction asserts no
smooth lift B, while the quotient lift has no Lambda, map phi, or factorization problem.
The combination also uses the existing ind standard smooth refinement (still sorry in the
baseline). No data definition or axiom was added. All three files compiled using lcompile;
the main proof compiled without warnings after replacing local letI bindings by let.

Edge cases checked mathematically before stating the new lemmas: for I = top the reduction
is zero and the factor construction can use A itself; any quotient-base algebra is zero,
so the lift can use R. For I = bot the factorization is the usual finite presentation
factorization through a standard smooth stage, and the lift can use C after carrier
transport. Empty relations use determinant 1 and the extra equation z - 1. A zero algebra
has the standard smooth subsingleton presentation supported by Mathlib. None of these
arguments uses nilpotence. The carrier bounds follow from finite polynomial presentations
and ULift, rather than a smallness assumption on A or C.

## No longer needed

None. No original import is removed, and no planned mathematical step is bypassed.
The old proof dependencies now occur under the two new construction nodes instead of
being immediate dependencies of the original node. In particular, reduction and finite
presentation factorization, relative finite presentation, composition, partial derivatives,
and the submersive presentation argument remain needed. No previously required module or
node is claimed globally pruned. The new statements do not need square-zero lifting,
formal smooth lifting into A prime, Nakayama, or the later kernel construction, which were
already outside the scope of this item.

## Where the brief, the DAG or earlier work was wrong

The brief says dependencies have been imported, but the assigned file only imported
`Sheaf.RingTheory.IndStandardSmooth`; most other recorded dependencies are Mathlib APIs.
No false statement or signature correction was needed. The source Stacks Tag 07CK assumes
I squared = zero for its final map B to A prime. Its presentation construction and reduction
isomorphism used here do not require that hypothesis, as the assigned statement specifies.
The local literature checkout has no smoothing.tex; the source was read at
https://stacks.math.columbia.edu/tag/07CK and checked against the existing detailed node.
LeanSearch returned Internal Server Error for both new-statement searches; these are
recorded as unavailable, not no-match. LeanFinder, Loogle, Mathlib source grep, and searches
of existing DAG/blueprint nodes found no exact theorem supplying either construction.
The ancestor helper returned None for the core node despite its explicit blueprint.from
record; the new records preserve that explicit ancestor and prepend the core node to via.

## New nodes

`lem-weil-pbc-popescu-standard-reduction-factor` groups original steps 1--6, after the
ind standard smooth refinement: descend the map, factor through a finite presentation
stage, add finite correction variables, and identify the standard smooth reduction.
Its statement retains arbitrary ideals and all original factorization data, but asserts
no lift B. Its module is `Sheaf.RingTheory.PopescuStandardReductionFactor`.

`lem-weil-pbc-standard-smooth-quotient-lift` groups original steps 7--8: lift a finite
submersive presentation, adjoin the inverse Jacobian minor, compute the enlarged minor,
and construct inverse reduction maps. Its module is
`Sheaf.RingTheory.StandardSmoothQuotientLift`. It is independent of the colimit and
factorization constructions and can be proved in parallel with the first node.
No change record is needed: no existing statement, definition, or public import changed.

## Second reading by R1

1. I compared `PopescuLiftOnceCore.lean` with the repository version. The existing theorem
   signature and all pre-existing declarations are byte-for-byte unchanged; only proof
   imports and the proof body changed. The two added modules contain only the split
   public theorem declarations listed in this report.

2. I compiled all three delivered modules with `lcompile.py --all`. They compile without
   errors or warnings. The core theorem has no `sorry`; the two split construction
   theorems retain exactly the named `sorry`s and no definition contains `sorry`. No
   forbidden axiom, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was
   added. The core proof uses only the existing ind-standard-smooth theorem, the two
   split constructions, and the standard-smooth-implies-smooth instance.

3. I checked the two split statements against their docstrings, source (Stacks Tag 07CK),
   and the original target. The factor statement is the first construction through a
   finitely presented factor with standard-smooth reduction and omits the later lift;
   the quotient-lift statement is the Jacobian presentation lift and omits the factor
   map. Both are strictly simpler than the original target, retain its hypotheses, and
   are true for edge cases such as zero and top ideals. Searches recorded in their node
   files found no existing declaration supplying either result.

4. The core node's proof, dependencies, and origin now match the proof body. The two new
   nodes have matching Lean declarations, sources, proof plans, and split status. The
   unit route remains intact: the core still applies the ind-standard-smooth refinement,
   then the factor construction, then the quotient lift, and finally smoothness and
   restriction of scalars. No old proof dependency is claimed pruned.

5. I checked imports and visibility. Imports needed only by proofs are plain `import`; the
   public imports of each new module support its public theorem statement. No existing
   target or definition was changed, and no downstream module requires adaptation.

I changed only the report by adding this second-reading record; the proof and node files
were otherwise left as delivered.
