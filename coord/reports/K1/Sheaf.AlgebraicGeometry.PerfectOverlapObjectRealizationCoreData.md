## What changed

Proved `AlgebraicGeometry.perfect_overlap_object_realization_core_data_at` in
`Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData`, with its statement
unchanged. The pointwise theorem appeared in the refreshed repository during this
session; the earlier version had the family theorem itself as the first hole.

The construction uses six proved private helpers. It constructs the three restricted
pullback functors, obtains beta from the fixed pullback composition and open-inclusion
comparisons, and lifts gamma through the fully faithful precomposition functor of exact
open restriction. `map_preimage` and cancellation prove both diagram coherence laws.
For composable scheme maps, the restricted composite equality gives kappa; theta is
its prescribed composite with phi and the site-return comparison. The cocone equation
provides the required equality of the finite-stage and apex base-change maps.

Added proof-only imports of `DerivedOpenRestrictionLocalization` and
`SingleComplexOpenRestrictionData`. The import change is recorded in
`coord/changes/perfect_overlap_object_realization_core_data_imports.md`. Updated the single-stage node's proof and
proof dependencies. All public signatures, definitions, and visibility are unchanged.

Validation: the scratch construction compiled without holes; the integrated module
compiled cleanly in 58.1 seconds before documentation-only edits. The required dry run
is the final validation. The construction includes empty and coincident opens and
arbitrary unbounded objects: it never assumes a point, a nonzero object, or an affine
open. It constructs the comparison data explicitly, rather than choosing an arbitrary
witness of the statement being proved.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.perfect_overlap_object_realization_core_data_at`
(node `lem-pc-perfect-overlap-object-realization-core-data-at`). The already proved
`perfect_overlap_object_realization_core_data_family` now obtains its data from this
proved constructor.

The only remaining literal hole is
`AlgebraicGeometry.perfect_overlap_object_realization_core_of_data`
(node `lem-pc-perfect-overlap-object-realization-core-of-data`). It is marked
`STATEMENT-DISPUTED`; the mathematical counterexample is given below. Its statement
and proof have not been weakened or replaced. The final
`perfect_overlap_object_realization_core_data` still depends on this unresolved theorem.

Added holes: none. Split-offs: none. This is one proof, not a decomposition.

## No longer needed

No imports, declarations, nodes, or modules are withdrawn. In particular, the stage
and apex equivalence module remains necessary for the unchanged core statement.

The single-stage proof needs no Hom continuity, perfect-Hom lifting, compactness,
finite-presentation, or finiteness theorem. It follows from restriction localization
and pullback composition. No such extra theorem is imported for this construction.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: perfect_overlap_object_realization_core_of_data` quantifies over
**every** family of `TwoOpenTransportData`. The type permits independent choices of
kappaU, kappaV, siteU and siteV at each stage. Its two theta equations merely prescribe
theta from these choices. There is no condition linking these transports to the
comparison diagram's beta/gamma, nor a condition relating them across stages. The
proof sketch assumes the canonical transports and therefore does not prove this
universal statement.

A mathematical counterexample (not a full Lean formalization of the schemes) is the
finite directed chain `0 < 1 < 2` with rings `R0 = R1 = Z`, the identity transition
`R0 -> R1`, and `R2 = Q`. The colimit is `Q`. Take `i = j = 0`, the geometric scheme
`Zgeom = Spec Z`, and `t` its identity. Take both covering opens to be total,
`A = B = O_SpecZ` in degree zero, `E = O_SpecQ` in degree zero, and the standard local
isomorphisms phiU and phiV. All finite-presentation, compactness, quasi-separatedness,
covering, and perfectness assumptions hold.

Start with the canonical diagrams and transports at every stage. At stage 1 only,
postcompose kappaU with multiplication by 2 on the rationalized functor and multiply
thetaU by 2 accordingly. Keep kappaV and every diagram unchanged. Multiplication by 2
is a natural automorphism on the Q-valued target, and the defining theta equations
still hold. This is therefore still a family of precisely the quantified data type.
The canonical identifications between the equal stage-0 and stage-1 rings identify
both Boolean stage objects with `O_SpecZ`, and their canonical apex images with
`O_SpecQ`.

Any asserted core implies the Hom pin: combine its object_pin, naturality of its
comparison, and transition_pin. This implication is already proved, without any
additional hypothesis, by the private `pinned_conjugation` and
`perfect_overlap_object_realization_hom_pin` lemmas in
`PerfectOverlapObjectRealization.lean`. Apply it to the identity morphism from the
false Boolean object to the true Boolean object. The ratio of the two fixed apex
object isomorphisms is a single rational unit r. At stage 0 the Hom pin says that r is
the image of an integral unit, hence `r = 1` or `r = -1`: the two stage object
isomorphisms are automorphisms of `O_SpecZ`, whose endomorphism ring is Z. At stage 1
it instead says that `r / 2` is an integral unit, hence `r = 2` or `r = -2`, because
psi for the false object was multiplied by 2. These requirements are incompatible.
The free choices of transition and baseComparison cannot repair this: transition_pin
fixes their conjugated Hom action to the already defined perfectLimitMap.

The needed repair is to construct the core together with the canonical comparison
data, or to impose precise compatibility conditions on the data. Restricting only
perfectness or geometric finiteness does not address the counterexample. No repair
of this false universal statement is silently made in this delivery, and no weaker
replacement is proved in its place. This finding should be sent upward by the reader.

Sources read: [Stacks 09RE](https://stacks.math.columbia.edu/tag/09RE),
[Stacks 08DW](https://stacks.math.columbia.edu/tag/08DW), and
[Stacks 0D5S](https://stacks.math.columbia.edu/tag/0D5S). They use canonical pullback and
restriction comparisons; they do not assert coherence of independently twisted ones.
The unit `sk-thm-picard-semicon` has no realized node for this intermediate statement,
and no unit or chapter statement or proof route is changed.

Searches recorded in `searches.jsonl`: LeanFinder found scheme restriction/pullback
identities, Loogle found generic whiskering tools, the initial Mathlib grep found no
project-specific overlap type, and LeanSearch was unavailable (HTTP internal server
error). Local searches found the exact open-restriction localization theorem and the
constructed open-pullback isomorphism, which the proof uses.

## Earlier second reading (a previous round; superseded)

Second reader: K1 delivery self-check. The pointwise theorem's binders and conclusion
match `lem-pc-perfect-overlap-object-realization-core-data-at` exactly, including the
independent localization instances, compact-open hypotheses, supplied `phiU` and
`phiV`, and the dependent `Nonempty` comparison type. The proof uses only canonical
composition and restriction constructions and constructs the data at the requested
`k`; no hypothesis is added and no edge case is excluded. The disputed
`core_of_data` signature is unchanged and its counterexample is recorded above.
The module compiles cleanly and the proof imports are private. The updated node records
the actual proof steps and dependencies.

## Second reading by K1

1. **Signatures and statements.** Compared the delivered module with the repository
   version. All existing public declarations, definitions, and visibility are unchanged;
   the additions are private proof imports and private helpers. Verdict: pass.
2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it compiled in
   56.4 seconds with no errors. The pointwise theorem has no `sorry`, and no forbidden
   declarations or hollow definitions were added. The unresolved `core_of_data` theorem is
   unchanged and explicitly marked disputed. Verdict: pass for the delivered proof.
3. **New or split statements.** The added pointwise node is a strict single-stage
   reduction, has a complete source and proof description, and matches the Lean
   declaration. No new sorry or split-off theorem was added. The universal `core_of_data`
   statement is false for independently twisted transports; its counterexample is
   recorded above. Verdict: pass.
4. **Pruning and route.** The proof uses the canonical pullback/restriction construction
   and localization lifting, while retaining the unit route. The two new imports are
   proof-only and are recorded in the change record; no unused import was found. Verdict:
   pass.
5. **DAG agreement.** Updated node `lem-pc-perfect-overlap-object-realization-core-data-at`
   records the actual proof steps, dependencies, origin, and Lean declaration. The family
   and final nodes remain unchanged except for their existing proof use of the pointwise
   theorem. Verdict: pass.

Changed in this second reading: added this required review section and made no code or
statement changes. The delivery is CODEX because it adds a node, a change record,
private imports, and a `STATEMENT-DISPUTED` marker, as required by the stage-3 contract.
