## What changed

Reduced `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_local_twist_descent`
to three geometric steps in new modules. Its signature, existing public imports, and docstring are
unchanged. The parent module contains a complete proof; no existing module besides the item changes.

The proof chooses the local integer normal forms, restricts two of them to their common open, and
uses integer twist separation to show that the chosen exponents define a locally constant function.
It identifies the concrete variable twist locally with L using the restriction identity, transports
invertibility from L, and takes the concrete dual-evaluation inverse. Tensoring this inverse with L
gives a module which the proof explicitly
trivializes over each chosen base neighbourhood. Relatively trivial line descent supplies the
coefficient line, and inverse evaluation plus associativity constructs the required presentation.

For uniqueness, a proved private lemma simultaneously makes a candidate degree constant and
trivializes its coefficient line. Pullback composition and the restriction square give an integer
normal form of L there. Comparing with the originally chosen form determines the degree pointwise.
The fully faithful tensor functor of the explicit two-sided inverse cancels the common twist;
reflection of base-line isomorphism classes then identifies the coefficients.

The five private helpers compare explicit and ordinary pullback, preserve the unit, restrict
isomorphisms to smaller opens, transport invertibility through local isomorphisms, and construct the
local integer normal form of a decomposition. All are proved or concrete constructions.
Existential isomorphisms are eliminated inside proofs; no data definition chooses an arbitrary
witness from an unproved existence theorem.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_local_twist_descent`.
Added three holes, each exactly the full body of a public theorem in its own new module:

- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_integer_twist_separation`
  (`lem-sfb-projective-bundle-integer-twist-separation`).
- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_relatively_trivial_line_descent`
  (`lem-sfb-projective-bundle-relatively-trivial-line-descent`).
- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_pullback_line_reflection`
  (`lem-sfb-projective-bundle-pullback-line-reflection`).

This is a decomposition: 1 upper hole closed, 3 lower holes added, net -2. The item module has zero
holes; each new module has one. The existing twist-identity theorem remains an imported dependency.
Every new hole has a source, a complete proof in words, and its matching DAG node. No definition,
instance, private declaration, or anonymous subproof contains a hole.

Validation: the final four-file compile succeeded without warnings in 12.8, 12.4, 12.5, and 20.3
seconds (the parent last). The parent uses the given invertibility hypothesis to prove invertibility
of the variable twist and construct its actual dual inverse. The unchanged direct consumer
`Sheaf.AlgebraicGeometry.ProjectiveBundlePicardClassification` compiled against the delivery in
15.2 seconds; its temporary verification copy was removed before delivery. Parent signature and
public imports match the original exactly, and new Lean signatures match their node records.

## No longer needed

No original public import was removed. The new proof imports only the three new modules, the existing
`LocallyConstantLineTwistIdentities`, and `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`.
The new coefficient-descent and coefficient-reflection modules omit the unused line-twist import;
their statements contain no degree or tautological line.

The original direct proof dependencies `lem-sfb-projective-bundle-local-normal-form`,
`lem-weil-pbc-glue-sheaves-of-modules`, and `lem-pc-projective-space-twist-cohomology` move to the
geometric steps which need them. They remain needed in those proof plans; this is not global pruning.
The quotient geometry likewise remains required by the geometric steps and the preserved statement.
No module is withdrawn, and no previously adopted source declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies do not directly provide local separation on an arbitrary residue-field
fibre, descent of a module trivial above base neighbourhoods, or reflection of base-line isomorphism
classes. The field normal-form theorem alone needs the fibre/tautological-line comparison before it
can be applied. General module-sheaf gluing alone does not descend scalar transition functions:
one must identify the canonical ring map on functions over every base open. The two coefficient
lemmas isolate precisely that remaining descent argument. The recorded projective-space cohomology
attachment is stated over a field, while its source module also contains the general ring-level
constant-monomial comparison; arbitrary-base and restriction compatibility still need to be supplied
in those geometric proofs. None of these gaps is filled by claiming an arbitrary ring isomorphism
is the structure map.

The new statements are strictly smaller than the item. Integer separation has no descent conclusion.
Relative triviality descent has no degree function, tautological line, or uniqueness clause.
Coefficient reflection assumes two base lines already exist and only reflects their isomorphism
classes. The latter two require positive rank, including rank one, rather than rank at least two.
Their natural-language proofs use the source's unit-transition argument. The original module proves
the gluing of degrees, residual triviality, tensor reassembly, and cancellation itself.

Edge cases checked: a base point in the neighbourhood prevents a vacuous degree-separation claim;
rank two gives projective lines, whereas rank one is excluded only for degree separation. The
coefficient statements include rank one and the empty base. Empty bases in the parent use the empty
choice family and a vacuously locally constant function. Negative and unbounded degrees use the
existing integer-power/twist calculus. Infinitely many degree strata are never commuted with
pullback as an arbitrary product. No Noetherian, reducedness, quasi-compactness, connectedness, or
section-of-the-projection hypothesis is added. The unit record assigns no realized statement or
proof step to this auxiliary node, and its route is retained.

## New nodes

`lem-sfb-projective-bundle-integer-twist-separation` is the residue-field exponent comparison of
original step 1. Source: EGA II Remark 4.2.7, Stacks Tag 0BXJ, and normalized quotient/base-change
geometry. It is used twice: to glue local degrees and to compare a competing decomposition.

`lem-sfb-projective-bundle-relatively-trivial-line-descent` is effective scalar-transition descent
for the degree-zero residual module (original steps 2-3). Source: the constant-monomial calculation
of Tag 01XS and gluing in Tags 00AL, 00AM, and 04TN.

`lem-sfb-projective-bundle-pullback-line-reflection` is the coefficient uniqueness argument in
original step 4, after tensor cancellation has already been performed in Lean. Source: the same
canonical function calculation and Tag 04TN.

Actual `msearch.py` searches were recorded for every node: separate LeanSearch queries for the three
geometric statements, Loogle on pullback/invertibility, and Mathlib grep on projective Picard and
locally constant gluing. LeanSearch returned basic Proj/power and general pullback/free-module APIs;
Loogle returned two unrelated vector-field pullback results; grep returned no match. A broader
LeanFinder query returned Proj and ring-Picard declarations, with no projective-bundle descent theorem.
Repository and DAG searches found the existing parent, local normal forms, twist identities, and the
projective-line consumer, which itself depends on the parent and cannot be imported without a cycle.
The three new node records contain the actual query texts, results, source plans, and Lean signatures.
No change record is needed because no existing interface changes.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
