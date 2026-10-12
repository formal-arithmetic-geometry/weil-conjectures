## What changed

Proved `henselian_pair_approximation` with its original signature and definitions unchanged.
The first worker's `henselian_pair_approximation_of_regular` moved essentially the whole
argument into a new sorry; the second reading removed it and its node. The delivery now
writes the smooth factorization, étale lifting, henselian retraction, quotient uniqueness,
polynomial evaluation and completion-kernel calculations as actual Lean proofs.

The proved helper `exists_smooth_polynomial_factorization` has its own new module
`Sheaf.RingTheory.SmoothPolynomialFactorization`. It factors solutions along any regular
map of Noetherian rings, using the existing `RingHom.popescu_smoothing` and Mathlib's
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`, with the finite polynomial
quotient constructed explicitly. Its public imports supply signature types; Popescu
and finite-presentation imports are private. Existing public imports of the item are unchanged.
No existing statement, definition or public import changes, so the preliminary change
record `coord/changes/henselian_pair_approximation.md` was removed as inapplicable.

## Proved and sorry left

The original item declaration `henselian_pair_approximation` is proved: 1 of 1 original
sorries replaced by a complete proof. The new `exists_smooth_polynomial_factorization`
is also proved. No sorry remains in either delivered module; zero statements are left
split off. The private Gabber-root helper is proved from `HenselianRing.is_henselian`.

These proofs depend on still-open imported declarations: Popescu smoothing, completion
Noetherianity, regularity of G-ring completion, smooth-section étale lifting, and Gabber-root
étale section lifting. Their transitive `sorryAx` therefore remains in the axiom output;
this delivery does not claim an axiom-free target closure.

## No longer needed

Removed proof imports `Sheaf.RingTheory.HenselianFactorizationCriterion` and
`WeilConjectures.Mathlib.RingTheory.Henselian`. The original direct proof dependency
`lem-weil-pbc-henselian-factorization-criterion` is pruned from this item: simple-root
Hensel gives the required Gabber root directly. No globally-unreachable module is claimed.

`lem-weil-pbc-popescu-smoothing` and
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit` move from direct
item dependencies to direct dependencies of the proved factorization helper. They are
still used transitively, and are not pruned. `Sheaf.RingTheory.PopescuSmoothing` is imported
only by the helper. The first worker's unused finite-presentation import of the item
is removed; Mathlib completion completeness remains necessary for the kernel calculation.

## Where the brief, the DAG or earlier work was wrong

The first worker's regular-completion approximation theorem was too close to the whole
item and did not implement the reduction from the existing plan's lemmas. Its new node
also recorded queries different from the logged searches, omitted the completion's
Noetherian hypothesis in its prose statement, and had no corresponding update to the
item's proof dependencies. These faults are repaired by removing that theorem and node,
proving the genuine polynomial-factorization step, and updating the original node.

Stacks 0AH5 writes “A → P smooth” in the factorization paragraph where B is intended;
the existing DAG already identifies that source typo. The quotient-agreement argument
left implicit in Stacks is fully written: the retraction modulo I^N factors through
A′/I^N A′, and composition with its A-algebra quotient isomorphism is the identity.

## New nodes

`lem-weil-pbc-smooth-polynomial-factorization` records the proved finite-equations
factorization step, in `lean/Sheaf/RingTheory/SmoothPolynomialFactorization.lean`.
Its statement assumes regularity and Noetherianity of both rings, and concludes a smooth
algebra with a solution mapping to the prescribed one. It has no henselian hypothesis,
no approximation conclusion, and no congruence clause. Its proof invokes the existing
Popescu and finite-presentation nodes, then explicitly evaluates generators and relations.
The three searches were run through msearch.py and exactly match searches.jsonl.
LeanSearch returned HTTP 500 and is recorded as unavailable; LeanFinder returned standard
smoothness/descent lemmas, none an exact match; grep found only unrelated Gabriel-Popescu.
Searches in lean/Sheaf, the upstream Lean sources, the DAG and imported blueprint found
no existing declaration or blueprint node with this precise statement. The blueprint
ancestor is `thm-weil-pbc-finite-etale-lifting`, via the approximation item's step 2.

## Second reading by C2

1. Compared both delivered modules with repository sources using diff. The only existing
public declaration is `henselian_pair_approximation`; its full signature is byte-for-byte
unchanged. No data definition changed. The item's original public imports are unchanged.
The new public theorem is in its own module with its matching node; the private Gabber
helper changes no public signature. Removed the first worker's inaccurate change record.

2. Compiled both modules in import order using lcompile.py: clean, without warnings.
Neither module contains sorry, axiom, unsafe, opaque, implemented_by or extern, and there
are no hollow definitions. Scratch #print axioms for both public theorems shows only
propext, Classical.choice, Quot.sound and transitive sorryAx from existing open dependencies.
The Gabber helper is Mathlib Hensel at the simple reduced root 1, with derivative 1.

3. No split-off sorry remains. Independently read Stacks 0AH5 and 07GC and the existing
Lean declarations. The new factorization theorem exactly implements step 2: the quotient
ideal is generated by the finite range of f; finite presentation comes from Mathlib;
the stage hom is proved to commute with A; the quotient equations and coprojection
values are checked by evaluation. Empty equations (m=0), empty variables (n=0), the
zero ring, and the identity regular map are admitted and the constructions still work.
For the target, I=0 gives the original solution, N=1 is allowed, and no local-ring or
proper-ideal hypothesis was introduced. N≥1 is used only for I^N≤I when reducing a section.
All new-node search records match actual msearch logs; unavailable service is not a match.

4. Read the proof top downward. Regularity and completion Noetherianity are established
before Popescu; smooth lifting is applied to J=I^N. Henselian section lifting is applied
to I, using σ1 obtained from σN and I^N≤I, so there is no illicit henselian instance for
I^N. The étale scheme hypothesis is converted to Algebra.Etale via Spec_iff. Every
A-algebra map to A/I^N kills the extended ideal, and quotient-hom extensionality shows
χbar∘α=id, which proves the congruence. Polynomial evaluation transports the equations;
Mathlib's completion evaluation kernel and Ideal.smul_top_eq_map prove ideal membership.
The No longer needed section lists every discarded original direct dependency and
separately names those moved below the helper. Read dag/units/sk-thm-p1.json: neither the
approximation lemma nor the removed factorization-criterion node is a realized unit
statement/step; all realized nodes and the six-step approximation route are retained.

5. Updated the item's proof steps 2 and 4, proof_deps and proof_origin to match the code.
The new node's lean.statement is the verbatim signature; its proof_deps are precisely the
union of its proof-step uses, its source is 0AH5's smooth-factorization paragraph, and
its created, blueprint, chapter, unit and search fields are present. No existing node's
statement, stmt_deps or other non-stage-3 field is changed.

Changes made by this second reading: replaced the near-restatement sorry with a fully
proved factorization theorem and a complete target proof; corrected the nodes, imports,
source docstrings and report; removed the unnecessary change record and linter suppression.
