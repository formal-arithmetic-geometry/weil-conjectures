## What changed

Proved `CategoryTheory.derived_homology_injective_surjective` in
`Sheaf.CategoryTheory.DerivedHomologyInjectiveSurjective`, preserving its signature,
universes and visibility. Added the proved private helper `homology_to_single_surjective`.
It extends a homology map across the monomorphism into opcycles using injectivity,
then precomposes with the opcycles quotient to construct a chain map.
The public proof transports this lift through a representative of the derived object
and the localization homology comparison. Added the proof-only import
`Mathlib.Algebra.Homology.SingleHomology`; removing it makes the single-object
homology comparison unavailable. The two existing public imports are preserved.
Updated the existing node's proof and proof_origin to match this construction.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.derived_homology_injective_surjective`
(node `new-stage3-derived-homology-injective-surjective`).
The private helper `homology_to_single_surjective` is also completely proved.
No sorry remains in the item's module, and no hole or new module was added.
The module compiles locally without warnings in approximately two seconds.
The construction includes zero complexes and zero injective objects, requires no
boundedness of the source, and introduces no enough-injectives assumption.

## No longer needed

No original imports, proof-dependency nodes or modules were removed: the node had
no proof dependencies. The planned K-injective model and a chain-map representation
of arbitrary derived morphisms are unnecessary for this surjectivity half.
No unit statement or unit proof step is bypassed; the unit's realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

The old proof plan combined surjectivity with the unrelated null-homotopy argument
for injectivity and suggested using a K-injective model. Surjectivity alone needs
only an explicit chain-map lift followed by localization. The map is extended from
homology into opcycles, rather than extending directly from cycles into the degree-zero
term: passing through opcycles ensures that incoming boundaries are killed.
No statement or definition was changed. No forced adaptations or new nodes were needed.

## Second reading by U1

1. **Visible changes and signatures.** Compared the delivered module with the repository
version. The existing public theorem signature is byte-for-byte unchanged; the added
helper is private, and the only added import is proof-only.
2. **Proof validity.** Compiled the delivered module with `lcompile.py`; it succeeds with
no warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`. The proof uses the explicit opcycles lift and the localization
homology naturality identities, so its construction also covers zero complexes and
zero injectives. The helper and public theorem have no unapproved axioms.
3. **Statements and declarations.** The public statement is exactly the existing DAG
statement and remains the required surjectivity assertion. The private helper is a
strictly simpler chain-level surjectivity lemma, is true by the displayed injective
factorization, and is not an existing library declaration.
4. **Pruning and imports.** Checked the proof dependencies and imports. The
`SingleHomology` import is required by the helper; the two public imports remain
necessary for the target statement and derived-category transport. No old proof
dependency is used or removed, and no new sorry or node was introduced.
5. **Unit route and DAG.** The unit `sk-prop-sf-cbc` remains represented by the existing
target node; the delivery changes only its proof and proof origin to record the
Mathlib-only chain-level route. The sandbox node's proof steps and metadata agree with
the Lean proof, and no unit statement or target statement was bypassed.

Changed in this second reading: added this review record only; no Lean declarations,
statements, definitions, or DAG statements were altered.
