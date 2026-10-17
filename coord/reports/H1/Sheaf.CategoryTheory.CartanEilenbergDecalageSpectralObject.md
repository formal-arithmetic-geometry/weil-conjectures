## What changed

Reduced `CategoryTheory.cartanEilenberg_decalage_spectralObject` to construction of a
natural spectral-object comparison morphism invertible on bottom intervals only.
Proved `CategoryTheory.Abelian.SpectralObject.isIso_of_bottom_intervals`: form the
six-term interval exact sequences, apply the abelian five lemma to their first five
terms, then assemble the componentwise natural inverses into a spectral-object inverse.
The original theorem now obtains its isomorphisms by this criterion and `asIso`;
their hom maps retain the construction's presentation naturality.

All three sandbox modules compile. The target signature and both existing augmentation
square theorems are unchanged.

## Proved and sorry left

Closed the item's sole original hole by reduction:
`CategoryTheory.cartanEilenberg_decalage_spectralObject`.
Added one hole, `CategoryTheory.cartanEilenberg_decalage_spectralObject_iso_exists`,
node `lem-sp-ce-decalage-spectral-object-iso-exists`. This is a decomposition, with
net zero holes closed. The remaining theorem constructs the comparison morphism
and proves invertibility only on intervals (minus infinity,b). It still needs the
normalized CE augmentation, derived truncation and cone comparison construction.

The new generic theorem
`CategoryTheory.Abelian.SpectralObject.isIso_of_bottom_intervals`, node
`lem-sp-spectral-object-bottom-iso-criterion`, is fully proved, with zero holes.
Its proof handles all intervals and connecting maps when assembling the inverse.

## No longer needed

Removed direct proof imports of `Sheaf.CategoryTheory.CartanEilenbergTruncationResolution`,
`Sheaf.CategoryTheory.CartanEilenbergMappedTotal`,
`Sheaf.CategoryTheory.LeftExactTruncationIso`,
`Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`,
`Sheaf.CategoryTheory.DoubleComplexTruncationDecalage`, and
`Sheaf.CategoryTheory.DerivedUpperTruncationComparison` from the item. These are now proof imports of the remaining construction module;
none is claimed globally pruned.
General interval invertibility no longer needs a CE-specific proof: the generic
five lemma derives it from bottom intervals. The corresponding original construction
nodes remain dependencies of the new comparison-morphism node.

## Where the brief, the DAG or earlier work was wrong

The plan combined construction of a comparison morphism and invertibility on every
interval. The latter requires only a generic five-lemma argument once invertibility
on bottom intervals is known. No hypothesis or conclusion of the original statement
was changed. An initial exploratory split with arbitrary comparison isomorphisms was
unsound and was removed before delivery; no such theorem remains in the sandbox.

## New nodes

`lem-sp-ce-decalage-spectral-object-iso-exists` states the comparison morphism,
presentation naturality, and invertibility on bottom intervals. The open work is its
normalized derived-resolution and triangle comparison construction.

`lem-sp-spectral-object-bottom-iso-criterion` is the proved, general abelian
spectral-object five lemma. It has no CE, functor, filtration or derived-category
hypotheses. The proof uses Mathlib's abelian five lemma on the interval exact sequences.

## Second reading by H1

1. I compared the delivered item module with the repository version. The target
   declaration and both existing augmentation-square signatures are byte-for-byte
   unchanged; only proof text and proof-only imports changed. The two added modules
   contain the split theorem and the generic criterion recorded by their new nodes.
   Verdict: pass.
2. I compiled all three sandbox modules with `lcompile.py --all`; compilation is
   clean. The generic criterion has no `sorry`, and its axiom probe reports only
   `propext`, `Classical.choice`, and `Quot.sound`. The sole remaining `sorry` is
   the named construction theorem listed above, with its node and proof docstring.
   Verdict: pass.
3. I checked the split statements against the source route and searched the library
   for duplicate declarations. The construction theorem is strictly weaker than the
   target (bottom intervals only), while the generic five-lemma criterion is a
   reusable intermediate result; neither restates the target. Verdict: pass.
4. I checked the proof from the target downward. The target uses the construction
   theorem and the generic criterion; the latter is proved directly from interval
   exactness and the abelian five lemma. The six former direct proof imports were
   removed from the item and remain available through the construction module.
   Verdict: pass; no additional pruning was found.
5. I checked the DAG nodes against the Lean declarations, including statements,
   proof steps, proof dependencies, origins, unit and chapter fields. The unit's
   realized route remains the construction followed by the bottom-interval
   criterion. Verdict: pass.

I changed the report by adding this second-reading record only; no Lean statement,
definition, or proof was changed during the review.
