## What changed

Replaced the hole in `Algebra.exists_localized_noetherian_approximation` with a complete
Lean reduction to two distinct parts of the existing fraction-localization argument.
The existing signature and docstring are unchanged. Added proof-only imports of
`Sheaf.RingTheory.LocalizedApproximationCocones`,
`Sheaf.RingTheory.LocalizedApproximationTransitions`,
`Mathlib.RingTheory.Localization.Submodule`.
The construction lemma assumes neither Noetherianity, finiteness nor transition tensor
isomorphisms. The transition lemma assumes neither colimits nor Noetherianity nor finiteness.
The main proof verifies contraction compatibility using cocone naturality, rewrites the
base-stage contracted prime, proves both stage Noetherian assertions with
`IsLocalization.isNoetherianRing`, proves stage module finiteness by transporting a
finite spanning set through its numerator map using `span_eq_top_of_isLocalizedModule`,
and combines the independent transition result with the constructed cocones.
A declaration-scoped `linter.unusedVariables false` preserves the existing named
nondependent forall binder `hmodel`, as in its caller IntegerApproximationFlatPointStage.
No definitions or existing signatures were changed; no downstream adaptation is necessary.

## Proved and sorry left

Closed the original hole in `Algebra.exists_localized_noetherian_approximation`
(node `lem-weil-pbc-noetherian-approximation-localized-diagrams`). Its proof has no sorry.
Added exactly two named holes, each the whole proof of a public theorem in its own module:

- `Algebra.exists_localized_approximation_cocones`
  (`lem-weil-pbc-localized-approximation-cocones`). This constructs prime-localized
  diagrams, numerator maps, and limit/stage comparisons, without assuming or asserting
  stage finiteness or transition tensor base changes.
- `Algebra.localized_approximation_transition_base_change`
  (`lem-weil-pbc-localized-approximation-transitions`). This proves the localized ring
  and module transition base changes from compatible localization witnesses and the
  original tensor isomorphisms; no colimit or finiteness construction is included.

This is a decomposition: one upper hole closed, two lower holes added, net minus one.
Stage Noetherianity and finite generation, and contraction compatibility, are proved
in the assembly rather than postponed. The remaining statements are strictly parts
of the argument, with different hypotheses. All three modules are checked with
`lcompile.py --all`; the delivery dry run includes the axiom probes.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
from the main module. Its node remains a dependency of the new cocone-construction node;
this removal does not claim that the filtered-localization argument is globally pruned.
Likewise `def-weil-directed-colimit-abelian-groups` remains under cocone construction,
and the two tensor-localization nodes remain under transition localization.
`lem-weil-pbc-localization-noetherian` remains a direct dependency used in the main proof.
No existing node or module is claimed globally unnecessary. No unit-realizing statement
or proof step is bypassed. Unused imports were removed from the new modules.

## Where the brief, the DAG or earlier work was wrong

The parent node's plan groups several constructions that the current dependency signatures
do not supply as one usable interface. In particular the ring-colimit theorem alone does
not construct the module cocone with its restricted-scalar comparisons; and the tensor
localization lemmas do not immediately state the prime-localized transition conclusion.
The delivery exposes these two separate tasks, with natural numerator maps included so
that the transition comparison is applicable to the constructed system.
The repository does not contain the referenced `literature/stacks-project/algebra.tex`
on this machine. Read the official Stacks pages for [00RC](https://stacks.math.columbia.edu/tag/00RC),
[00QX](https://stacks.math.columbia.edu/tag/00QX), and
[037D](https://stacks.math.columbia.edu/tag/037D) instead.
Tag 037D states normality of directed colimits; its proof contains the localized-colimit
identity being used, exactly as the existing dependency docstring specifies.
No mathematical error or statement dispute was found. Checked edge cases: a singleton
index reduces to ordinary prime localization; zero modules give zero localized modules
and zero tensor comparisons; zero rings admit no primes, so introduce no exceptional case;
noninjective transitions are allowed since fraction relations can be killed by denominators.

## New nodes

`lem-weil-pbc-localized-approximation-cocones`, module
`Sheaf.RingTheory.LocalizedApproximationCocones`, records steps 1, 2 and 5 of the parent's
plan and the local-ring/local-map part of step 3. It deliberately drops all finiteness
hypotheses and conclusions. Its natural stage-localization witnesses and numerator maps
are the interface required for the second part. No arbitrary witness is used in a definition.

`lem-weil-pbc-localized-approximation-transitions`, module
`Sheaf.RingTheory.LocalizedApproximationTransitions`, records step 4 for an arbitrary
preorder system of compatible prime localizations. Its IsLocalizedModule witnesses
include the exact numerator maps, so its pure-tensor formulas concern the actual diagram
transitions. No colimit is assumed or constructed.

Both nodes inherit the parent's chapter and unit. Their searches record LeanFinder,
Loogle and local grep; LeanSearch was unavailable (Internal Server Error), not treated as
an absence result. No change record is needed because existing interfaces stay identical.

## Second reading by J3

1. Compared the delivered item module with the repository version. The existing target
   signature is unchanged; only proof imports, proof code, and the DAG proof route changed.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no errors or
   forbidden declarations. The only remaining `sorry`s are the two named split-off
   theorems, each with a matching node and proof docstring.
3. Checked both split-off statements against their hypotheses and edge cases (singleton
   index, zero module, and noninjective transitions). They are true, strictly smaller parts
   of the parent argument, and do not duplicate an existing library result.
4. Verified the shortest route through the cocone and transition interfaces, removed unused
   direct imports, and checked that the DAG proof, dependencies, and origin agree with Lean.
   No unit step is bypassed.
5. Confirmed unit `sk-thm-p1` remains realized by the parent and both split nodes; no target
   or existing public signature was weakened or changed.

The second reading changed only this report section.
