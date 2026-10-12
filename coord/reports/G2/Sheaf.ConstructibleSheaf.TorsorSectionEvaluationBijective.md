## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.GaloisCover.sectionEvaluation_bijective` without changing its
signature or visibility. Its proof now constructs the singleton etale surjective cover
`W ×_V Y -> W`, uses bijectivity on an object admitting a morphism to `Y` to prove the
covering equalizer and image sieve conditions, and applies Mathlib's general
`Sheaf.isLocallyBijective_iff_isIso` followed by componentwise module bijectivity.

Added `Sheaf.ConstructibleSheaf.TorsorSectionEvaluationLocal`, containing the remaining
local evaluation step, and `Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf`, whose
sheaf theorem is proved. The latter uses the existing continuous-function sheaf on the
small etale site, continuous base change, and `Subfunctor.isSheaf_iff`: equivariance is a
local condition because the ambient function sheaf is separated. An explicit natural
isomorphism identifies discrete continuous functions with locally constant functions,
and the module forgetful functor reflects the sheaf condition. All private helpers are
proved, and the helper definitions are actual constructions.

The target module imports the two new modules and Mathlib's locally bijective criterion
as proof-only imports. The new local module publicly imports the inverse-image definitions
needed in its statement. The existing target module's public imports remain unchanged.
The parent's DAG proof, dependencies, and proof origin now follow the Lean argument.
No target, existing definition, or existing statement changed. No forced adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.sectionEvaluation_bijective`
(node `lem-weil-pbc-torsor-section-evaluation-bijective`).

Added and proved:
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`
(node `lem-weil-pbc-torsor-equivariant-presheaf-sheaf`). This theorem is valid for arbitrary
coefficient natural numbers, arbitrary representations, and disconnected bases and total
spaces; it does not require primality, finite generation, or the trivialization hypothesis.

The delivery leaves exactly one hole, in the new module:
`AlgebraicGeometry.Scheme.GaloisCover.sectionEvaluation_bijective_of_section`
(node `lem-weil-pbc-torsor-section-evaluation-local`). It is the local statement on an
etale object with a supplied morphism to the total space of the torsor. That morphism
splits the torsor above the object. The statement retains the original trivialization
and normalization assumptions. Its docstring gives the constant-section identification
and inverse formulas, including the empty-object and zero-module cases.

Thus this is a decomposition of the original hole into one strictly local hole, with
both the entire global descent argument and the general equivariant sheaf condition
proved. Holes closed: one. Holes added: one. Net hole count: zero. There is no `sorry`
in the original module or in the new sheaf module, and none in any definition or private
helper. All three modules compile without warnings through `lcompile.py --all`.

## No longer needed

Removed the direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` from the original module: the
new local statement already publicly provides its necessary inverse-image interface.
That module is still needed transitively, so no library module is claimed to be
unreachable. No public import was removed or privatized.

The parent no longer directly uses the connectedness, constant-sheaf, or inverse-image
nodes (`def-weil-connected-scheme`, `def-weil-pbc-constant-sheaf`, and
`def-weil-pbc-inverse-image`); these are retained in the local lemma, where the argument
needs them. The representation definition remains a parent dependency. No unit statement
or realized unit step is bypassed. No planned theory module becomes entirely unnecessary.

The new sheaf proof needs no extra module for module limits: its existing imports already
provide the needed limit lemmas. Its only three proof imports are the continuous-function
sheaf, the continuous base-change interface, and Mathlib's subsheaf criterion.

## Where the brief, the DAG or earlier work was wrong

The original DAG marks its three proof steps non-elementary but names only definition
nodes as dependencies. Those declarations do not state the local evaluation assertion
or the equivariant presheaf sheaf condition. This delivery supplies those two missing
interfaces and proves the second one. The global gluing step is already available in
Mathlib's locally bijective sheaf criterion, so a separate new global gluing theorem
is unnecessary.

LeanSearch returned Internal Server Error; this is recorded without a match verdict.
LeanFinder, Loogle, project search, and Mathlib search supplied no duplicate local
normalized evaluation result. The useful existing tools were inspected in source and
used in the compiling proof. The Stacks sources were read in the available local mirror;
the repository's advertised `literature/stacks-project/` files are absent on this clone.

For the next worker on the local statement, the useful independently proved interfaces
are `Etale.upperStarIsoLocalizationRestriction` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
`Scheme.Etale.constantSheafIsoContinuousMapSheaf` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`, and
`Scheme.bijective_toSheafify_app_terminal` in
`WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections` (the last is abelian-valued,
so module forgetful compatibility is needed). These are not imported merely as prospects.
The harder remaining work is to connect these interfaces to graph evaluation and to
extend values along the torsor translates with the inverse-deck-action convention.

## New nodes

`lem-weil-pbc-torsor-section-evaluation-local` is the remaining local part of the original
first proof step. Its module is
`lean/Sheaf/ConstructibleSheaf/TorsorSectionEvaluationLocal.lean`; its supplied map to the
torsor is essential. The original module's proof establishes that this special local
statement implies the global result using a genuine cover and sheaf descent.

`lem-weil-pbc-torsor-equivariant-presheaf-sheaf` records the fully proved sheaf condition
for scalar-restricted equivariant locally constant torsor functions. Its module is
`lean/Sheaf/ConstructibleSheaf/TorsorEquivariantPresheafSheaf.lean`. It provides the sheaf
needed to apply Mathlib's descent criterion and contains no remaining hole.

Both nodes stay in chapter `sec-proper-base-change` and unit `sk-thm-p1`. No change record
is needed because no existing interface changed.

## Second reading by G2

1. Compared each delivered module against the repository versions. The existing target theorem's
signature and visibility are byte-for-byte unchanged; only its proof and imports changed. The two
new modules and three node records are additions declared in this report. Verdict: pass.

2. Compiled all three modules with `lcompile.py --all`; compilation succeeds without warnings.
There is no axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The only
remaining `sorry` is the explicitly split theorem
`Scheme.GaloisCover.sectionEvaluation_bijective_of_section`; the proved target and sheaf theorem
have no sorry. Verdict: pass, with that named split hole retained.

3. Checked the split local statement and the equivariant sheaf statement against their node
records and source. The local statement is strictly stronger in hypotheses than the target and
is exactly the supplied-section reduction used by the parent; the sheaf statement is general in
V, P, and N and has no unnecessary connectedness or primality assumptions. Searches recorded in
the node files found no duplicate declaration. Verdict: pass.

4. Read the proofs from the target downward. The parent uses the local evaluation theorem and the
proved equivariant sheaf theorem, then Mathlib's locally-bijective sheaf criterion. Its covering,
local injectivity, and local surjectivity arguments match the stated proof steps. Removed the old
direct proof import and retained the public imports required by the new statements. Verdict: pass.

5. Checked the DAG proof, proof dependencies, proof origins, unit, and realized route against the
Lean proofs. The parent records both split interfaces and the Mathlib descent route; the new nodes
record their actual constructions and remaining local hole. Verdict: pass.

Changed during second reading: made the two new nodes’ `lean.statement` fields verbatim
multiline copies of their Lean signatures and added this review section. No Lean proof or
statement needed repair.

The scratch axiom checks show exactly `propext`, `Classical.choice`, and `Quot.sound` for
`equivariantModulePresheaf_isSheaf`; the target and the local split theorem additionally use
`sorryAx`, as expected from the one retained local hole. Fresh second-reader LeanFinder and
project searches using graph-evaluation and torsor-constant terminology found general local
bijectivity tools but no duplicate normalized local evaluation theorem. Checked the realized
steps of `sk-thm-p1`: none is removed or bypassed. Small cases checked: empty W has unique
sections, the zero coefficient module gives unique functions, and the identity torsor gives
the usual constant-function evaluation. Closing the local hole requires the substantial
constant-sheaf/localization comparison and torsor translate construction, rather than a
few-minute application of an existing lemma.
