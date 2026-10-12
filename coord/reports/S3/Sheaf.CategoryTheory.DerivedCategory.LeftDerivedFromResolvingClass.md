## What changed

Proved `CategoryTheory.Functor.leftDerived_from_resolvingClass` without changing its
statement, binders or universes. The proof uses the existing quasi-isomorphism-system and
Stacks-to-Kan bridge declarations, constructs the total left derived functor with Mathlib,
and compares limit cones to prove invertibility of the counit on P.

Added two proved helper modules: `ResolvingClassEssentialConstancy` proves the resolving-class
argument, and `LeftDerivedExactOfLocalization` transports the existing exactness theorem
from the strict constructed localization to the chosen derived category. Both helpers
have complete Lean proofs and introduce no holes. Updated the parent and helper DAG proofs
to follow the Lean. All three modules compile without warnings using lcompile.py.

## Proved and sorry left

Closed the original hole in `CategoryTheory.Functor.leftDerived_from_resolvingClass`.
One original hole closed, zero holes added, zero statements left split off with sorry.
The two new proved declarations are:

- `CategoryTheory.Functor.resolvingClass_essentialConstancy`
  (`lem-pur-resolving-class-essential-constancy`).
- `CategoryTheory.Functor.leftDerived_exact_of_localization`
  (`lem-pur-left-derived-exact-chosen-localization`).

There is no sorry in any delivered module. Existing imported holes remain in
`CategoryTheory.leftDerived_defined_pointwiseKan_bridge`,
`HomotopyCategory.quasiIso_saturated_triangulated`, and
`CategoryTheory.Functor.leftDerived_exact_when_defined` (via the exactness helper).
The delivery proves the assigned statement from these existing stated dependencies;
it does not claim the entire dependency closure is sorry-free.

The resolving helper builds the cofiltered denominator category and its initial full
subcategory of resolving denominators. Every restricted transition is inverted by F;
Mathlib's EventuallyConstant cone extends along the initial inclusion. Naturality gives
the explicit retraction/factorization criterion, and the identity leg on P is invertible.
The exactness helper precomposes LF with the localization equivalence, applies the existing
strict-localization exactness theorem, and descends the resulting shift structure and
exactness along the equivalence.

## No longer needed

Removed the item's direct import of `Sheaf.CategoryTheory.LeftDerivedExactWhenDefined`.
That module and its node remain needed through `LeftDerivedExactOfLocalization`; this is
not pruning of its branch. No existing node or module is rendered unnecessary. The existing
bridge, quasi-isomorphism-system and Mathlib total-left-derived construction are all used.
Removed a redundant `Mathlib.CategoryTheory.Limits.Final` proof import from the new resolving
helper: `Mathlib.CategoryTheory.Filtered.Final` already provides it.

## Where the brief, the DAG or earlier work was wrong

The plan's Step 1 omitted the Lean construction of a natural cone on all denominators.
The proved resolving helper makes initiality, cofilteredness, the normalized cone, and its
factorization/comparison clauses explicit using Mathlib.

The existing exactness theorem assumes `Q.IsStrictLocalizationAt S`, which demands literal
factorization and literal uniqueness of functors. Mathlib's `HasDerivedCategory` allows any
chosen localization up to equivalence and does not give this strict property for Qh. The
proved exactness helper supplies the missing transport. No existing statement or definition
has been changed.

Checked edge cases: an empty source category makes the resolving witness theorem vacuous;
in a nonempty category hres excludes P being empty; identity denominators lie in W; for
X in P the identity denominator is resolving and its comparison leg is invertible. No
closure of P under shifts, cones or isomorphisms is required. The exactness theorem uses
essential constancy, not merely existence of a pointwise Kan limit. The unit's realized
statement/steps are empty; its ambient six-operation route is retained.

The local checkout lacks literature/stacks-project/derived.tex. Read the primary source
online at https://stacks.math.columbia.edu/tag/06XN and
https://stacks.math.columbia.edu/tag/05SE. LeanSearch was attempted for both new nodes and
returned Internal Server Error; the unavailable searches and other search results are
recorded in the node files.

## New nodes

`lem-pur-resolving-class-essential-constancy`, in
`dag/nodes/sec-smooth-purity/lem-pur-resolving-class-essential-constancy.json`, is proved in
`Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy` and records the
resolving-class denominator cone with its retraction/factorization and identity-leg clauses.

`lem-pur-left-derived-exact-chosen-localization`, in
`dag/nodes/sec-smooth-purity/lem-pur-left-derived-exact-chosen-localization.json`, is proved in
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization` and records exactness
transport to the chosen derived category. No change records are needed: existing public
signatures and definitions are unchanged, and new proof imports are non-public.

## Second reading by S3

1. Compared the existing item module against the repository with `diff`: only its proof
   and private proof imports changed. The original declaration signature, universes,
   hypotheses, conclusion, docstring and all definitions are byte-for-byte unchanged.
   Compared the existing DAG node as parsed JSON: only `proof`, `proof_deps` and
   `proof_origin` changed. Verdict: pass; no change record is required.
2. Independently compiled all three delivered modules with `lcompile.py --all`, without
   errors or warnings. Scanned every delivered Lean file: no sorry, axiom, unsafe,
   opaque, extern or implemented_by declaration and no hollow definition. Compiled scratch
   copies with `#print axioms` for all three theorems. The resolving helper uses only
   `propext`, `Classical.choice`, `Quot.sound`; the item and exactness helper additionally
   use `sorryAx` through the explicitly reported existing dependencies. Verdict: pass
   as a proof relative to the existing open dependencies, not a closed import closure.
3. No statements are split off with sorry. Read both proved helpers in full, including
   their docstring proofs. The resolving helper is a genuine denominator-cone argument;
   the exactness helper supplies the genuinely missing transport from strict to chosen
   localization. Neither restates the assigned theorem. Checked the empty-category case,
   nonemptiness of the resolving subcategory, cancellation by two-out-of-three, common
   refinements, and the identity-denominator clause. Independently searched with
   LeanFinder for cofiltered localization denominators and eventually constant cones,
   Loogle for right Kan extensions, and grep for eventual constancy and exactness
   transport; inspected the upstream EventuallyConstant supplement and project exactness
   and bridge modules. Results give the component constructions already used, no complete
   replacement for either helper. Verdict: pass.
4. Read the proof from the item down to the two helpers and existing dependencies. The
   proof uses Mathlib totalLeftDerived and cone uniqueness directly, and Mathlib initial
   functors, eventually constant cones, and localization transport in the helpers.
   Public imports provide objects appearing in signatures; proof-only imports are plain
   imports. No unused proof-dependency branch was found. In particular
   `lem-pur-left-derived-exact-when-defined` remains required through the exactness helper,
   although removed from the item's direct `proof_deps`. The unit
   `sk-def-sf-operations` has empty realized statement and step lists; its route is retained.
   Verdict: pass; no module is pruned.
5. Checked the three DAG nodes against the actual declarations and proof steps, the
   existing node's old dependency list against the report, and both new nodes' complete
   signatures, source, provenance, search records, chapter/unit and creation records.
   All dependencies listed by the new proof are used; the former exactness dependency
   is retained transitively. Verdict: pass.

Second reading changed only this report, adding the independent checks and their limits.
No repair to the Lean proofs or DAG records was necessary. One original hole is closed,
zero holes are added, and there are zero split-off open statements.
