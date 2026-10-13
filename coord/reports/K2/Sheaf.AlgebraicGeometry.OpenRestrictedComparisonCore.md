## What changed

Completed a reduction of
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_square`
without changing its statement, universes, hypotheses or public imports.
The new proof imports OpenRestrictedCanonicalSquare and Modules.IsKFlatRestriction
privately.

OpenDerivedStalkIso constructs the natural additive derived-stalk isomorphism
along any open immersion. It identifies tensor pullback with exact restriction
by uniqueness of left adjoints, uses uniqueness of left-derived functors, and
combines exact-functor homology with Mathlib's restrictStalkNatIso. It also
constructs the representing isomorphism for literal restriction using the
exact-functor localization factor. All these definitions have complete Lean
bodies, with no data selected from a merely existential unproved statement.
The restriction functor abbreviation only gives the existing functor the
module-category spelling used by the project; its exactness and additive
instances are proved.

The remaining compatibility theorem is restricted to these fixed, explicitly
constructed isomorphisms and the literal derived object DQ(P). The parent proves
transport to arbitrary K and eP by naturality of the derived-stalk isomorphism
and the specified composition map. It then proves transport to arbitrary eQ by
applying the existing comparison-source isomorphism and comparisonIntoPullback
naturality to the derived automorphism of the restricted representative. Open
restriction K-flatness is supplied by the existing isKFlat_restrict theorem.

Validation: all three delivered modules compile together with lcompile.py --all,
without errors or warnings. The delivery dry run is checked separately.

Only the new canonical-square theorem has sorry. Its node contains the
ring/stalk, derived tensor, universal counit and composition compatibility steps.
The existing node now follows the actual proof, and the new definitions have a
node. No existing interface or target meaning changes; no forced adaptations.

## Proved and sorry left

One original hole is closed by a compiling reduction:
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_square`
(lem-pc-open-restricted-comparison-core).

One hole is added:
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_canonical_square`
(lem-pc-open-restricted-canonical-square).
There are no other sorries in the delivered files. Thus the authored hole change is
zero: this is a decomposition, not a complete proof of the geometric square.
No numerical claim about the full targets import closure is made here.

The completed parts include construction of η and the canonical restricted
representative, composition-map naturality, arbitrary-object transport, and
arbitrary-representative transport. The new hole requires only the compatibility
calculation for the fixed constructions. Empty opens have no z; top opens,
zero complexes, zero rings, unbounded complexes and arbitrary integer degrees
require no excluded cases.

## No longer needed

No original imports or planned geometric dependencies are pruned: the
ring/stalk tensor compatibility remains necessary for the canonical square.
The original restriction-stalk extension and tensor-model dependencies move to
the canonical-square node; representative naturality, source transport and
K-flat restriction are used directly in the parent.

The previous unverified OpenRestrictedLiteralSquare module and its
new-open-restricted-literal-square node were never delivered and have been
removed from this sandbox. Their almost-whole-statement reduction is superseded
by the explicit stalk/representative constructions and the genuinely smaller
canonical compatibility lemma. An exploratory direct import of
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf in OpenDerivedStalkIso
was removed; additivity is proved directly for the existing restriction functor.
These are discarded draft files/imports, not claimed pruning of baseline modules.

## Where the brief, the DAG or earlier work was wrong

The published OpenRestrictedComparisonComposition compiled object is now
available. The earlier build blocker is resolved; no dependency was copied or
rebuilt to bypass the published build.

The old draft did not compile: it placed set_option between a declaration
docstring and its theorem, and broad simplification unfolded functor maps so
that naturality rewrites could not match. The replacement introduces the let
binders and keeps the stalk functors as named local functors during transport.
The old proposed literal-square lemma retained η construction and arbitrary eQ;
its specialization of K alone was too close to restating the original problem.
The new reduction actually constructs η and eR and proves both transports.

Mathlib searches were repeated: LeanSearch returned Internal Server Error;
LeanFinder and Loogle found ordinary restriction/stalk/adjunction lemmas, and
source rg found exact-derived homology and restriction limits. These existing
constructions are used. Blueprint search for restriction stalk found no match.
The unit record sk-thm-picard-semicon has no realized statement or steps for this
item, and none of the unit's fixed statements or routes is changed.

## Second reading by K2

1. Interface check: compared the delivered core module and its existing node with
the repository versions; the public theorem statement is unchanged byte for byte.
Verdict: pass.
2. Proof check: compiled all three delivered modules with `lcompile.py`; the core
theorem has no `sorry`, and the sole remaining `sorry` is the named canonical-square
theorem with its matching node. No forbidden declarations or hollow definitions were
found. Verdict: pass.
3. Statement check: the canonical-square split is a strictly smaller compatibility
statement for the fixed literal restriction, with its source, docstring, and DAG
record; it does not restate the parent theorem. Verdict: pass.
4. Pruning check: proof-only imports are private, and the proof uses the canonical
square, derived-stalk construction, composition naturality, source transport, and
K-flat restriction exactly as recorded. No baseline import or realized unit route
was removed. Verdict: pass.
5. DAG check: the existing node's proof and dependencies follow the Lean proof, and
the two new construction/canonical-square nodes match their declarations and sources.
Verdict: pass.

Changed only the proof modules, their corresponding proof metadata, and this report;
no target statement, public interface, or definition was changed.


## New nodes

`def-pc-open-derived-stalk-iso`, module OpenDerivedStalkIso: the explicitly
constructed derived restriction, literal representing isomorphism and additive
derived-stalk comparison. All code is complete. The node records the exact
restriction and stalk construction, its source and searches.

`lem-pc-open-restricted-canonical-square`, module OpenRestrictedCanonicalSquare:
compatibility on a literal restricted complex using the fixed constructions.
Its one named sorry is sourced to Tags 0DJ8, 0DJ9 and 0D5U, with the full
ring/stalk and universal-counit argument in both the node and docstring.
No change record is needed, since no existing statement or definition changes.

