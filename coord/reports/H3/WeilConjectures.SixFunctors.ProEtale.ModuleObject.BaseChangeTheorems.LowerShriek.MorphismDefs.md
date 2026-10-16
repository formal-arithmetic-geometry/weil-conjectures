## What changed

Added the two sourced inverse subclaims for the cartesian extension-by-zero exchange and proved the
assigned `IsIso` theorem from them using `CategoryTheory.IsIso.mk`. The existing definitions and
imports were preserved. Local compilation used refreshed sibling artifacts for the source dependency
build; no shared-repository files were changed.

## Proved and sorry left

The target theorem `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`
is proved. Two strictly smaller inverse equations remain as named sorries:
`boundedConstructibleOpenImmersionLowerShriekBaseChange_leftInverse` (node
`stage3-sfb-open-base-change-left-inverse`) and
`boundedConstructibleOpenImmersionLowerShriekBaseChange_rightInverse` (node
`stage3-sfb-open-base-change-right-inverse`). Thus one original hole is closed and two subclaims are
split off.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The earlier BLOCKED report was accurate for the published build: it lacked
`Derived.LowerShriekIndependence.olean`. The local sandbox became compilable only after reusing the
refreshed source artifacts from sibling sandboxes; the server artifact skew remains a delivery risk.

## New nodes

`stage3-sfb-open-base-change-left-inverse` and `stage3-sfb-open-base-change-right-inverse` record the
left and right componentwise inverse equations separately, with the blueprint proof as source. Each
is strictly one half of the `IsIso` conclusion and is imported only through the declarations in this
item module.

## Second reading by H3

1. Compared the delivered module with the repository version. All existing declaration signatures,
visibility, definitions, and public imports are byte-for-byte unchanged. The only existing proof
changed is the proof of `isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`; the two
additional declarations are the named split-off nodes listed above. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The only
`sorry`s are the two named inverse subclaims, each with its source, proof description, blueprint
tag, and matching DAG node. There are no `axiom`, `unsafe`, `opaque`, `extern`,
`implemented_by`, or hollow definitions. The proved `IsIso` assembly uses only the permitted
categorical API; its dependency axioms include `sorryAx` only through the two intentionally open
subclaims. Verdict: pass.

3. Checked the target theorem and both split statements against the source and blueprint. The
target statement is unchanged. Each new statement is one inverse equation for the same exchange
morphism, with exactly the original cartesian and open-immersion hypotheses; together they are
strictly sufficient for `CategoryTheory.IsIso.mk` and are strictly smaller than the target. The
componentwise cartesian-section argument in the blueprint is the stated source for both nodes.
No existing library declaration duplicates either statement. Verdict: pass.

4. Read the proof downward. The `IsIso` proof obtains the left and right inverse equations,
derives equality of the two witnesses by associativity and the inverse equations, and constructs
`IsIso` with `CategoryTheory.IsIso.mk`. Both split nodes are therefore used, and no old proof
dependency or import is removed. The unit route remains the extension-by-zero exchange followed
by its cartesian isomorphism and inverse; the split only makes the two inverse equations explicit.
Verdict: pass.

5. Checked the DAG against Lean. The two new node statements match their declarations verbatim,
and the parent theorem node now records those nodes as the proof dependencies and the final
categorical assembly. The unit record and its realized route are unchanged. Verdict: pass.

Changed in this second reading: synchronized the parent theorem node's proof metadata with the
implemented inverse-equation assembly and added this review section; no mathematical statement or
definition was changed.
