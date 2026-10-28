## What changed

Marked `AlgebraicGeometry.Scheme.lisseTower_localized_constants_normalization`
`STATEMENT-DISPUTED`, as required by brief §4 and worker §2.7. Its statement and
original sorry remain unchanged. Added the private proof import
`Mathlib.Data.ZMod.Basic` and two completely proved private diagnostics:

- `independent_model_square_forces_self_neg`: in a preadditive category, requiring
  a fixed square to commute for every choice of the target comparison isomorphism
  forces its fixed right-hand arrow to equal its negative. The proof compares a
  comparison with its negative and cancels the source comparison.
- `independent_model_square_counterexample`: the corresponding universal assertion
  already fails for the identity arrow of the rank-one `ZMod 3` module, checked by
  evaluating the identity and its negative at `1`.

The second lemma is a concrete categorical counterexample, not a claim that Lean
has checked the literal negation of the full scheme/adic theorem. The exact
specialization to the original functors is explained below. Neither diagnostic
uses the disputed theorem or any new unproved statement. The item compiles through
`lcompile.py` without warnings. Its node's `lean.note` records the defect; the
existing statement, proof plan, dependencies and unit route are preserved for review.

## Proved and sorry left

Original holes closed: **0 of 1**. The remaining original hole is
`AlgebraicGeometry.Scheme.lisseTower_localized_constants_normalization`, node
`lem-weil-pbc-lisse-tower-localized-constants-normalization`.

Added holes: **0**. Split-off obligations: **0**. The two private diagnostic lemmas
are completely proved. This is a disputed-statement delivery, not a proof of the
false statement and not a reduction of it. No definition contains a hole.

## No longer needed

None. No module, declaration, import or dependency is withdrawn. The parent
`Sheaf.Paper.LisseTowerLocalizedConstants` still imports the item, and its DAG
needs remain recorded. No claim of pruning is based on the defect.

## Where the brief, the DAG or earlier work was wrong

**STATEMENT-DISPUTED:** the J8 split changed the quantifier needed by the parent.
The parent asks for existence of a family `model` together with a semilinear
compatibility equation. Its two children assert existence of an arbitrary
objectwise family and that *every* such family satisfies the equation. The latter
is strictly stronger and false. This is visible in the actual Lean type: `model`
is an unconstrained dependent function to isomorphisms. It has no normalization,
naturality or compatibility field. Even naturality separately at each level would
not suffice: negating all components at just one level preserves that naturality.

Fix a family `model` and define another allowed family by
`model' j E := if j = 0 then -(model j E) else model j E`.
For the equation at `n = 0`, all its other data are fixed. Scalar restriction is
additive, so `c' 0 E' = -(c 0 E')`, while `c' 1 E = c 1 E`.
If both families satisfied the displayed equation, comparing the equations and
cancelling the isomorphism `c 1 E` would give `s = -s`, where
`s = (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d 0 k)`.
The private generic lemma checks precisely this sign obstruction.

For a concrete mathematical specialization take all four schemes to be one
nonempty point and `g`, `a`, `b` identities; take the adic coefficient ring to be
`F_3` (with the harmless universe lift) and the ideal zero. This satisfies the
Noetherian, finite quotient, additive torsion and quotient-perfect hypotheses.
All finite coefficients are canonically `F_3`, their consecutive quotient map is
an isomorphism, and choose the rank-one complex in degree zero with `k` the
canonical identity under these coefficient identifications. The prescribed
restriction compositors and constant realization make `s` an isomorphism of a
nonzero constant rank-one object. At a geometric stalk in degree zero its source
is `F_3`. Thus `s = -s` would imply `1 = -1` in `F_3`, contradicted by evaluation
at `1` exactly as in the private checked example. The standard constant
comparisons provide a model family in this specialization; their existence does
not constrain all other possible families.

Read the cited Stacks source in the local checkout:
`sites-modules.tex`, labels `lemma-sheafification-presheaf-modules` (03CY) and
`lemma-abelian` (03DA); `sites.tex`, `example-constant-sheaf` (0H7J);
`sites-cohomology.tex`, `lemma-derived-base-change` (06YY). These give
sheafification, exactness, the constant-sheaf universal property and derived
pullback. They do not normalize an arbitrary supplied objectwise isomorphism.
The original docstring's constant-section argument assumes exactly that missing
normalization when it says both composites act by the supplied semilinear map.

The required repair is to construct the canonical constant model comparisons and
prove their compatibility as part of the same construction, retaining the
parent's existential statement. Another split which merely assumes arbitrary
models and asserts their coherence repeats the defect. The parent's existing
assembly proof relies on this false universal assertion; it needs review when
that interface is repaired. The adjacent actual-normalization split also accepts
arbitrary level isomorphisms, so the same issue should be checked there.

No public signature, target, definition or consumer was changed in this packet.
The brief expressly requires a suspected false statement to be marked and
reported instead of proving a weaker replacement. No new nodes were created.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerLocalizedConstantsNormalization": "8b3d09736ae2081438e8e2289b383f0383cd0cfb"}, "results": {"Sheaf.Paper.LisseTowerLocalizedConstants": {"hash": "af59fb5c01eecc20d186fdb899372f95a204c5e9", "status": "OK"}}, "seconds": 75, "time": "2026-10-28T10:38:48+0800", "transitive": 0, "version": 1}
```

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
