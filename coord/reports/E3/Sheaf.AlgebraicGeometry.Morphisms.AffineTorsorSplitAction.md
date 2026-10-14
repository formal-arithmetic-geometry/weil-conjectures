## What changed

Repaired reviewer X-e9fd4 point 4 in
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction`.
`fixedPunctureDeck` now restricts `Spec.map (rho zeta)` rather than
`Spec.map (rho zeta inverse)`, including the basic-open preservation proof.
`fixedPunctureDeck_base` uses `(rho zeta).commutes`.
The private `puncture_deck_mul` states and proves deck(a*b)=deck(a) followed by deck(b).
Removed the reverse-law diagnostic and used its connected-summand reconstruction
argument to prove the public `fixedPunctureLabel_laws` with the forward law.
Updated the deck, label and law docstrings; removed the now-resolved dispute marker.
Every existing public signature and visibility is unchanged.

The module imports Mathlib's connected/clopen and scheme-irreducibility APIs for
its proof. All definitions remain explicit constructions, with no postponed data
and no existence witness choices. No new module or node is added.
Updated the existing node's construction to rho(g), its complete proof and proof
origin, with a statement_change recording the convention correction and its citer.
Change record: `coord/changes/fixed-puncture-deck-forward-convention.md`.

Verification through lcompile.py: the repaired module compiles with no warnings.
The unchanged original sources of AffineTorsorOrbitComponentDescent,
AffineTorsorFixedPunctureDescentGeometric, AffineTorsorEquivariantDescent,
AffineTorsorFixedPunctureDescentCore and AffineTorsorFixedPunctureDescent compile
against a sandbox overlay containing the repair (3.4, 3.9, 6.0, 6.9 and 3.5 seconds).
The affected target modules Curve.FieldExtension, ProjectiveLine.GeometricStalk
and ProjectiveLine compile unchanged against that overlay (13.6, 21.3 and 4.3 seconds).
These contain targets 3/4, 1 and 2, respectively. Target 5 is outside the source
import closure of this module. Challenge.lean is untouched. None of the five target
statements mentions the corrected definitions, so their mathematical meanings stay
unchanged; the correction is in an intermediate proof construction. No global build
was run. Scratch copies and compile logs are under scratchpad/verification only.

## Proved and sorry left

Original holes closed: `AlgebraicGeometry.Scheme.fixedPunctureLabel_laws`, node
`lem-sbc-affine-torsor-split-label-laws` (1 of 1). Holes added: none. Split off: none.
Every theorem and definition in the delivered module is free of sorry.
`fixedPunctureDescentAction` now depends on the fully proved forward label laws.

The proof uses only Mathlib, with proved private helpers `puncture_deck_one`,
`puncture_deck_mul`, `split_ι_clopen`, `split_section_reconstruction`, and
`split_section_injective`. The zero prime establishes nonemptiness of the puncture;
irreducibility gives connectedness. A transformed section lies in one clopen
summand, whose index is evaluated at that point. The projection condition
reconstructs the section, and disjointness makes the indexing injective. The deck
identity and multiplication equations then prove both laws by injectivity.
For d=0 there are no indices to quantify over; nothing assumes d>0. Arbitrary
nonabelian groups are covered, as required by the S3 counterexample.

## No longer needed

None: no module or DAG node is pruned, and no import is removed. Both original
imports are needed, and the two added proof-only imports support connectedness
and clopen ranges. The obsolete private reverse-law diagnostic is removed.

## Where the brief, the DAG or earlier work was wrong

The original definition applied rho to an inverse group element. Contrary to its
docstring and node, that convention gives deck(ab)=deck(b) followed by deck(a),
so its labels satisfy the reverse-order law. The returned delivery demonstrated
this without correcting the convention or filling the hole. Reviewer X-e9fd4's
S3 example over the splitting field of X^3-2 over Q shows that the displayed
forward law was false with that original definition. The requested correction
is now implemented and the forward law fully proved; no false lemma is retained.
The unit and chapter route are unchanged.

## Forced adaptations

None. All three direct users and both intervening descent modules compile
unchanged against the corrected dependency. No external module is changed or
delivered, and there is no counterfactual compiler error requiring an adaptation.

## Statement corrected

Old node statement (verbatim):

Let R,H be commutative rings, g in R, iota:R -> H, and C a domain H-algebra with h=iota(g) nonzero in C. Let rho be an H-algebra action of a group G on C. Let p:Y -> Spec R and t:T -> Spec R, with k:D(h) in Spec C -> T over Spec R. Suppose delta splits pullback p t into d copies of T over T. Define a(g,i) by precomposing the i-th pulled-back section with the restricted Spec map of rho(g inverse), lifting with k into pullback p t, applying delta, and reading the unique coproduct index at the zero prime. Then a(1,i)=i and a(gh,i)=a(g,a(h,i)).

The corrected statement replaces only "rho(g inverse)" with "rho(g)".
The Lean law theorem's binders and conclusion do not change. Source: Stacks
Project Tag 03SF, finite Galois covers and permutation sets. The complete
correction metadata, including the old proof, is in the delivered node.

Citer `lem-sbc-affine-torsor-orbit-component-descent`: holds. Inversion reindexes
all group elements, leaving orbit sets and stabilizer subgroups unchanged. Its
stabilizer invariant-ring descent conclusion is unchanged. The corrected action
also agrees with rho in the equivariant-function coordinate equation.

## Second reading by E3

1. **Visible declarations.** Compared the delivered module with the repository version. Every
existing public signature is byte for byte unchanged; the only semantic definition change is the
reported `fixedPunctureDeck` convention correction, covered by
`coord/changes/fixed-puncture-deck-forward-convention.md`. No target statement changed.
Verdict: pass.

2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds without warnings.
Searched the delivered source for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
`implemented_by`, and `sorryAx`; none occur. The former hole in
`fixedPunctureLabel_laws` is fully proved, and no new holes or hollow definitions were added.
The proof uses connectedness of the nonzero principal open, clopen coproduct summands,
reconstruction, injectivity, and the deck identity/multiplication equations. Verdict: pass.

3. **Statements and nodes.** Checked the corrected node, its Lean declaration, proof route,
proof dependencies, source, and statement-change metadata. The forward `rho(g)` convention is
mathematically required for the displayed left-action law; the S3 counterexample to the old
inverse convention is recorded in the change record and report. No split-off statement was added,
and the node's statement agrees with the Lean theorem. Verdict: pass.

4. **Pruning and route.** Both proof-only Mathlib imports are used, while the original public
imports remain needed. The unit's realized route is retained; no proof dependency or module is
pruned. The proof takes the direct connected-summand reconstruction route and removes the obsolete
reverse-law diagnostic. Verdict: pass.

5. **Downstream compatibility.** Compiled the unchanged direct and intervening importers and the
affected target modules against the repaired overlay, as recorded above. Their declarations and
all target statements remain unchanged. Verdict: pass.

Changed during this second reading: added this review record only; no Lean source, node, or change
record required further repair.
