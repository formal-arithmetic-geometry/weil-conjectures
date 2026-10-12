## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions`, declaration
`AlgebraicGeometry.IsCurve.assertions_iff_dense_open_prime`, with a complete Lean reduction.
The existing declaration's signature and its public imports are unchanged. Three new
proof-only imports supply three strictly partial intermediate statements:
`DenseOpenHighCohomology`, `DenseOpenPrimaryFiniteness`, and `DenseOpenBaseChange`.

The main proof uses the actual forgotten adjunction counit. For C1 and C2, it constructs
an equivalence from its higher-degree cohomology map and transfers `Subsingleton`.
For C8, it uses the already proved `Etale.cohomologyMap_map`, the counit's bijections on X
and each open immersion, and a proved private lemma about commuting squares. The private
lemma explicitly lifts elements in each direction. C3-C5 and C6-C7 are supplied by two
separate conditional comparison theorems. Finally `assertions_iff` and `Iff.and` assemble
all eight equivalences. None of the residual statements restates the eight-assertion
package or either full implication of it.

All four modules compile locally in import order without warnings. The delivery dry run
checks them again locally, checks the new modules on the project server, and runs the
stage-3 preflight. The item's DAG proof and dependencies now follow this implementation.

## Proved and sorry left

The body of `AlgebraicGeometry.IsCurve.assertions_iff_dense_open_prime` is now proved,
reducing the item's one original `sorry` to three named independent parts. This is a
stage-3 reduction, not an assertion that its transitive axioms are already sorry-free.
The private `surjective_iff_of_bijective_square` is fully proved.

Exactly these three declarations in the delivery remain `:= by sorry`:

- `AlgebraicGeometry.IsCurve.dense_open_high_cohomology`, node
  `lem-pbc-s2-dense-open-high-cohomology`, module
  `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology`.
- `AlgebraicGeometry.IsCurve.dense_open_primary_finiteness`, node
  `lem-pbc-s2-dense-open-primary-finiteness`, module
  `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness`.
- `AlgebraicGeometry.IsCurve.dense_open_base_change`, node
  `lem-pbc-s2-dense-open-base-change`, module
  `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange`.

Each has a complete proof in words in its docstring, its source and blueprint tag,
and a matching complete node. There is no `sorry` in a definition or private helper.

## No longer needed

No existing imports were removed: both original public imports are needed by the
unchanged signature. All three added proof imports are used. The high-cohomology module
imports the curve setting and cohomology directly instead of importing Assertions.

The item's route no longer needs `lem-weil-pbc-curve-assertions-dense-open` or its module
`Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions`. Its coefficient conversion to
`ULift ℤ` is not needed. The new statements work directly over the original coefficient
ring and use the same cohomology maps as Assertions.

The route also no longer needs `lem-weil-pbc-zero-dimensional-field-extension`, whose
recorded declaration is in `WeilConjectures.AlgebraicGeometry.Curve.Reductions`.
The new base-change part instead uses the independent degree-zero statement
`lem-weil-pbc-zero-dimensional-pullback-global-sections` and positive-degree vanishing.
This avoids importing Reductions, which already imports this item. These pruning claims
are about this item's route; they do not claim those modules have no other target users.

The remaining original ingredients (open-closed exactness, zero-dimensional cohomology,
long-exact ladders and the five lemma) remain in the new nodes' proof plans; they are not
claimed as globally unnecessary. The unit's dense-open/open-closed reduction is retained.

For completeness, the old direct `proof_deps` absent from the new main proof are:
`def-weil-pbc-primary-torsion`, `lem-weil-pbc-curve-assertions-dense-open`,
`lem-weil-pbc-five-lemma`, `lem-weil-pbc-open-closed-short-exact`,
`lem-weil-pbc-pullback-cohomology-long-exact-ladder`,
`lem-weil-pbc-zero-dimensional-cohomology`, and
`lem-weil-pbc-zero-dimensional-field-extension`. Except for DenseOpenAssertions and the
zero-dimensional field-extension module, these remain transitive ingredients of the
three residual statements; their removal here is from the main node's direct dependency
list, not from the entire target closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's existing `dense_open_assertions` statement uses a
`CurveCoefficientPair`, an abelian sheaf, and modules over `ULift ℤ`. Its signature is not
an immediate specialization to arbitrary `ModuleCat Λ`. No matching coefficient
transport theorem was found. Rather than move the whole statement to a new name, the
reduction separates the canonical higher-cohomology comparisons, C3-C5 and C6-C7.

Importing the recorded zero-dimensional field-extension module would introduce a Lean
import cycle because Reductions already imports DenseOpenPrimeAssertions. No such import
was added, and the new proof plans use the independent global-sections theorem instead.

The source's local TeX file is not present in this remote clone. The full proof of
[Stacks Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA) was read online, including
its finite boundary product, five-term sequence, higher-degree isomorphisms and remarks
(a)-(d). The node/docstring sources retain the repository's conventional TeX path and
label `lemma-restrict-to-open`. LeanSearch returned Internal Server Error on both
attempted queries; this is recorded as unavailable, not as proof of absence.

Edge cases checked against each new statement and its proof: empty X gives zero groups;
U=X gives an invertible counit and a zero boundary; a zero F gives zero groups and
bijective zero comparison maps; disconnected and zero-dimensional curves have a finite
discrete complement, possibly empty. The high-cohomology statement deliberately needs
neither reducedness, torsion, constructibility nor finite Λ: only the complement's
positive-degree vanishing is used. For the conditional statements, characteristic zero,
r equal to the positive characteristic, and r distinct from it are treated separately.
In particular invertible-order and primary predicates on F and G are not asserted to be
equivalent; an exceptional hypothesis makes the corresponding r-torsion sheaf zero by
coprimality. This is essential to preserving the original conditional statements.

## New nodes

`lem-pbc-s2-dense-open-high-cohomology` states bijectivity of `Sheaf.H.map` of the
forgotten canonical counit in degrees greater than one, and degree two after pullback
along every open immersion. It is a geometric comparison result with no assertion
package in its conclusion; it enables actual Lean proofs of C1, C2 and C8.

`lem-pbc-s2-dense-open-primary-finiteness` states just the three conditional equivalences
for primary vanishing and finiteness (C3-C5). Its proof uses the finite degree-zero boundary,
vanishing of positive boundary cohomology, and the prime-torsion coprimality cases.

`lem-pbc-s2-dense-open-base-change` states just the two conditional equivalences for
field-extension invariance (C6-C7). Its proof uses stalk-product invariance of the closed
complement and the five-term long-exact ladder, with the same coprimality cases.

All three inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`, cite the original
blueprint dense-open reduction through the item's node, and record the actual semantic,
type-pattern and Mathlib-source searches. The blueprint-wide searches for `0GJA` and
`dense open cohomology` found no imported matching blueprint node; the existing
DenseOpenAssertions node was read explicitly and has a different coefficient interface.
No statement or definition was changed, so no change record is required.

## Second reading by S2

1. Interface: PASS. Compared every delivered module with the repository. Only
   DenseOpenPrimeAssertions already exists. Its existing theorem signature and docstring
   are byte-for-byte unchanged; the diff adds three plain proof imports, a private proved
   square lemma, and the proof body. No definition, hypothesis, target, public import or
   existing declaration was changed. No change record is needed.
2. Kernel and compilation: PASS. Independently compiled all four modules in import order
   using lcompile.py, with no errors or warnings. There are exactly three occurrences of
   `sorry`, each the complete proof of the public theorem listed above; the main theorem
   and square helper contain none. No prohibited declaration or hollow definition occurs.
   A scratch module prints axioms for the main theorem and all three residual theorems;
   the main proof still depends transitively on sorryAx, as this report explicitly states.
   The delivery tool additionally probes every declaration, including the private helper.
3. Residual statements: PASS. Read all three signatures, docstrings and nodes against
   Stacks Tag 0GJA and the actual C1-C8 definitions. They are strict partial results, not a
   renamed assertion package. The higher comparison is valid even for arbitrary abelian
   coefficients: positive cohomology on a separably closed point vanishes without torsion.
   Checked empty X, U=X, the zero sheaf, disconnected and zero-dimensional curves, and
   characteristic zero / r equal to or different from positive characteristic. In the
   exceptional conditional cases, the sheaf to which the hypothesis applies is zero;
   there is no illicit implication from invertible-order or primary torsion of G to F.
   Checked the low-degree exact sequence in both directions for finiteness and base
   change, as well as the natural degree-two restriction square.
   Independent leanfinder search for a cohomology isomorphism for extension by zero with
   a finite algebraically closed complement found group-cohomology results only. Loogle
   search for Function.Surjective and Function.Bijective found composition lemmas, not a
   geometric replacement. Local rg searches found the proved
   Etale.bijective_H_map_of_isIso_upperStar_map in Sites.FiniteSupport: it is useful for
   completing the higher comparison once finite closed complement, separably closed
   residue fields and the restricted forgotten counit isomorphism are supplied, but it
   does not itself have the new statement's curve assumptions. Also read the existing
   DenseOpenAssertions, zero-dimensional cohomology, and pullback long-exact ladder.
   No residual can be closed by a direct available theorem application in a few minutes.
4. Route and pruning: PASS after report repair. The proof explicitly transfers C1/C2 by
   canonical bijections, C8 by naturality, and assembles the eight equivalences. Every
   import is needed by its signature or proof. The unit sk-thm-p1's realized entries and
   dense-open/open-closed route stay intact; no unit step is bypassed. Added the complete
   seven-node list of old direct dependencies absent from the new main proof and explained
   which remain transitive ingredients. The two route-pruning claims are appropriately
   local to this item.
5. DAG: PASS. The only changed fields of the existing node are proof, proof_deps and
   proof_origin. Each node's proof_deps equals the union of its proof steps' uses; every
   referenced dependency exists. New nodes have the required source, provenance, searches,
   status, chapter, unit, and Lean records; their recorded signatures match their Lean
   statements and their natural-language proofs describe the required canonical maps.

Second reading changed only this report: completed the direct-dependency pruning list
and added the independent review. No Lean or node repair was warranted.
