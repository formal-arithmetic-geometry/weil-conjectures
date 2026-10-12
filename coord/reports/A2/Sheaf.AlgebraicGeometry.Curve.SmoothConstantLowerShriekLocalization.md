## What changed

Proved `AlgebraicGeometry.IsCurve.smoothConstantLowerShriekAssertions_of_constant` in
`Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization`, with its original
signature and public imports unchanged. Updated the existing node's proof, proof_deps
and proof_origin to match the proof. No new modules, nodes or statements.

The shorter argument applies H only to X. For V = image(j), adjoin the disjoint open
E = X minus closure(V). Their union is dense (`dense_coborder`). The existing
`assertions_iff_dense_open_prime` transfers H f to this union, and
`assertions_iff_disjoint_open_prime` gives assertions on the first of its two summands.
Constant-sheaf pullback, the image isomorphism U ≅ V, and lower-shriek composition identify
that summand with the sheaf in the theorem. The public
`assertions_of_underlying_abelian_iso` transports the eight assertions.
Its constructibility hypotheses follow from constructible pullback, the open-closed
extension-by-zero theorem, and invariance of constructibility under isomorphism.
All four copied private helpers have been removed.

Proof imports added: Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions;
WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp;
WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction; and
Sheaf.AlgebraicGeometry.Curve.UnderlyingAbelianAssertions. The original DenseOpenPrimeAssertions
and Regular proof imports remain. Three redundant direct imports were removed during the
second reading; the retained imports expose the topology and open-closed constructibility
facts used in the proof.

Sources read: https://stacks.math.columbia.edu/tag/03SG,
https://stacks.math.columbia.edu/tag/0GJA, and https://stacks.math.columbia.edu/tag/0A5C.
No unit statement or realized step is bypassed: this is the same constant-coefficient
localization below the curve-calculation step of sk-thm-p1.

Searches: msearch leanfinder for smooth curve constant etale lower-shriek assertions
returned eight unrelated smooth/etale-locus results; loogle for irreducibleComponents and
IsOpen returned no hits; grep for assertions and clopen or constantModSheaf isomorphisms
returned no hits. Local rg then located the dense-open and disjoint-open prime comparison
lemmas, constant-sheaf pullback, lower-shriek composition, finite-constant-sheaf instance,
and the existing private iso-transport proof. Mathlib dense_coborder supplies the
shorter topological construction.

## Proved and sorry left

Proved the item's only original sorry:
`AlgebraicGeometry.IsCurve.smoothConstantLowerShriekAssertions_of_constant`
(node `lem-pbc-u2-smooth-constant-lower-shriek-localization`).
No sorry remains in the item and no sorry is added anywhere. Imported assertion-comparison
lemmas remain the intended next-stage obligations; this is not a claim that the whole
reachable library is sorry-free.

The repaired proof compiled locally without warnings against the refreshed last green
build. The delivery dry run is the final validation.
The unchanged statement includes the empty scheme, the empty open, disconnected curves,
and zero-dimensional components. The two-open construction covers each: V empty gives
the pair (empty, X), V = X gives (X, empty), and neither construction requires a point.
All coefficient and characteristic hypotheses are exactly those of the two imported
prime-torsion comparisons, with R finite and the constant sheaf constructible and r-killed.

## No longer needed

Both original public imports remain and are used by the unchanged statement. The original
proof imports `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions` and
`WeilConjectures.AlgebraicGeometry.Curve.Reductions` were removed. The second reading also
removed redundant direct proof imports `Mathlib.Topology.LocallyClosed`,
`WeilConjectures.ConstructibleSheaf.OpenClosed`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`; their needed declarations
are already exposed through retained imports. These three import removals do not prune the
constructible-pullback or extension-by-zero nodes, whose results the proof still uses.
Repair removed the proof import
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` and the copied
`cohomologyEquiv`, `comparison_surjective_of_iso`, `comparison_bijective_of_iso`,
and `assertions_of_iso` helpers. The direct proof no longer needs
`def-weil-pbc-cohomology-pullback`; assertion transport is delegated to
`lem-v2-underlying-abelian-assertions`.
Removed the proposed proof import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial:
the final transport proof uses UnderlyingAbelianAssertions instead of explicit naturality.
The revised direct proof dependencies omit:

- `lem-weil-pbc-noetherian-finitely-many-components` (component enumeration is absent from the new proof).
- `lem-sc-smooth-normal` (the integrally-closed-stalk result in
  WeilConjectures.AlgebraicGeometry.Regular; that module is used instead for smooth regularity).
- `lem-weil-pbc-curve-assertions-finite-pushforward`
  (Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions).
- `lemma-weil-pbc-eight-curve-devissage`
  (WeilConjectures.AlgebraicGeometry.Curve.Reductions).

There is no direct finite component decomposition, finite-pushforward coefficient bridge,
or iterative short-exact assembly to prove for this item. Finite-sum behavior is supplied
by the existing DisjointOpenPrimeAssertions theorem. These are removals from this item's
route; other targets may still need the listed modules.

## Where the brief, the DAG or earlier work was wrong

The old DAG route was mathematically valid but unnecessarily long. The union of any open
with the complement of its closure is dense, so the existing dense-open comparison and
finite disjoint-open comparison suffice without enumerating smooth components. Smoothness
is used to obtain reducedness, and H supplies the ambient constant assertion package.
No statement was disputed or changed. No tool workaround was used.


The landing return correctly identified duplicate transport proofs. Their source module
uses private declarations and depends on this item, so direct reuse from that module
would be inaccessible and cyclic. The repair imports the existing, more general public
`assertions_of_underlying_abelian_iso` from `UnderlyingAbelianAssertions` instead.
No statement, definition, public import, or additional library module was changed.
The duplicate proofs are removed rather than renamed. The node now records the
constructibility argument and the existing transport node. The fresh second reading is recorded below.

## Second reading by A2

1. PASS: compared the entire delivered module with the repository version. The sole existing
   theorem signature is byte for byte identical, both public imports are unchanged, and no
   declaration, definition, target statement, or change record was added. The existing node
   changes only `proof`, `proof_deps`, and `proof_origin`.
2. PASS: compiled the complete module locally without errors or warnings. A scratch copy
   with `#print axioms AlgebraicGeometry.IsCurve.smoothConstantLowerShriekAssertions_of_constant`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is
   inherited from imported open obligations, not a sorry in this module. There are no
   forbidden declarations or attributes, no new helpers, and no sorry in the delivered file.
3. PASS: there are no split-off statements or new nodes to validate or search. Read the
   signatures of the dense-open, disjoint-open, and underlying-abelian assertion comparisons:
   all their hypotheses are supplied, including reducedness, finite coefficients,
   constructibility on both sides of the transport, and annihilation by r. The image
   isomorphism and its direction agree with the composed sheaf isomorphism. For V empty,
   E is X; for V = X, E is empty; when X is empty both are empty. No nonemptiness,
   connectedness, purity of dimension, or coefficient characteristic assumption is added.
4. PASS AFTER REPAIR: reviewed from the theorem through the existing comparisons and searched
   local Lean for other assertion reductions and transports. The upstream dense-localization
   reductions require irrelevant irreducible-open decomposition; they do not shorten this
   arbitrary-open argument. Reviewed Stacks [03SG](https://stacks.math.columbia.edu/tag/03SG),
   [0GJA](https://stacks.math.columbia.edu/tag/0GJA), and
   [0A5C](https://stacks.math.columbia.edu/tag/0A5C). The unit sk-thm-p1 realized statement and
   steps remain intact: this only changes the assembly below its curve-calculation step.
   All four removed original proof dependencies are listed under No longer needed. Import
   deletion probes found three redundant direct imports, and a combined deletion probe
   compiled without warnings with the same axiom list; removed those imports.
5. PASS: the node's five proof steps follow the actual Lean proof, and their uses have union
   exactly equal to proof_deps. The constructibility, constant-pullback, smooth-regularity,
   dense/disjoint comparisons, and assertion transport nodes all match their uses. Source,
   statement, statement dependencies, blueprint, unit, and all other non-proof fields are
   unchanged. Removing redundant imports does not change these mathematical dependencies.

Changed in this second reading: removed the three redundant direct proof imports named
above; corrected the report's original-import account and its unused-component explanation.
The mathematical proof and existing theorem signature were left unchanged.
