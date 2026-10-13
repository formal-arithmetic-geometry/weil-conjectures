## What changed

The existing module `Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermTransport` now
combines a canonical chain-coordinate construction and a homology factorization
lemma. Its existing theorem signature and docstring are unchanged. The two new
helper modules are imported only for the proof. Duplicate helper imports and the
redundant `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` import were
removed. The required homology declarations remain available through the existing
public imports.

The second reader repaired the proposed decomposition. The coordinate theorem now
requires an explicit degreewise square: tau followed by ambient tensorStalkIso is
the restricted tensorStalkIso followed by the stalk of the inverse constructed
openPinnedTensorRestrictionIso and the same-germ restriction-stalk comparison.
The equation theorem assumes this square, rather than claiming homology transport
for arbitrary scalar and chain coordinates. Its scalar-coordinate arguments and
unused lets were removed. The coordinate helper does not use a homology degree or
derived homology comparisons; its unused degree argument and those lets were removed,
and its public imports now name just the two modules its statement needs.

Both remaining holes have complete natural-language proofs and matching DAG records.
No definition or existing statement changed; no change record or forced adaptation
is needed. No object is defined by choosing an arbitrary unproved existence witness.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.exists_openOrdinaryTensor_germ_transport`.
Its proof assembles the witnesses and compatibility equations from the coordinate
lemma, and applies the factorization lemma to the canonical degreewise square.

Holes added and still open:

- `AlgebraicGeometry.exists_openOrdinaryTensor_germ_coordinates`, node
  `lem-pc-open-ordinary-tensor-germ-coordinates`, in
  `Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermCoordinates`.
- `AlgebraicGeometry.openOrdinaryTensor_germ_transport_equation`, node
  `lem-pc-open-ordinary-tensor-germ-equation`, in
  `Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermEquation`.

This is a decomposition, not an unconditional proof: one original hole closed,
two holes added, net minus one before any subsequent pruning. No target is certified
axiom-free by this delivery. The geometric chain-coordinate construction and exact
homology factorization are separate parts of the original route; neither is a
renaming of the full target statement. Each new proof is exactly `by sorry`; the
existing theorem has no local sorry. All three declarations still depend on
`sorryAx`, as expected for this decomposition and the open imported statements.

## No longer needed

Removed the item's redundant proof import
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` and duplicate imports
of the two helpers. The coordinate helper no longer imports
`Sheaf.AlgebraicGeometry.OpenDerivedAdditiveStalkIso` or
`Sheaf.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso`; it imports the
underlying stalk-complex and pinned ordinary restriction definitions directly.
The equation helper also drops the redundant Mathlib import.

The original item's direct `proof_deps` are all replaced by the two new helper
nodes: `def-pc-open-derived-additive-stalk-iso`,
`def-pc-single-complex-base-change-stalk-condition`,
`def-pc-single-complex-open-tensor-restriction-iso`,
`lem-pc-open-restriction-stalk-extension-iso`, and
`lem-pc-stalk-comparison-source-transport`.
The first three and the last still supply definitions or factorization lemmas to
the signatures or the helpers' routes. The unpinned restriction extension
existence theorem does not provide the specified same-germ and pinned square;
its underlying germ argument is used directly instead. No whole library module
is claimed globally unreachable or pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's `openOrdinaryTensor_germ_transport_equation` was false.
It universally quantified eC, alpha, and tau and assumed only the pure-tensor
formula. Even with identity scalar equivalences, replacing alpha and tau by their
negatives preserves that formula and semilinearity, while changing the right-hand
homology map by a sign. The left-hand map is fixed. For top opens, identity scheme
maps on Spec(Q), and the structure-sheaf complex concentrated in degree zero,
this would identify the canonical identity map with its negative on a nonzero
Q-vector space. Thus scalar compatibility alone cannot pin the transport map.

The repaired equation requires the actual chain square. The coordinate theorem
establishes that square as part of its geometric construction. The original
helper docstrings supplied only source tags, not complete proofs; those were
replaced. Their nodes also contained generic, inaccurate proof routes and copied
searches for a different derived-tensor question; those were repaired.

## New nodes

`lem-pc-open-ordinary-tensor-germ-coordinates` records the four compatible ring
equivalences, semilinear input chain iso, pure-tensor chain iso, and canonical
chain square. It is the stalk/germ and adjunction-mate portion of the original
plan, with no derived homology equation.

`lem-pc-open-ordinary-tensor-germ-equation` records the exact-homology consequence
of the canonical chain square. It neither constructs scalar coordinates nor
asserts the existence of the target witnesses. Both nodes include the verbatim
Lean statements, complete proof routes, source, creation information, blueprint
ancestry, chapter/unit and LeanFinder, Loogle, source grep and an attempted LeanSearch query.
LeanSearch returned Internal Server Error, recorded as unavailable.

## Second reading by N2

1. Compared the item's sandbox module with the repository using `diff` and the
   declaration parser. The sole existing signature is byte-for-byte identical;
   no definition changed. The helper modules are absent from the repository.
   Verdict: pass after repair; no change record is required.
2. Compiled all three modules in import order using lcompile.py, with no errors
   or warnings. Scanned for forbidden declarations and hollow definitions: none.
   The only two local sorries are the named helper theorems listed above.
   Printed axioms of each declaration from scratch copies; only standard axioms
   and sorryAx are permitted. Verdict: a checked conditional decomposition,
   not an axiom-free proof of the original mathematical result.
3. Rejected the original universally quantified equation by the sign test above.
   The repaired helper assumes the canonical degreewise square; the coordinate
   helper supplies it. Empty opens have no z; top opens give the same-germ
   comparison, and zero complexes/rings require no nonzero or flatness condition.
   These statements isolate the geometric chain construction and the homology
   coherence step, respectively. Read upstream pinned adjunction, composition,
   tensorStalkIso, openDerivedAdditiveStalkIso and comparisonStalkHomologyIso
   definitions. Searched with LeanFinder, Loogle and grep for restriction-stalk
   semilinearity and exact homology/localization naturality, and searched local
   Sheaf/WeilConjectures sources. LeanSearch was also attempted for each lemma,
   but returned Internal Server Error; no result is attributed to it. Existing extension isomorphisms lack the pinned
   generator and chain-square specifications; exact functor lemmas are
   constituents, not duplicate statements. Verdict: true strict intermediate
   statements, with complete docstring proofs and matching nodes, still unproved.
4. The target now combines the chain-coordinate construction with exact homology
   factorization. Public imports in new helpers serve signatures; imports of the
   helpers in the existing item serve only its proof. Removed duplicate and
   redundant imports and recorded all replaced old proof dependencies above.
   Read dag/units/sk-thm-picard-semicon.json: its realized statement and sole step
   arrays are empty, and no unit route is altered or bypassed. Verdict: pass;
   no unconditional proof or globally pruned module is claimed.
5. Updated the existing node's proof, proof_deps and proof_origin to the actual
   two-helper assembly. Updated each new node's statement, verbatim Lean record,
   proof steps and union of their uses, sources and the required search records (LeanSearch was attempted but unavailable).
   All nodes retain the item's chapter/unit and blueprint ancestry.
   Verdict: DAG and Lean agree after repair.

Changes made by this reading: repaired false arbitrary-coordinate transport with
a canonical degreewise chain-square hypothesis and corresponding existence
conclusion; removed unused parameters/lets and duplicate/redundant imports;
added full helper proof docstrings; corrected all three DAG proof routes and the
report's decomposition accounting. No existing signature or definition changed.
