## What changed
The existing module now obtains an etale open neighborhood from
`Sheaf.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions`, proves that the open is
all of X using `Sheaf.AlgebraicGeometry.ProperEtaleOpen`, and transports etaleness along
`Scheme.topIso`. The existing theorem signature and its docstring are byte-for-byte unchanged.
The new imports in the existing module are plain proof-only imports.

The second reader replaced the false draft `proper_etale_open_eq_top` by
`proper_closed_fiber_open_eq_top`, with the complete-base and proper-composite hypotheses,
and proved it using the closed image of the complement. The neighborhood declaration
was moved to its own new module and given a complete natural-language proof.
No existing statement or definition changes; no change record is needed for correcting
new, undelivered draft declarations.

## Proved and sorry left
The one original sorry is replaced by a reduction:
`AlgebraicGeometry.etale_of_infinitesimal_restrictions_of_proper`.
The new `AlgebraicGeometry.proper_closed_fiber_open_eq_top` is proved without sorry or
nonstandard axioms.

Exactly one sorry remains in this delivery:
`AlgebraicGeometry.etale_open_of_infinitesimal_restrictions`, in
`Sheaf.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions`, node
`lem-weil-pbc-etale-infinitesimal-restrictions-proper-neighborhood`.
The original theorem still depends on this sorry; it is not axiom-free yet.
The two new nodes are strict subarguments: the first needs no properness and concludes
only existence of an etale neighborhood; the second has no infinitesimal etaleness
hypothesis or conclusion, and only proves that a containing open is top.

## No longer needed
Removed direct proof imports from the existing module:
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: no declarations from it occur in the reduction.
- `Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods`: now imported only by the
  new neighborhood module, where it is the remaining proof's planned theorem.

All twelve old direct proof dependencies of the original node are replaced by the two
new helper nodes (none of the unit-level realized nodes is bypassed):
- `def-pc-base-change`
- `def-pc-fibre-product`
- `lem-weil-pbc-closed-immersion-base-change`
- `def-sbc-closed-immersion-ideal-sheaf`
- `def-sbc-ideal-sheaf-powers`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-etale-infinitesimal-neighbourhoods`
- `pqf-def-locnoeth`
- `def-weil-finite-type-morphism`
- `def-weil-proper-morphism`
- `lem-weil-pbc-adic-complete-jacobson-radical`
- `def-weil-etale-morphism`

The closed-immersion/ideal-sheaf identification dependencies and the infinitesimal theorem
remain under the neighborhood node. Properness, spectra, fiber products and the
Mathlib-matched adic Jacobson result remain under the proved open-equals-top node.
The etale definition remains a statement dependency. This is a change of direct proof
edges, not a claim that all these concepts or modules disappear from the global closure.
Removed redundant imports from the new proper-open module: Pullbacks, PullbackCarrier,
and Spectrum.Prime.RingHom are already available through Morphisms.Proper.

## Where the brief, the DAG or earlier work was wrong
The first worker's draft `proper_etale_open_eq_top` was false: it allowed arbitrary Z
and i and had neither properness nor a complete base. For example take Z and W empty
and g : affine line over a field → Spec(field). Its empty restriction is etale and the
containment is vacuous, but g is not etale. No false draft declaration remains.
The draft report did not enumerate removed proof edges, the helper docstrings lacked
complete proofs, and the neighborhood declaration had not been placed in a separate module.
The original node's proof steps had not been updated to agree with its new proof_deps.
These have been repaired.

## New nodes
`lem-weil-pbc-etale-infinitesimal-restrictions-proper-neighborhood` states the quotient
base-change neighborhood result in its own module. Its proof identifies the kernel ideal
and its powers on affine charts, glues the canonical quotient identifications, and applies
the existing infinitesimal-neighborhood theorem. This is the only remaining sorry.

`lem-weil-pbc-etale-infinitesimal-restrictions-proper-open` now states that an open containing
the actual closed fiber is top when the source is proper over the complete base. Its Lean
proof uses the closed image of the complement, existence of a maximal ideal above a prime,
`IsAdicComplete.le_jacobson_bot`, `range_comap_of_surjective`, and
`Scheme.Pullback.range_fst`. It is fully proved. No change records.

## Second reading by G2
1. Compared all delivered modules to the repository. There is exactly one existing
   declaration; its complete signature is byte-for-byte identical (checked by script).
   Its docstring is also unchanged. The two other modules are new. No definitions or
   target statements were modified.
2. Compiled all three modules through lcompile.py in import order, without errors or
   warnings. Inspected the files for forbidden declarations and hollow definitions:
   none. The only sorry is the named neighborhood theorem. A scratch-copy #print axioms
   check reports only propext, Classical.choice and Quot.sound for the proper-open lemma;
   the neighborhood lemma and original theorem additionally use sorryAx, as reported above.
3. Read Stacks Tags 0GS2 (complete Noetherian essential-surjectivity proof) and 0A43(2).
   The neighborhood argument needs the locally Noetherian target and finite type g,
   while the proper-open argument needs exactly properness of g ≫ f and completeness.
   Edge cases: I = 0 makes the closed fiber all of Y, so W must be top; I = top with
   adic completeness forces the zero ring and hence empty source over its spectrum;
   empty X works throughout. Without properness an open may miss the special fiber,
   which is why it is present in the corrected lemma. The false arbitrary-fiber lemma
   was rejected using the affine-line counterexample above. Searches with new wording
   through leanfinder, loogle and grep, plus rg over lean/Sheaf and lean/WeilConjectures,
   found no existing exact result. LeanSearch was unavailable (HTTP 500), recorded as such.
4. The top-down reduction now uses the two strict parts of the original argument, and
   the proper-open part was closed using Mathlib rather than left as a new sorry.
   Proof-only imports use plain import. The removed imports and every replaced old
   direct dependency are listed above. Read dag/units/sk-thm-p1.json realized: neither
   the item nor its helpers realizes a unit statement or step, and none of that route
   is bypassed or changed.
5. Checked the nodes against the Lean signatures. Updated new-node signatures verbatim,
   statements with all hypotheses, proof steps and their union proof_deps, source,
   proof_origin and actual search records. Updated the original node's two steps to
   match the reduction exactly. New-node creation and blueprint records remain tied
   to this item. Verdict: repaired delivery passes the five reading points, with the
   single explicitly reported neighborhood proof still open.

Changes by second reading: corrected and proved the false specialization helper; moved
the neighborhood helper to its own module; completed its docstring proof; removed redundant
imports; synchronized node signatures, proof edges and search evidence; corrected this report.
