## What changed

Completed `AlgebraicGeometry.derived_open_union_adjunction_triangle` in
`Sheaf.AlgebraicGeometry.DerivedOpenUnionAdjunctionTriangle`, with its signature and
existing docstring unchanged. Added private proved helper `transport_triangle` for
transporting a distinguished triangle while retaining a specified middle arrow.
Added proof imports of `Sheaf.AlgebraicGeometry.DerivedOpenUnionSESPresentation`,
`Mathlib.CategoryTheory.Shift.Adjunction`, and
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.

The new module states the geometric short exact complex presentation. The parent applies
the SES triangle constructor, inverse rotation, the overlap right adjoint's induced
shift comparison, shift addition, and explicit triangle transport. Both modules compile
individually in dependency order with the required local wrapper and no warnings.
No definitions, existing signatures, target statements, or other modules were changed.
The theorem-local heartbeat setting is for elaborating the composite shift comparison;
the completed target compiles in under 25 seconds, within the 60-second limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.derived_open_union_adjunction_triangle`
(node `lem-sc-derived-open-union-adjunction-triangle`).

Added one hole, exactly the whole proof of the public theorem
`AlgebraicGeometry.derived_open_union_ses_presentation`
(node `lem-sc-derived-open-union-ses-presentation`), in its own new module.
This is a decomposition: one hole closed and one added, net zero holes. The new statement
asserts a short exact sequence of complexes and its first-arrow comparison, with no
connecting morphism, shift, or distinguished-triangle assertion. It is the complex
presentation step of Tag 08BV, not a renamed or repackaged triangle theorem. The parent
constructs and transports the triangle in a complete Lean proof. Its private helper
is proved and has no hole. No sorry remains in the item's module. The delivery axiom probe found no forbidden axioms;
the parent still depends on the named presentation hole, as expected for a decomposition.

## No longer needed

The second reading removed the redundant public import
`Mathlib.Algebra.Homology.HomologicalComplexAbelian` from the new presentation
module; its statement already obtains these declarations through
`Sheaf.AlgebraicGeometry.DerivedCategory`. No original import was removed:
the original file imported only
`Sheaf.AlgebraicGeometry.DerivedCategory`, which its statement still needs.

The parent's direct proof dependencies
`lem-pc-open-derived-localization-adjunction`,
`prop-pur-kinjective-resolutions-exist`, and
`def-pc-derived-open-restriction-maps` now occur in the geometric presentation node.
They remain needed below that node and are not claimed as pruned work.

The route no longer uses `lem-pc-right-derived-functor-triangulated`
(module `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`):
we construct the short exact sequence on X and apply its triangle constructor there,
instead of pushing a distinguished triangle from the union to X.
The covered-space theorem `lem-pc-kinjective-mayer-vietoris-presentation`
(module `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`) is also no longer
used by this route. The new presentation retains its needed computational comparisons
through `lem-pc-kinjective-mayer-vietoris-comparisons` and
`lem-pc-open-image-complex-comparison-restriction`. No whole-library unreachability
claim is made for either removed dependency; other callers may still use them.
The SES-triangle and exact-derived-factorization nodes remain dependencies of the parent.

## Where the brief, the DAG or earlier work was wrong

The planned whole-space presentation cannot directly supply this statement: it assumes
U union V = top and uses derived categories on open schemes, while this item's opens
are arbitrary and its supplied adjoints use localized sites. The new statement records
precisely the geometric bridge needed. The existing statements are not disputed.

The arbitrary-union proof can construct its short exact sequence on X directly from
an injective-term K-injective representative, evaluating on Z intersect (U union V).
Thus a triangulated pushforward from the union is unnecessary. The short exactness
argument still follows Tag 08BV, and the unit's Mayer--Vietoris route is retained.
The source checkout lacks the cited cohomology.tex on this machine, so the proof was
checked on the authoritative Stacks pages https://stacks.math.columbia.edu/tag/08BV
and https://stacks.math.columbia.edu/tag/079W. Blueprint searches for 08BV and
Mayer--Vietoris found no blueprint node with this exact presentation.

## New nodes

`lem-sc-derived-open-union-ses-presentation`:
`dag/nodes/sec-picard-framework/lem-sc-derived-open-union-ses-presentation.json`,
module `Sheaf.AlgebraicGeometry.DerivedOpenUnionSESPresentation`, declaration
`AlgebraicGeometry.derived_open_union_ses_presentation`. It isolates the short exact
complex and canonical first-arrow comparison. Its source, complete proof in words,
existing lower dependencies, and actual Mathlib searches are recorded. LeanSearch
returned an internal server error and is recorded as unavailable. The empty-open and
repeated-open cases are checked in its proof text. No change record is needed because
no existing interface was changed. The parent node's proof and proof_deps were updated
to agree with the completed Lean reduction; its other fields are unchanged.

## Second reading by Q2

1. **Interfaces: pass.** Compared the parent module with the repository using
   `diff -u`, and compared its theorem signature byte for byte. The existing
   signature, visibility, public import and docstring are unchanged. The only
   existing node fields changed are `proof`, `proof_deps` and `proof_origin`.
   No definition, target, forced adaptation or change record is involved.
2. **Proof and axioms: pass as a decomposition.** Compiled both delivered modules
   in dependency order using `lcompile.py`, without errors or warnings. Inspected
   inverse rotation, the direction of each shift comparison, and all three
   transport squares. Scratch-copy `#print axioms` checks show only `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx` for the two public theorems;
   the private transport helper uses only the three standard axioms. The parent
   has no `sorry`; the new presentation has exactly its reported named theorem
   hole. No forbidden declaration or data definition was added. The existential
   presentation is eliminated inside a proposition proof, not used to define
   data from an arbitrary unproved existence witness.
3. **Split statement: pass.** Read the complete presentation docstring and node
   against [Tag 08BV](https://stacks.math.columbia.edu/tag/08BV) and
   [Tag 079W](https://stacks.math.columbia.edu/tag/079W). Applying the construction
   on X with first term j_(U union V)* I|_(U union V) gives the section sequence
   on Z intersect (U union V); sheaf gluing and injective-term flasqueness prove
   the claimed exactness. Empty opens yield zero overlap and the evident split
   sequence; equal opens yield the diagonal/difference sequence; disjoint opens
   yield an isomorphism onto the biproduct. Arbitrary supplied adjunctions are
   handled by the unique right-adjoint comparison compatible with counits.
   The assertion supplies precisely S, its three object comparisons and the
   first-arrow equality needed by the parent. It asserts neither a triangle
   nor a shifted connecting map, so is a genuine intermediate geometric step.
   Independent `msearch.py` leanfinder and grep searches using direct-image,
   counit, interUnionPullback and MayerVietorisSquare vocabulary found only
   underived restriction and sheaf-gluing tools. Loogle queries for unqualified
   ShortComplex names were unresolved; this is not evidence of absence. A
   qualified `CategoryTheory.ShortComplex.ShortExact` query succeeded and found
   only generic exactness, splitting and isomorphism-transport declarations,
   not the geometric presentation.
   Read the upstream whole-cover presentation, its comparisons and the nested
   restriction comparison: the whole-cover hypothesis and open-scheme carriers
   prevent direct application to this arbitrary-union localized-site statement.
   This remaining geometric bridge cannot be closed in a few-minute repair.
4. **Route and pruning: pass.** The reduction starts with the original upper
   hole and uses Mathlib's SES triangle, inverse rotation, right-adjoint shift
   comparison and triangle-isomorphism constructor. No shorter ready-made
   presentation was found. Checked every old proof dependency against the
   `No longer needed` section: three move below the new presentation, two
   remain directly used, and the triangulated-right-derived-functor and
   whole-cover presentation dependencies are no longer used by this route.
   The unit `sk-thm-picard-duality` has empty `realized.statement` and an empty
   realization for its one step, so there is no realized node being bypassed.
   The Mayer--Vietoris construction remains the route. No newly unreachable
   library module is claimed. All remaining direct imports are needed.
5. **DAG agreement: pass.** Checked both node proofs against the Lean reduction
   and the docstring construction. Each `proof_deps` is exactly the union of
   its step `uses`; the new node has source, proof origin, searches, split
   status, creation record, blueprint ancestry, chapter, unit and Lean record.
   Its recorded Lean signature matches the new theorem after whitespace
   normalization. The parent preserves all fields outside the stage-3-owned
   proof fields.

Second-reading changes: removed the redundant public import
`Mathlib.Algebra.Homology.HomologicalComplexAbelian` from the new presentation
and recorded this import pruning above. The proof, all signatures, and both
node files needed no repair. Added this independent review and axiom evidence.
The counts remain one original hole closed, one strictly intermediate hole
added, net zero: a decomposition, not a completed axiom-free geometric proof.
