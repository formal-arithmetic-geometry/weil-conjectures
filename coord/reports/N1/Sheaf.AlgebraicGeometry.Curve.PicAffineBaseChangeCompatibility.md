## What changed

Repair C1: replaced the uncited faithfully flat descent argument in the transport
node and docstring with the requested elementary affine-chart argument. All other
proof text and Lean declarations are unchanged.

Proved `AlgebraicGeometry.pic_affine_base_change_compatibility` with its signature
unchanged. The proof installs the base-changed curve instances, proves that the
boundary is finite, applies the existing boundary restriction theorem twice,
constructs the quotient witnesses, proves the fixed-basepoint/pairwise-generator
closure equality, and proves the final square using `Pic.map_comp` and
`Compactification.baseChange_i_fst`.

Added one strictly smaller geometric theorem in
`Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport`: preservation of
Pic⁰ and an isomorphism of the boundary-difference subgroups. It asserts no affine
Picard quotient or restriction formula. Its docstring and node give the complete
argument from rational boundary points, flat Cartier pullback, degree invariance,
and the injective Jacobian point map.

BaseChangeCurve and PicRestrictionBoundary are now private proof imports.
Both modules compile cleanly through lcompile.py. No target or existing statement
changed. Import pruning is recorded in
`coord/changes/PicAffineBaseChangeCompatibility-imports.md`.

## Proved and sorry left

Proved the original module's only sorry:
`AlgebraicGeometry.pic_affine_base_change_compatibility`
(node `lem-sc-pic-affine-base-change-compatibility`).

This is a decomposition: one original hole is closed and one strictly smaller
geometric hole is added; no net reduction in the number of holes is claimed.

One new sorry remains:
`AlgebraicGeometry.pic_boundary_base_change_transport`
(node `lem-sc-pic-boundary-base-change-transport`). Existing imported sorries,
including `Scheme.Hom.pic_restriction_boundary`, are untouched.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.GenusInvariant` (its Jacobian compatibility is retained
  below the new transport theorem, so this node is not globally pruned).
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` (no symbol needed directly).
- `WeilConjectures.AlgebraicGeometry.Curve.Affine`: the abstract Picard divisibility
  theorem `lem-sc-pic-affine` is not needed; the actual restriction quotient from
  `lem-sc-pic-restriction-boundary` supplies the stronger map-specific description.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier` (retained below transport).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected` (handled inside
  `baseChange_curve`; no direct need).

The original direct dependencies
`lem-weil-separably-closed-geometrically-connected`,
`def-pc-geometrically-irreducible`,
`lem-weil-pbc-closed-point-residue-field-base`,
`lem-pc-divisor-line-bundle-properties`, and `lem-sc-genus-invariant` are now handled
by BaseChangeCurve or the new transport node. They remain needed there, rather than
being new independent work in this theorem. `lem-sc-compactification` is a statement
not invoked to construct another compactification; the supplied c and its actual
baseChange data suffice. The unit's affine compactification/Jacobian route is kept.

## Where the brief, the DAG or earlier work was wrong

The existing Lean statement leaves several conjunctions inside preceding `∀ L`
binders. The proof respects that exact syntax; no signature was changed.
The existing restriction theorem supplies the map-specific quotient descriptions,
so the original plan's separate abstract affine Picard theorem is redundant here.
The literature tree is not materialized on this machine; the source proof read was
the full three-step proof recorded in the original node, together with the unit
record and existing declarations. The new node explicitly marks its proof as an
agent expansion of that recorded source argument.

The regular-connected-integral and Picard-functoriality nodes are used as generic
tools; compactification base change is also a generic tool. The new boundary
transport theorem retains the original Jacobian route. No unit step is bypassed.

## New nodes

`lem-sc-pic-boundary-base-change-transport`, in
`dag/nodes/sec-curve-estimates/lem-sc-pic-boundary-base-change-transport.json`, states
only the transport of degree-zero boundary subgroups. Checked empty-boundary
exclusion (P₀ exists), singleton boundary (both generated subgroups are trivial),
and identity extension. Mathlib searches found abstract subgroup tools only;
LeanSearch returned an unavailable-service error. The new module is
`lean/Sheaf/AlgebraicGeometry/Curve/PicBoundaryBaseChangeTransport.lean`.
Change record: `coord/changes/PicAffineBaseChangeCompatibility-imports.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered original module with the repository using diff and a
   byte comparison of the entire theorem signature: identical. No existing
   declaration or definition changed. The public import changes have a change
   record; checked the two direct importers and the unchanged statement's imports.
   Verdict: pass.
2. Compiled both modules in import order with lcompile.py: no errors or warnings.
   Scratch copies with #print axioms for both declarations report only propext,
   Classical.choice, Quot.sound and sorryAx. The original theorem's local sorry
   is closed, but it is not yet an axiom-free theorem: it uses the new transport
   theorem and existing open restriction/Jacobian results. The only delivered
   sorry is the named transport theorem listed above. No forbidden declaration
   or hollow definition is introduced. Verdict: pass as a partial reduction.
3. Read the transport signature, docstring, and node. It is strictly part of the
   argument: no affine quotient, restriction kernel, quotient formula, or final
   commuting square is asserted there. Rational boundary points remain single
   reduced points under field extension, flat Cartier pullback preserves their
   classes, degree is invariant, and the Jacobian point map is injective. The
   image equalities determine the subgroups because their subtype maps are
   injective. Checked the identity extension, a singleton boundary (trivial
   difference subgroups), genus zero (trivial Pic-zero), and exclusion of empty
   boundary by P₀. Independent searches with leanfinder (line bundle pullback
   injectivity), loogle, msearch grep and rg on both Lean roots found no duplicate
   geometric theorem. Loogle does not recognize the upstream Scheme.Pic.mapHom
   identifier; local source inspection supplies that check. The upstream
   injective_pic_map_snd concerns pullback from the base of a proper family and
   does not close this field-extension/boundary transport statement. No split
   theorem could be closed in a short pass. Verdict: pass.
4. Read the assembly top down: baseChange_curve, finite complement, the two
   restriction quotients, transport, fixed-basepoint versus pairwise generators,
   and actual Picard functoriality. The generator-closure calculation and final
   square are correct. Public imports serve the statements; plain imports serve
   the proof or the documented remaining geometric proof. Every removed old
   proof dependency is accounted for in No longer needed: only lem-sc-pic-affine
   is bypassed rather than moved below an existing/new dependency. The supplied
   compactification replaces an existence invocation. The unit's realized lists
   are empty in the repository and were not altered; its affine compactification
   and Jacobian route is retained mathematically. Verdict: pass.
5. Existing node changes are exactly proof, proof_deps, proof_origin. Checked
   that each proof_deps equals the union of the steps' uses. Checked the new
   node's source, searches, provenance, created record, chapter/unit, blueprint
   and Lean record; its recorded Lean signature is byte-identical to the new
   declaration. Both nodes describe the implemented reduction and remaining
   transport proof. Verdict: pass.

Changed the import change record to quote the complete old and new import blocks
verbatim, including their actual order. Added this review and explicit axiom
qualification. No Lean proof or statement needed repair.

## Second reading by N1

1. Compared the original module with the repository using diff and a byte-for-byte
   comparison of the complete theorem signature: identical. The only existing
   declaration has its proof changed; no definition or target changed. Public
   import pruning is covered by the change record, whose old/new blocks match
   the files. Read the two direct importers and their explicit imports. Pass.
2. Compiled both delivered modules in dependency order through lcompile.py with
   no errors or warnings. Fresh scratch copies of the current files with
   `#print axioms` show exactly propext, Classical.choice, Quot.sound and sorryAx
   for both declarations. The sole delivered sorry is the named transport
   theorem; there are no forbidden declarations or hollow definitions. Pass as
   a partial reduction, not an axiom-free proof of the target.
3. Read the transport statement, its complete docstring proof, and its node.
   Rational boundary points give singleton fibres; flat Cartier pullback and
   degree invariance transport the generators and Pic-zero. Jacobian
   compatibility reduces injectivity to the elementary affine-chart argument
   now recorded in both docstring and node. The subgroup image equalities and
   injective subtype maps determine the required equivalence. Checked identity
   extension, singleton boundary, genus zero, and the exclusion of empty
   boundary by P₀. Fresh leanfinder search for Picard pullback injectivity,
   loogle search for subgroup map/closure, msearch grep and local rg found no
   duplicate transport theorem. The existing injective_pic_map_snd pulls back
   from the base of a proper family and does not prove this statement. The
   remaining geometric lemma cannot be closed in a short pass. Pass.
4. Read the target proof top down: base-changed curve structures, finite
   complement, restriction twice, transport, generator-closure algebra, and
   functoriality of the actual pullback maps. These are genuine reductions;
   transport asserts neither a quotient description nor the final square.
   The imports serve the signatures or these proof steps (including the
   documented geometric proof still open). Every old proof dependency is
   accounted for under No longer needed; lem-sc-pic-affine is the redundant
   abstract quotient result. The unit's affine compactification/Jacobian route
   is retained. Its realized lists are empty in the repository and unchanged.
   Pass; count this as one-hole-to-one-hole decomposition.
5. Compared the existing node to the repository: only proof, proof_deps and
   proof_origin changed. Each node's proof_deps is exactly the union of its
   steps' uses. The new node has source, search records, provenance, creation,
   blueprint, chapter/unit and Lean records; its Lean statement is byte-for-byte
   the new theorem signature. The nodes agree with the assembly and the
   remaining transport argument. Pass.

Changed only this report: made the decomposition count explicit and recorded
this independent reading of the repaired affine-chart argument. No further
Lean or DAG repair was needed.
