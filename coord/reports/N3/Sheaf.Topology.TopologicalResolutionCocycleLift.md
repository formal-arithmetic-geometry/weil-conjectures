## What changed

Proved `CategoryTheory.exists_topological_resolution_cocycle_lift` without changing its
signature or visibility. Added proved private helpers for comparison into an arbitrary
termwise injective cochain complex and the free representable/sheafification section
equivalence. The comparison uses `Injective.factorThru`, `ShortComplex.Exact.descToInjective`,
and `CochainComplex.mkHom`; it requires exactness only of the source resolution.

The terminal-section bijection is proved directly from the sheafification adjunction,
free-forgetful adjunction, Yoneda, the prescribed generator equation for `a`, and naturality.
Surjectivity supplies the lifted section. Injectivity in the next degree, the chain-map
identity, and the original cocycle equation prove that its differential vanishes.
The proof uses the existing imports; the redundant added Whiskering import was removed
during second reading.

## Proved and sorry left

Closed the sole hole: `CategoryTheory.exists_topological_resolution_cocycle_lift`
(node `lem-sc-topological-resolution-cocycle-lift`). No holes remain in this module,
no holes were added, and nothing was split off. All three private helpers are proved.
The delivery dry run checks compilation and declaration axioms.

The construction handles degree zero, the zero sheaf, and empty topological spaces:
there is no positivity assumption, no nonzero generator assumption, and no assertion
that direct image preserves exactness. The inverse-image top open is handled by its
canonical isomorphism, rather than a nondefinitional identification of section types.

## No longer needed

None of the original imports, nodes, or modules are pruned. Both numbered steps of
the existing DAG proof are implemented as written; all three listed proof dependencies
remain used. No node update is needed because the proof route is unchanged.
A redundant explicit `Mathlib.Algebra.Category.Grp.Adjunctions` import tried during
construction was removed; it was absent from the original module. Second reading also
removed the added `Mathlib.CategoryTheory.Adjunction.Whiskering` import after a scratch
compile showed its API already available through the existing imports. Neither removal
prunes an original proof dependency or module from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. `InjectiveResolution.desc` alone does not apply because
`f_*I` need not be a resolution of `f_*F`; the proof uses the same inductive exactness
API with an arbitrary termwise injective target complex instead. The existing source
`TopCat.Sheaf.injective_pushforwardAb_obj` already proves the required preservation
of injectives. No new nodes or forced adaptations are required.

## Second reading by N3

1. Compared the only delivered Lean module with the repository using `diff -u`.
   The existing theorem signature and visibility, module header, docstring, and
   original imports are byte for byte unchanged. The only substantive additions
   are its proof and three private proved helpers. No change records are needed.
2. Compiled locally with `lcompile.py` without errors or warnings. A scratch copy
   with `#print axioms` for `exists_comparison`, `sectionEquiv`,
   `sectionEquiv_apply`, and `exists_topological_resolution_cocycle_lift` reported
   only `propext`, `Classical.choice`, and `Quot.sound` for every declaration.
   Scanned the delivered Lean source: no sorry or forbidden declarations. The
   section equivalence is actual adjunction data; no arbitrary witness is chosen
   from an unproved existence statement. Verdict: a complete proof.
3. No statements were split off and no holes added. Checked the private
   comparison's degree-zero extension and inductive square-zero calculation;
   its target needs injectivity, not exactness. Checked the equivalence's
   direction at inverse-image top and the generator/naturality calculation.
   The argument also applies to degree zero, the zero sheaf, and empty spaces.
   Searched with Loogle for injective-resolution/cochain-complex APIs and with
   `rg` for comparison and section-equivalence declarations in both Lean roots
   and Mathlib. Existing analogous generic helpers are private, and public
   comparisons found are specialized to other sites or injective resolutions;
   no shorter applicable public theorem was found.
4. Read both DAG proof steps and `dag/units/sk-thm-curveestimate.json`, including
   its `realized` field. The source-resolution comparison and terminal-section
   representation are implemented directly with Mathlib APIs and the existing
   injective-pushforward theorem. No unit route is bypassed. All original imports
   and all three original proof dependencies remain needed for this route/model;
   `No longer needed` records the only redundant added imports. Verdict: pruned.
5. Read the item's node and all three dependency records. Its proof,
   `proof_deps`, and `proof_origin` describe the proof as written, so no node
   edits are necessary. Its Lean statement matches the preserved signature.
   No new node, statement change, or forced adaptation is delivered.

Changed only the redundant added Whiskering import and this report. A scratch
compile without that import succeeded. The delivery dry run performs the final
compile and axiom probe on the repaired file.
