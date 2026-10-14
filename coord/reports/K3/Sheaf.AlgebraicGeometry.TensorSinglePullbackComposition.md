## What changed

Repair H10 (reviewer X-d9d1e): optimized `single_naturality` and `derived_glue`
without changing either signature or conclusion. Naturality names the single,
homotopy and termwise functors, uses explicit `change` statements, and combines
the three component equations with the elementary private `naturality_three`.
The glue calculation applies the elementary private `paste_maps` with every
morphism explicit, rather than repeatedly normalizing concrete derived functors.
Both elementary calculations are proved from associativity in this same file;
no module or unfinished obligation was split off. The local
`cleanup.letToHave false` setting preserves the named bindings. No public
signature, definition body, import, timeout or heartbeat limit changed.

Reduced `AlgebraicGeometry.tensorSinglePullback_composition` to ordinary coefficient
pullback composition. Proved private single-pullback naturality and a generic derived
composition helper, then combined them with canonicalSinglePullbackComposition.
All existing signatures and public imports remain unchanged. Local irreducibility
attributes keep large definitions folded inside the private proof calculations.
Added one proof import and one new underived theorem module (now proved in the
second reading); updated the parent node to record this reduction.

Successful H10 checks (2026-10-14):

- Two fresh `lcompile.py --all` runs, each starting with no sandbox `.lbuild`:
  the underived module compiled in 3.2 and 3.9 seconds, and the assigned module
  compiled in 40.5 and 39.2 seconds. Both runs were warning-free and used the
  unchanged 60-second per-file limit, compiling the modules in import order.
- An unchanged sandbox scratch copy of `PicardCoefficientTransposePasting`
  compiled warning-free in 21.8 seconds against a copy of the first fresh run's
  actual outputs, selected by the wrapper's sandbox import overlay.
- Declaration-table comparison against the returned delivery reports no changed
  signature and no removed declaration. Both existing private helper signatures
  remain identical. The only new declarations are the two proved elementary
  category helpers, and neither has the derived-category section hypothesis.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.tensorSinglePullback_composition`.
The already-proved wrapper `AlgebraicGeometry.tensorSingleCoefficientMap_composition`
remains proved. The first worker added the named hole
`AlgebraicGeometry.Scheme.Modules.tensorCoefficientPullback_composition`, node
`lem-sc-tensor-coefficient-pullback-composition`; the second reader proved it using
Mathlib `Adjunction.leftAdjointCompIso_assoc`. There are no remaining or added
holes in either delivered module. The private helpers are also sorry-free, including the newly proved
`AlgebraicGeometry.naturality_three` and `AlgebraicGeometry.paste_maps`.
Relative to the repository: one hole closed, zero holes added, net one.
Axiom probes show only `propext`, `Classical.choice` and `Quot.sound` for
both public composition theorems, the wrappers and all private helpers;
no `sorryAx` remains in their proof closures.

## No longer needed

None. The canonical single-pullback composition and module-pullback adjunction route
remain necessary; the latter is retained in the new underived node's proof plan.
No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

H10 correctly identified insufficient compilation margin in the returned
helpers: the original full set took 54.2 seconds locally, and a separate
original-file check took 55.6 seconds. Fresh reviewer runs exceeded 60 seconds.
Profiling identified expensive reassociation rewrites and kernel checking around
expanded single-functor/module-category expressions. The repair keeps those
expressions named and checks the elementary association calculations generically.
The new generic helpers have no derived-category section hypothesis.

Earlier attempts were blocked by the unpublished TensorCoefficientComparison object
file. During this retry the published build supplied that dependency. The draft
reduction then compiled. A temporary unchanged dependency copy used for diagnosis
was removed, together with its sandbox compilation artifacts, before the dry run.
Only the assigned module, new theorem module, two node records, local
transparency change record and this report are included in the delivery.

## New nodes

`lem-sc-tensor-coefficient-pullback-composition`, in
`Sheaf.AlgebraicGeometry.TensorCoefficientPullbackComposition`, isolates step 2 of
the assigned node: the ordinary coefficient comparison identity. Its source is
Stacks Project, Tags 0096 and 0D5S, and Mathlib
`Adjunction.leftAdjointCompIso_assoc`. Its docstring and node describe the proved
mixed-adjunction calculation and associativity argument. Identity morphisms,
empty schemes and zero modules introduce no additional assumptions. The derived proof combines this identity with independently proved
naturality and canonical single-pullback composition; it does not merely rename
the original statement.

The local transparency commands are documented in
`coord/changes/tensorSinglePullbackProofTransparency.md`; they have no effect on importers.
LeanSearch was retried and returned an internal server error; no match is claimed.

## Earlier second reading (a previous round; superseded)

1. Compared the entire assigned module with the repository using `diff -u`.
   All four existing declaration signatures, the coefficient-map definition body,
   universe and derived-category hypotheses, and public imports are unchanged.
   The additions are a proof import, private proved helpers, local transparency
   attributes, and the proof replacing the original sorry. The transparency
   record accurately describes their local scope. No other existing Lean module
   is delivered. Verdict: no accidental interface or target change.

2. Compiled both modules in import order with `lcompile.py`. Inspected all proof
   bodies and definitions; there is no axiom, unsafe, opaque, implemented_by,
   extern or hollow definition, and after repair neither module has any sorry.
   Scratch copies print axioms for all four existing declarations, the new
   public theorem, and every private helper. Only `propext`, `Classical.choice`
   and `Quot.sound` occur; there is no `sorryAx`, including in either composition
   theorem. The derived proof moves d1 by the naturality
   of the selected counit, termwise single comparison and adjoint uniqueness;
   derived_glue then maps the ordinary identity and applies
   canonicalSinglePullbackComposition. No comparison is inverted in this step.
   Verdict: kernel-checked proofs with no remaining axiom holes.

3. Read the new ordinary coefficient statement against the fixed definitions in
   TensorCoefficientComparison. Its objects and morphism directions match:
   ordinary a-pullback of tensor q-pullback L maps to tensor q1-pullback L,
   and b-pullback of that map composes through ordinary pullbackComp b a.
   There is no derived-category or flatness hypothesis; it is a strict
   underived part of the original argument, not a renamed derived conclusion.
   Read Stacks Tags 0096 (lemma-adjoint-pullback-pushforward-modules) and 0D5S
   (composition of derived pullbacks) online, and Mathlib
   Adjunction/CompositionIso.lean 60-85 and 170-181, Mates.lean, and
   AlgebraicGeometry/Modules/Sheaf.lean 235-269. The kernel proof now verifies
   the complete mate/coherence argument. Identity arrows only specialize the
   same adjunction coherence, zero modules keep the same functorial equality,
   and empty schemes never require a section, point, or nonzero object.
   Searched with different queries via msearch Loogle, LeanFinder and grep,
   and searched lean/Sheaf, lean/WeilConjectures, the upstream algebraic-geometry
   tree and dag/nodes. Found the generic Mathlib associativity theorem and its
   existing Mathlib leaf lem-sc-left-adjoint-composition-iso-associativity;
   found no duplicate fixed coefficient theorem. Verdict: true, strictly
   simpler, and now proved rather than left split with sorry.

4. Checked the route from the original sorry downward. The private naturality
   proof uses only naturality of the three existing constructions. The generic
   derived_glue proof genuinely combines this with canonical single-pullback
   composition. Public imports provide the pinned derived-composition wrapper,
   coefficient definitions and canonical single comparison required by public
   signatures; both plain imports are used in proofs. None can be pruned here.
   Both original proof dependencies remain used (the module adjunction directly
   in naturality and in the new theorem). Read dag/units/sk-prop-av-cube.json:
   its statement and sole step are unchanged; its realized lists are currently
   empty, and this delivery bypasses no recorded unit node or step.
   Verdict: no missing pruning and no unit-route change.

5. Compared the old and new parent nodes: changes are confined to proof,
   proof_deps and proof_origin. Expanded the parent dependencies to record the
   canonical comparison, selected derived counit and tensor adjunction used in
   naturality. Updated the new node's proof and origin to record the actual
   mixed-adjoint calculation and Mathlib associativity application, reusing the
   existing Mathlib leaf. Its Lean signature is verbatim and its chapter, unit,
   created, blueprint and search records are present. Existing unsuccessful
   LeanSearch calls remain explicitly unavailable, not claimed as no matches.
   Verdict: the DAG records the checked Lean proof.

Second-reading changes: proved tensorCoefficientPullback_composition using
private mixed and coefficient_hom_comp helpers and Mathlib associativity;
updated its docstring, node proof and origin, the parent's proof dependencies,
and this report. No existing signature or definition changed. One original
hole is closed and no new hole remains; this is no longer merely a decomposition.


## Second reading by K3

1. Compared the full assigned module with the read-only repository using
   `diff -u`, then independently compared all existing declarations with the
   declaration-table parser. All four existing statements are unchanged, as is
   the sole existing definition body. No declaration is removed; all public
   imports are preserved. The new underived module contains only proved theorems.
   Verdict: no accidental change to a target, signature or construction.

2. Read every delivered proof and checked both modules with `lcompile.py --all`:
   warning-free, 3.8 seconds and 39.5 seconds respectively. Fresh scratch copies
   of the current sources print axioms for all eleven declarations, including
   the private helpers. Only propext, Classical.choice and Quot.sound occur;
   the elementary helpers use only propext. No sorry, forbidden trust mechanism,
   hollow definition, or arbitrary object chosen from unproved existence is
   introduced. The derived proof uses naturality, maps the ordinary equality,
   and applies the canonical composition equation without inverting the single
   comparison. Verdict: complete kernel-checked proofs, one original hole
   closed and zero added.

3. Checked the ordinary theorem against TensorCoefficientComparison and the
   Mathlib definitions of conjugateIsoEquiv and leftAdjointCompIso. Its mixed
   adjunction identification and component directions are correct. Substitution
   removes only the supplied equalities; identity arrows, zero modules and empty
   schemes need no additional assumptions. The theorem is a strictly underived
   part of the argument and is fully proved. Fresh Loogle and LeanFinder searches
   identify leftAdjointCompIso_assoc; source searches for coefficient triangles
   and single-pullback naturality find no duplicate public coefficient theorem.
   CanonicalStructureMapBaseChange has a similar private naturality calculation,
   which cannot be imported as a public lemma. Verdict: no unsupported split-off
   statement and no avoidable new public theorem duplicating the library.

4. Followed the argument from the original hole down to canonical single
   composition and Mathlib adjunction associativity. Both plain imports are
   proof-only and used. Each public import supplies a declaration occurring in
   the existing signatures or definition: the canonical derived composition
   wrapper, coefficient comparison, and single comparison. Both old proof
   dependencies remain used, so the No longer needed list is complete. Read
   sk-prop-av-cube: its statement and sole step are preserved; its realized
   lists remain empty and no recorded unit route is bypassed.
   Verdict: no missing pruning or route change.

5. Compared parent node JSON with the repository: only proof, proof_deps and
   proof_origin differ. Their union matches the actual derived reduction.
   The new node has its source, complete proof, verbatim Lean statement,
   creation, blueprint, chapter, unit and search records; its Mathlib dependency
   is the existing leaf in sec-curve-estimates. The proof uses the coherent
   right-isomorphism form of that Mathlib declaration, as the node explicitly
   records. Verdict: node metadata agrees with the delivered Lean.

Changes in this reading: appended this independent review and refreshed the
search and compilation evidence. No Lean proof, signature, definition, import,
node or change-record repair was needed.

The unchanged direct importer PicardCoefficientTransposePasting also compiled
warning-free in 20.7 seconds against this reading's actual sandbox outputs.
