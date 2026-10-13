## What changed

Replaced the sorry in `AlgebraicGeometry.derivedPullback_tensor_unit_kFlat` with
both complex unit calculations and a categorical localization/cancellation argument.
All existing public signatures and definitions are unchanged. The proof uses private,
proved helpers for inverse complex unit laws, componentwise lax-square cancellation,
and invertibility of the supplied counit at a K-flat complex. The unit complex is
K-flat directly by transporting acyclicity across the right unitor.

Imported `WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare` privately for its
actual-unit localization tensorator invertibility lemmas, and imported the new
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization` privately for the
explicit-unit normalization. Updated the parent node's proof route and dependencies.
The new normalization module has one public theorem and its own node.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.derivedPullback_tensor_unit_kFlat`
(node `lem-pc-derived-pullback-tensor-unit-kflat-coherence`). The item contains no
remaining sorry. Added one smaller hole:
`AlgebraicGeometry.derivedPullback_tensorUnitIso_normalization`, in
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization`, node
`lem-pc-derived-pullback-tensor-unit-normalization`.

This is a decomposition: one original hole closed, one new hole added, not a claim
of a net reduction in holes. The new statement concerns only the explicit unit
comparison and localization unit maps. It has no tensor comparison mu, complex
tensor comparison phi, K-flat representative P, or unit-law conclusion. Its
complete proof in words is in its docstring and node. The parent combines it with
proved complex calculations, naturality, the supplied K-flat compatibility hmu,
and cancellation to prove both requested unit equations.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`, and removed
`lem-pc-bounded-above-flat-kflat` from this node's proof dependencies. The proof
uses the right unitor to show K-flatness of the unit, so it needs neither a flatness
proof for each unit term nor a boundedness argument. That module remains a
transitive dependency of the unchanged public counit module; this is pruning of
this proof route, not a claim that it disappears from the entire target closure.
No other original imports or DAG proof dependencies are pruned.

General tensorator invertibility on arbitrary K-flat pairs, preservation of all
coproducts by the termwise pullback, and an induced global monoidal structure on
that functor are unnecessary for this argument and are not imported. The inverse
unitor formula singles out only the (0,n) or (n,0) tensor summand.

## Where the brief, the DAG or earlier work was wrong

No disputed statement, target change, hollow definition, or forced adaptation.
The plan's full summand-by-summand coproduct extensionality calculation can be
shortened using the inverse unitor formula: it uses only hphi on the unique unit
summand and underived oplax unitality. The localization argument cancels the
counit at P and the target tensorator at its actual tensor unit, rather than
requiring tensorator invertibility on arbitrary K-flat pairs.

Concrete Q/Qh unit normalization repeatedly requires expensive comparison of the
sheaf tensor/localization instances. This calculation is isolated as the smaller
new statement so that the substantive coherence argument is reviewable and can
be delivered within the worker interval.

## New nodes

`lem-pc-derived-pullback-tensor-unit-normalization`, in
`dag/nodes/sec-picard-framework/lem-pc-derived-pullback-tensor-unit-normalization.json`,
states invertibility of the target localization unit and the formula for the
explicit derived unit inverse composed with that unit. Its hypotheses omit all
tensor comparison and K-flat data. Its proof is expansion of the four explicit
iso factors and identity quotient/factorization components, then cancellation.
Edge cases include zero rings and empty schemes because the construction uses
only functorial unit isomorphisms. No change record is needed: no existing public
statement, definition, or visibility was changed.

## Second reading by M3

1. **Unchanged public declarations: pass after whitespace repair.** I diffed the
   existing module against the read-only repository and compared its theorem
   signature byte for byte. The only signature difference was one extra space
   before `:= by`; I removed it. No hypothesis, conclusion, definition, existing
   visibility or public import changed. The normalization module is new and is
   imported only for the proof.
2. **Proof and axioms: pass with the reported residual hole.** Both delivered
   modules compiled through `lcompile.py --all` without errors or warnings.
   Scratch copies with `#print axioms` also compiled (10.9 and 55.7 seconds).
   Both public theorems use only `propext`, `Classical.choice`, `Quot.sound` and
   `sorryAx`, consistent with the remaining normalization and upstream holes.
   The sole textual sorry in this delivery is the complete proof of the named
   normalization theorem. There is no forbidden declaration, hollow definition
   or data chosen from a new existence hole. The private helpers are proved;
   the counit helper uses only proof consequences of the recorded derived
   pullback construction.
3. **Split statement: pass as a decomposition.** I read the explicit four-factor
   unit construction, the homotopy quotient and termwise-factorization
   comparisons, and the localization lax structure transported by
   `quotientCompQhIso`. Their identity components give precisely the new
   normalization formula by inversion and cancellation. This holds for any
   supplied additive strong monoidal F and invertible unit counit; it does not
   assume that F is the pullback. Identity functors reduce to unit-map
   cancellation; zero rings and empty schemes need no nonzero objects or extra
   hypotheses. The new statement omits P, hP, phi, mu and both unit-law
   conclusions, so it is strictly a part of the argument rather than a renamed
   target. Its docstring contains the full calculation and source, and its node
   records the same statement. Fresh LeanFinder, Loogle and grep searches using
   composite unit comparisons and monoidal localization found generic unit
   formulas and left-derived uniqueness, not a replacement for this particular
   normalization. I also searched both library roots for unit normalization and
   inspected the existing etale derived-pullback comparison. No short direct
   replacement for the residual concrete normalization was found.
4. **Top-down route and pruning: pass.** I followed both inverse complex-unit
   calculations, the K-flat counit uniqueness argument, compatibility hmu and
   the categorical cancellation helpers through the final inversion of the two
   isomorphisms. Using just the (0,n) or (n,0) inclusion of the inverse unitor
   avoids a full coproduct-extensionality argument. K-flatness of U follows
   directly from the right unitor. The actual-unit tensorator invertibility
   lemmas of OplaxOfLaxSquare are used, without assuming arbitrary-pair
   invertibility or a global monoidal structure on termwise pullback. The
   removed bounded-above-flat import and its node are the entire old dependency
   pruning; its transitive presence is accurately reported above. Proof-only
   imports are plain imports. The unit record sk-thm-picard-duality has empty
   realized statement and step lists, so this refinement bypasses no recorded
   realized step. This remains a one-hole-closed, one-hole-added decomposition,
   with no claim of net hole progress or a module leaving the target closure.
5. **DAG agreement: pass after dependency repair.** The existing node changes
   only proof, proof_deps and proof_origin. Its union of proof-step dependencies
   agrees with the Lean route. I added the normalization node to the right-unit
   step's uses as well, since that step uses the shared normalized eta formula.
   The new node has the required source, proof, searches, creation, blueprint,
   chapter, unit and verbatim Lean signature, with status split. No existing
   statement or unit record changed and no change record is needed.

Changes in this reading: restored exact signature whitespace, recorded the
normalization dependency in the right-unit DAG step, and added this review.
