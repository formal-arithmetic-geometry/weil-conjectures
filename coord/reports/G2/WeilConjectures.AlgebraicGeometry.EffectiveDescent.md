## What changed

Replaced all three remaining sorries of `WeilConjectures.AlgebraicGeometry.EffectiveDescent` with compiling proofs from named intermediate results. The previously proved `existsUnique_hom_of_isPullback` is unchanged. No existing signature, definition, docstring, public import or target changed. All added imports in the item are proof-only imports.

Effective descent follows the given Stacks route: invariant affine neighbourhoods, then affine effectiveness and gluing. The two remaining steps are stated separately, with their actual geometric conclusions, rather than restating effective descent under another name.

Group descent is reduced to descent of multiplication and unit as a commutative monoid. The item itself proves that transport respects inverse using `MonoidHom.map_inv`, descends the inverse using the existing morphism-descent theorem, proves both inverse identities after projection, cancels the fpqc projection, and constructs the commutative group structure. This uses only multiplication/unit compatibility hypotheses already present in the statement; no inverse-compatibility hypothesis was added.

The geometric-properties proof obtains fixed relative smooth dimension via ring-level faithfully-flat codescent and `HasRingHomProperty.descendsAlong_flat`. Smoothness supplies the local finite type needed by the existing field-extension properness theorem; quasi-compactness is descended separately. Geometric integrality is proved in the item, using the existing common-extension-fields theorem and explicit pullback pasting. The new private helper `integral_of_flat_surjective` proves reducedness by injective faithfully-flat local stalk maps and irreducibility by continuous surjectivity. Both private helpers have complete proofs and no direct sorry.

The three corresponding existing DAG nodes have updated proof routes and proof dependencies. Four new modules each contain exactly one public theorem with its source and complete proof in words. All five delivered modules compile together, in import order, without warnings. Import-direction checks for the existing imported Sheaf modules passed.

## Proved and sorry left

Removed the original sorries from:

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite` (`thm-pd-effective-descent`), reduced to the two invariant-affine steps.
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback` (`lem-pd-group-scheme-descent`), reduced to commutative-monoid operations; inverse descent and its laws are proved here.
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback` (`thm-pd-fpqc-local-properties`), reduced to the ring codescent result and existing properness/quasi-compactness/common-field statements; geometric-integrality descent is proved here.

No direct sorry remains in the item. This is a reduction delivery, not a claim that its transitive axioms are already sorry-free. Existing imported theorem gaps remain with their existing nodes.

The delivery adds exactly these four named sorries:

- `CategoryTheory.Over.DescentDatum.exists_invariant_affine_neighbourhood`: `lem-pd-invariant-affine-neighbourhoods`, module `Sheaf.AlgebraicGeometry.InvariantAffineNeighbourhoods`.
- `CategoryTheory.Over.DescentDatum.isEffective_of_invariant_affine_neighbourhoods`: `lem-pd-invariant-affine-descent-gluing`, module `Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing`.
- `CategoryTheory.Over.DescentDatum.exists_commMonObj_of_effective_projection`: `lem-pd-comm-monoid-operations-descent`, module `Sheaf.AlgebraicGeometry.CommMonoidDescent`.
- `RingHom.locally_standardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat`: `lem-pd-relative-smooth-dimension-codescent`, module `Sheaf.RingTheory.RelativeSmoothDimensionDescent`.

Edge cases checked in the statements and natural proofs: empty V makes the neighbourhood condition vacuous and the gluing result uses the empty descended scheme; non-quasi-compact Y needs no global bound on the finite locally free degree; invariant opens are invariant in both directions by inverse transport. The monoid result uses no inverse and remains meaningful for arbitrary test schemes, including the empty one. The ring theorem allows n=0 and zero rings; local smoothness on the empty spectrum is vacuous. The geometric-integrality proof works with arbitrary, including inseparable or infinite, field extensions and obtains nonemptiness from the integral common base change.

## No longer needed

No original import was removed: the public imports provide the unchanged statements and structures, and the original proof-only Fpqc import supplies the effective epimorphism used in morphism and inverse descent. During development the explicit `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` import was removed as redundant, and the trial `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent` import was replaced by `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`; the final argument gets smoothness from fixed relative dimension rather than descending smoothness twice. These were trial imports, not imports in the base version. The new commutative-monoid module imports only the Flat and CommMon interfaces, rather than the larger Fpqc and CommGrp interfaces.

The effective-descent node no longer needs `cor-pd-finite-level` or `def-pc-projective-morphism` as proof dependencies. The theorem already receives the finite-subset affine-neighbourhood hypothesis. Obtaining a projective finite-level Jacobian is work of the caller, not part of proving this descent criterion. The properties node no longer needs `def-pc-finite-locally-free`: its field extension is arbitrary and the fpqc properties follow from Mathlib instances. These are pruned edges of these nodes, not assertions that the finite-level/projectivity nodes are unnecessary to the entire Jacobian unit. No unit step is bypassed.

The new commutative-monoid lemma needs no inverse-compatibility lemma or group-object descent theorem. The main item proves inverse compatibility and inverse descent, so no extra inverse node/module was introduced. The geometric-integrality argument needs no separate scheme-level geometric-integrality-descent module.

## Where the brief, the DAG or earlier work was wrong

The starting module has three sorries, not four: the T1 morphism-descent proof is already present and was reused unchanged. The older `lean_audit` entries still label that declaration as sorry-containing. This delivery changes only the three routes actually changed in Lean, not that historical audit.

The effective-descent DAG cites `cor-pd-finite-level` in the proof even though that is an application prerequisite. Its Lean theorem assumes the needed affine-neighbourhood property directly; the old dependency is not used. The properties DAG describes finite extensions and connectedness, while the adopted Lean statement already uses arbitrary field extensions, fixed smooth dimension and geometric integrality. The updated proof addresses that exact existing Lean statement without changing either its signature or the node's statement fields.

All source tags used for the new affine steps were checked: 03JE gives the norm construction; 0245 is affine effectiveness; 0AP4 is gluing effectiveness on invariant opens. No new mathematical source error or disputed statement was found. The unit's effective-descent and group/property-descent steps stay in place.

Mathlib searches used the prescribed launcher: LeanFinder/Loogle and grep returned interfaces but no exact result for each new statement. LeanSearch was attempted for all four and returned Internal Server Error; this is recorded as unavailable without a fabricated search verdict. Repository searches also checked the existing affine-effectiveness, fpqc morphism-descent and geometric-property modules before stating the missing conclusions. In particular affine effectiveness alone does not construct invariant neighbourhoods or glue them, and morphism descent alone does not package descended monoid axioms.

## New nodes

`lem-pd-invariant-affine-neighbourhoods` states the neighbourhood-construction part of Stacks 0H8K/03JE, including containment over an affine base open and transport invariance. It produces opens, not an effective descended scheme, and its proof includes the finite-orbit and norm construction.

`lem-pd-invariant-affine-descent-gluing` takes an already available invariant affine cover and carries out affine descent and gluing, using Stacks 0245/0AP4. It has no finite-subset neighbourhood hypothesis and does not construct the neighbourhoods. Its proof uses the existing affine-effectiveness and fpqc open/morphism descent nodes.

`lem-pd-comm-monoid-operations-descent` supplies only the multiplication, unit and commutative monoid laws plus their point identities. It assumes only a commutative monoid upstairs; the inverse and group laws are deliberately absent from its conclusion and are proved in the item. The blueprint source's multiplication/unit descent step and Stacks 02W0 are its sources.

`lem-pd-relative-smooth-dimension-codescent` is the affine ring-level fixed-dimension assertion needed to use Mathlib's generic scheme descent mechanism. It concludes neither properness nor geometric integrality and contains no scheme pullback square. Its proof descends smoothness and reflects the rank of differentials by faithful scalar extension, using 02VL, 02G1 and 00T7.

No change record is required: no existing statement, definition or public import changed.

## Second reading by G2

1. I compared the delivered `EffectiveDescent.lean` with the repository version. Existing declaration signatures and definitions are unchanged; the import changes are proof-only imports, and the four added modules are new declarations with their own nodes. Verdict: pass.

2. I compiled all five delivered modules with `lcompile.py --all`. They compile without errors or warnings. The item has no direct `sorry`; the four remaining `sorry`s are exactly the named split-off theorems listed above, with no `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. Verdict: pass.

3. I checked the four split-off statements against their docstrings, source tags, and node files. Each is a genuine intermediate conclusion: invariant affine neighbourhood construction, affine descent gluing, commutative-monoid operation descent, and fixed relative smooth-dimension codescent. None restates the item, and repository searches found no existing declaration with these statements. Verdict: pass.

4. I checked the proof routes from the target downward. The effective-descent proof uses neighbourhood construction and gluing; group descent uses operation descent and independently proves inverse compatibility and inverse laws; property descent uses ring-level dimension codescent, properness and quasi-compactness descent, and the common-field argument for geometric integrality. The report's `No longer needed` list records pruned dependencies, and the unit route remains represented by the updated nodes. Verdict: pass.

5. I checked that the updated node proof routes and dependencies match the Lean proofs, and that each new node has the required statement, source, proof, search, Lean, blueprint, chapter, and unit metadata. Verdict: pass.

I changed only this report section during second reading; no Lean statement, proof, import, or DAG node required repair.
