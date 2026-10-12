## What changed

Replaced the sorry in `AlgebraicGeometry.connectedSpace_generic_fibre_of_flat_trait`
by a complete Lean reduction preserving its signature. Proved generic-fibre nonemptiness
by lifting a generalization along the flat map. Proved injectivity of restriction on
every open by flat base change of the scheme-theoretically dominant generic point.
On affine opens, used the already proved DVR algebraic idempotent extension theorem.
Proved overlap compatibility, glued the lifts with the structure-sheaf axiom, proved the
glued section is idempotent, and applied the already proved scheme connectedness criterion.
All additional imports in the item are private proof imports.

Added `Sheaf.AlgebraicGeometry.GenericFibreAffineRingModels`, isolating the canonical
localization and reduced quotient descriptions of affine fibre section rings. This
statement assumes neither flatness nor connectedness and has no idempotent hypothesis
or connectedness conclusion. Its canonical isomorphism is required to commute with
restriction. The new node includes a complete proof following Tag 055J and the general
Mathlib affine pullback, localization base change and quotient base change results.
The statement was checked on an empty affine open, an empty closed fibre and a
nonflat morphism; no finiteness or separatedness is needed.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.connectedSpace_generic_fibre_of_flat_trait`
(node `lem-sbc-connected-generic-fibre-trait`). Its proof contains no sorry.
The three private helpers `generic_nonempty`, `generic_injective` and
`generic_affine_extension` are proved, together with the naturality argument inside
the main theorem.

Added one named hole:
`AlgebraicGeometry.generic_fibre_affine_ring_models`
(node `lem-sbc-generic-fibre-affine-ring-models`) in its own module, with proof
exactly `:= by sorry`. No other sorry is left or added by this delivery.

This is a decomposition, not a sorry-free proof of the mathematical theorem:
one upper hole closed, one strictly different lower hole added, net zero holes.
The ring-level extension declaration used from the source library is already proved.

## No longer needed

None. The original module had no proof-dependency imports or nodes to prune.
The final proof imports only the fibre ring-model statement, the existing DVR
idempotent extension, the existing scheme idempotent criterion, and the Mathlib
flat-generalization and scheme-theoretic-dominance APIs actually used.
No component-theory, properness, quasi-separatedness or finiteness modules are needed.

## Where the brief, the DAG or earlier work was wrong

The existing argument was mathematically correct. Its first and third steps conceal
the affine fibre identifications and the gluing work; these are now explicit in Lean.
The remaining ring-model lemma is more elementary than affine idempotent extension:
all idempotent reasoning, flatness and global gluing have already been formalized.
The nonemptiness argument is shorter via Mathlib's flat generalization theorem.
No statement or definition was changed, and no unit route was bypassed.

A scratch compilation verified the affine fibre square on section rings using
`isIso_pushoutSection_of_isAffineOpen` and `isIso_pushoutSection_iff`, with
`US := ⊤`, `UT := ⊤`, `UX := U.1` and `UY := f.fiberι η ⁻¹ᵁ U.1`.
Simplifying `Scheme.Hom.appLE`, `Scheme.Hom.fiber`, `Scheme.Hom.fiberι` and
`Scheme.Hom.fiberToSpecResidueField` gives a pushout of the four section maps.
To finish the remaining node, transport this square across `Scheme.ΓSpecIso`
and `Scheme.Spec.residueFieldIso`, then use the canonical localization and
quotient base-change equivalences. This scratch result is not an additional
public declaration or hole in the delivery.

## New nodes

`lem-sbc-generic-fibre-affine-ring-models` states the canonical affine generic
localization comparison and reduced uniformizer quotient. Source: Tag 055J;
proof dependencies: the existing Mathlib affine-spectrum pullback, localization
base-change and tensor-quotient nodes. LeanSearch was unavailable; LeanFinder,
Loogle and source grep found the general tools but no exact comparison statement.

`lem-sbc-dvr-idempotent-extension` records the existing, proved declaration
`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem` in
`WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic`. This adds no
Lean module or hole. Source: the denominator induction in Tag 055J.
The whole blueprint was searched for Tag 055J; no imported blueprint node matched.
No change records or forced adaptations are needed.

## Second reading by R3

1. **Interfaces — pass.** Compared the complete item with the repository using
   `diff -u`, then compared the existing theorem signature byte for byte through
   `:=`. The signature and original docstring are identical. The only additional
   declarations in that module are private proved helpers. The other delivered
   module is new. No definition, target, existing public import, or existing
   declaration visibility changed; no change record is required.
2. **Proof and axioms — pass as a decomposition.** Recompiled both delivered
   modules in import order using `lcompile.py --all`; both compiled without
   warnings or errors. A scratch copy with `#print axioms` checked the main
   theorem, all three private helpers, the ring-model theorem, and the two
   upstream theorems. Nonemptiness, restriction injectivity, the upstream DVR
   extension, and the scheme idempotent criterion use only `propext`,
   `Classical.choice`, and `Quot.sound`. The ring model, affine extension, and
   main theorem additionally use `sorryAx`, as expected from the one reported
   lower hole. The delivered files contain exactly one `sorry`, as the entire
   proof of the reported named theorem; no forbidden declaration or hollow
   definition occurs. Local choices of affine lifts are inside a proof, not
   definitions of data from an undetermined existence theorem.
3. **Split statement — pass.** Read the full ring-model statement, its proof
   docstring, its node, and the source [Stacks Tag 055J](https://stacks.math.columbia.edu/tag/055J).
   The remaining statement is a canonical ring comparison, strictly a part of
   the argument, with neither flatness nor connectedness nor an idempotent
   assumption or conclusion. Checked the empty affine open (zero rings),
   `X = Spec Frac(R)` (empty closed fibre, uniformizer a unit, zero quotient),
   and the nonflat `X = Spec(R/(pi))` (generic fibre and localization zero,
   reduced closed quotient). These cases satisfy exactly the written statement.
   The generic comparison must commute with restriction, which is precisely
   the equation used by the affine extension proof. Independently searched with
   LeanFinder for sections of affine scheme fibres over a fraction field and
   with Loogle for `"IsLocalization", "ResidueField"`, and searched the local
   Sheaf, upstream, Mathlib geometry and DVR sources for fibre/localization,
   residue-field/Away and quotient/fibre combinations. Found general affine
   fibre and localization tools, but no exact existing comparison. The lower
   statement's canonical identifications require further formalization; it is
   retained, rather than claimed proved.
4. **Route and pruning — pass.** Read the whole reduction: flat generalization
   gives nonemptiness, flat base change of scheme-theoretic dominance gives
   injectivity on all opens, the already proved DVR theorem gives affine
   lifts, and injectivity plus sheaf gluing gives the global idempotent. These
   steps implement Tag 055J. Each added private import supplies declarations
   used in those steps; each public import of the new module supplies its
   signature. The old node had empty `proof_deps`, so the complete list of old
   dependencies no longer needed is empty. Read
   `dag/units/sk-prop-normal-form.json`: this item is a lower auxiliary node,
   not the unit statement or a recorded realization. No unit step, chapter
   route or realization was replaced or bypassed.
5. **DAG — pass.** Compared the existing node with the repository and checked
   its new proof steps against the Lean body. Its three proof dependencies are
   exactly the affine ring models, the existing DVR extension, and the scheme
   idempotent criterion. Read those nodes and the three Mathlib leaf nodes used
   in the ring-model proof plan. Both new nodes have the required provenance,
   source, searches, dependency lists, blueprint origin and Lean records; the
   new hole's Lean signature matches its node verbatim. The algebraic extension
   node points to an already proved declaration and adds no hole.

Second reading changed only this review record and appended independent search
checks to the ring-model node. No Lean repair was needed. The accounting remains
one original hole closed and one strictly simpler hole added: a decomposition
with net zero holes, not a sorry-free proof of the target.
