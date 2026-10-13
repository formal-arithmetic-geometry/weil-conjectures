## What changed

Reduced `AlgebraicGeometry.exists_openRestriction_closedMonoidal` without changing its
signature, visibility, local standard localization, or specified tensor-Hom families.
The proof obtains a monoidal structure, constructs each Hom comparison as the explicit mate
of restricted evaluation, proves that mate invertible, and establishes the required equation
for every morphism by naturality. The private generic lemma
`monoidal_restriction_mate_equation` proves the categorical calculation for categories with
unrelated universes; it uses tensorator naturality, the two canonical-family naturality
identities, functoriality, and `Equiv.apply_symm_apply`.

Three new modules make the reduction explicit:
`Sheaf.AlgebraicGeometry.OpenRestrictionDerivedMonoidal` states strong monoidal descent alone;
`Sheaf.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso` proves pointwise invertibility
of the explicitly constructed mate for any monoidal structure;
`Sheaf.AlgebraicGeometry.OpenExtensionProjectionFormula` states the geometric extension-by-zero
projection formula used in that proof. None states the parent's existential closed-monoidal
comparison or its equation for arbitrary morphisms. The parent
constructs the comparison maps explicitly, rather than choosing unspecified Hom witnesses.
No definition contains a hole or chooses arbitrary data from an unproved existence theorem.
The monoidal witness is eliminated inside the theorem proof, not used to define data.
The projection theorem determines J by its universal property as a left adjoint to R;
its proof-in-words constructs it by exact extension by zero. The mate proof eliminates
that existential solely to prove invertibility of c, whose explicit formula does not
contain J. No data from this existential enters a public definition.

The parent's node now follows this proof. The three new nodes include the complete argument,
sources, Lean signatures, and actual search results. No existing statement or definition
was changed, and no forced adaptations are needed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_openRestriction_closedMonoidal`
(node `lem-pc-open-restriction-closed-monoidal`). The main module now contains no `sorry`.
The generic private mate calculation is proved without holes.
`AlgebraicGeometry.openRestriction_evaluationMate_isIso` is also proved, from the projection
formula and canonical-family naturality. Its private `mate_isIso_of_projection` constructs
an explicit composite of five Hom equivalences and proves that composite equals
postcomposition by the mate; `isIso_of_yoneda_map_bijective` then proves invertibility.
This module contains no `sorry`.

Added exactly two named theorem holes, each in its own new module:

- `AlgebraicGeometry.exists_openRestriction_derivedMonoidal`
  (`lem-pc-open-restriction-derived-monoidal`,
  `Sheaf.AlgebraicGeometry.OpenRestrictionDerivedMonoidal`).
- `AlgebraicGeometry.exists_openExtension_projectionFormula`
  (`lem-pc-open-extension-projection-formula`,
  `Sheaf.AlgebraicGeometry.OpenExtensionProjectionFormula`).

This is a decomposition: one upper hole closed and two lower holes added, a net increase
of one directly introduced hole, not a completed axiom-free proof of the underlying theorem.
Existing imported holes are unchanged. All delivered files compile through `lcompile.py`;
the main proof compiles without warnings. The increased heartbeat limit is solely for
elaboration of the canonical-family predicate and its sheaf tensor instances.

Edge cases checked before stating the lower results: empty open (all open-side objects are
zero), zero inputs, unbounded complexes (use full total coproducts, not finite truncations),
and arbitrary morphism universe w (the target remains the standard u+1 localization).
The mate-invertibility proof works for every monoidal structure: its projection morphism
is invertible because it restricts to invertible tensorators and both objects are supported
on the open. It does not claim that evaluation itself is invertible.

## No longer needed

Removed these nine proof-only imports from the main module:

- `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`
- `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`
- `Sheaf.Algebra.Homology.HomComplexRestrictOpen`
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`

The monoidal lower step still needs the K-flat-model, total-tensor, K-flat-resolution,
tensor-naturality and ordinary pullback-monoidal nodes; these are imported in its module.
The geometric projection lower step also needs K-flat resolutions and exact extension
by zero/stalks. The now-proved mate module needs only that projection statement and the
canonical family; its former resolution/stalk imports have been removed.
`KInjectiveHomComplex` remains part of the canonical tensor-Hom family's imported theory.
These six removals from the main module are relocation/redundancy, not global pruning.

The replacement mate argument no longer needs these three nodes or their modules as steps
of this item's proof:
`lem-sc-hom-complex-restrict-open` (`Sheaf.Algebra.Homology.HomComplexRestrictOpen`),
`lem-sc-derived-k-injective-restrict-open`
(`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`), and
`lem-sc-derived-internal-hom-restrict-open`
(`Sheaf.Paper.DerivedInternalHomRestrictOpen`). Other library users may still need them;
no claim about their removal from the entire targets' import closure is made.
The parent's proof dependencies are now exactly the canonical tensor-Hom node and the
monoidal-descent and proved evaluation-mate nodes. Its statement dependencies and the unit
route stay unchanged.

For completeness, all thirteen old proof-dependency entries removed from the parent's
`proof_deps` are accounted for below. These are changes to direct proof steps, not a claim
that each module has left the targets' import closure.

| Old node | Disposition |
| --- | --- |
| `def-pc-derived-category` | Still needed by signatures; provided transitively. |
| `def-pc-scheme-derived-tensor-structure` | Still needed by signatures; provided transitively. |
| `def-pur-derived-internal-hom` | Still needed by signatures and canonical family. |
| `lem-weil-pbc-module-restriction-open-immersion-colimits` | Still needed to define R; also used in the monoidal and projection plans. |
| `lem-pc-adjoint-module-pullback-monoidal` | Relocated to monoidal descent. |
| `lem-pc-kflat-resolution` | Relocated to monoidal descent and projection formula. |
| `lem-pc-open-restriction-kflat-model` | Relocated to monoidal descent. |
| `lem-pc-open-restriction-tensor-natural` | Relocated to monoidal descent. |
| `lem-pc-open-restriction-total-tensor` | Relocated to monoidal descent. |
| `lem-pur-hom-kflat-into-kinjective` | Provided by the canonical tensor-Hom theory; no direct use here. |
| `lem-sc-derived-internal-hom-restrict-open` | Removed from this item's proof route. |
| `lem-sc-derived-k-injective-restrict-open` | Removed from this item's proof route. |
| `lem-sc-hom-complex-restrict-open` | Removed from this item's proof route. |

Second reading additionally removed the redundant proof-only import
`Mathlib.CategoryTheory.Adjunction.Basic` from
`Sheaf.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso`; the canonical-family import
already supplies the adjunction API. The module compiles without it.

## Where the brief, the DAG or earlier work was wrong

The existing `Scheme.exists_derivedRestriction_tensorHom_coherence` and its two lower lemmas
require a common localization universe, a family of over-site localizations for every open,
and the derived category of the composite ordinary restriction. They cannot be applied
directly to this theorem's composite of two derived functors with the standard open-side
universe u+1. They also discard the monoidal structure after obtaining tensor naturality.
Their mate argument is useful, but importing them does not solve the present interface.
The new lower statements address precisely these independent-localization interfaces.
The mate theorem itself is now proved by the generic adjunction calculation, so its only
unproved geometric input is the projection statement without internal Hom.

The earlier restriction tensor nodes cite Stacks Tag 08DX(1) as their main source. That tag
is actually a quasi-coherence result, with an affine tensor calculation in part (2).
The direct tensor-pullback statement is Tag 079U (`lemma-pullback-tensor-product`), whose
proof uses K-flat representatives and the termwise module tensor comparison. The new
monoidal node cites 079U and 06YH (`definition-derived-tor`), not 08DX.
This source correction does not dispute any Lean statement or modify the lower nodes.

Read Stacks cohomology.tex at `lemma-internal-hom`, `lemma-restriction-RHom-to-U`,
`lemma-restrict-K-injective-to-open`, `lemma-pullback-tensor-product`, and
`definition-derived-tor`, and the published pages for Tags 08DJ, 08DL, 08BS, 079U and 01AK.
The source is downloaded only in the sandbox scratchpad. The extension-by-zero mate
argument is explicitly marked agent-written in the new node, following the earlier
mate-invertibility node's argument with the localization-universe issue made explicit.
A further Lean proof removed the Hom-side gap: the remaining geometry is exactly the
first three steps, split into `OpenExtensionProjectionFormula`.

Searches ran through msearch: LeanSearch for both new statements returned HTTP 500 and is
recorded as unavailable. LeanFinder returned eight generic cartesian-closed functor
comparison results; Loogle returned generic monoidal constructions. Neither matches the
mixed-universe derived restriction. The logged grep returned no match. Local rg found and
we read the common-universe comparison modules and the module monoidal construction.
Blueprint searches for open restriction monoidal, restricted evaluation mate, and extension
by zero projection found no
existing blueprint statement. The item's recorded nearest ancestor is `lem-sc-finite-duality`;
its inherited blueprint path is retained. The unit record realizes no step by this node,
and the changes stay below its route.

## New nodes

`lem-pc-open-restriction-derived-monoidal`: strong monoidal descent of the specified exact
restriction. It contains no internal-Hom construction. Module:
`lean/Sheaf/AlgebraicGeometry/OpenRestrictionDerivedMonoidal.lean`.

`lem-pc-open-restriction-evaluation-mate-is-iso`: pointwise invertibility of the explicit
curried restricted evaluation, for an arbitrary supplied monoidal structure. It contains
no compatibility conclusion for arbitrary ξ. Its proof is complete, reducing geometric
input to the projection formula. Module:
`lean/Sheaf/AlgebraicGeometry/OpenRestrictionEvaluationMateIsIso.lean`.

`lem-pc-open-extension-projection-formula`: existence of the extension/restriction
adjunction and invertibility of its tensor projection mate. This is the remaining geometric
step; its statement contains neither internal Hom nor a tensor-Hom equivalence. Module:
`lean/Sheaf/AlgebraicGeometry/OpenExtensionProjectionFormula.lean`.

No change records are needed because every existing signature and definition is unchanged.


## Second reading by H4

1. **Existing interface: PASS.** Diffed the sole existing delivered module against the
repository. Extracted the original declaration's raw signature and compared it byte for
byte: `exists_openRestriction_closedMonoidal` is unchanged. Its visibility, standard
localization instance, existing docstrings, definitions and public import are unchanged.
Only private proved helpers, declaration-local elaboration options, proof bodies and
proof-only imports were added or changed. No change record or forced adaptation is needed.
The three other modules and their statements are new.

2. **Proof and axioms: PASS as a decomposition.** Compiled all four modules in import order
through `lcompile.py`, then compiled scratch copies with explicit `#print axioms` for all
four public theorem names and both generic private helpers. The public theorems use only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the listed open inputs.
`monoidal_restriction_mate_equation` uses only `propext` and `Quot.sound`;
`mate_isIso_of_projection` uses only the three permitted axioms, with no `sorryAx`.
There are exactly two direct holes, both whole proofs of the named public theorems listed
above. No prohibited declaration, hidden hole, hollow definition or arbitrary data choice
was found. Existential J and m are eliminated inside theorem proofs; c is the explicit
curried evaluation. The projection morphism supplies an explicit isomorphism via `asIso`.
Scratch audit copies were removed before delivery. One original hole is closed and two
new holes remain: a decomposition, not an axiom-free proof or a positive net hole reduction.

3. **Split statements and duplicate search: PASS.** Read the monoidal-descent and projection
formula docstrings and node arguments in full. The first retains only the tensor/unit
structure; the second retains only the extension adjunction and tensor projection mate.
Neither restates the parent's internal-Hom comparison and arbitrary-morphism equation.
Checked empty and full opens, zero inputs, unbounded total tensors, and independent
localization universes. In particular the projection result really allows every m:
its source and target are supported on U, R reflects isomorphisms between them, and its
restriction is a composite of the invertible adjunction unit and supplied tensorator.
Read the source's exact extension adjunction argument and K-flat tensor pullback argument.
Fresh msearch queries used "fully faithful left adjoint", "tensor projection formula",
"frobenius", and monoidal derived functor terminology, with LeanFinder, Loogle and grep.
LeanFinder's nearest Mathlib Frobenius/closed-functor results require cartesian tensors;
Mathlib's `Monoidal.Reflective` results have a different reflective-subcategory interface.
Local rg and direct reading found the existing derived evaluation-mate and coherence
modules: they require a common localization universe and an over-site localization family,
and apply to the derived composite ordinary functor. They do not supply this statement.
The upstream derived tensor instances likewise do not directly give R.Monoidal.
Neither geometric hole has an immediate existing-library proof that can be substituted.

4. **Route, imports and pruning: PASS after report correction.** Read the categorical
calculation from the original theorem down to the five-Hom-equivalence argument and its
geometric inputs. Both private helpers give real reductions. Public imports are precisely
for signature types; lower proof-dependency imports are retained for the recorded plans.
Removed redundant `Mathlib.CategoryTheory.Adjunction.Basic` from the mate module and
compiled that file cleanly without it. Completed `No longer needed` with every old parent
proof-dependency entry absent from the new direct dependencies, distinguishing relocation,
transitive/signature use, and the three restriction-Hom steps genuinely bypassed here.
Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists are empty,
and no realized unit node is bypassed. The unit and chapter records are unchanged.

5. **DAG agreement: PASS.** All four recorded Lean signatures agree with their declarations
under the contract's whitespace normalization. The existing node changes only `proof`,
`proof_deps` and `proof_origin`; its mathematical statement and statement dependencies
remain unchanged. Every proof dependency list equals the union of the steps' uses. The
parent uses monoidal descent, the proved evaluation mate and canonical naturality; the
mate uses the projection input and canonical naturality. The three new nodes carry the
required source, proof-in-words, searches, origin, creation, blueprint ancestry, chapter,
unit and Lean records. Their geometric dependencies exist in the library.

Second reading changed only the redundant proof import and report dependency accounting;
no theorem statement, definition, proof body, node or unit route needed repair.
