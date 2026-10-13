## What changed
The original target `globalTensorPullback_monoidal_normalization` now has a categorical
reduction through the concrete global-sections lax structure, adjunction-induced oplax
structure, Mathlib `Functor.Monoidal.ofOplaxMonoidal`, and the counit compatibility identity.
Its signature and all existing definitions are unchanged.

The new statements live in their own modules: `Sheaf.Paper.GlobalSectionsLaxMonoidalData`,
`Sheaf.Paper.GlobalTensorPullbackMatesIsIso`, and `Sheaf.Paper.GlobalTensorPullbackOplaxIsIso`.
The target imports its two helper modules privately; the oplax module imports the mates
module privately. The three original public imports are needed by the target signature.
Local linter suppression preserves the original automatically included section instance.

## Proved and sorry left
Original hole closed: `AlgebraicGeometry.Scheme.Modules.globalTensorPullback_monoidal_normalization`
(node `lem-sc-global-tensor-pullback-monoidal-normalization`). This is a decomposition,
not a completed proof with only standard axioms: it rests on the two smaller holes below.

Additional helper hole closed during second reading:
`AlgebraicGeometry.Scheme.Modules.globalTensorPullback_oplax_isIso`
(node `lem-sc-global-tensor-pullback-oplax-isiso`), by unfolding the transported components
and rewriting the concrete lax maps before applying the mates lemma.

Holes added relative to the repository, and the only literal `sorry`s delivered:
- `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor_laxMonoidal_data`
  (`lem-sc-global-sections-lax-monoidal-data`, GlobalSectionsLaxMonoidalData).
- `AlgebraicGeometry.Scheme.Modules.globalTensorPullback_mates_isIso`
  (`lem-sc-global-tensor-pullback-mates-isiso`, GlobalTensorPullbackMatesIsIso).

Thus one original hole is closed and two new holes are added (local net -1); no
whole-library progress or pruning count is claimed. The target and the proved oplax
helper still have `sorryAx` through these named open dependencies.

## No longer needed
No repository import or module is pruned: all three existing public imports occur in
the unchanged target signature or its instance context. The old target `proof_deps`
were `def-pc-global-derived-rhom` and `lem-sc-module-cup-naive-map-chain`; neither is
used directly by the new target proof. GlobalDerivedHom remains a statement dependency;
ModuleCupNaiveMap remains a statement dependency and a transitive helper dependency.
The target's direct proof dependencies are now the concrete lax-data node and the
oplax-isomorphism node. The latter uses the mates node.

The earlier sandbox's abandoned `Sheaf.Paper.GlobalTensorPullbackTransport` was never
an import of the repository version and is not counted as a pruned module.

## Where the brief, the DAG or earlier work was wrong
The earlier transport theorem restated the target and was rightly abandoned. The
first-worker reduction was genuine, but its oplax helper was still `sorry` despite
being a direct consequence of the stated mates. Earlier second-reading text incorrectly
claimed only the oplax node was a direct target dependency: the lax-data node is also
used. The helpers were placed in the target module instead of their own new modules.
The lax-data docstring lacked a source and a complete proof of the coherence laws.
The lax-data blueprint provenance still mentioned nonexistent
`lem-sc-global-sections-lax-monoidal`; this dangling reference is removed.

## New nodes
`lem-sc-global-sections-lax-monoidal-data`: concrete global-sections unit and tensorator,
with naturality, associativity and unit laws verified on pure tensors.

`lem-sc-global-tensor-pullback-mates-isiso`: invertibility of the unit and tensor mates,
using pullback from the global-sections point, extension-of-scalars tensor identities,
and uniqueness of a left adjoint with its adjunction.

`lem-sc-global-tensor-pullback-oplax-isiso`: the proved bridge from the concrete mates
to Mathlib's transported oplax components.

Change record: `coord/changes/GlobalTensorPullbackMonoidalNormalization-linter-options.md`.
It changes diagnostics only, with no interface change.

## Second reading by D4
1. Compared every delivered module with the repository. The three helper modules are
new. The sole existing target signature is byte-for-byte identical, including its
hypotheses and conclusion. No existing definition changed. Verdict: pass.
2. Compiled the delivered modules locally with lcompile.py and checked the four
public theorem axiom reports in a scratch copy. Only `propext`, `Classical.choice`,
`Quot.sound` and open-dependency `sorryAx` occur. The only literal holes are the two
named theorems listed above. No axiom, unsafe, opaque, implemented_by, extern, hollow
definition or arbitrary witness construction is introduced. The chosen lax structure
is determined by the prescribed unit and tensorator; its other fields are proofs.
Verdict: valid partial reduction, with two open dependencies.
3. Read the intermediate statements and the local tensor-section API, verified Stacks
Section 17.16 (https://stacks.math.columbia.edu/tag/01CA), especially Lemma 17.16.4,
and searched with leanfinder, loogle and grep through msearch.py and rg on both Lean
roots. Mathlib supplies the generic transported structure and component formulas,
not the specialized geometric isomorphism claim. Checked zero modules, the zero ring
and empty scheme: the tensor and unit formulas remain valid. The mates claim does
not require flatness or finite generation. Neither remaining hole restates the target:
one supplies right-adjoint coherence, the other only invertibility of two families
of explicit mates. Verdict: true, strictly smaller, source-backed statements.
4. Followed the proof from the target downward. It now takes the generic Mathlib route,
and the easy oplax bridge is proved. All helper imports used only in proofs are plain
imports; original public imports remain needed by the unchanged signature. Compared
the unit sk-prop-av-cube: its realized fields are unchanged, and no chapter or unit
step is bypassed. The pruning section names both old direct proof dependencies and
does not claim a never-imported sandbox module as pruning. Verdict: pass.
5. Compared each node's Lean record verbatim with its declaration, and checked proof,
proof_deps and proof_origin against the actual calls. The target uses lax data and
oplax invertibility; the proved oplax bridge uses mates invertibility. New nodes have
source, search, provenance and creation fields. Verdict: pass.

Second reading changed: proved the oplax bridge; moved three helpers to separate new
modules with private proof imports; completed the lax-data proof docstring and source;
gave helper-local instances distinct names to prevent collisions when imported together;
removed a dangling blueprint provenance reference; corrected the oplax node description
(the Lean helper needs no additivity assumption), target proof metadata,
pruning and hole accounting; suppressed the unused-section-instance warning while
preserving the target signature. No mathematical statement was weakened.
