## What changed

Proved `AlgebraicGeometry.exists_schemeHomTensorPullbackIso` in
`Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso`, preserving its complete signature.
The comparison family is supplied by the existing canonical comparison theorem.
Its representative equation, invertible localization tensor maps and universal
pullback counits prove invertibility on K-flat pairs. K-flat resolutions and
naturality transport this to all pairs. `NatIso.ofComponents` packages the same
family, so its canonical predicate is retained definitionally.

Added proved private helpers `pullbackTensorModelMap_isIso` and
`pullbackCounit_isIso`, and proof-only imports of
`Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.Algebra.Homology.KFlatTensorProduct`, and
`Sheaf.Algebra.Homology.KFlatPullback`. Updated the existing DAG proof and its
proof dependencies. No new modules, definitions, public declarations, or nodes.

Scoped transparency-respecting elaboration to the existing
`internalHomMate_exists`, `tensorAdjunctionCore`, `lerayCore`, and
`schemeGlobalHomAdjunctionMap_isIso` proofs: the original file exceeded the
60-second compiler limit on this machine, while these scoped settings let the
complete proof compile within the limit. Suppressed the unused section-variable
warning only for `exists_schemeHomTensorPullbackIso`, retaining its original
ModuleCat derived-category binder rather than changing the public signature.

The earlier attempt logged the required leanfinder, loogle and grep searches;
this continuation checked those logs and read the matching upstream lemmas. No Mathlib theorem
states this canonical scheme comparison directly. The existing monoidal-model
module allows a different underived functor and counit; it does not directly pin
the counit used here, so the canonical comparison family is the shorter route.
Read Stacks Tags 079U and 06YH online because the literature text is not installed
in this clone. The unit record has no realized nodes bypassed by this proof.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_schemeHomTensorPullbackIso`
(blueprint `lem-pc-global-hom-adjunction`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
This proof uses existing stated dependencies, including
`exists_canonicalPullbackTensorComparison`; it does not claim that the entire
import closure is axiom-free. Both new private helpers are fully proved.

## No longer needed

None. No existing imports were removed. The existing global Hom, coherator,
Leray, adjunction and canonical tensor-Hom dependencies are all still used.
No additional dependency on `Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel`
is needed; it was investigated but never imported.

## Where the brief, the DAG or earlier work was wrong

The current module already proves every other theorem, so only the canonical
pullback tensor isomorphism was open. The previous first DAG step described this
as a remaining hole; it now records its complete proof. No mathematical statement
or definition was changed. The unchanged module timed out at 60 seconds with its
original global unfolding options; scoped proof elaboration settings resolved
this without modifying dependencies or bypassing the compiler limit.

Edge cases: the argument needs no flatness of f, qcqs, nonemptiness, or boundedness.
It applies to identity maps, empty schemes and zero complexes. Pullback K-flatness
uses the existing theorem for arbitrary ringed-space morphisms, and resolutions
are unbounded. All selected data in the public constructions keep their existing
characterising equations; no arbitrary existence witness was introduced as data.

The static checker requests a record for scoped helper commands; see
`coord/changes/global-hom-tensor-proof-elaboration.md`. This continuation rechecked both private helpers against the upstream K-flat
acyclicity and derived-monoidal counit lemmas, and checked the canonical
representative equation and all new dependency signatures. The module compiled
cleanly in 51.5 seconds. The delivery dry run printed OK: compilation and the
axiom probe passed, and the tool now explicitly permits the second-reading section
to be supplied later by the independent second reader. Nothing was pushed.
The reserved second-reading section has not been written.

## Second reading by V2

1. **Existing interfaces: pass.** Read the complete delivered module and its diff
   against the repository. Every existing declaration signature and definition
   body is unchanged. The declaration-table comparison reports no changed
   statements. The only additional declarations are the two proved private
   helpers. The scoped transparency options affect elaboration only; the scoped
   linter option preserves the original unused ModuleCat instance binder. Read
   `coord/changes/global-hom-tensor-proof-elaboration.md`; it accurately records
   these commands and the absence of downstream interface changes.

2. **Proof and trust: pass.** Independently compiled the delivered file using
   `lcompile.py`: no errors or warnings, 50.1 seconds. Scanned its Lean source:
   no `sorry`, custom axiom, unsafe/opaque declaration, implementation override,
   external implementation or kernel-check bypass. Compiled a scratch copy with
   explicit `#print axioms` commands (48.8 seconds). The tensor-model helper uses
   only `propext`, `Classical.choice`, `Quot.sound`; the pullback-counit helper,
   newly proved existence theorem and final global Hom theorem additionally use
   `sorryAx` through existing imported statements. This is one local hole closed,
   zero holes added, not an assertion that the target import closure is proved.
   The new proof only eliminates existence witnesses inside a theorem; it adds
   no data definition or arbitrary chosen object.

3. **Split statements and mathematical checks: pass.** No statements were split
   off and no new holes or nodes were added. Read the K-flat resolution, tensor
   closure and pullback preservation statements, the canonical comparison's exact
   representative equation, the defining derived-pullback theorem and the shared
   counit. Checked both private arguments: symmetry supplies the second-sided
   categorical K-flat criterion, and uniqueness of the universal left-derived
   lift transports counit invertibility to the fixed counit. The representative
   equation then permits cancellation of invertible factors. The two resolution
   augmentations localize to the correctly directed isomorphisms used by
   `NatTrans.isIso_app_iff_of_iso`. No step assumes flatness of f, boundedness or a
   point of either scheme, so zero complexes, identities and empty schemes are
   included without exceptional cases.

4. **Shortest route and pruning: pass.** Repeated leanfinder, loogle and grep
   searches with localization/counit queries and searched the local Lean sources.
   Read the upstream categorical K-flat acyclicity and derived-monoidal counit
   lemmas actually used. Investigated
   `kFlat_derivedTensor_comparison_natIso`: its public statement supplies only
   `Nonempty` of an isomorphism and does not identify its hom with the fixed
   localization tensor map, so it cannot replace the first helper. The generic
   bifunctor descent theorem requires more data than transporting the already
   natural comparison along representative isomorphisms. The present proof is a
   direct reduction through existing dependencies, with no restatement hole.
   Each added import is proof-only and used; each existing public import supplies
   declarations used by public statements or definition bodies. All old proof
   dependencies remain used, so `## No longer needed` is complete. The unit
   `sk-thm-picard-duality` has empty realized statement/step lists; none is bypassed.

5. **DAG agreement: pass.** Compared the node diff: only `proof`, `proof_deps`
   and `proof_origin` change. Checked each dependency's Lean record and checked
   mechanically that `proof_deps` equals the union of the proof steps' `uses`.
   The new first step matches the two private helpers, K-flat component argument,
   resolution transport and `NatIso.ofComponents`; the remaining steps match the
   unchanged evaluation-mate, coherator and Leray arguments. The node's statement,
   Lean declaration records, chapter and unit remain unchanged.

Second-reading changes: appended this independent review and search evidence;
no Lean proof or DAG repair was necessary. Closed:
`AlgebraicGeometry.exists_schemeHomTensorPullbackIso` (1 of 1 original holes).
Added holes: none. Split off: none. Pruned: none.
