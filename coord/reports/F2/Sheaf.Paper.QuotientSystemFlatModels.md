## What changed

Moved the unchanged projection, constant-system and ordinary reduction constructions to
Sheaf.Paper.QuotientReductionCore, publicly re-exported by the original module. This
permits acyclic proof imports; it is not a workaround for a compilation time limit.
Constructed normalized ScalarData from the existing SystemScalarModel. Proved constant
K-flatness by the geometric projection and identity scalar unitor. Assembled the original
flat-model theorem from this and the existing scalar, evaluation and fixed-factor tensor
results. Proved the recorded tensor-evaluation chain map invertible by coproduct inverses.
The reduction transition follows from naturality of the actual scalar-adjunction unit.
The unresolved ordinary scalar/slice comparison is isolated in QuotientOrdinaryModels.

Validation: the final main module compiled without warnings in 42.0 seconds, with
strict transparency respected and all profiling options removed. The core, constant
K-flatness and ordinary comparison modules compiled separately (8.6, 9.7 and 4.2 seconds).
The proof uses the existing generic fixed-factor cone lemma directly and explicit
functor identity equations. Ordinary wrappers have local implicit-reducibility
annotations; larger category structures stay opaque to elaboration.
The unchanged external consumer Sheaf.Paper.MixedReductionUnitComposition
compiled against the re-exported interface in 20.4 seconds, with no adaptation. Its
temporary validation copy was removed from the packet.

Change record: coord/changes/quotient-reduction-core-module.md. No existing signatures,
definition bodies, target statements, or mathematical hypotheses change.

## Proved and sorry left

Original hole closed: WeilConjectures.SemilinearSections.quotientSystemFlatModels
(lem-pur-quotient-system-flat-models). This is a decomposition, not a net hole reduction.

New hole: WeilConjectures.SemilinearSections.quotientOrdinaryModels
(lem-pur-quotient-ordinary-models). It only asserts the underived slice isomorphism and
its generator normalization for already supplied scalar models; it makes no K-flat,
flat-term, quasi-isomorphism, tensor, inverse-image or derived counit assertion.
The proof combining it with the existing theorems is complete.

New proved theorem: WeilConjectures.SemilinearSections.quotientConstant_preservesGood
(lem-pur-quotient-constant-kflat). The main module has zero holes; the delivery has
one named theorem hole, closed 1 and added 1. No data definitions contain sorry.

## No longer needed

The main proof does not need lem-pur-kflat-total-tensor-model or its module
Sheaf.Algebra.Homology.KFlatTotalTensorModel: tensor quasi-isomorphism preservation
follows directly from the two K-flat fixed-factor clauses of the existing signed
cone theorem. It also does not need the separate homotopy-category derived-pullback
existence theorem lem-weil-pbc-ringed-topoi-derived-pullback or its module
Sheaf.Paper.RingedTopoiDerivedPullbackIndependent: the already normalized ScalarData
model provides exactly its cochain counit and invariance clauses. The original module
had no direct imports of these modules, so none is removed. The ringed sequence-site
identification remains used through the existing evaluation theorem. No unit is pruned. These two obsolete entries are also removed from the top-level
tool_uses list. No Lean module is withdrawn.

The original proof-only import of SemilinearDerivedCalculus now belongs to the core,
where its module-pushforward exactness result is used. The new lower lemmas are
proof-only imports of the main module; the core is public because its definitions
occur in the unchanged public statements.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG described a second derived-pullback construction
although the existing ScalarData already exposes the required normalized comparison.
The unit record has no realized statement or proof-step nodes for this refinement;
the original geometric projection and componentwise proof route are retained.

Edge cases of the new slice assertion: zero modules, the identity coefficient map,
constant towers, nonflat/nonsurjective coefficient transitions, and an empty site all
use the same vertical sheafification identity, with no cancellation or flatness premise.
The constant K-flat theorem has no varying tower and uses the identity structural map.
The ordinary comparison is determined by the normalization: local pure tensors
generate, and linearity determines its value on b tensor x from its value on 1 tensor x.

## New nodes

- def-pur-quotient-reduction-core owns the unchanged quotient ring map, reduction
  and tensor constructions now located in the core module.
- lem-pur-quotient-constant-kflat is the proved specialization of ringed-topos
  K-flat pullback to the constant-sequence projection.
- lem-pur-quotient-ordinary-models isolates the strictly ordinary vertical slice
  comparison and generator normalization. Its docstring gives the complete argument
  via balanced presheaf tensors and commuting vertical sheafification.

The existing def-pur-quotient-constant-system attachment follows its unchanged
constructions to the core module. Searches used LeanSearch, Lean Finder, Loogle,
Mathlib/project grep, and blueprint_refs; results are recorded in the new nodes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
