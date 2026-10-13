## What changed

Replaced the sole hole in `Module.flat_of_local_criterion_baseChange` by a compiling
reduction to two new algebra statements and the existing, proved local criterion
`Module.Flat.of_flat_quotient_of_lTensor_injective`.

The proof transports quotient flatness through the quotient-tensor equivalence,
extending scalars through the surjective quotient map. It kills the span of the
images of the original multiplication kernel using `hker`, obtains injectivity by
tensor symmetry, checks the multiplication/subtype-tensor identity on pure tensors,
and proves Jacobson containment using properness and the two local maps. Finiteness
of `S' ⊗[S] M` is Mathlib's base-change instance. All original signatures and
visibility are unchanged.

Added `Sheaf.RingTheory.LocalizedBaseChangeQuotientFlat` and
`Sheaf.RingTheory.LocalizedBaseChangeIdealKernelSpan`; each has one public theorem,
a complete proof in words, and a matching node. Both apply to arbitrary commutative
rings and arbitrary modules, without Noetherianity, locality, finiteness or a proper
ideal. The kernel statement gives generators, without assuming `hker` or flatness
of the resulting module; the quotient statement does not involve theta or kernels.
These are separate parts of the source argument, not restatements of the target.

Checked Stacks Tags 00MO, 00MM, and 00MN on their official web pages because the
literature TeX file is absent in this read-only checkout. The route remains within
`sk-thm-p1` and changes none of its realized statements or proof steps. Compiled the
whole sandbox in import order with `lcompile.py` and compiled the final module
again after correcting the tensor-map composition proof.

## Proved and sorry left

Closed: `Module.flat_of_local_criterion_baseChange`
(node `lem-weil-pbc-flat-another-variant-local-criterion`). It has no local sorry.
This is a decomposition, not an unconditional proof or a net reduction of holes.

Added and still sorry:
- `Module.flat_quotient_localized_baseChange`
  (`lem-weil-pbc-localized-base-change-quotient-flat`).
- `Module.mem_span_ideal_kernel_localized_baseChange`
  (`lem-weil-pbc-localized-base-change-ideal-kernel-span`).

One upper hole closed, two strictly smaller holes added. No other declaration,
definition, statement, axiom, or existing module changed.

## No longer needed

Removed direct proof imports from the original module:
- `Sheaf.Algebra.TorOneSurjectiveChangeRings`.
- `Sheaf.RingTheory.TorIdealKernelNaturality`.
- `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle`.

They are not globally obsolete: their nodes remain needed inside the new
kernel-generation argument. The new kernel node retains the canonical-map
naturality and both Tor surjections in its proof dependencies. The original
module's proof dependencies are now the two new statements, quotient-tensor
conversion, and the existing local criterion. All the former tensor cancellation,
quotient base change, module base change, Tor, localization exactness and localization
tensor dependencies are retained below the two new nodes. No mathematical node or
module in that route can be declared globally pruned from this delivery.

Added only ordinary proof imports to the original module for the two new modules,
Mathlib tensor finiteness and local-ring homomorphism lemmas. Kept the original
public imports needed by its statement. No unit-level node is bypassed.

Every former direct proof dependency absent from the new parent proof is:
- `lem-weil-pbc-module-tensor-cancel-base-change`.
- `lem-weil-pbc-tensor-quotient-base-change`.
- `lem-weil-pbc-flat-module-base-change`.
- `lem-weil-pbc-tor-one-surjective-flat-middle`.
- `lem-weil-pbc-tor-one-surjective-change-rings`.
- `lem-weil-pbc-tor-ideal-kernel-naturality`.
- `def-weil-pbc-tor-modules`.
- `lem-weil-pbc-localization-module-exact`.
- `lem-weil-pbc-localization-tensor-over-base`.
- `def-weil-pbc-flat-ring-map`.

The tensor, base-change, Tor and localization nodes above remain in the new
statements' planned subproofs; `def-weil-pbc-flat-ring-map` supplies the flatness
notion in their statements. This list records direct dependency removal, not a
claim that the corresponding mathematics is globally obsolete.

## Where the brief, the DAG or earlier work was wrong

`CategoryTheory.torOne_surjective_flat_middle` currently concludes existence of
an epimorphism without a characterization identifying it as the canonical
base-change map. The source uses the canonical map, whose generator formula is
needed to compose with the naturality theorem. Existence of an arbitrary epi
cannot establish that formula. In addition, the three Tor interfaces use a single
universe, while the target has five independent universe parameters. None is a
reason to reject the mathematical result: the new kernel-span node states precisely
the needed canonical generator consequence, with a full source-based proof to
formalize next. No existing signature was changed to address those interface gaps.

Edge cases of both new statements: I=0 gives zero ideal tensors; I=R gives zero
quotients and an isomorphic multiplication map, hence a zero kernel. A zero module
or localization at a multiplicative set containing zero has zero output modules.
An identity square with W={1} makes the kernel-span assertion the tautological
containment of the original kernel in its own span and leaves quotient flatness
unchanged. Thus the new statements do not accidentally require nontrivial rings,
proper ideals or finite modules.

Mathlib searches are logged in `searches.jsonl`: LeanFinder, Loogle and grep for
the overall criterion; LeanSearch, Loogle and grep for each new statement.
LeanSearch returned HTTP Internal Server Error, recorded as unavailable.
Loogle found localization flatness and a compatible-scalar tensor kernel lemma,
but no exact match for either new statement. Library searches found the proved
local criterion and relative-purity lemmas in `Filtration`, and localization
injectivity lemmas in the source library; none directly supplies the two missing
localized-base-change interfaces. Blueprint searches for local criterion and
kernel gave no duplicate of the new statements.

## New nodes

`lem-weil-pbc-localized-base-change-quotient-flat` in
`dag/nodes/sec-proper-base-change/` isolates flatness of the quotient under tensor
base change and localization (00MO, first proof paragraph). Its module is
`Sheaf.RingTheory.LocalizedBaseChangeQuotientFlat`; its dependencies retain the
original tensor, quotient and localization route.

`lem-weil-pbc-localized-base-change-ideal-kernel-span` in the same chapter isolates
generation of the localized multiplication kernel by the image of the old kernel
(00MO, second and third proof paragraphs, 00MM/00MN and naturality of 00M6).
Its module is `Sheaf.RingTheory.LocalizedBaseChangeIdealKernelSpan`. It does not
assume that those generators vanish; the target proof establishes that separately.

Updated the parent node's `proof`, `proof_deps` and `proof_origin` to follow the
Lean reduction. No change records or forced adaptations are needed.

## Second reading by Q1

1. Interface: PASS. Compared the delivered target module with the repository by
   `diff` and checked its theorem signature byte for byte with a script. Only
   ordinary proof imports and the proof body differ; the docstring, universes,
   hypotheses, conclusion, public imports and visibility are unchanged. The other
   two modules are new. There are no definitions or change records.
2. Kernel-checked reduction: PASS, conditional on the two reported split statements.
   Compiled all three modules in import order with `lcompile.py`, without errors or
   warnings. Independently printed axioms for all three declarations in a scratch
   copy: exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   A source scan found exactly the two reported theorem holes and no prohibited
   declarations or hollow definitions. The target proof correctly transports the
   quotient action, kills the S'-span using hker, transfers injectivity by tensor
   symmetry, and establishes Jacobson containment before applying the proved
   finite-module local criterion. This is a decomposition: one hole closed, two
   added, not an unconditional proof or positive net hole reduction.
3. Split statements: PASS. Read both signatures and their complete docstring
   arguments. Verified the canonical surjections against Stacks Tags 00MM and
   00MN and the whole route against [Tag 00MO](https://stacks.math.columbia.edu/tag/00MO).
   The kernel statement does not assume vanishing of theta or the target's
   flatness; quotient flatness is independent of theta. Both are strictly separate
   parts of the argument. Checked I=0, I=R, M=0, the identity square with W={1},
   and localization at a set containing zero. In the identity case the kernel
   statement reduces to containment of the kernel in its own span; the extreme
   ideals have zero multiplication kernels. Searched each statement with new
   LeanFinder wording, Loogle for tensor kernels, launcher grep, and rg in the
   library. Read the returned `ker_mapOfCompatibleSMul` and the existing local
   criterion. Flat-kernel equivalences require additional flatness hypotheses and
   are not replacements for the kernel statement; localization flatness lemmas
   still require the quotient/localization identifications. No duplicate or short
   complete proof was found. The canonical-map gap in the existing Tor interface
   is real; no arbitrary epi or arbitrary witness is used in the delivered proof.
4. Route and pruning: PASS. The target first uses Mathlib equivalences and the
   already proved local criterion; only quotient flatness and kernel generation
   remain open. Added imports are ordinary proof imports and each supplies a
   declaration or instance used by the proof. The new modules' public imports
   supply the flatness, quotient, ideal-map, tensor-algebra and localization notions
   in their signatures. Compared old and new parent proof_deps and expanded
   `## No longer needed` to enumerate every removed direct dependency. Inspected
   `dag/units/sk-thm-p1.json` realized: neither a realized statement nor a realized
   proof step is bypassed by this below-unit algebra decomposition.
5. DAG: PASS. Checked the parent proof against the actual quotient, kernel and
   local-criterion steps. Checked both new nodes' Lean signatures against their
   files verbatim and checked proof_deps equals the union of proof-step uses for
   all three delivered nodes. New nodes have source, self-contained statement,
   docstring proof, search records, split status, created record, blueprint,
   chapter, unit and Lean records. Their dependencies describe the remaining
   source-based proof plans, including the reported canonical Tor-interface gap.

Second reading changed only this report: made the direct dependency-removal list
complete and recorded independent compilation, axiom, source, edge-case, search,
interface, route and node checks. No Lean repair was necessary; the two smaller
statements remain explicitly open.
