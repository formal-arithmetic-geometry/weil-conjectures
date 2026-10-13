## What changed

The existing public signature of
`CochainComplex.quasiIso_tensor_of_termwise_tor_acyclic` is unchanged. Its proof is now
an induction on the natural width of a support interval. The private induction lemma
universally quantifies over the complex, lower endpoint and K-flat resolution. It constructs
the stupid tail, proves its smaller support bound, transports Tor vanishing through term
isomorphisms, handles zero tail terms using Mathlib's positive Tor vanishing for projectives,
and combines the tail comparison with the singleton comparison. The final homology-map
isomorphisms follow by typeclass inference from QuasiIso.

Two new modules state strictly separate parts of the original plan: the one-degree base
calculation and the single truncation gluing step. Each has a named public theorem with a
source, a complete proof in words, and a new DAG node. Neither states the bounded-complex
result under a different name: the base theorem requires support in a single degree; the
gluing theorem assumes the singleton and tail comparisons, has no Tor hypothesis or upper
bound, and does not carry out the finite induction. The finite induction is fully proved in
the assigned module.

All three sandbox modules compile together with lcompile.py without errors or warnings.
No existing statement, definition, universe or visibility was changed. No data is chosen
from an unproved existence theorem, and no private theorem contains sorry.

## Proved and sorry left

Closed the assigned module's sole hole:
`CochainComplex.quasiIso_tensor_of_termwise_tor_acyclic`
(node `lem-pc-termwise-tor-acyclic-derived-tensor`). The private lemma
`CochainComplex.quasiIso_tensor_of_tor_acyclic_interval` is also fully proved.

Added exactly two holes, each in its own new module:

- `CochainComplex.quasiIso_tensor_of_single_support_tor_acyclic`, node
  `lem-pc-single-support-tor-acyclic-tensor`, module
  `Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor`.
- `CochainComplex.quasiIso_tensor_of_stupid_tail`, node
  `lem-pc-tensor-comparison-stupid-tail`, module
  `Sheaf.Algebra.Homology.TensorComparisonStupidTail`.

This is a decomposition: one upper hole closed, two strictly smaller holes added. It is
not a sorry-free proof of the original mathematical result. The assigned module itself
contains zero sorries. The two new statements are exactly the base case and gluing step
needed by the real induction, so they can be proved independently.

Edge cases were checked mathematically: the one-degree lemma includes the zero complex,
zero coefficient algebra and arbitrary unbounded K-flat sources. Positive Tor vanishing
is only required for the actual singleton term. The gluing statement does not assume
that Q or its tail is K-flat, or that the truncation sequence splits as complexes; only
its degreewise split short exact sequence is used. When the input upper bound is less
than the lower bound, d=(b-a).toNat is zero and the support argument remains valid.
At d=0 the Lean proof establishes vanishing in every degree unequal to the lower bound.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Algebra.Homology.BoundedFlatKFlat`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`.
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`.

The assigned theorem now directly uses only the Tor definition and the two new nodes.
The old parent proof dependencies `lem-pc-module-bounded-flat-kflat`,
`lem-weil-pbc-complex-ses-triangle`,
`lem-weil-pbc-commshift-nattrans-triangle-morphism`,
`lem-weil-pbc-derived-cohomology-ladder` and `lem-weil-pbc-five-lemma` remain mathematical
ingredients of the deferred base/gluing nodes. They are moved below those nodes, not
claimed globally unnecessary.

`lem-pur-derived-change-of-rings` and its module
`Sheaf.Algebra.Homology.DerivedChangeOfRings` are unnecessary on this ordinary-module route.
The gluing node uses the generic resolving-class theorem
`lem-pur-left-derived-from-kflat-class`, with ordinary-module K-flat resolutions and
`lem-pc-mixed-tensor-kflat-quasi-iso`, rather than a sheaf theorem on a one-point site.
No unit statement or realized unit step is bypassed: sk-thm-picard-duality has empty
realized entries, and the assigned comparison remains on the original ancestor route.

## Where the brief, the DAG or earlier work was wrong

The DAG's finite truncation induction is mathematically valid, but its stated ingredients
do not directly express the one-term comparison for an arbitrary ordinary-module K-flat
resolution, or the comparison ladder for the stupid tail. In particular,
`SheafOfModules.derivedChangeOfRings` is about SheafOfModules on a ringed site, whereas the
assigned theorem is about ModuleCat R. Applying it on a one-point site would require an
additional equivalence and compatibility of tensor, homology and K-flatness. No such
bridge is silently assumed here. Its replacement is the generic resolving-class route
recorded in the new gluing node.

The existing source attribution also overstates Tag 08IB: its published proof contains
the affine Tor-independent one-term calculation, but not the finite stupid-truncation
induction written in the DAG. The new proof origins explicitly mark the detailed expansion
as agent-written, using the published Section 15.60 (Tag 06XY) for K-flat model independence,
derived tensor exactness and the degreewise split stupid-tail argument. The local
literature/stacks-project/perfect.tex is absent on this machine, so the official published
pages https://stacks.math.columbia.edu/tag/08IB and /tag/06XY were read; the new node source
records the available published URL.

Mathlib and both library roots were searched before splitting. LeanFinder found the Tor
projective vanishing and ordinary short-exact comparison lemmas, but no exact one-term
Tor-acyclic K-flat comparison or derived-comparison stupid-tail gluing theorem. LeanSearch
returned Internal Server Error on both searches; this is recorded as unavailable. Source
grep and whole-blueprint searches found no duplicate. In the implemented induction,
Mathlib does not supply a PreservesZeroMorphisms instance for Functor.leftDerived, so
vanishing on zero terms is proved through projectivity and isZero_Tor'_succ_of_projective
instead of assuming that unavailable instance.

## New nodes

`lem-pc-single-support-tor-acyclic-tensor` states the one-degree base case on arbitrary
K-flat resolutions. Its proof constructs a shifted projective resolution, computes tensor
homology as Tor, and transfers the augmentation calculation to the specified resolution
through K-flat model independence. It is in
lean/Sheaf/Algebra/Homology/SingleSupportTorAcyclicTensor.lean.

`lem-pc-tensor-comparison-stupid-tail` states only closure of the comparison under adjoining
one bottom term, with universally quantified outer-resolution comparisons as hypotheses.
Its proof forms the degreewise split truncation triangle, applies exact derived tensor,
and uses the cohomology ladder and five lemma. It is in
lean/Sheaf/Algebra/Homology/TensorComparisonStupidTail.lean.

Both node files inherit sec-picard-framework and sk-thm-picard-duality and trace their
blueprint ancestor to lem-sc-finite-duality through the original comparison route.
There are no change records or forced adaptations.

## Second reading by A3

1. Interface preservation: PASS. Read the full diff against the repository module.
   The existing public theorem signature, from its keyword to `:= by`, is byte for
   byte unchanged, checked independently by a string comparison. The only other
   existing-file edits are proof imports, the private proved induction helper,
   the proof description and the proof body. No definition, target, universe or
   visibility changed; no change record is required. Both additional modules are new.
2. Proof and axioms: PASS as a decomposition. All three files compile together
   with lcompile.py without errors or warnings. A scratch copy with `#print axioms`
   for the public parent, private interval helper and both new theorems reports
   exactly propext, Classical.choice, Quot.sound and sorryAx. The two new public
   theorems are the only direct sorry holes. No forbidden declaration or hollow
   definition occurs, and no data is chosen from an unproved existence theorem.
3. Split statements: PASS. Independently checked the zero complex, k arbitrary,
   zero coefficient ring, singleton support, empty interval b<a, and unbounded
   K-flat sources. The base statement is a one-degree calculation, while the
   gluing statement is closure under one degreewise split extension with outer
   comparisons as hypotheses; neither restates the finite bounded result.
   The split sequence is only degreewise split, as its differential need not split.
   Model independence is valid for arbitrary K-flat sources, without requiring
   their terms to be projective. Each new theorem has a complete mathematical
   proof docstring and matching node. Read the published Stacks Section 15.60
   (https://stacks.math.columbia.edu/tag/06XY), particularly Lemmas 15.60.7,
   15.60.9, 15.60.10 and 15.60.12 and the construction before Definition 15.60.13,
   and Tag 08IB. Independent LeanFinder search used “acyclic resolution computes
   left derived functor on a single object; tensor comparison stable under
   degreewise split extension of cochain complexes”; grep used
   `leftDerived.*(single|quasiIso)|quasiIso.*leftDerived|tensor.*(shortExact|ShortExact)`.
   Also searched both source roots for acyclic/tensor/resolution comparisons and
   read the bounded-flat, mixed-tensor invariance and fixed-second-factor derived
   tensor modules. These provide ingredients, not either entire new statement.
   Neither remaining hole has a short direct closure using those declarations.
4. Route and pruning: PASS. The real induction decreases the interval width,
   quantifies over all tail resolutions, transports Tor through term isomorphisms
   and uses projectivity for the zero terms. Each of the seven old direct
   proof dependencies is accounted for under No longer needed: Tor stays direct,
   five ingredients move below the new lemmas and the sheaf change-of-rings route
   is replaced by the ordinary-module resolving-class route. Removed imports
   were private proof imports; existing public imports supply the statement's
   structures and instances. The two new proof imports are private. The unit
   sk-thm-picard-duality has empty realized entries; its original ancestor route
   is preserved. This delivery closes one upper hole and adds two lower holes,
   a decomposition with raw hole difference -1, not a sorry-free proof.
5. DAG correspondence: PASS. Read all three delivered nodes. The parent's proof,
   proof_deps and agent proof_origin describe the implemented interval induction;
   each new node states exactly its Lean theorem, with complete source, searches,
   creation, blueprint, chapter, unit and lean records. The union of each node's
   step dependencies equals its proof_deps. No existing node statement changed.

Second-reading changes: appended this independent review and recorded fresh
searches; no Lean proof or node repair was necessary. The temporary axiom-check
copy was removed before delivery. Holes closed and added remain exactly those
listed in Proved and sorry left above.
