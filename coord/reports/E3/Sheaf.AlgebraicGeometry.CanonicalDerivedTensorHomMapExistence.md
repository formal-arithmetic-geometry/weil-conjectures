## What changed

The assigned theorem `AlgebraicGeometry.exists_canonicalDerivedTensorHomMap` now has
an unchanged statement and a complete Lean proof combining three separate steps.
The new Differential module explicitly constructs degreewise uncurrying using
`HomologicalComplex.mapBifunctorDesc`, builds a chain map from its named differential
compatibility theorem, and proves the exact component normalization using
`HomologicalComplex.ι_mapBifunctorDesc`. No data are selected from a mere unproved
existence theorem. The existential descended family is eliminated within a theorem.

The Descent module asserts localization of this explicit construction and compatibility
with isomorphisms. The DescentNaturality module proves arbitrary-morphism naturality
conditional on that localization equation and isomorphism compatibility. The assigned
proof obtains the family, applies the conditional naturality theorem, and supplies the
explicit chain map, its proved summand identity, and its localization equation.

All four modules compile through `lcompile.py --all`. The early missing shared artifact
was published during this attempt; subsequent compilation works. No shared dependencies
were built by this worker. No existing signature, definition or public import changed.

## Proved and sorry left

Closed the sole assigned hole, `AlgebraicGeometry.exists_canonicalDerivedTensorHomMap`
(node lem-pc-canonical-derived-tensor-hom-map-existence), by decomposition.
The new proved theorem `AlgebraicGeometry.schemeTensorHomUncurry_component` establishes
the normalization of the explicitly constructed map. Its data definitions contain no holes.

Three new holes remain, each the complete proof of a separate public theorem:

- `AlgebraicGeometry.schemeTensorHomUncurryGraded_comm`:
  lem-pc-tensor-hom-uncurry-differential, the signed differential equation only.
- `AlgebraicGeometry.exists_tensorHomUncurry_descent`:
  lem-pc-tensor-hom-uncurry-descent, localization and isomorphism transport only.
- `AlgebraicGeometry.tensorHomUncurry_descent_natural`:
  lem-pc-tensor-hom-uncurry-descent-naturality, arbitrary-morphism naturality conditional
  on a supplied family, its representative equation and isomorphism transport.

This closes one upper hole and adds three strictly partial lower holes; it is a
decomposition, not a claim of positive net hole reduction or an axiom-free final result.
Each new hole has its source, complete proof in words, and matching DAG node.

## No longer needed

Removed these proof-only imports from the assigned module:

- Sheaf.Algebra.Homology.KFlatResolution
- Sheaf.Algebra.Homology.KInjectiveHomComplex
- Mathlib.Algebra.Homology.DerivedCategory.KInjective
- Sheaf.Algebra.Homology.HomTensorDifferential
- Sheaf.Algebra.Homology.HomTensorNaturality
- Sheaf.Algebra.Homology.HomComplexGlobalCochains

The previous direct proof-dependency edges are replaced by the three new nodes.
The degreewise Hom-complex comparison nodes lem-sc-hom-tensor-degreewise,
lem-sc-hom-tensor-differential and lem-sc-hom-tensor-naturality are unnecessary for
this direct coproduct construction and its componentwise differential and naturality
arguments. The other previous dependencies remain tools for the new lower steps:
K-flat resolutions, K-injective Hom, derived Hom computation, the global cochain
comparison, and the sheaf tensor-Hom adjunction. No assertion is made that any of their
modules is globally unreachable: other target branches may still import them.

An unused HomComplexProjections import was removed from the preserved Differential
draft before promotion. Its projection formulas are already available through the model.

For completeness, every removed OLD DIRECT proof_deps edge of the assigned node is:
lem-pc-kflat-resolution; lem-pur-hom-kflat-into-kinjective;
lem-weil-pbc-kinjective-hom-derived; lem-pc-sheaf-modules-tensor-closed;
lem-sc-hom-tensor-degreewise; lem-sc-hom-tensor-differential;
lem-sc-hom-tensor-naturality; lem-pur-hom-complex-global-cochains.
The first, second, third, fourth and eighth remain dependencies of lower nodes;
only the three HomTensor comparison edges are unnecessary for this construction.
This lists removed direct edges, without claiming global module unreachability.


## Where the brief, the DAG or earlier work was wrong

The earlier attempts were blocked by a genuinely absent compiled model artifact. That
blocker resolved during this attempt without any worker build of shared dependencies.
The old scratchpad component proof omitted explicit bifunctor arguments and failed
elaboration; specifying K₁, K₂, F and c fixes it.

The old scratchpad naturality statement was insufficient for an arbitrary chosen derived
category: prescribing a family only on literal Q-images does not prescribe its values
on isomorphic objects outside that image. The new descent step additionally asserts
transport along isomorphisms and the naturality step explicitly assumes it. This is a
correction to an unlanded draft, not a change to an existing library statement.

Edge cases checked mathematically: zero complexes and zero maps, all integer degrees,
nonconsecutive differentials (both vanish), arbitrary unbounded complexes, arbitrary L
in the representative equation (resolve L; K-flat P and K-injective I invert its
quasi-isomorphism), and derived objects only isomorphic to complex representatives.
The construction and statements require no extra boundedness or pointwise flatness.
No unit statement or realized step is bypassed; the owning unit's realized lists are empty.

Searches were repeated through msearch LeanFinder, Loogle, grep and local rg.
LeanFinder found tensor maps and unrelated Tor results; Loogle found the coproduct
constructor and summand identity used here. LeanSearch returned Internal Server Error;
its unavailability is recorded without claiming a negative search result. The current
library's normalized degreewise Hom comparison does not directly give the required
chain-map component equation or the derived localization equation. Stacks Tags 08DJ,
0A90 and 0A96 were read online because the local source files are absent.

## New nodes

lem-pc-tensor-hom-uncurry-differential records the differential equation for the explicit
coproduct evaluation; the same module defines the resulting chain map and proves its
summand equation. It asserts no descent or derived naturality.

lem-pc-tensor-hom-uncurry-descent records functions on derived morphisms with the
localization equation and isomorphism transport. It asserts no naturality for arbitrary
morphisms and uses a chain map already constructed explicitly in the Differential module.

lem-pc-tensor-hom-uncurry-descent-naturality records arbitrary-morphism naturality as a
conditional theorem about a supplied family with the representative and isomorphism
transport equations. It asserts neither existence of a family nor component normalization.

No change record is needed: existing declarations and importer-visible interfaces stay
identical. These are three new modules and nodes for independent review.

The second reader also removed the redundant direct
CanonicalDerivedTensorHomModel import from the two new Descent modules; their
public Differential import supplies it. This removes no import from the existing
assigned module's public interface.

## Second reading by E3

1. Compared every delivery module with the read-only repository. Only the assigned
   module exists there: its declaration signature and docstring are byte-for-byte
   unchanged; its only edits are proof-only imports and the proof body. The three
   other modules and their declarations are new. The existing node changes only
   proof, proof_deps and proof_origin. No change record is required. Verdict: pass.
2. Compiled all four modules in dependency order with lcompile.py. The only three
   syntactic holes are exactly the public named theorems listed above; no data
   definition contains sorry and no forbidden declaration mechanism is used.
   The coproduct data are constructed, and the chain-map structure uses a named
   theorem solely for its propositional commutativity field. The descended family
   is eliminated inside the existence proof, never selected into a definition.
   Checked all seven declarations with #print axioms in a scratch module: only
   propext, Classical.choice, Quot.sound and the expected sorryAx occur. Verdict: pass
   as a decomposition, not a completed axiom-free proof.
3. Read the three new signatures, docstrings and nodes together. The differential
   equation uses the standard d_I phi - (-1)^p phi d_L sign and is valid for all
   integer degrees; nonconsecutive degrees vanish. Descent fixes the value on an
   explicit chain map, and asserts only isomorphism transport. Conditional naturality
   asserts no family existence. K-flat L representatives ensure Hom(L,I) is
   K-injective; arbitrary L in the normalization follows by its K-flat resolution.
   Isomorphism transport covers derived objects merely isomorphic to Q-images.
   Checked zero maps/complexes, negative degrees and unbounded complexes. These
   are strictly partial steps, rather than a renamed copy of the assigned theorem.
   Repeated searches with evaluation/differential terminology via LeanFinder,
   Loogle and grep, and read the upstream InternalHom construction. Its differential
   convention is (-1)^q times (d_I f - f d_L), unlike this Hom complex's
   d_I f - (-1)^p f d_L; its adjunction does not directly prove the normalization
   here without a comparison construction. The existing HomTensor differential
   compares iterated Hom complexes, not evaluation of an arbitrary chain map.
   No immediately reusable exact theorem or few-minute closure was found. Verdict: pass.
4. Followed the upper proof downward: descent, conditional naturality, explicit
   chain-map witness, coproduct summand equation, localization equation. Removed
   the redundant direct model public import in both new Descent modules, since
   their public Differential import already supplies the model and their signatures
   need Differential. All remaining public imports support signatures or definitions;
   the assigned module's added imports are proof-only. Read the unit record:
   sk-thm-picard-duality has empty realized statement and step lists; no recorded
   realized node is pruned or unit statement changed. Verdict: pass.
5. Checked each new node's fields, Lean declaration/statement, source, proof text,
   dependency union, origin and creation record. Checked the existing node's new
   proof against the actual three-stage application. Nodes agree with Lean and the
   existing statement metadata is preserved. Verdict: pass.

Second-reading changes: removed two redundant imports, clarified the complete
list of old direct dependency edges below, and added this independent review.
No proof or statement was rewritten.


Source spot checks: read [Stacks 08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[0A90](https://stacks.math.columbia.edu/tag/0A90), and
[0A96](https://stacks.math.columbia.edu/tag/0A96). They respectively give the
K-flat/K-injective derived comparison route, the functorial Hom-total-tensor
comparison, and K-injectivity of Hom from a K-flat source into a K-injective target.
The explicit component and transport calculations in the new docstrings expand
that route; they are not claimed to be verbatim proofs supplied by those sources.
