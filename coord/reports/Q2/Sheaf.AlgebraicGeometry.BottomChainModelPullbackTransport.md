## What changed

Proved `AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport` without changing
its signature or docstring. The pulled complexes and chain map are explicitly the termwise
images under `Scheme.Modules.localizedPullback`; no complexes are selected from existence
statements. Added a proved natural-comparison theorem in
`Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectCounit`, using the canonical derived counit.
The original module privately imports this comparison, the universe-aware restriction
comparison, and the source exact-functor/homology tools. Its original public imports stay.
Updated the original node's proof route and added the node for the proved comparison.

The main proof combines three squares in the derived category, reflects through the derived
open-site equivalence, and combines three more squares on homology. It proves zero terms,
zero differentials and preservation of the invertible bottom component directly. The new
comparison is proved using finite-free retract flatness, bounded-above K-flatness, and one
natural counit on all complexes. Empty opens and zero-rank terms require no exceptions.
The standard localized target derived category avoids an extra target hypothesis.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport`
(`lem-sc-bottom-chain-model-pullback-transport`).
Also fully proved `AlgebraicGeometry.localizedPullback_perfectCounit`
(`lem-pc-localized-pullback-perfect-counit`), with the proved private `flat_retract` helper.
The main module's private `compose_squares` is proved. No sorry remains in either delivered
module, and no holes are added or split off. Existing lower library dependencies are used
as supplied; this is one original hole closed, not a decomposition.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
and `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel` from the original module;
the latter remains available through the new comparison module. The direct planned use of
`AlgebraicGeometry.flatComplexDerivedPullback` / `lem-pc-flat-complex-derived-pullback`
is replaced by the canonical counit from `exists_derivedPullback` together with
`lem-pc-bounded-above-flat-kflat`. Its module still occurs transitively through the
public import of `LocalizedPullbackPerfectModel`, which supplies `localizedPullback`;
this delivery does not claim that module leaves the target import closure.
The object-only `localizedPullback_perfectModel_iso` theorem is not used; the
`LocalizedPullbackPerfectModel` module and its node remain needed for the explicit functor.
No other node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or interface change. The object-only local-model theorem does not
state the common natural comparison needed for the specified chain map. The new proved
comparison supplies this missing interface. The unit's route is unchanged.
LeanSearch returned Internal Server Error; this is recorded as unavailable. LeanFinder,
Loogle, source grep, existing-module reading, and blueprint search were performed.

## New nodes

`lem-pc-localized-pullback-perfect-counit` records the proved natural transformation on
all localized complexes, invertible on strictly perfect complexes. It isolates the
termwise counit computation, rather than restating the target's bottom conditions or
homology square. No new sorry or change record. The blueprint search for
“derived pullback counit” returned no matching blueprint node.


## Second reading by Q2

1. Compared both delivered modules with the repository. The comparison module is new;
   the existing module has exactly the same theorem signature and docstring. The declaration
   scanner reports no signature change. No definition or target interface is changed, and
   no change record or forced adaptation is required. Verdict: pass.
2. Compiled both modules in import order using lcompile.py: 33.3 seconds and 18.9 seconds,
   with no errors or warnings. Source scans find no sorry, axiom, unsafe, opaque,
   implemented_by or extern in either file. A scratch copy with #print axioms reports
   only propext, Classical.choice and Quot.sound for localizedPullback_perfectCounit;
   bottom_chain_model_pullback_transport additionally depends on sorryAx from the
   existing library. P, Q and beta are explicit functor images. The counit comes from
   the chosen derived functor's universal property, rather than an arbitrary existence
   witness used to define data. Verdict: pass relative to existing open dependencies.
3. No statements are split off with sorry. Read the new proved counit statement and its
   entire proof: it is a genuine natural comparison, independent of all the target's
   bottom-degree conditions. Checked the zero complex, empty open and rank-zero cases:
   coproduct flatness and retract flatness include the empty coproduct, mapped zero terms
   remain zero, and no inhabitance of an open is used in the comparison. The main target
   on an empty U has an impossible hy. Independent searches using “leftAdjointUniq”
   (Loogle), “left derived functor counit invertible K flat bounded above complex finite
   projective sheaves” (LeanFinder), “IsLeftDerivedFunctor|leftDerived_from_resolvingClass”
   (grep), and repository searches for localizedPullback and counit found the generic
   tools used here and the existing object-only perfectModel theorem, but no existing
   natural localized comparison replacing this theorem. Verdict: pass.
4. Read the target proof from its conclusion down through restriction, the supplied
   model square, and counit naturality. The reflection and homology squares preserve
   the specified alpha; zero terms, outgoing differentials and invertibility follow
   directly from the ordinary additive pullback. No shorter applicable library route
   was found. Public imports of the original module are unchanged; the new module's
   public model import supplies localizedPullback and the notions in its signature.
   Its remaining imports and the target's new imports are proof dependencies. Corrected
   the report's false claim that no direct import was removed. The sole old proof_dep
   removed is lem-pc-flat-complex-derived-pullback, already named above. Neither that
   module nor the model module is claimed removed from the target import closure.
   sk-prop-av-cube.json has empty realized entries in the repository; this delivery
   changes none of them and stays below its general-cube step. Verdict: pass.
5. Compared the old and delivered target node: only proof, proof_deps and proof_origin
   change. Their steps match the explicit construction and the two three-square
   compositions. Checked the new node's source, dependencies, searches, creation record,
   blueprint ancestry, chapter, unit and Lean record; its recorded Lean statement is
   verbatim the new theorem signature. Verdict: pass.

Second reading changed only the report: corrected the removed-import inventory and
recorded these checks. The Lean proofs and DAG records needed no repair.
