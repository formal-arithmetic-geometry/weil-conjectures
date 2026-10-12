## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.mono_of_mono_generic_stalk by a
complete Lean reduction, preserving its signature and existing docstring. The
proof applies Abelian.mono_of_kernel_ι_eq_zero, obtains a locally nonzero section
of the kernel inclusion, lifts its nonempty etale neighbourhood to the fixed
geometric generic point using Mathlib, and derives a contradiction by cancellation
of the monic generic stalk map and naturality of the germ maps.

Added Sheaf.AlgebraicGeometry.LocallyConstantNonzeroGerms, containing one public
intermediate theorem for the local section construction in the original first
proof step. This theorem concerns an arbitrary nonzero morphism on an arbitrary
scheme: it contains neither a generic point nor a monic generic stalk assumption.
It is a strict part of the original argument, not a renamed kernel-detection theorem.
Added its proof-only import and Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen.
Updated the original DAG proof to match the actual reduction.

Local compilation through lcompile.py succeeds without warnings. The two
hypotheses hX and hne are retained exactly: existence of the specified generic point
already gives the nonemptiness and irreducibility needed in this proof. The helper
uses only the locally constant underlying set sheaf, as required by the signature.

## Proved and sorry left

AlgebraicGeometry.Scheme.mono_of_mono_generic_stalk
(node lem-weil-pbc-lisse-generic-kernel) has a complete proof, conditional on the
new intermediate theorem. There is no direct sorry left in the item's module.

The single sorry added by this delivery is
AlgebraicGeometry.Scheme.exists_section_everywhere_nonzero_germ
(node lem-weil-pbc-locally-constant-nonzero-germs), in its own module. Its docstring
and node give the complete local-constancy, stalk, and filtered-refinement argument.
Thus this is a reduction, not a claim that all transitive sorries have disappeared.

## No longer needed

Removed proof imports:
- Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk.
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint.

The main proof uses only Mathlib's etale geometric-point lifting, so it needs no
source-library universe-lifted stalk conservativity import directly. The new
local-section node still needs geometric stalk conservativity/joint faithfulness
and exactness, so those nodes are not globally pruned by this delivery.

Node lem-weil-pbc-constant-sheaf-geometric-stalk and module
Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk are no longer needed by this
route. The helper's trivialization is a set-sheaf trivialization, so its constant
stalk computation instead uses the existing Mathlib leaves
lem-weil-pbc-sets-sheafification-geometric-stalk and
lem-weil-pbc-colimit-constant-connected-diagram. All definition dependencies of the
original statement remain. No unit statement or realized proof step is bypassed:
sk-prop-sf-cbc has empty realized.statement and realized.steps lists.

## Where the brief, the DAG or earlier work was wrong

The existing docstring describes a constant set M but cites
constantSheaf_geometricStalk_isIso, whose signature is only for abelian constant
sheaves. That declaration cannot directly justify a constant set trivialization.
The new node records the set-valued sheafification and connected-colimit leaves
instead. The source library's proved Point.sheafFiberConstantSheafIso also provides
the general concrete-coefficient constant-stalk computation for future proof work.
The old docstring is retained; the updated DAG and this report describe the exact
route and the type mismatch in its old citation.

The searched clopen zero-locus theorem is for topological sheaves, not etale
sheaves, and therefore was not imported. Semantic searches found no existing
local nonzero-germ theorem. LeanSearch returned Internal Server Error; LeanFinder,
Loogle, and local source/DAG searches worked.

Edge cases checked for the helper: on an empty scheme or with N or F zero there
is no nonzero ψ, so its premise is impossible. On a disconnected scheme the
neighbourhood can lie in just one nonzero component; no global nonvanishing is
claimed. No finiteness, noetherianity, connectedness, or additive trivialization is
assumed. The two distinct constant set values represent image and zero separately.

## New nodes

lem-weil-pbc-locally-constant-nonzero-germs: the first proof step split into a
standalone public theorem in
lean/Sheaf/AlgebraicGeometry/LocallyConstantNonzeroGerms.lean. Its source is the
original blueprint proof step, and its proof handles all geometric fields in the
scheme universe and all lifts to the selected nonempty neighbourhood. No existing
statement or definition was changed, and no change record is needed.

## Second reading by W2

1. Compared the delivered `LisseGenericKernel` module with the repository version. The theorem
   signature is byte-for-byte unchanged; only proof text and proof-only imports changed. The new
   helper is a separate theorem with its own node and does not alter an existing declaration.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or
   warnings. The main theorem has no `sorry`; the helper's sole `sorry` is named and documented,
   with a matching split node. No forbidden declarations or hollow definitions occur. Verdict:
   pass.
3. The helper statement is a strict local-section reduction of the original first proof step,
   with arbitrary source sheaf and no generic-point assumptions. Its edge cases and disconnected
   schemes are addressed in the report, and searches found no existing equivalent declaration.
   Verdict: pass.
4. The proof follows the unit route: kernel reduction, open etale image, lift over the generic
   point, and cancellation at the generic stalk. The route's realized unit statements are kept.
   The proof-only constant-stalk imports were pruned; the direct Mathlib universally-open route
   also makes the old flat-lfp node unnecessary.
5. Updated the main node's `proof_deps` to remove the unused `lem-weil-pbc-flat-lfp-open`, so its
   DAG dependencies now match the proof and imports. The helper node, proof origin, and report
   agree with its Lean declaration.

Changed in this second reading: removed the stale flat-lfp proof dependency from the main node and
recorded this review.
