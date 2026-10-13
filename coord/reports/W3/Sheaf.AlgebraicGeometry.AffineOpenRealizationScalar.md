## What changed

Replaced the sorry in `affine_open_realization_scalar` by a complete Lean reduction to
`affine_perfect_sheafification_scalar`, an underived identity for one module in a new module.
The proof-only import of AffineSheafificationScalar is new. Existing signatures and public
imports are unchanged. Private proved helpers establish scalar centrality, conjugation, and
compatibility of derived over-site restriction. No definitions or other modules were adapted.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.affine_open_realization_scalar`
(node lem-sc-affine-open-realization-scalar). No sorry remains in the item module.
Added: `AlgebraicGeometry.Scheme.affine_perfect_sheafification_scalar`
(node lem-sc-affine-sheafification-scalar), in AffineSheafificationScalar.
This is a decomposition: one upper hole closed and one strictly smaller underived hole added,
net zero holes. The derived/comparison/restriction glue is proved, not postponed.
The new statement was checked on zero scalars, zero modules, and the empty affine open;
its sectionwise equation is valid in each case without nonemptiness or finite-generation assumptions.

## No longer needed

None. There were no proof-dependency imports or nodes to prune. The existing public imports
are retained for the original interface. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node gave a prose scalar-linearity argument with no proof dependencies. Its
underived affine transport identity was not available as a Lean declaration. That strictly
smaller part is now explicitly stated; all subsequent steps are implemented in Lean.
The local literature files were absent, so the cited Stacks Tags 06Z0, 08EJ, and the underived
construction in Tag 01I6 were read on the official Stacks website. Tag 01I6 explicitly records
linearity of the associated-sheaf functor in its discussion of internal Hom.

## New nodes

`lem-sc-affine-sheafification-scalar`: single-module scalar compatibility of the actual
composite tilde/restriction/inverse-over-equivalence functor. It does not mention a derived
category, F, K, E, or an arbitrary comparison isomorphism. Its docstring gives the local-fraction
calculation and the two scalar transports. Blueprint searches for affine scalar and associated
sheaf found no duplicate. Mathlib searches found sectionwise tilde scalar lemmas only.
No change record is required: no existing signature, definition, or public import changed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered affine realization module with the repository version. The
   theorem signature is byte-for-byte unchanged; only a proof-only import, private
   helpers, and the proof body were added. The new affine sheafification module and
   node are declared explicitly in this report.

2. Compiled `AffineSheafificationScalar.lean` successfully with `lcompile.py`; the
   affine realization file has an existing successful local build artifact and was
   rechecked with `lcompile.py`. There are no forbidden declarations and the only
   remaining `sorry` is the named split-off theorem
   `affine_perfect_sheafification_scalar`, whose node and proof docstring are present.

3. Read the split-off statement and its edge-case discussion. It is a single-module,
   underived scalar compatibility identity, strictly smaller than the target and
   exactly the identity used termwise by the target proof. It adds no hypotheses or
   weakened conclusion to the target, and searches found no existing duplicate.

4. Checked the proof route and imports. The target uses the split-off theorem,
   restriction scalar transport, comparison naturality, and scalar centrality; the
   proof-only import is therefore needed. No prior proof dependency or DAG node is
   unused, and the unit route remains represented by the target node.

5. Compared both DAG nodes with the Lean declarations. The target node records the
   new proof dependency and the split node records its exact declaration, source,
   docstring-level argument, and creation metadata. Verdict: the statements and
   dependencies agree.

Changed during second reading: no Lean proof or statement changes were necessary;
added this review section and retained the worker's proof and split-off node.

## Second reading by W3

1. Compared both delivered modules with the read-only repository. The existing
   `affine_open_realization_scalar` signature is byte-for-byte identical (checked by
   extracting the text from `theorem` to `:=`). Its docstring and three public imports
   are unchanged. Only its proof, three private proved helpers, and a plain proof-only
   import were added. AffineSheafificationScalar is the declared new module; there are
   no adaptations, changed definitions, or changed existing statements.

2. Independently compiled the two-file set with `lcompile.py --all`: both passed with
   no warnings (reported times 36.9 s and 28.4 s, including slot waits). Scanned the
   sources: exactly one `sorry`, the named split theorem, and no forbidden declarations
   or hollow definitions. Both public theorems were independently checked with scratch copies and
   `#print axioms`: exactly
   propext, Classical.choice, Quot.sound, and sorryAx. The scalar/conjugation
   helpers are proved by `simp`.
   The restriction proof uses the compatibility equation of the actual global section
   family on each object over U, then naturality of mapDerivedCategoryFactors and
   essential surjectivity of Q. It does not assume linearity of an arbitrary F.

3. Read the split statement against the actual construction in AffinePerfectModuleModel:
   tilde, restriction along hU.isoSpec.hom, then the inverse over equivalence. The module
   and scalar have exactly the coordinate ring X.presheaf(U); the right-hand action is
   the explicit HomModule action and overSections family. Read Stacks Tags
   [01I6](https://stacks.math.columbia.edu/tag/01I6),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
   [08EJ](https://stacks.math.columbia.edu/tag/08EJ).
   The first gives associated-sheaf linearity; 06Z0 supplies termwise tilde in the
   derived comparison; 08EJ is the parent power-annihilation application, not an extra
   hypothesis required here. On basic opens the localized map m/s ↦ rm/s is scalar
   multiplication, and the sheaf condition extends equality to arbitrary opens.
   Transport through the canonical affine isomorphism and over-site ring identification
   gives exactly overSections U r. For r=0 both maps vanish; for a zero module both
   maps are the unique map; for empty U the coordinate ring is zero and every module
   is zero. No finite presentation or nonemptiness is needed. This underived identity
   contains none of F, K, E, e, derived restriction, or derived comparison, so it is
   strictly smaller than the item. Independent LeanFinder search for tilde/scalar/
   restriction, Loogle for Functor.map_smul, source grep for tilde.map/overSections,
   and project/upstream/DAG searches for associated-sheaf linearity found component
   APIs but no theorem for this composite functor. The existing source tilde.map and
   restriction definitions explain why closing this transport calculation is further
   work rather than a direct application of Functor.map_smul.

4. Read the main proof top down: the split identity is applied to K.X n; naturality
   of the supplied comparison c and linearity of Q yield hFscalar; hR is the proved
   restriction identity; scalar centrality with e.hom completes the equality.
   Every new proof ingredient is used. The new module's public imports provide the
   functor and the scalar action appearing in its signature. The item's new import
   is correctly private to proofs. Old proof_deps was empty, so nothing is omitted
   from No longer needed. The unit sk-thm-picard-duality has empty realized statement
   and step lists in the repository; this delivery does not change them or replace
   a unit route. It preserves the original target node and its blueprint ancestry.

5. Compared both JSON nodes and their Lean declarations. The old node's statement,
   statement dependencies, and Lean signature are unchanged. Its three proof steps
   match restriction_scalar, termwise split/comparison naturality, and centrality;
   proof_deps is precisely the new scalar node. The split node's statement matches
   the new theorem, and its source, word proof, creation metadata, blueprint ancestry,
   chapter, unit, and Lean record are present. No existing proof dependency was dropped.

Changed during this second reading: added this independent review and fresh compilation
and axiom evidence. No Lean or node repair was necessary. The earlier saved dry-run and
push logs recorded timeouts; the fresh successful compile supersedes those attempts.
The delivery remains a decomposition: one upper hole closed and one underived hole added,
with net zero holes and no claimed pruning.
