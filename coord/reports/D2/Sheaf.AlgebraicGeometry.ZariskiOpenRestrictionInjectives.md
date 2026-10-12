## What changed

Replaced all three original sorries in
`Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives` by complete Lean proofs,
without changing any declaration signature or public import. Additivity is a componentwise
reflexivity proof. Exactness uses the definitional identification of open restriction with
localized-site restriction followed by `U.sheafEquivOver.functor`; the source library already
proves preservation of finite limits and finite colimits for the former. Injectivity follows
from clause (2) of `zariski_extensionByZero_exact`, the Mathlib localized-site adjunction,
and preservation of injectives by equivalences. The resolution is constructed explicitly
using `singleMapHomologicalComplex` and preservation of quasi-isomorphisms. The equality
of section complexes follows by applying congrArg to the equality between the image of the
terminal open and U.

Added proof-only imports `Mathlib.Topology.Sheaves.Over`,
`Mathlib.CategoryTheory.Preadditive.Injective.Preserves`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.
Updated the item's DAG proof, proof_deps and proof_origin to describe this route.
The unit `sk-thm-p1` realized statements and proof steps are unaffected.

## Proved and sorry left

Proved:
- `AlgebraicGeometry.zariski_open_restriction_additive`;
- `AlgebraicGeometry.zariski_open_restriction_injectives`;
- `AlgebraicGeometry.zariski_open_restriction_injectiveResolution`.

No sorry remains in the delivered module, and no new sorry is introduced.
All three proofs compile cleanly with the required local compiler.
The additivity theorem has only propext, Classical.choice and Quot.sound as axioms.
The other two still transitively depend on sorryAx through the existing
`AlgebraicGeometry.zariski_extensionByZero_exact`
(and its signature's `AlgebraicGeometry.zariski_extensionByZero_additive`), node
`lem-weil-pbc-zariski-extension-by-zero-exact`. Those unchanged declarations are
existing proof dependencies to be proved in later items, as intended by stage 3.

## No longer needed

Removed redundant direct proof import `Mathlib.CategoryTheory.Abelian.Exact`; its declarations
are already available through the retained imports.
Removed direct proof import `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction`.
Its full presheaf/sheafification universal-property theorem is unused: Mathlib provides
the specific localized-site adjunction needed here. Removed direct proof import
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`, using instead
the Mathlib match of the same node, which needs only mono preservation.

Removed these direct DAG proof dependencies:
- `lem-weil-pbc-abelian-presheaves-evaluation-exact` (additivity is reflexivity);
- `lem-weil-pbc-sheafification-exact` (exactness comes from proved preservation instances);
- `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift` (use ShortComplex.Exact.map);
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective` (no local-lift argument needed);
- `lem-weil-pbc-zariski-extension-by-zero-adjunction` (Mathlib gives the needed adjunction);
- `lem-weil-pbc-site-sheaves-enough-injectives` (map the given resolution explicitly).

These removals concern this item's proof. They do not assert that the nodes have no
other users. In particular, the unchanged extension-by-zero exactness module still
privately imports the extension-by-zero adjunction module, so that module remains
transitively reachable until its own proof is worked on.

## Where the brief, the DAG or earlier work was wrong

The old search concluded that restriction exactness needed the sectionwise-kernel and
locally-surjective-epi route. The source library already has the requisite localized-site
limit/colimit preservation instances. Also, the planned adjunction theorem is stated for
TopCat.Sheaf.pullback and includes a large presheaf universal property, whereas the exactness
theorem is stated for the localized-site functor. Mathlib's
`sheafPullbackConstruction.sheafAdjunctionContinuous` directly matches the latter.
No statement was disputed or changed, and no unit route was bypassed.

## Second reading by D2

1. Compared the sole delivered Lean module with the repository version using diff and
   the delivery declaration parser. All three existing signatures and all public imports
   are byte-for-byte unchanged; no definition, new declaration, or change record is present.
   Verdict: pass.
2. Compiled the module cleanly with lcompile.py and compiled a scratch copy containing
   #print axioms for all three declarations. Additivity uses only propext, Classical.choice,
   and Quot.sound. Injectivity/exactness and the resolution theorem additionally use
   sorryAx through the unchanged extension-by-zero exactness/additivity dependency.
   No sorry or forbidden declaration is present in this delivery. Read the explicit
   resolution construction, including its inferred quasi-isomorphism field, and checked
   the augmentation and section-complex equalities. Verdict: pass with the existing open
   dependency explicitly recorded above.
3. No statement is split off, and no new node or sorry is introduced. Read the Mathlib
   adjunction, injective-preservation, and equivalence instances used in the proof.
   The arguments impose no nonemptiness or proper-open hypothesis, so empty and terminal
   opens are covered. Verdict: pass; no split-off statement requires repair.
4. Searched the library and Mathlib for restriction/injectivity and mapped injective
   resolutions, and ran an independent Lean Finder search for an exact functor mapping
   an injective resolution. No shorter matching theorem was found. Tested deletion of
   each added proof import: Over, Injective.Preserves, and ConstantSheafOver are necessary;
   Abelian.Exact is redundant and was removed. The six nodes in the old proof_deps absent
   from the new proof_deps are exactly those listed under No longer needed. Read
   dag/units/sk-thm-p1.json and its realized statement/steps: none of the pruned nodes
   realizes a unit step, and the route is preserved. Verdict: pass after import pruning.
5. Compared the node JSON against the repository: only proof, proof_deps, and proof_origin
   change. The new proof_deps is exactly the union of the steps' uses. Read the source
   finite-limit/colimit instances, the retained extension-by-zero statement, and the
   Mathlib match of lem-sp-right-adjoint-preserves-injectives; they agree with the Lean
   proof and the updated plan. No new nodes require field validation. Verdict: pass.

Second-reading change: removed only the redundant proof import
Mathlib.CategoryTheory.Abelian.Exact and updated this report; the proofs and DAG route
were retained unchanged.
