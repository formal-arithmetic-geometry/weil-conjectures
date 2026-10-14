## What changed

The delivered module retains all existing declarations, signatures, definitions, visibility,
and imports. Its only Lean difference from the repository is replacing `simpa using` with
`exact` in `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`: the witness already has
exactly the required conclusion. The second reader retained this correct simplification.

## Proved and sorry left

Both public declarations are proved:
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`.
The private helpers `epi_locally_surjective` and `exists_presheaf_cover_lift` are also proved.
No sorry remains in this module, and no split-off statement or module is added.

Holes newly closed against the current repository: none. Holes added: none.
Both public proofs were already present in the baseline; this is verification of a queued
repair, not new proof progress or a decomposition. Net hole reduction for this delivery is zero.

## No longer needed

None. No old proof dependency is dropped: the conclusion uses
`lem-sc-presheaf-free-ext-local-killing-witness`, which uses
`lem-sc-ext-epi-effacement`. No module is pruned.

`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` supplies the public Ext/free-abelian/sheaf
API and the abelian-sheaf instances used in the proof;
`Mathlib.CategoryTheory.Sites.LocallySurjective` supplies the public local-surjectivity predicate
and its image-sieve/subsheaf API. The epi-effacement import is correctly private to the proof.

## Where the brief, the DAG or earlier work was wrong

The repair queue still requests removal of the existential proof witness and `True` padding
from upstream review #1428. The current repository and sandbox already have the unpadded
vanishing equation; the landed record
`coord/changes/presheaf-ext-local-killing-witness-padding.md` explains its removal and the
subsequent explicit type annotation of zero. No further statement change is needed.
The first report incorrectly said the sandbox was an unchanged copy: its corollary uses
`exact` where the repository uses `simpa using`. It also did not distinguish existing proofs
from newly closed holes. Both reporting points are corrected here.

## Second reading by H2

1. Interface verdict: PASS. Compared the complete module with the repository using `diff`
   and the declaration parser. All four declaration statements are byte-identical, with
   identical visibility. The only code change is the final corollary's proof application.
   In both public statements the site has object universe u and morphism universe v,
   sheafification is for v-small abelian groups, HasExt has independent universe w',
   P and E are Type v-valued, q is positive, and the given Ext class is killed by Z[f]
   for a locally surjective f. No hypothesis or conclusion was changed; no definition or
   target was changed. The delivered witness contains neither an existential proof witness
   nor a True marker.

2. Proof verdict: PASS. Compiled the delivered module with lcompile.py without warnings
   (17.8 seconds). A scratch copy with `#print axioms` for both public theorems and both
   private helpers also compiled (17.6 seconds); each depends only on propext,
   Classical.choice, and Quot.sound, with no sorryAx. There is no sorry, axiom, unsafe,
   opaque, implemented_by, or extern in the delivered module. Read the construction:
   the sheafified image is closed under the group operations (intersection of covers for
   addition); its inclusion is mono and epi, hence an isomorphism. The presheaf E consists
   explicitly of pairs (p,t) satisfying g(t)=a(p), with coordinatewise restrictions.
   Projection is locally surjective, the free lift followed by sheafification factors Z[f]
   through g, and Ext associativity reduces its pullback to the zero furnished by
   Ext.exists_epi_comp_eq_zero. All existential choices are local proof witnesses;
   no data definition chooses a witness from an unproved existence assertion.

3. Split-off verdict: PASS, none added or left open. The existing witness theorem has the
   same mathematical conclusion as the corollary, but is fully proved by the two concrete
   helpers and the proved epi-effacement theorem, rather than shifting a sorry to a renamed
   statement. Read ExtEpiEffacement.lean: its proof uses a derived fraction and degree-zero
   cycles, with the target shifted out of degree zero for q>0. Small cases are consistent:
   q=1 uses the same positive-shift argument; x=0 is allowed; an empty-valued P gives
   empty E objectwise without selecting generators; no inhabitance or enough-injectives
   assumption is added.

4. Route and pruning verdict: PASS. The corollary takes the direct witness application,
   and the witness takes the existing epi-effacement route. Searched the Lean roots and
   Mathlib for epi/local-surjectivity and effacement APIs. Mathlib's
   Sheaf.isLocallySurjective_iff_epi applies to Type-valued sheaves, while its generalized
   isLocallySurjective_iff_epi' additionally requires WEqualsLocallyBijective and functorial
   factorization hypotheses. Those are not assumptions of this arbitrary-object-universe,
   v-small-coefficient statement; the direct subsheaf argument avoids adding them.
   The three existing imports provide statement or proof API; there is no unused standalone
   proof import. Read dag/units/sk-prop-cd.json: its realized statement and step lists
   currently contain no node IDs. This delivery changes no unit realization or dependency,
   and bypasses no realized unit step. No old proof dependency becomes unnecessary.

5. DAG verdict: PASS. Read both local-killing nodes and the epi-effacement dependency node.
   The conclusion node cites only the witness; the witness cites only epi-effacement and
   describes, in order, the image-subsheaf argument, the explicit pairs presheaf, the free
   and sheafification lift, and Ext composition. These match the Lean proof. Their
   proof_origin retains Tags 06XU and 03F9 and no metadata update or new node is required.

Second-reading changes: corrected the report's claimed unchanged copy and progress count,
and added this independent review. No Lean proof repair was necessary.
