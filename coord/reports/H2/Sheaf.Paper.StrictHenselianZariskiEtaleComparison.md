## What changed

Replaced the only sorry in `Sheaf.Paper.StrictHenselianZariskiEtaleComparison` by a
complete Lean reduction. For each positive degree and pair of sections, apply local
vanishing to their difference. Additivity of restriction turns its zero restriction
into equality of the two restrictions. The resulting opens witness membership of
the equalizer sieve in the Zariski topology, proving local injectivity of zero.
Apply the canonical Leray bridge at the top open and rewrite by `hc`.

Added two modules, each with one public intermediate theorem, and their DAG nodes:
`Sheaf.Paper.StrictHenselianCohomologyLocallyZero` covers step 3, including the
Ext/resolution and coefficient-universe bridges; `Sheaf.Paper.ZariskiEtaleCanonicalLeray`
covers steps 1, 2, 4 and 5, identifying the canonical comparison, not merely some
invertible family. Neither is the original statement renamed: the first concludes
local annihilation of classes, while the second assumes local injectivity of positive
cohomology presheaves, has no strictly-henselian assumption, and applies on every open.
The original theorem's signature and public imports are unchanged. All new imports
of the item's proof are private. Updated its DAG proof and proof dependencies.

Both intermediate docstrings contain sources and complete proof arguments, including
transport between coefficient universes and identification of restriction maps.
The unit `sk-thm-p1` and every realized unit node remain unchanged.

## Proved and sorry left

Closed one original hole by decomposition: `strictHenselian_zariski_etale_comparison`, node
`lem-weil-pbc-gabber-strict-henselian-zariski-comparison`. No sorry remains in the item.

Added two holes, both named theorems in new modules:

- `strictHenselian_cohomology_locally_zero`, node
  `lem-weil-pbc-strict-henselian-cohomology-locally-zero`.
- `zariski_etale_canonical_leray`, node `lem-weil-pbc-zariski-etale-canonical-leray`.

Each proof is exactly `:= by sorry`. This is a reduction, not an axiom-free proof of
the full comparison: its proof still depends on these two named obligations.
This is a decomposition: one original hole closed, two holes added, net -1 in this
delivery; no dependency module is pruned. It is not an axiom-free comparison proof.
Local compilation of all three modules succeeds. The final delivery dry run supplies
local/server compilation, axiom-policy probes and mechanical preflight validation.

Edge cases checked in the statements and argument: positive degree is essential to
local annihilation (degree-zero constant sections need not vanish); empty opens have
no points and their empty covering suffices; the empty scheme is harmless; the zero
sheaf satisfies the local hypothesis; degree zero of the canonical comparison follows
from the unit/counit triangle identity, independently of positive-degree vanishing.
The Ext universe remains arbitrary, exactly as in the original signature.

## No longer needed

Removed these eight direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit`
- `Sheaf.CategoryTheory.KInjectiveComputes`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.CategoryTheory.SiteLerayDegenerate`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

The first seven move into the appropriate intermediate modules as their planned
proof dependencies. LowerShriek was redundant as a direct import and is still
available transitively through the local-ring and acyclicity modules. Accordingly
no entire dependency module or node is claimed pruned from the targets' closure.
The item's direct proof dependencies are now exactly the two new nodes. The original
sheafification, colimit, acyclicity, pullback and Leray nodes remain below them.


Every old direct `proof_deps` entry removed from the item's node is listed here:

- `lem-weil-pbc-etale-cohomology-local-ring-colimit`
- `lem-weil-pbc-strictly-henselian-etale-acyclic`
- `lem-sp-kinjective-computes`
- `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`
- `lem-weil-pbc-site-cohomology-pullback`
- `lem-weil-pbc-site-leray-degenerate`
- `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`
- `lem-weil-pbc-site-sheafification-iso-locally-bijective`
- `def-weil-pbc-sheafification`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-pbc-etale-cohomology`
- `def-sc-zariski-cohomology`
- `def-weil-pbc-henselian-terminology`

The first ten remain dependencies of the new obligations (or their statements).
The final three remain statement dependencies of the original comparison. This
removes direct proof edges, not these nodes from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The existing `siteLeray_degenerate` concludes existence of an unspecified invertible
family. Its node describes the canonical edge map, but its Lean statement does not
identify the family with the supplied `fstar` followed by the counit. It cannot prove
invertibility of the specified `c` without the canonical-map bridge recorded here.

The colimit statement is for `Scheme.{u}` and coefficients `AddCommGrpCat.{u + 1}`,
using `uliftYoneda`; this item is for `Scheme.{u + 1}` with coefficients
`AddCommGrpCat.{u + 1}`, using the ordinary cohomology presheaf. A direct specialization
would require coefficients one universe larger. Acyclicity is stated in derived
cohomology, whereas this item uses Ext. These are interface obligations, not reasons
to reject the underlying mathematics. The local-vanishing bridge records them.

The original signature also quantifies over an independent Ext universe. Introducing
sheafification of its cohomology presheaf at the coefficient universe would silently
specialize that universe or require additional sheafification assumptions. The
reduction instead passes local injectivity, which is meaningful in the original
Ext universe, to the Leray bridge. Its proof transfers through the natural
section-complex description before sheafifying.

`hi_inclusion` fixes the underlying scheme functor, not the structural morphism of
`i(⊤)` over `X`. The intermediate arguments therefore first restrict to the etale
object `i(⊤)`, whose underlying scheme is `X`, and treat its open restrictions.
No assertion that `i(⊤)` is the terminal etale object is used by the reduction.
This also avoids silently strengthening the supplied hypothesis.

The cited TeX documents are absent from this clone's `literature` directory but were
read from the existing local Stacks source copy: 09AX, 03QO, 072W and 0733(1).
LeanSearch returned Internal Server Error for both new-node searches; recorded as
unavailable, with no absence verdict inferred. LeanFinder and source grep returned
no matching statement. Blueprint search found no duplicate; the existing Zariski
local-vanishing theorem concerns Zariski, not etale, cohomology.

## New nodes

`lem-weil-pbc-strict-henselian-cohomology-locally-zero`: positive etale object
cohomology classes vanish on smaller Zariski neighbourhoods at each point.
Source: 09AX, proof, via 03Q6 and 03QO. The proof records the natural Ext/resolution
identification and the local-ring colimit/acyclicity transport. Module:
`Sheaf.Paper.StrictHenselianCohomologyLocallyZero`.

`lem-weil-pbc-zariski-etale-canonical-leray`: local injectivity of zero in every
positive cohomology presheaf implies invertibility of the canonical pullback/counit
comparison on every open. Source: 072W and 0733(1), with the route of 09AX.
The proof explicitly identifies the edge map and accommodates the independent Ext
universe. Module: `Sheaf.Paper.ZariskiEtaleCanonicalLeray`.

No definition, existing statement, target, or change record was altered.

## Second reading by H2

1. PASS. Compared the existing module with the repository using `diff`: its
   declaration signature is byte for byte unchanged, as are its public imports,
   definitions and mathematical docstring. Only private proof imports and the
   proof body changed. The other two modules are new. Read the landed V1 change
   record; this delivery preserves its repaired signature.
2. PASS AS DECOMPOSITION. Compiled all three files in dependency order using
   `lcompile.py --all`, without errors or warnings. Scanned the delivered Lean:
   exactly the two reported public theorems have `:= by sorry`; no definition,
   helper or partial proof contains a hole, and no forbidden mechanism appears.
   A scratch copy with `#print axioms` for all three declarations compiled and
   printed only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Thus the original hole is closed conditionally on the two new obligations;
   none of the three declarations is claimed axiom-free.
3. PASS. Read both new signatures and their complete proof docstrings against
   local Stacks TeX: 09AX's local-ring colimit/acyclicity argument, 072W's
   sheafified section-complex calculation, and 0733(1)'s acyclic Leray comparison.
   Checked positive-degree exclusion, empty opens and schemes, zero coefficients,
   degree-zero unit/counit identity, and arbitrary Ext universe. The underlying
   functor equality identifies open restrictions of the etale object `i(top)`;
   neither new argument assumes it is terminal. Exact etale extension by zero
   justifies restriction preserving injectives and the factorization used in the
   canonical bridge. Local vanishing is strictly the geometric step; canonical
   Leray has a local-vanishing hypothesis and no henselian hypothesis. Neither
   restates the original comparison. Repeated LeanFinder searches using
   "class dies after shrinking" and "unit and counit cohomology comparison";
   hits were etale-locus or underived sheaf-adjunction results, not either lemma.
   Loogle did not recognize the queried local-injectivity name; no negative
   conclusion is drawn from that failure. Grepped Mathlib and both source roots.
   Examined the upstream topological pushforward comparison and Ext counit
   bijectivity: the former uses topological sites, the latter requires global
   exactness of direct image, stronger than vanishing for this particular F.
   The existing site Leray theorem leaves the comparison unspecified. Neither
   remaining obligation can be closed by a short application of these results.
4. PASS. Read the proof top down: annihilation of `s-t`, additivity of restriction,
   covering equalizer sieve, canonical comparison at the top open, and `hc`.
   Every proof import has a role in this reduction or the recorded lower plan;
   no newly added proof-only import is public. Checked `sk-thm-p1.json` and its
   `realized` entries; no realized unit statement or step is bypassed or changed.
   Completed the list of all old direct proof dependencies removed. No entire
   module is reported pruned, since these imports remain below the new obligations.
5. PASS. The original node changes only `proof`, `proof_deps`, `proof_origin`.
   All three recorded Lean signatures match verbatim. For every node, the union
   of the proof-step `uses` is exactly `proof_deps`, and every dependency exists.
   New nodes have source, full proof steps, searches, creation record, blueprint
   provenance, chapter/unit, split status, and matching Lean record. The two new
   nodes carry the original five-step route, rather than substituting a unit route.

Second reading changed the report and new-node search records: enumerated all 13
removed direct proof edges, explicitly counted one hole closed and two added
(net -1, decomposition), recorded the checks above, and appended independent
LeanFinder searches to both new nodes. The Lean proof and signatures needed no repair.
