## What changed
Repair of return X-fb28c (B7): corrected the cartesian sheaf-adjunction node's
failed `Functor.IsContinuous` Loogle search verdict to exactly
`query failed to resolve its identifier; no absence verdict`. No Lean declaration,
proof, or import changed in this repair.

Repair of return X-33dfc (B2, B9): replaced the geometry node's entire informal
statement with the reviewer's self-contained text, explicitly introducing I, D, c and
both sites. Replaced both helpers' blueprint records with the requested original
blueprint ancestor, precise place, three-node via chain and same_as: []. No Lean file,
existing signature, proof, or import was changed in this repair.

The existing theorem `AlgebraicGeometry.Scheme.exists_affineEtale_baseChange_system`
now assembles a geometric system and applies a single-morphism cartesian sheaf-adjunction
lemma to each transition and each cone projection. Its signature is byte-for-byte unchanged.
Mathlib's `AlgebraicGeometry.isAffineHom_π_app` supplies affineness of the latter.

New module `Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeGeometry` contains the data record,
the explicit geometric predicate, and existence of normalized cartesian/coherent data
preserving coverings and pullbacks, with continuity. It omits all sheaf-adjunction clauses.
New module `Sheaf.AlgebraicGeometry.AffineEtaleCartesianSheafAdjunction` states only the
left exact sheaf adjunction for one affine morphism and an arbitrary continuous functor
with natural cartesian first projections. Both helpers are imported privately by the item.

Replaced the item's broad public `FullAffineEtaleTopos` import with `FullAffineEtaleSite`,
which supplies its signature, and removed unused public `Mathlib.CategoryTheory.Category.Cat`.
The only direct user, `AffineEtaleSiteColimit`, already imports `FullAffineEtaleTopos` itself.
Added proof-only imports of the two helper modules and `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
No existing declaration, definition, or target statement changed.

## Proved and sorry left
`AlgebraicGeometry.Scheme.exists_affineEtale_baseChange_system` has a complete reduction
proof and no local sorry. This is not yet an axiom-closed proof: it depends on the following
two genuine, strictly smaller obligations, each exactly `:= by sorry`:

- `exists_affineEtale_baseChange_geometry`, node
  `lem-weil-pbc-affine-etale-base-change-geometry`;
- `affineEtale_cartesian_sheafAdjunction`, node
  `lem-weil-pbc-affine-etale-cartesian-sheaf-adjunction`.

The structure and geometric predicate have no sorry in their bodies. There are no other
new sorries, axioms, unsafe declarations, externs, opaque declarations, implemented_by
attributes, or kernel-check bypasses. Every split theorem has a source and full prose proof.

## No longer needed
Removed imports: `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos` (replaced by its smaller
statement dependency `FullAffineEtaleSite`) and `Mathlib.CategoryTheory.Category.Cat`.
Also removed proof-only imports `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
`Sheaf.AlgebraicGeometry.LimitAffineTransition`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` from the item. The corresponding
mathematics remains in the helper plans or is supplied directly by Mathlib.
Reduced `Mathlib.CategoryTheory.Sites.Pullback` to `Sites.Continuous` in all three
modules: only continuity and continuous pushforward occur in their signatures or proofs.
No original mathematical node is globally pruned: the old dependencies remain in the
geometric and sheaf helper plans. The item's old direct dependencies
`lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-etale-base-change-finite-limits`,
`def-pc-fibre-product`, `lem-weil-pbc-cartesian-square-pasting`,
`lem-weil-pbc-etale-base-change-continuous`, `lem-weil-pbc-affine-etale-site-topos`, and
`lem-weil-pbc-etale-inverse-image-algebraic-structures` are now indirect through the two
helpers. `lem-weil-pbc-limit-affine-transition` remains a direct dependency, represented
by Mathlib's affine-projection theorem. Nothing in the unit's realized route was removed.

Removed the first worker's unused tautological nonemptiness declaration and node, and its
unconstrained-data and universally quantified properties splits. None had landed.

## Where the brief, the DAG or earlier work was wrong
The first worker's `affineEtale_baseChangeSystemProperties` asserted all desired properties
for every arbitrary data record, without assuming that its functors were base change.
This is false. Take a singleton index and a constant diagram at a nonempty affine scheme.
Choose every U and v constant at the empty affine étale object, all first projections
unique, and all comparison isomorphisms identities of the constant functor. These satisfy
the record's field types, but U on the diagonal is not the identity: it sends the identity
étale object of the nonempty scheme to the empty scheme. Pullback and covering claims
also cannot follow from the unconstrained record. Its asserted prose proof silently
assumed properties absent from its signature. The arbitrary-data lemma was removed.
The unused nonemptiness tautology was not progress and was removed.

The old new-node records also lacked full verbatim signatures, substantive searches and
complete proof dependency accounting. Those records were replaced, not delivered.
LeanSearch returned an Internal Server Error; the failed request is recorded without
claiming an absence result. Actual LeanFinder, Loogle and grep searches were also performed.
Mathlib has ordinary pullback composition and a continuity criterion, but not the
normalized full-affine system. The existing `affineEtaleSiteBaseChange` and
`etaleInverseImageAlgebraicStructures` use Type (u + 1); they do not directly provide the
required Type u cartesian-functor statement. The sheaf-universe transport remains explicit
in the second split and is not treated as an already compiled proof.

## New nodes
`lem-weil-pbc-affine-etale-base-change-geometry`: the normalized geometric part of the
original statement, omitting every sheaf-adjunction clause. Its plan retains original
geometric dependencies and uses the general generated-topology continuity criterion.

`lem-weil-pbc-affine-etale-cartesian-sheaf-adjunction`: a tool for one affine morphism,
assuming a continuous functor and natural cartesian squares. Its proof identifies that
functor with restricted ordinary base change, compares affine and small-site topoi (04HR),
and transports the left exact adjunction of 03Q1(2), in Type u throughout.
Change record: `coord/changes/AffineEtaleBaseChangeSystem-imports.md` records the public
import reduction and its direct user. Every existing signature and definition is unchanged.


Whole-blueprint search for each helper (B9 repair): searched every imported blueprint
node, including chapters outside target reach: 2,331 nodes across all 16 chapters.
Ran `python3 tools/blueprint_refs.py search` with separate words `affine etale`
(73 hits), `affine étale` (8), `etale adjoint` (45), `04HR` (0), `03Q1` (0),
`0EYL` (1), `normalized` (56), and `cartesian sheaf` (28), plus whole-DAG rg
for affine étale, cartesian sheaf/adjunction and the source tags. Reviewed candidate
statements, not just names. The local raw search log is blueprint-search-repair.txt.
For the geometry helper, `lem-kun-descent-limit` concerns recovery of torsion abelian
sheaves at an affine limit, and `lem-weil-pbc-etale-finite-data-descent` concerns descent
of finite-presentation objects, maps and covers; neither states a normalized geometric
functor system with cartesian projections, both cocycles and covering/pullback
preservation. No imported blueprint statement matches this helper: same_as = [].
For the cartesian sheaf-adjunction helper, `def-weil-pbc-inverse-image` and
`prop-weil-pbc-inverse-image-exact` concern ordinary small-site abelian inverse images;
étale extension-adjunction statements concern étale maps and module sheaves. None states
the Type u full-affine-site adjunction for an arbitrary continuous functor with natural
cartesian first projections along one affine morphism. No imported blueprint statement
matches this helper: same_as = []. These are recorded absence results for the helpers'
precise statements, not claims that their constituent facts are absent.
`python3 tools/blueprint_refs.py ancestor lem-weil-pbc-affine-etale-base-change-system`
confirms `lemma-weil-pbc-injective-restriction-acyclicity` as the blueprint ancestor.

## Earlier second reading (a previous round; superseded)
1. Compared the delivered item against the repository using diff and the declaration
   parser, and checked the existing theorem's complete raw signature byte-for-byte.
   Verdict: unchanged. All additional declarations are new, in the two new helper modules;
   removed first-worker declarations and nodes were unlanded. Checked the only direct
   user's explicit imports before reducing the item's public imports.
2. Compiled every delivered module in import order through lcompile.py. Verdict: clean,
   with no errors or style warnings. Checked all Lean source for prohibited constructs and
   hollow definitions. Printed axioms in scratch copies and reviewed the delivery probe:
   only the allowed standard axioms and sorryAx from named remaining obligations occur.
3. Checked both revised split statements from their full signatures. Verdict: true and
   strictly partial: the first does not assert adjunctions, and the second concerns one
   morphism and does not assert existence or coherence of any system. Checked identity
   base change, singleton indices, empty schemes and empty covers; these cases preserve
   the assertions. Checked naturality is an explicit hypothesis of the cartesian tool,
   so objectwise pullbacks really yield a functor isomorphism. Repeated genuine searches
   with different terminology, including upstream and Sheaf searches. Neither is already
   present with its precise normalization, hypotheses and coefficient universe.
4. Read the top-level conjunction and proof downward. Verdict: each original geometric
   clause is extracted unchanged, and each sheaf clause is obtained by applying the same
   smaller cartesian tool with the relevant p/q squares. Affineness of cone projections
   comes directly from Mathlib, not a new sorry. Pruning below the unit only; the
   `sk-thm-p1.json` realized statement and steps remain untouched. New proof-only imports
   are private. All old direct dependencies moved into helper plans are listed above;
   no original unit-route node is globally discarded.
5. Read all three delivered node records against the Lean. Verdict: full signatures,
   proof steps, dependency unions, source, origin, creation, search records, module paths,
   chapter and unit agree. The original node's mathematical statement is unchanged;
   its proof fields now describe the actual reduction.

Changed the false arbitrary-data properties split into the geometric-existence and
single-morphism cartesian-adjunction obligations; removed the unused tautology; moved
new statements into their own modules; repaired docstrings, node records, searches and
import visibility/minimality. The existing theorem remains a reduction over two open
obligations, rather than a completed axiom-free construction.

## Earlier second reading (a previous round; superseded)
1. Compared the item with the repository using diff and checked the complete raw
   theorem signature byte-for-byte: unchanged. The existing node differs only in
   proof, proof_deps and proof_origin. The two helper modules are new. The public
   import reduction has its change record; the sole direct user explicitly imports
   FullAffineEtaleTopos and uses no declaration supplied only by Sites.Pullback.
   Verdict: no accidental statement or definition change.
2. Compiled all three modules in import order with lcompile.py, then compiled scratch
   copies with #print axioms for the original theorem, both helper theorems, the data
   structure and the geometric predicate. The structure and predicate use only
   propext, Classical.choice and Quot.sound; the three theorems additionally use sorryAx.
   Source scan found exactly the two reported named whole-proof sorries and no forbidden
   constructs or hollow definitions. Verdict: valid reduction, not axiom-closed.
3. Read the helpers, their full signatures and prose proofs against Stacks 0EYL,
   04HR and 03Q1(2). Checked singleton and diagonal indices, identity morphisms,
   empty schemes and empty covering families. Cartesian squares and naturality
   constrain the functors; pullback uniqueness supplies the comparisons. Geometry
   omits adjunctions; the adjunction tool treats one morphism without a system.
   Repeated LeanFinder search for normalized pullback pseudofunctor identity coherence,
   Loogle search for sheafPushforwardContinuous, and grep for RepresentablyFlat,
   IsLeftAdjoint and sheafPullback, plus upstream and Sheaf searches. Mathlib provides
   ordinary comparisons and general Kan-extension adjunctions, not these precise
   statements. Existing affineEtaleSiteBaseChange and inverse-image structures have
   Type (u + 1) coefficients. The Type u universe transport is still an obligation;
   neither split can be closed by those declarations in a few minutes. Verdict:
   genuine smaller obligations with sources and nodes, no tautological restatement.
4. Read the proof downward: all geometric clauses are unpacked, transition adjunctions
   use the cartesian tool, and projection adjunctions also use Mathlib affineness.
   Checked sk-thm-p1 realized statement and every step: the unit route is untouched.
   Completed No longer needed for all removed private imports and reduced Pullback
   to Continuous in all three modules. No original mathematical node is globally
   pruned. Verdict: reduction and dependency pruning retain the unit route.
5. Checked the three node signatures against Lean verbatim and checked proof_deps
   equals the union of the proof steps' uses. Read the new nodes' sources, origins,
   blueprint ancestor/via chains, searches, creation and Lean records. Verdict:
   records agree with the declarations and reduction. Corrected the geometry node's
   failed unknown-identifier Loogle entry to make no absence claim.

This reading changed only import minimality, the import change record, completeness
of the pruning report, and the failed-search verdict. It preserved all proofs,
statements, definitions and unit realization records.

## Second reading by G1
1. Compared the item against the current repository with diff and independently checked
   its full raw theorem signature byte-for-byte. It is unchanged. The existing node
   changes only proof, proof_deps and proof_origin. The two helper modules are new;
   the public import reduction has its change record. The sole direct user explicitly
   imports FullAffineEtaleTopos. Verdict: no accidental visible statement change.
2. Compiled all three delivered modules in import order with lcompile.py: no errors
   or warnings. Independently printed axioms in scratch copies for the original theorem,
   both helper theorems, the data structure and the predicate. Only propext,
   Classical.choice and Quot.sound occur in the structure and predicate; the theorems
   also use sorryAx. Source scan finds exactly two named whole-proof sorries and no
   prohibited constructs. Verdict: valid decomposition, not an axiom-closed proof.
3. Read both complete signatures and docstring arguments and checked Stacks 0EYL,
   04HR and 03Q1(2). Tested singleton indices, equal adjacent indices, identity base
   change, empty schemes and the empty cover. Cartesian squares and naturality constrain
   F; both comparison cocycles follow from uniqueness with fixed projections. Geometry
   omits adjunctions; the adjunction theorem concerns one morphism without any system.
   Repeated LeanFinder search for geometric morphisms from base change, a successfully
   resolved Loogle search for CategoryTheory.Functor.sheafAdjunctionContinuous, and grep
   for RepresentablyFlat, HasSheafify and finite-limit preservation, plus rg in both
   library roots. General adjunction machinery still needs the cartesian identification
   and finite-limit argument. The existing inverse-image algebraic-structures theorem
   has Type (u + 1) coefficients. Neither obligation has a direct existing replacement
   or a proof closable in a few minutes. Verdict: true, strictly smaller obligations.
4. Read the proof from the top: all original geometric clauses are unpacked unchanged;
   both adjunction families use the cartesian helper, and cone affineness comes from
   Mathlib isAffineHom_π_app. Checked private proof imports, the full No longer needed
   accounting, and sk-thm-p1's realized statement and steps. No unit route is removed;
   no original node is globally pruned. Verdict: route and pruning accounting agree.
5. Independently checked every helper's recorded verbatim Lean signature and every
   node's proof_deps against the union of proof-step uses. Read the sources, origins,
   creation records, blueprint ancestor and via chains, searches, chapter and unit.
   The unsuccessful identifier searches explicitly make no absence claim. Verdict:
   node records agree with Lean and the actual reduction.

This reading changes only this report: no additional mathematical or Lean repair was
needed. One original local hole is closed by reduction and two named lower holes are
added, as listed in Proved and sorry left; this is a decomposition, not net proof progress.
