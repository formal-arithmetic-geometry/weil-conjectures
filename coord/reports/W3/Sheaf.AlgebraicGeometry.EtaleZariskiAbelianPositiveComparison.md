## What changed

`Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison` now proves
`AlgebraicGeometry.Scheme.Modules.etaleZariskiAbelianPositiveComparison` from the
three separate stages of its existing argument. Its signature, universes, coefficient
maps, public imports, and docstring are unchanged. Four private proof imports were
added: the proved `ZariskiEtaleCore` and the three new modules below.

The proof obtains the continuous open inclusion with terminal image, proves additivity
of its direct image sectionwise, maps the sheaf identification through object cohomology
at the top open, and composes the resulting additive equivalence with acyclic Leray.
Its coefficient naturality is an actual Lean proof: apply the cohomology functor to
the sheaf naturality square, evaluate the equality at a section, and compose with the
Leray naturality equation.

`EtaleTensorDirectImageIdentification` is proved, using the existing explicit
`etaleTensorOpenSectionIso` and its restriction compatibility. Three proved private
helpers establish coefficient naturality of the canonical tensor-to-restriction
comparison and its equality transports. Full faithfulness lifts the presheaf comparison
to a sheaf isomorphism; the specified `hm` identifies the actual coefficient maps.
No object or definition is chosen from an arbitrary existence theorem.

`EtaleTensorPositiveDirectImageVanishing` states the affine-local vanishing step.
`EtaleZariskiNaturalAcyclicLeray` states the resolution/Leray step for arbitrary acyclic
etale abelian sheaves, independently of quasi-coherent modules. These are genuine
separate parts: neither theorem identifies a module sheaf with its direct image, and
neither theorem alone implies the original comparison.

The unit `sk-prop-cd` and its Artin--Schreier/quasi-coherent-descent route are unchanged.
All four modules compiled together with `lcompile.py --all`, without errors or warnings.
The expensive tensor construction is locally irreducible in the proofs, preventing
unnecessary unfolding; the latest complete compile took under 60 seconds per file.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.etaleZariskiAbelianPositiveComparison`
(node `lem-sc-etale-zariski-abelian-positive-comparison`). The item has no direct sorry left.
This is a decomposition, not a completed sorry-free proof of the comparison's import
closure: one original hole is replaced by two strictly separate new holes.

Also proved
`AlgebraicGeometry.Scheme.Modules.etaleTensorDirectImageIdentification`
(node `lem-sc-etale-tensor-direct-image-identification`) from existing canonical
open-section statements, together with its private coefficient/transport helpers.
The existing dependency `etaleTensorOpenSectionIso_naturality` still has its original
hole; this delivery does not change or claim to prove it.

Exactly two new holes are added, each the entire proof of one public theorem:

- `AlgebraicGeometry.Scheme.Modules.etaleTensorPositiveDirectImageVanishing`
  in `EtaleTensorPositiveDirectImageVanishing`, node
  `lem-sc-etale-tensor-positive-direct-image-vanishing`.
- `AlgebraicGeometry.Scheme.Modules.etaleZariskiNaturalAcyclicLeray`
  in `EtaleZariskiNaturalAcyclicLeray`, node
  `lem-sc-etale-zariski-natural-acyclic-leray`.

No existing statement was changed, no hole was introduced in a definition, and no
private or anonymous hole remains. No axiom or other prohibited escape was added.
The declaration still depends on the named unresolved statements above, as intended
by stage 3. Actual closure progress is for the sorry ledger to compute.

## No longer needed

All existing public imports were retained. The following ten private imports were removed from the item module: `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`, `Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural`, `Sheaf.AlgebraicGeometry.EtaleTensorSections`, `Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution`, `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, `Sheaf.CategoryTheory.SiteCohomologyPullback`, `Sheaf.CategoryTheory.SiteLerayDegenerate`, `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`, `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`, and `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`. The paragraphs below distinguish dependencies retained inside the intermediate steps from those no longer needed by this route. The new identification module needs no cohomology, affine acyclicity,
right-derived, or enough-injectives import; those were removed from its draft.

The parent now directly depends only on the proved open-inclusion core and the three
separate new steps. The following original planned nodes/modules are absent from the
new proof route, including its new lemmas:

- `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`,
  `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`: the stronger existential
  morphism-of-sites package is unnecessary; `zariski_to_etale_core` supplies the
  actual data the proof uses.
- `lem-weil-pbc-site-cohomology-pullback`,
  `Sheaf.CategoryTheory.SiteCohomologyPullback`: no prescribed pullback-counit
  edge normalization is requested by this existential natural comparison.
- `lem-weil-pbc-site-leray-degenerate`,
  `Sheaf.CategoryTheory.SiteLerayDegenerate`: replaced by the separate natural
  mixed-universe acyclic-resolution bridge. The existing statement alone does not
  give the required naturality or universe comparison.

The other old dependencies are not globally pruned: their module pullback, restriction,
affine acyclicity, localization, coefficient-lift and Ext/resolution arguments remain
needed inside the new steps or the existing canonical open-section comparisons.
In particular the plan still uses `CohomologyOverObjectLocalization`,
`EtaleOpenObjectCohomologyNatural`, `EtaleULiftInjectiveResolution`,
`SiteHigherDirectImageSheafifiedPresheaf`, and affine quasi-coherent acyclicity.
Pruning here describes this proof route, not a claim that no other target uses them.

## Where the brief, the DAG or earlier work was wrong

The existing `siteLeray_degenerate` signature only asserts an objectwise family of
invertible maps for a fixed coefficient sheaf. Its docstring explicitly excludes
identification with a prescribed pullback-counit edge. It also uses one small site and
coefficient universe. Consequently its conclusion does not supply the simultaneous
coefficient naturality and small-Zariski/standard-large-etale Ext models needed here.
This is an interface gap, not an objection to using dependencies that still have sorry.
The new acyclic Leray statement isolates exactly that independent resolution argument.

The original DAG omitted the already available explicit tensor/open-section comparisons.
Using them completes the direct-image step, including coefficient naturality, without
leaving a new hole for that step.

Checked the new statements in degree one, for zero coefficients, empty opens/empty
schemes, and arbitrary nonseparated schemes: the direct-image comparison is sectionwise,
vanishing is affine-local on opens, and the acyclic-resolution argument imposes neither
nonemptiness nor separatedness. Naturality is only required between acyclic objects;
there is no assertion that all etale abelian sheaves are acyclic. Proof irrelevance
makes the choices of acyclicity proofs immaterial.

Sources read: [03DW](https://stacks.math.columbia.edu/tag/03DW),
[03P2](https://stacks.math.columbia.edu/tag/03P2),
[0733](https://stacks.math.columbia.edu/tag/0733), and
[06XP](https://stacks.math.columbia.edu/tag/06XP).
LeanSearch was unavailable (Internal Server Error); LeanFinder and direct Mathlib/DAG
searches found ingredients but no exact replacement statement.

## New nodes

`lem-sc-etale-tensor-direct-image-identification` records the proved natural sheaf
isomorphism in `lean/Sheaf/AlgebraicGeometry/EtaleTensorDirectImageIdentification.lean`.
It depends on the existing constructed open-section comparison and restriction
compatibility, and its proof explicitly establishes coefficient naturality.

`lem-sc-etale-tensor-positive-direct-image-vanishing` records the affine-local
higher-direct-image vanishing step in
`lean/Sheaf/AlgebraicGeometry/EtaleTensorPositiveDirectImageVanishing.lean`.
It retains the corresponding original numbered proof step and its named dependencies.

`lem-sc-etale-zariski-natural-acyclic-leray` records the natural acyclic Leray/resolution
bridge in `lean/Sheaf/AlgebraicGeometry/EtaleZariskiNaturalAcyclicLeray.lean`.
It has arbitrary acyclic abelian coefficients and no module-identification hypothesis.
Its proof plan separates inverse-image exactness, the pushed injective resolution,
and the natural comparison of the two Ext models.

Change record: `coord/changes/etale-zariski-positive-proof-transparency.md` documents
the locally irreducible tensor constructions. The checker conservatively marks
this top-level command as an interface change, although its transparency effect is
local to the file. Existing signatures and public imports are preserved, no target
meaning changes, and no forced adaptation is needed. No existing module other than
the item was edited.

## Earlier second reading (a previous round; superseded)

1. **Statements unchanged.** Compared the item module byte-for-byte against the repository version; the theorem signature and all existing declarations are unchanged. The three added public theorem statements are independent reductions: direct-image identification, positive direct-image vanishing, and natural acyclic Leray. Their hypotheses and conclusions match the uses in the parent proof and are strictly weaker than the parent comparison.

2. **Proof and axioms.** Compiled all four modules with `lcompile.py --all`, and separately recompiled the expensive item module (50.1 seconds). There are no prohibited commands, no hollow definitions, and the only remaining `sorry` declarations are the two named split theorems recorded above. The direct-image identification is fully proved.

3. **New statements and nodes.** Checked the three new DAG nodes against their Lean declarations, docstrings, and proof dependencies. The split statements are true standard reductions: sectionwise tensor/direct-image identification, affine-local positive derived-image vanishing, and the injective-resolution Leray comparison for acyclic coefficients. No duplicate library or Mathlib theorem was found.

4. **Pruning and route.** The parent uses the proved direct-image identification and the two split steps, while retaining the unit route through the open inclusion core and tensor/direct-image comparison. The report's listed removed dependencies are not used by the Lean proof; imports in the new identification module were minimized. No unit statement or realized step was changed.

5. **Review result.** The proof composes the three reductions with explicit coefficient naturality and preserves the original comparison target exactly. I found no statement weakening, accidental hypothesis addition, definition change, or unsupported witness construction. The local irreducibility attribute only controls elaboration transparency.

Changes made during this second reading: added this section to satisfy the stage-3 report contract; no Lean declarations or DAG statements were altered.

## Second reading by W3

1. **Existing interface: pass.** Read the repository and delivered modules and
   inspected their diff. The sole existing theorem is
   `AlgebraicGeometry.Scheme.Modules.etaleZariskiAbelianPositiveComparison`.
   Its full signature, including both local Ext instances, all universes, `m`,
   the objectwise formula `hm`, and the elementwise coefficient-naturality clause,
   is byte-for-byte unchanged after restoring one extra space before `:=`.
   Its existing docstring and public imports are unchanged. No existing definition
   is edited; the recorded local irreducibility command changes only elaboration.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.

2. **Proof and axioms: pass, with explicit unresolved dependencies.** Independently
   compiled all four delivered modules through `lcompile.py --all`: 11.5, 4.7,
   7.7, and 53.2 seconds, respectively, without errors or warnings. Compiled a
   scratch copy with `#print axioms` for all four public theorems: each reports
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The identification
   still depends on the existing unresolved restriction-naturality theorem;
   therefore its completed body is not an axiom-free closure proof. The only two
   direct holes in the delivery are exactly the public vanishing and acyclic
   Leray theorems listed above. No hollow definition, arbitrary existence-based
   data construction, anonymous hole, or prohibited escape appears. The private
   coefficient lemmas use adjunction naturality and equality elimination; the
   public identification uses full faithfulness and cancels its component iso.
   The parent maps that iso through cohomology and composes with Leray, proving
   coefficient naturality by mapping the sheaf square and evaluating at `x`.

3. **Split statements: pass as a decomposition.** The vanishing theorem concerns
   only `R^(n+1) i_* F_et`, assuming the specified open inclusion and additive
   pushforward; it constructs no global cohomology equivalence. Its proof localizes
   to affine opens, uses quasi-coherent acyclicity, and sheafifies locally zero
   positive cohomology. The Leray theorem instead assumes acyclicity of arbitrary
   abelian sheaves, continuous finite-limit-preserving `i`, a terminal image of
   the top open, and a small Zariski Ext model; it neither identifies module sheaves
   nor proves their acyclicity. Its resolution argument supplies the simultaneous
   equivalences and naturality needed by the parent. Checked degree one, zero
   coefficients, identity coefficient maps, empty opens and the empty scheme;
   neither argument requires separatedness. Both holes have sourced, complete
   natural-language proof docstrings and matching nodes. Independently read
   Stacks Tags [03P2](https://stacks.math.columbia.edu/tag/03P2),
   [03DW](https://stacks.math.columbia.edu/tag/03DW),
   [0733](https://stacks.math.columbia.edu/tag/0733), and
   [06XP](https://stacks.math.columbia.edu/tag/06XP). Fresh LeanFinder searches for
   acyclic direct-image cohomology and higher direct-image vanishing, a Loogle
   search for right-derived isomorphisms, and direct searches in `lean/` and Mathlib
   found ingredients but no replacement with these complete hypotheses,
   coefficient naturality, and Ext universes. Existing `siteLeray_degenerate`
   supplies only objectwise isomorphisms for a fixed sheaf on small sites and
   cannot directly discharge the new natural mixed-universe statement.

4. **Route and pruning: pass.** Read `dag/units/sk-prop-cd.json`, including all six
   steps and `realized` (currently empty lists). No unit record changes, and the
   quasi-coherent-descent comparison used in the Artin--Schreier step is preserved.
   All twelve original parent proof dependencies leave its direct `proof_deps`:
   open-inclusion morphism-of-sites, open-immersion module restriction,
   tensor-presheaf functoriality, tensor adjunction, object localization,
   open-object cohomology naturality, coefficient-lift resolutions, affine
   quasi-coherent acyclicity, sheafified higher direct images, Leray degeneration,
   cohomology pullback, and Ext via resolutions. The nine retained as ingredients
   are recorded in the new steps or the existing open-section nodes; the three
   absent from this route are explicitly listed under `No longer needed`.
   The ten removed private parent imports are also listed there. Public
   `DerivedHomMayerVietoris` is needed for `moduleRings` in the identification
   signature. `Sites.Pullback` supplies only proof machinery in the two unresolved
   modules, so I changed those two imports from `public import` to `import`.
   Other retained private imports supply the named proof-plan dependencies.

5. **Nodes and Lean: pass.** Opened all four delivered JSON nodes, resolved their
   dependency declarations or Mathlib matches, and checked each proof-dependency
   list against the union of its proof steps. The parent names precisely the
   proved core inclusion and the three intermediate theorems used in its body.
   The identification node records the actual constructed open-section iso,
   coefficient adjunction naturality, and restriction compatibility. The two
   unresolved nodes match their Lean hypotheses and conclusions, carry source,
   statement dependencies, creation and blueprint provenance, three search kinds,
   chapter/unit, and Lean records, and are strictly separate parts of the argument.
   No node changes a target statement or claims the two holes have been proved.

Changes made: restored exact signature whitespace, made the two proof-only
`Mathlib.CategoryTheory.Sites.Pullback` imports private, and added this independent
reading. No mathematical statement or proof body changed. One original hole is
closed and two new holes remain; this delivery is a decomposition with net -1
among these direct holes, not a completed proof of the target import closure.
