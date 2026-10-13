## What changed

Proved `AlgebraicGeometry.Etale.etale_inverse_image_unit_eventual_equality` with its
signature and existing docstring unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.EtaleAbelianUnitEqualOpen` and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.

The new module proves `AlgebraicGeometry.Etale.etale_abelian_unit_equal_open`:
equality under an arbitrary base-change unit is equivalent to whole inverse image
of an agreement open in the original etale object. It uses the existing
`existsUnique_etaleSections_equal_open` and `etaleSetCartesianUnit_eq_iff`.
The private coefficient comparison is proved by commuting forgetting abelian groups
with the filtered Kan extension and sheafification, then verifying its unit equation.
The returned delivery duplicated the private generic `pullback_unit_hom` from
`EtaleModuleSetPullbackComparison.lean`. That declaration has now been removed.
At the two concrete unit occurrences the proof instead applies the existing
Mathlib equations `Adjunction.map_restrictFullyFaithful_unit_app`,
`Adjunction.comp_unit_app`, `Functor.lanAdjunction_unit`, and
`sheafificationAdjunction_unit_app` directly. No new generic helper is declared.
The upstream module remains unchanged and is not imported: its helper is private
and importing it does not expose the name (verified by a compiler probe).

The original theorem now base changes the inverse system to U over `Over (op i)`,
uses the proved `isLimitBaseChangeCone`, applies Mathlib `exists_map_eq_top`, and
converts the resulting containment back to equality of the requested unit images.
No finite affine cover or section-colimit presentation is required. The unit route
in `dag/units/sk-thm-p1.json` is preserved; this item is below its realized nodes.
Updated the original DAG proof and added one node for the new proved helper.
Both delivered modules compile individually and together with lcompile.py.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.etale_inverse_image_unit_eventual_equality`
(node `lem-weil-pbc-etale-inverse-image-unit-eventual-equality`).

Also proved the new public helper:
`AlgebraicGeometry.Etale.etale_abelian_unit_equal_open`
(node `lem-weil-pbc-etale-abelian-unit-equal-open`).
The remaining private `isIso_abelian_forget_comparison` is fully proved;
the redundant private `pullback_unit_hom` declaration has been deleted.
No `sorry` remains in either delivered module; no new hole is added or split off.
The earlier independent second-reader axiom probes showed only `propext`, `Classical.choice`, and `Quot.sound`: no transitive
`sorryAx` is present in these results.

Edge cases: the open-containment argument and the agreement-open criterion both
allow empty U and empty stage pullbacks. For identical sections the agreement
open is top. Identity base change and singleton directed indices are covered by
the same unit equation. No sheaf or scheme is defined by an arbitrary existence witness.

## No longer needed

The duplicate private `pullback_unit_hom` declaration was removed.
The proof directly uses existing Mathlib adjunction-unit equations at the two
concrete occurrences. No upstream module, visibility, or signature is changed.
No existing import is removed and no previously imported module is pruned.

The geometric plan in the original docstring can discard its affine-site filtered
colimit presentation (Tag 0EYL), restriction to the affine basis (Tag 04HR),
inverse-image section-colimit formula (Tag 0A35), finite affine cover, common-stage
selection for that cover, and subsequent gluing. These are not needed by this proof.
In particular, this item does not import the affine-etale-site-colimit or
colimit-of-sites section machinery. The original node had no proof_deps to remove;
its new proof_deps precisely record the agreement-open helper and the Mathlib
open-containment leaf. Other users may still need the discarded machinery.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned duplicate-declaration finding: the named existing helper
is private, so it cannot be imported under its source name. A visibility promotion
was tested but refused by deliver3 as an unforced adaptation; that attempted copy
was removed. The final repair deletes the duplicate declaration and uses the
existing public Mathlib equations directly in the coefficient comparison.
The DAG argument and all public statements are unchanged.

The original one-step DAG plan supplied no named lower-level declarations. Its
section-colimit approach is longer than necessary for equality of two fixed sections.
The existing set-valued agreement-open and cartesian-unit lemmas supply the shorter
route after a proved coefficient comparison. `sitePullback_abelian_underlying`
provides an abstract natural isomorphism but not the canonical unit equation needed
here, so it is not imported.

The blueprint ancestor helper returns None for this item because its created.item
is a module name. The new node follows the recorded scalar-continuity branch back
through EtaleLimitScalarSectionColimit to the blueprint ancestor
`lemma-weil-pbc-injective-restriction-acyclicity`; no existing blueprint metadata is changed.

The local literature TeX is absent on this machine. The source statements were read
on the Stacks website at https://stacks.math.columbia.edu/tag/09XM,
https://stacks.math.columbia.edu/tag/03Q1 and https://stacks.math.columbia.edu/tag/03S2.

## New nodes

`lem-weil-pbc-etale-abelian-unit-equal-open`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-abelian-unit-equal-open.json`,
records the new fully proved helper module
`lean/Sheaf/AlgebraicGeometry/EtaleAbelianUnitEqualOpen.lean`.
It has no limit, directedness, compactness, or eventual-stage hypothesis or conclusion;
it isolates the sheaf-theoretic agreement-open criterion. No change record is needed:
all existing signatures, definitions, and public imports are unchanged.


The second reading below is the preserved review of the previous delivery, before
this repair; its references to the deleted generic private helper are historical.
The independent second reader should review the repaired two concrete calculations.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations: PASS.** Read the diff of the existing module against
   the repository: the only differences are the two plain proof imports and the
   replacement of `by sorry` by the proof. The existing signature, visibility,
   universes, hypotheses, conclusion and docstrings are byte-for-byte unchanged.
   The agreement-open module is new (absent in the repository); no existing
   definition or public import changed, and no change record is required.
2. **Proof and axioms: PASS.** Compiled both modules together in import order with
   `lcompile.py` (8.3 s and 3.1 s; no warnings). Then compiled scratch copies with
   `#print axioms` for `pullback_unit_hom`,
   `isIso_abelian_forget_comparison`, `etale_abelian_unit_equal_open`, and
   `etale_inverse_image_unit_eventual_equality`. Every probe printed only
   `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, forbidden
   axiom or implementation escape in the delivered files, and no new definition.
   The comparison is explicitly the adjoint transpose of the forgotten unit:
   `hq` verifies its canonical identification, and `hvalue` evaluates the
   adjunction equation before injectivity is used. Thus an arbitrary unrelated
   isomorphism is not being used to identify the units.
3. **New statements and search: PASS.** No statement is split off with `sorry`.
   Read the new helper, its node, and Stacks
   [09XM](https://stacks.math.columbia.edu/tag/09XM),
   [03Q1](https://stacks.math.columbia.edu/tag/03Q1), and the restriction paragraph
   of [03S2](https://stacks.math.columbia.edu/tag/03S2).
   The helper applies 09XM over U to the underlying set sheaf. Arbitrary f is
   allowed: 03Q1 identifies pullbacks of underlying sets and abelian sheaves,
   and 03S2 identifies etale inverse image with restriction. The existing
   `etaleSetCartesianUnit_eq_iff` is applied to the actual cartesian object with
   the identity isomorphism, then the agreement-open criterion is applied to
   its first projection. Whole inverse image is equivalent to factorization
   through the open immersion by range containment and its lifting property.
   Checked empty U and empty pullback (both sides hold), s=t (W is top), identity
   base change (ordinary equality), and a singleton index (the original stage
   suffices). No compactness or limit hypothesis is concealed in the helper;
   it is strictly a sheaf-theoretic part of the target, with no eventual-stage
   conclusion. Independent `msearch.py` searches used LeanFinder's query
   "forgetful functor abelian group sheaves commutes with inverse image and
   adjunction unit", Loogle `CategoryTheory.sheafComposeNatIso`, and grep
   `PreservesSheafification|PreservesPointwiseLeftKanExtension`. Read local
   `SitePullbackAbelianUnderlying`, `EtaleModuleSetPullbackComparison`, and
   `ConstructibleIntegralCoefficientsBackward`, and searched lean/ with
   `unit.*equal.*open|abelian.*underlying|forget.*comparison|lanCompIsoOfPreserves`.
   The abstract underlying comparison has no unit equation; the module helper
   has different coefficients; the other abelian comparison is private and
   has no unit equation. None duplicates this public agreement-open statement.
4. **Route, imports and pruning: PASS.** Read the entire target from its equality
   hypothesis downward. The cofiltered tail is `Over (op i)`; its schemes are
   compact because their first projections are affine over compact U. Read
   the implemented `baseChangeDiagram`, `baseChangeCone`, their first-projection
   formulas, compactness instance, and `isLimitBaseChangeCone` in upstream
   `AffineTransitionLimit`. The latter uses initiality of `Over.forget` and
   pullback of the limiting cone, and introduces no new existence-based data.
   Read Mathlib `exists_map_eq_top` (lines 182-198): it requires precisely
   cofilteredness, compact stages, affine transitions and the whole-preimage
   hypothesis supplied here; it needs no compactness of W. The returned
   j.hom supplies the correctly oriented arrow i to j.left.unop. Both target
   proof imports are needed, and the helper's plain imports supply its two
   set-valued criteria and canonical sheafification comparison. The original
   public import remains required for the statement's coefficient instances.
   Read `dag/units/sk-thm-p1.json`, including every `realized` entry: this item
   realizes none of the fixed unit steps, so the shorter node-level route
   does not bypass one. Old `proof_deps` is empty: `No longer needed` correctly
   lists no removed dependency or module, while recording the abandoned plan.
5. **DAG agreement: PASS.** Compared the existing node with its repository
   version: only proof, proof_deps and proof_origin changed. The new helper
   node has the source, three search kinds (plus Loogle), created provenance,
   chapter/unit, blueprint ancestry, verbatim Lean signature and all requested
   fields. The target's dependencies are exactly the helper and the Mathlib
   open-containment leaf; its base-change construction is fully proved in
   upstream. The helper's dependencies are exactly the two existing set-valued
   criteria; its coefficient comparison is proved from Mathlib ingredients.
   The new helper's docstring spells out the complete argument and edge cases.

**Changes in this second reading:** no Lean or DAG repair was needed. Added this
independent review and replaced the report's cautious transitive-dependency
sentence with the observed axiom-probe result. One original hole is closed;
zero holes are added, zero split off, and no module is pruned.

## Second reading by S3

Independent review of the repaired delivery, 2026-10-13. This reading supersedes
 the historical review above, including its deleted-helper axiom probe.

1. **Visible declarations: PASS.** Compared the existing module and node with
   their repository versions. The module changes only two plain proof imports
   and the original theorem's proof. Independently compared the theorem signature
   as text: it is byte-identical, including all hypotheses and the conclusion.
   Existing docstrings and public imports are unchanged. The other module is new;
   there are no adapted modules, changed definitions, or interface change records.
2. **Proof and axioms: PASS.** Compiled both modules in import order using
   `lcompile.py`: 9.1 s and 2.7 s, with no errors or warnings. No delivered file
   contains `sorry`, an axiom, unsafe/opaque declaration, implementation escape,
   or definition with unproved data. Compiled fresh scratch copies with
   `#print axioms` for `isIso_abelian_forget_comparison`,
   `etale_abelian_unit_equal_open`, and
   `etale_inverse_image_unit_eventual_equality`: all three use only `propext`,
   `Classical.choice`, and `Quot.sound`. Read both repaired concrete calculations:
   restriction along the fully faithful sheaf inclusion, composition of
   adjunctions, the Kan-extension unit, and the sheafification unit give the
   displayed unit homomorphisms for sets and abelian groups. The subsequent
   naturality and factorization equations prove `hq`; `hfac` and `hvalue` then
   evaluate this canonical comparison on the original sections. Its injectivity
   legitimately reflects equality. The removed generic helper has not returned.
3. **New statements and search: PASS.** No statement is split off with a hole.
   The new proved agreement-open theorem isolates a strictly smaller part of the
   argument: it has no limiting system or eventual-stage assertion. Read Stacks
   [09XM](https://stacks.math.columbia.edu/tag/09XM),
   [03Q1](https://stacks.math.columbia.edu/tag/03Q1), and the restriction functors in
   [03S2](https://stacks.math.columbia.edu/tag/03S2). Checked the two set-valued
   criterion signatures against their actual applications. The final equivalence
   between open factorization and whole inverse image uses the open-immersion
   lift, not an invalid factorization through an arbitrary subscheme. Empty U,
   empty base change, identical sections, identity base change, and a singleton
   directed system introduce no exception. Independent msearch queries used
   LeanFinder on the equality locus under pullback, Loogle on
   `CategoryTheory.Functor.lanCompIsoOfPreserves`, and grep on the sheafification
   and Kan-extension factorization identities. Results supply ingredients, not
   this agreement-open theorem. Also searched local Lean and read
   `SitePullbackAbelianUnderlying`, `ConstructibleIntegralCoefficientsBackward`,
   and `EtaleModuleSetPullbackComparison`: their comparisons either lack the unit
   equation, are private, or have module coefficients. No duplicate public result
   was found; using their private declarations by import is unavailable.
4. **Route, imports and pruning: PASS.** The proof converts equality at the limit
   to whole inverse image of W, applies `exists_map_eq_top` to the explicitly
   constructed base-changed cone over `Over (op i)`, and converts back at the
   returned stage. Read the base-change definitions, limiting-cone proof,
   first-projection formulas and compactness instances, and Mathlib's
   `exists_map_eq_top` proof. Compactness comes from affine first projections
   over compact U; affine transitions and cofilteredness meet the leaf's exact
   hypotheses. The returned arrow is correctly `j.hom.unop : i ⟶ j.left.unop`.
   All added imports are proof-only and used. The existing public import supplies
   coefficient infrastructure needed to elaborate the signature. The original
   node's proof_deps was empty, so there is no omitted removed dependency.
   Read every `realized` entry of `dag/units/sk-thm-p1.json`: this item realizes
   none of the fixed unit steps, which the shorter argument does not replace.
   No module is pruned.
5. **DAG agreement: PASS.** Only proof, proof_deps and proof_origin changed in
   the existing node. Both dependency lists equal the union of their steps' uses
   and match the Lean argument: agreement open plus the Mathlib containment leaf
   for the item, and the two existing set-valued criteria for the helper. The
   coefficient calculation and base-change infrastructure are proved directly.
   The new node has the required provenance, source, searches, chapter/unit,
   blueprint ancestry and Lean record; independently checked its signature
   verbatim against the new module. Its docstring describes the full proof.

**Changes in this second reading:** added this current independent review only;
no Lean or DAG repair was needed. One original hole is closed, zero holes are
added, zero statements are split off with sorry, and no module is pruned.
