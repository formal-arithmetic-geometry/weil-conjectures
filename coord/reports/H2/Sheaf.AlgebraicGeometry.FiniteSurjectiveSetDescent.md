## What changed
The original theorem `AlgebraicGeometry.finiteSurjectiveSetDescent` keeps its complete
signature. Its proof now combines two strictly smaller obligations with a Lean proof of
the converse: every unit-pulled-back section is compatible. The converse uses the chosen
composition comparison's unit equation, cancellation of its fibre-product pasting
isomorphism, and dependent transport along `pullback.condition`. The compatibility
calculation follows the already proved private calculation in GabberH0EtaleCriterion;
that module is not imported because it depends on this item.

The definitions `AlgebraicGeometry.etaleSetDescentUnit` and
`AlgebraicGeometry.etaleSetDescentComparison` move into the injectivity module to avoid a
cyclic import. Their mathematical data and public names are preserved; the main module
publicly imports their new home. The lifting module is a proof-only import. The change
record is `coord/changes/finite-surjective-set-descent-definition-location.md`.

## Proved and sorry left
The original `AlgebraicGeometry.finiteSurjectiveSetDescent` is reduced by a complete Lean
proof with its signature unchanged. Injectivity is proved by
`AlgebraicGeometry.finiteSurjectiveSetDescent_injective`, using the existing inverse-image
germ theorem, finite geometric-point lifting, and the fully proved new theorem
`AlgebraicGeometry.etaleSetSection_ext_of_geometric_germs`. The reverse implication
(unit sections are compatible) is also proved directly in the main module.

Exactly one new sorry remains:
- `AlgebraicGeometry.finiteSurjectiveSetDescent_compatible_lift`, node
  `lem-weil-pbc-sets-finite-surjective-descent-equalizer`.

It states only existence of a lift for a compatible section, with its complete source-based
stalkwise argument in the docstring. The original injectivity auxiliary is proved, not a
renamed gap. The upstream theorem `AlgebraicGeometry.etaleSetInverseImageStalkGerm`
remains sorry in the existing library; it is used, not duplicated. No partial tactic proof
or definition contains a gap.

## No longer needed
The main module removes its proof-only imports
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`,
`Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`.
The composition-units module remains publicly available through the injectivity module.
The unused standalone sandbox definitions module and the duplicate auxiliary node are
not delivered.

The old parent proof dependencies no longer directly used by its Lean reduction are:
- `def-weil-algebraic-closure`
- `def-weil-geometric-point`
- `def-weil-pbc-category-colimit`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-geometric-stalks`
- `def-weil-surjective-morphism`
- `lem-weil-pbc-finite-composition`
- `lem-weil-pbc-finite-geometric-point-lift`
- `lem-weil-pbc-finite-morphism-permanence`
- `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`
- `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`
- `lem-weil-pbc-sets-etale-stalk-finite-limits`
- `lem-weil-pbc-sets-finite-pushforward-stalk`
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`

These are removed as direct edges of the parent only. They remain necessary for the
mathematical proofs of the split lifting obligation and injectivity proof, as their nodes record; no claim is
made that these modules are globally unreachable. The lifting module also removes its unused proof-only import
`Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk`; its named open theorem needs
no proof imports until its proof is supplied. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong
The earlier report described injectivity as sorry after its proof was completed. This
report now matches the compiled files. The old equalizer lemma postponed both directions of the equivalence; it is
now narrowed to compatible lifting, while the other direction is proved in Lean.
The definition relocation is documented in its change record, and the parent
proof metadata now describes the complete reduction. The new nodes had fragmentary statements, non-verbatim Lean
records, no real three-kind search record, and incorrect blueprint ancestry. These
were repaired. LeanSearch returned HTTP 500 during this reading and is recorded as
unavailable, not as a failed mathematical match.

## Earlier second reading (a previous round; superseded)
1. Compared every delivered module with the read-only repository. The sole existing
   theorem's signature is byte-for-byte unchanged. The definition relocation is declared
   in the change record, with old/new text and the downstream-user audit. Public names
   and mathematical meanings are preserved, and no target statement changes.
2. Compiled all delivered modules through lcompile, in import order. Inspected every
   declaration for forbidden escape mechanisms and direct gaps. Only the one named
   lifting theorem above retains a direct gap; definitions contain actual constructions. A scratch
   copy with `#print axioms` was checked for every delivered declaration, and deliver3's
   axiom probe also checks them. Transitive `sorryAx` is expected from the named gaps.
3. Read [Stacks 09Z3](https://stacks.math.columbia.edu/tag/09Z3) and
   [09Z2](https://stacks.math.columbia.edu/tag/09Z2). Checked the hypotheses finite,
   surjective, arbitrary set sheaf, and the two projection comparisons. Tested empty
   base and source (surjectivity forces both empty), identity morphism, singleton
   geometric fibre, several fibre points, and the empty sheaf. Injectivity uses a
   nonempty geometric fibre; compatible lifting uses the equalizer of the two coordinate
   maps, exactly as in 09Z3. Complete docstrings spell out germs, comparison compatibility,
   constant families, and descent to sections. The remaining obligations are strict parts
   of the argument, with neither a converse nor a uniqueness requirement in the lifting
   lemma. Searched Mathlib through LeanFinder, Loogle and grep, with different queries
   from the original worker, plus the repository and upstream sources; no exact theorem
   was found. The blueprint search found finite-pullback restriction descent and étale
   Galois descent, neither of which gives this arbitrary finite-surjective claim.
4. The target reduction now performs the composition-unit calculation in Lean. Removed
   unused imports and listed all old direct proof edges it no longer uses. The two new
   nodes retain the geometric-stalk route of the original proof. Read
   `dag/units/sk-thm-iff.json`: its realized statement and step still name
   `lemma-weil-pbc-property-iff-acyclicity`, and are unchanged. This delivery works below
   that unit and bypasses no realized unit step.
5. Read the parent and both new nodes alongside Lean. The parent proof and proof_deps
   now describe injectivity, compatible lifting, the unit calculation and pullback
   transport. Every new node has a self-contained statement, verbatim Lean signature,
   source, complete proof steps with dependency union, provenance, actual search records,
   chapter/unit, and the correct nearest blueprint ancestor. No cycle is introduced:
   each new node depends only on existing geometric tools, never the parent.

Changes made in this reading: removed the relabeled auxiliary and unused definitions
module; proved unit compatibility; separated only the lifting implication; restored
full docstrings, source/search records, self-contained node statements and blueprint
ancestry; updated the parent route; documented the definitions' relocation and users.

## New nodes
`lem-weil-pbc-sets-finite-surjective-descent-injective` records the proved injectivity
argument in `Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective`. Its only open
proof dependency is the existing inverse-image germ theorem.

`lem-weil-pbc-sets-sections-geometric-germ-ext` records the fully proved section
extensionality theorem in `Sheaf.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt`,
using algebraic closures, equality on a pointed refinement, and sheaf separatedness.

`lem-weil-pbc-sets-finite-surjective-descent-equalizer` records the remaining compatible
lifting theorem in `Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer`.
It asserts only the forward implication of the original equalizer equivalence.

Change record: `coord/changes/finite-surjective-set-descent-definition-location.md`.

Edge cases checked against the source argument: the identity morphism, an empty base
(the empty covering gives a unique section), and finite covers with more than one lift.
The lifting argument uses nonempty geometric fibres only when the base has a point.


## Second reading by H2
1. PASS. Compared the main module with the repository using diff and exact string
   comparisons: the existing theorem signature is byte-identical, and both definitions
   moved with byte-identical signatures, bodies and docstrings. The relocation is recorded
   in coord/changes/finite-surjective-set-descent-definition-location.md. The downstream
   uses in GabberH0EtaleInjective, GabberH0FiniteLift and GabberH0EtaleCriterion still
   obtain both names through the original import. No target statement or meaning changes.
2. PASS. Compiled all four delivered modules in import order through lcompile. There is
   exactly one direct sorry, the whole proof of finiteSurjectiveSetDescent_compatible_lift.
   No definition has a gap, and no forbidden declaration or escape mechanism occurs.
   Compiled a scratch import file with #print axioms for all six public declarations.
   etaleSetDescentUnit and etaleSetSection_ext_of_geometric_germs use only propext,
   Classical.choice and Quot.sound. The other four additionally use sorryAx, arising
   from the named lifting gap and existing inverse-image comparison/germ theorems.
   Thus the target is reduced, not yet axiom-free; injectivity has no new direct gap.
3. PASS. Independently checked the sole open lifting implication against
   https://stacks.math.columbia.edu/tag/09Z3 and
   https://stacks.math.columbia.edu/tag/09Z2. Read its complete stalkwise proof and node.
   For identity covers it is ordinary section lifting; for an empty base the empty
   cover forces a unique section; for a nonempty geometric fibre compatibility says
   all coordinates agree, including singleton and multiple-point fibres. An empty stalk
   over a nonempty fibre has no compatible family, so the implication remains valid.
   The lifting lemma omits injectivity and the converse and is strictly part of the item.
   Fresh LeanFinder search for finite-surjective compatible-section descent found only
   coherent-topology and affine-limit results. Qualified Loogle search
   CategoryTheory.Sheaf, Function.Injective found local injectivity/mono criteria, not
   this descent theorem (an initial unqualified Sheaf query was invalid).
   Grep for surjective descent found only fpqc descent of morphism properties.
   Repository/upstream searches found the downstream private unit calculation already
   used by the worker, and no replacement for the lifting theorem. The lifting proof
   requires a substantial equalizer/stalk construction and cannot be closed in a few minutes.
4. PASS after removing an unused import. The main proof closes injectivity by geometric
   lifting and germs, applies only the lifting implication, and proves unit compatibility
   by the chosen composition-unit equation and dependent transport along pullback.condition.
   Proof imports are private; public imports provide the statements or definitions.
   Removed the unused FinitePushforwardSetStalk import from the open lifting module.
   Checked all fourteen old parent proof edges removed by the reduction against
   No longer needed: every one is listed. They are removed only as direct parent edges,
   not claimed globally unreachable. Read dag/units/sk-thm-iff.json; its realized
   statement and step remain lemma-weil-pbc-property-iff-acyclicity. No unit is bypassed.
5. PASS. Read all four delivered nodes beside the Lean files. The existing node changes
   only lean, proof, proof_deps and proof_origin. Each proof_deps is precisely the union
   of its proof steps' uses. New nodes include source, self-contained statement,
   documented proof, provenance, searches, creation record, blueprint ancestry,
   chapter/unit and matching verbatim Lean signatures. The parent names the two smaller
   obligations and its actual composition/transport calculation; the proved helpers
   match their germ and separatedness arguments. No dependency points back to the parent.

Changes in this second reading: removed the unused lifting-module proof import; corrected
an obsolete two-gap count in the earlier reading; appended this independent five-point
review. Existing correct proofs, signatures and node routes were retained.
