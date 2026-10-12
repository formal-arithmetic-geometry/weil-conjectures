## What changed

Replaced the earlier sandbox attempt with a reduction of
`AlgebraicGeometry.properPerfect_compactTests` to three independent subarguments.
The existing theorem signature and docstring are unchanged. The main proof chooses
small representatives of all compact objects, applies proper perfect preservation
of compactness to their images, and transfers Hom injectivity and surjectivity
through each representative isomorphism. Detection by all compact objects then
proves the requested isomorphism assertion.

Each remaining subargument has one new module and one DAG node. The parent node's
proof, proof dependencies, and proof origin now describe the actual Lean argument.
The auxiliary modules retain the existing geometric/generation inputs as their
proof dependencies. Localization transport for arbitrary derived universes, and
the compact-implies-perfect direction of Stacks Tag 09M1, are explicitly included
in their proof descriptions. No definition, existing signature, or target changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.properPerfect_compactTests`
(`lem-sc-proper-perfect-compact-tests`). Its proof has no direct `sorry`.

Added three holes, each the whole proof of a named public theorem:

- `AlgebraicGeometry.derivedQCoh_compact_representatives`
  (`lem-sc-derived-qcoh-compact-representatives`), in
  `Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives`.
- `AlgebraicGeometry.properPerfect_preserves_compact`
  (`lem-sc-proper-perfect-preserves-compact`), in
  `Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact`.
- `AlgebraicGeometry.derivedQCoh_compact_detection`
  (`lem-sc-derived-qcoh-compact-detection`), in
  `Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection`.

This is a decomposition, not an axiom-free proof: one hole closed and three added
(net minus two). None of the new statements restates the parent. The first has no
pushforward or detection assertion; the second concerns one arbitrary compact
object and constructs no family; the third has no pushforward or small family.
The main proof genuinely combines them and proves representative transport.

All four modules compile with lcompile.py. The empty scheme, the zero object,
identity morphisms, and different derived universes were checked against the
mathematical argument: no nonempty family assumption or common-universe hypothesis
was introduced. The representative theorem includes the zero object; detection
uses every compact object, including all shifts of every perfect generator.

## No longer needed

No original dependency node or module is pruned from the overall argument.
Removed these direct proof imports from the parent, relocating their use to the
new subarguments:

- `Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration`
  (`lem-pc-derived-qcoh-perfect-generation`).
- `Sheaf.AlgebraicGeometry.PerfectObjectCompact`
  (`lem-pc-perfect-object-compact`).
- `Sheaf.AlgebraicGeometry.ProperPerfectDirectImagePerfect`
  (`lem-pc-proper-perfect-direct-image-perfect`).
- `Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives`
  (`lem-pc-perfect-complexes-compact-set`).
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
  (`prop-pur-kinjective-resolutions-exist`).
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`
  (`lem-pc-derived-category-locally-small`).

Discarded the uncommitted earlier `ProperPerfectCompactTestsCore` module and its
`lem-sc-proper-perfect-compact-family` and `lem-sc-proper-perfect-detects` nodes.
They are not library nodes and should not be delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier `properPerfect_detects S G` asserted detection for an arbitrary family,
with no generation or representative coverage hypothesis. Taking S empty makes
its premise vacuous, so it would assert every morphism is invertible. On a nonempty
affine scheme the zero endomorphism of the nonzero structure sheaf contradicts
that conclusion. The earlier compact-family theorem allowed the empty family and
therefore did not justify detection. Neither discarded assertion is used here.
Their node statements and proof descriptions were also placeholders, both holes
were placed in one module, the parent node still described the old dependency
route, and the report contained a premature second-reading section. All were
replaced or removed.

The planned existing perfect-complex declarations require models on all opens
and, for direct image, a shared Hom universe. The parent has neither hypothesis.
Its node already prescribes localization transport to small-Hom models; the new
subarguments isolate that still-unformalized transport rather than silently add
hypotheses. Using compact objects directly additionally requires the converse
of Tag 09M1, which `perfectObjectCompact` alone does not state. This converse is
explicitly part of the representative and preservation subarguments.

The unit route is preserved: these are refinements below
`sk-thm-picard-duality`, whose realization record attaches no unit step to this
module. Source texts checked: Stacks Tags 0A9R, 0B6G, 09M1, 09IS. LeanSearch
returned HTTP 500 and is honestly recorded unavailable. LeanFinder and Mathlib
source searches found no matching scheme-level theorem. Mathlib's Yoneda
criterion requires all objects, so it alone cannot supply compact detection.

## New nodes

`lem-sc-derived-qcoh-compact-representatives` states small representatives of all
compact quasi-coherent derived objects, including compactness of the representatives.
It refines the parent's set-of-perfect-representatives step using both implications
of Tag 09M1 and explicit localization transport.

`lem-sc-proper-perfect-preserves-compact` states preservation of one compact
object under the given proper perfect pushforward. It isolates the parent's
geometric direct-image step, including unequal derived universes and eR transport.

`lem-sc-derived-qcoh-compact-detection` states detection by all compact objects.
Its cone-orthogonality proof uses shifted perfect compact objects and perfect
localizing generation; it assumes no arbitrary small family detects anything.

Each node has a complete self-contained statement, proof steps, actual searches,
source, blueprint ancestry, and its single-theorem module record. No change record
is necessary because all existing statements, definitions, and visibility stay
identical.

## Second reading by R1

1. **Visible declarations: pass.** Read the diff of the parent module against the
repository. The only changes are six private proof imports replaced by three
private proof imports, and the body of `properPerfect_compactTests`. Its signature
and original declaration docstring are byte-for-byte identical. There are no new
definitions, adapted existing modules, changed targets, or interface changes.
The three auxiliary modules are new. No change record is required.

2. **Lean proof and axioms: pass as a decomposition.** Compiled all four modules
in import order using lcompile.py, with no errors or warnings. Independently
compiled scratch copies with `#print axioms` for all four declarations: each
reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Exactly
three direct sorries remain, namely the three auxiliary theorems listed above;
the parent contains none. No forbidden declaration or attribute, hollow data,
or unproved arbitrary witness used in a definition occurs. The representative
family is unpacked inside a proposition proof. For injectivity, precomposition
with e.inv transports the equality to the representative and cancellation gives
the result. For surjectivity, lifting e.inv composed with b and precomposing
with e.hom gives b by the inverse identities.

3. **Split statements: pass.** Read the three new Lean statements and node files
alongside [Tag 09M1](https://stacks.math.columbia.edu/tag/09M1),
[Tag 09IS](https://stacks.math.columbia.edu/tag/09IS),
[Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G), and
[Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R). Representatives require only
Noetherian X and its derived model; compact equals perfect on this qcqs scheme,
so the small perfect representative argument gives their coverage and compactness.
Preservation retains precisely properness, both Noetherian hypotheses, the
stalkwise finite Tor bound, R, and eR; it requires neither a right adjoint nor a
common derived Hom universe. Detection tests every compact object, so in
particular every shift of every perfect object. The exact Hom sequence kills
the cone, and the localizing-closure argument kills its identity. These are
three different strictly smaller tasks; none repeats the parent's combined
existence-and-detection statement.

Tested the reasoning on the empty scheme (zero category), Spec of a field
(nonzero perfect objects and their shifts), the zero object, identity f, an
identity morphism g, and different wX/wY. Testing only the zero object on a
nonzero scheme does not satisfy representative coverage or the all-compact
hypothesis, so there is no vacuous detection error. The small model has
universe-u Hom sets; this is essential to the representative-set argument.
Read `grothendieckAbelian_and_functorial_kInjective_resolutions` and
`HasDerivedCategory.ofHasKInjectiveResolutions` to check the stated normalization
route, and read the existing perfect-representative, compactness, direct-image,
and perfect-generation declarations. Their extra open-model and shared-universe
requirements are addressed by normalization in the new proof docstrings, not
added to the parent.

Repeated searches with different terms: Mathlib grep for IsCompactObject,
compact/perfect, and Skeleton/Small; LeanFinder for zero-cone detection by shifted
Hom from a compact generator; and Loogle for the qualified Yoneda bijectivity
criterion. Also searched lean/Sheaf, lean/WeilConjectures, and the upstream
WeilConjectures sources. The Skeleton results require already-established
essential smallness. Yoneda requires all objects. Neither proves these
scheme-level assertions. The existing `schemeDerivedQCoh_compactlyGenerated`
is relevant to detection but still requires the shift/compactness and exact
triangle argument; no ready generic isomorphism-detection lemma was found.
The first Loogle Skeleton query did not resolve its identifier, and is not
evidence of absence. No split hole could be closed in a few minutes.

4. **Top-down route and pruning: pass.** The parent uses all three intermediate
theorems directly and performs the representative transport itself. All original
proof dependencies are retained in the auxiliary arguments; the six removed
direct imports and their node names are listed under No longer needed. No module
is claimed pruned from the import closure. Read
`dag/units/sk-thm-picard-duality.json`: its realized statement and step lists are
empty and it assigns no unit realization to the parent. This decomposition is
below that unit, retains the proper-perfect direct-image and perfect-generation
route, and bypasses no realized unit step.

5. **DAG agreement: pass after repair.** The parent proof steps and proof_deps
are exactly the three intermediate theorem applications plus the elementary
representative transport written in Lean. Each new node has its own theorem,
source, complete proof description, statement dependencies, proof dependencies,
proof origin, actual search records, creation fields, blueprint ancestry,
chapter/unit, and Lean record. Original node metadata outside stage-3 ownership
is preserved. The three auxiliary nodes retain the original geometric and
generation dependencies needed by their stated proof routes.

**Second-reader changes:** added source and blueprint references to the three
new module docstrings and replaced whitespace-collapsed Lean statement records
in all four delivered nodes with the verbatim multiline signatures. No proof or
statement needed repair; the original one-hole-to-three-hole decomposition
remains, with net minus two holes and no closure pruning.
