## Worker report

The module `Sheaf.TraceFormula.AmpleSchemeTestLinePreparation` states
`AlgebraicGeometry.AlgebraicSpace.exists_ampleSchemeTestLinePreparation`. Its result
is an existential `P : AmpleSchemeTestLinePreparation ...` with its normalized
etale-test comparison: a bundled witness of exactly the
geometric and module data required by the node. Every definition has explicit data;
the existence theorem alone has proof `sorry`. The bundle's proof-valued fields are
requirements on the witness, not additional existence assumptions. The local
formula helpers and the comparison predicate belong to these output clauses and
introduce no independently chosen line module, map, or equivalence.

Hypotheses, in the order of the node:

- `S : Scheme.{u}`, `F Y : AlgebraicSpace S`, and `f : F ⟶ Y` give the base,
  algebraic spaces, and morphism over it.
- `M : F.Modules` and `hM : F.IsLineModule M` give exactly a small-etale line module.
- `I : Type v` is independent of `u`; `Yᵢ : I → Y.EtaleSite` gives scheme charts
  with representable etale maps to `Y`. `hcover : IsJointlySurjective ...` is joint
  surjectivity on field-valued point classes, allowing field extension, without a
  finiteness assumption or an objectwise global-lifting requirement.
- `Fᵢ : I → F.EtaleSite`, `pᵢ`, and `hpb` specify the scheme fibre products
  `F ×_Y Y_i`. Their being etale over `F` follows already from base change of the
  given etale charts; bundling that property in the site object adds no assumption.
- The expression `(F.schemeRestriction (Fᵢ i)).obj M` is exactly `M_i`, using the
  recorded restriction-to-opens construction. `hample` quantifies over every
  affine open `V` of `Y_i` and asserts absolute `IsAmple` of its pullback to the
  inverse-image open. The existential invertibility proof only supplies the
  proof argument of `IsAmple`. Tensor pullback along the open immersion is the
  ordinary restriction via the recorded unit-normalized open comparison.
- `T : Over S`, `h : yoneda.obj T ⟶ Y.obj.obj` is an arbitrary scheme test, without
  a flatness, etaleness, affine, nonempty, or quasi-compactness assumption.

Output clauses, using fields of `AmpleSchemeTestLinePreparation`:

- `X`, `toF`, `toT`, `cartesian` give the algebraic space `F ×_Y T` with its actual
  cartesian square of presheaves. The sheaf/algebraic-space structures are carried
  by `X`; no separate arbitrary replacement of the fibre product is used.
- `Tᵢ`, `tY`, `tT`, `baseCartesian` represent `Y_i ×_Y T` by schemes;
  `baseEtale` and `baseSurjective` give the jointly surjective etale base cover.
- `Xᵢ`, `xF`, `xT`, `sourceCartesian`, `sourceToF`, and `schemeCartesian` give
  scheme charts of `X`, both displayed fibre-product descriptions, and the
  compatible projections to `F_i`. `Xᵢ` already carries etaleness to `X`, and
  `sourceSurjective` supplies joint surjectivity. A cartesian square is the
  choice-free universal-property formulation of each fibre product/isomorphism.
- `original_invertible` states invertibility of the original `M_i`. `invertible`
  states invertibility of exactly `N_i = tensorPullback (xF i).left (M_i)`.
  `ample` quantifies over every affine open of `T_i` and asserts absolute
  ampleness of the pullback of this same `N_i` to its inverse image.
- `original` is the existing `OrdinaryEtaleIdentification` between ordinary
  tensor-pullback sections and restrictions of `M`. `original_normalized` fixes
  it on every Zariski open by the actual tensor unit `1 ⊗ s`. It includes sections
  not extending globally. The quantified open inclusion and its inverse-image
  top equation are the canonical open-subscheme equations, not an added
  hypothesis on the scheme. Such inclusions exist for every open, so this
  characterization is not vacuous, including for the empty open.
- `R`, `r₁`, `r₂`, `overlapCartesian` give `F_i ×_F F_j`. `α` and
  `original_transitions` characterize its transition as the identity between the
  two restrictions of the same `M`, in the normalized section coordinates.
- `D`, `d₁`, `d₂`, `newOverlapCartesian` give `X_i ×_X X_j`.
  `overlapMap` with its two equations gives the actual induced map to `R`.
  `transition_eq` fixes `β` to the pullback of `α` using `ampleTestPulledTransition`;
  that definition is the existing `atlasTransitionOver` between the two
  unit-normalized `tensorSectionsComp` comparisons. It allows no arbitrary
  transition isomorphism. `diagonal` is identity after the diagonal pullback,
  not a claim that the self-overlap is itself the diagonal. `cocycle` is equality
  on every test of the triple fibre product, with all six leg equations retained.
- `N`, `isLine`, `identification`, `induces` give the descended line module with
  local ordinary/etale identifications inducing exactly `β`.
- `unique`, through `AmpleTestUniqueRealization`, quantifies over every other line module with identifications inducing
  the same transitions and asserts `∃! z : N ≅ N'` with the prescribed section
  equations. Thus uniqueness retains identifications, rather than asserting
  uniqueness of a bare unframed line module.
- `quasiCompact` and `separated` use exactly the two recorded presheaf-map
  predicates owned by `def-sfb-space-quasi-compact-presheaf-map` and
  `def-sfb-presheaf-map-separated-diagonal`, applied to `toT`.
- `etale_toF` supplies etaleness of `X → F` when `h` is etale.
  The theorem's final `AmpleTestEtaleComparison` clause asserts the unique isomorphism
  `N ≅ (AlgebraicSpace.pullback toF hp).obj M` with the local formula obtained
  from `original`, `identification`, and the normalized tensor composition.
  `AmpleTestEtaleComparison` includes each leg equality explicitly. `HEq` in its
  section equation compares the two canonical restriction encodings without
  expanding their definitionally equal section carrier types. It does not
  replace the isomorphism or its local normalization by mere existence.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `Modules`, `IsLineModule`, `IsEtale`, `pullback`, `etaleMap`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`
  and `schemeOpens`, with their actual restriction/structure-ring construction.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the upstream
  `tensorPullback` reexport, `tensorPullbackSection`, and normalized adjunction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent`:
  `OrdinaryEtaleIdentification`, `atlasTransitionOver`. The existing index-small
  `InvertibleAtlasDescentDatum` is not copied or imposed on our arbitrary index
  type: the output contains its diagonal and cocycle clauses explicitly.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`: `tensorSectionsComp`
  and `tensorSectionsUnit`, owned by
  `def-trf-tensor-sections-unit-composition` (existing definitions).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: existing
  `IsQuasiCompactPresheafMap` and `IsSeparatedPresheafMap`, retained by the repaired
  dependency's public import. The repaired locality statement is listed below.

All recorded proof-dependency modules with available declarations are imported,
including fibre-product/cover stability, invertible tensor pullback, relative
ampleness base change, the two scheme/etale comparisons, open restriction,
canonical-Proj preparation, and scheme base-change permanence. The theorem
docstring carries the node's eight proof steps with these node names. For a
large covering index, descent can first refine to a small atlas and then extend
its identifications to the remaining members by full faithfulness; no universe
identification or restriction is made in the statement.

Edge cases checked: the empty index set can cover only an empty target and no
`Nonempty I` is imposed; empty schemes and empty overlap schemes are retained;
self-overlaps need not be diagonals; arbitrary infinite/redundant covers and
independent index universes are allowed; every affine open is quantified over,
not only a chosen basis; arbitrary non-flat test maps are allowed; characteristic
is unrestricted. The tensor and restriction normalizations keep identity and
arbitrary etale-test cases, and uniqueness includes automorphisms by requiring
preservation of all identifications.

Searches made:

- `msearch.py leanfinder`: “Line module preparation on arbitrary scheme test of
  locally polarized algebraic space: descend tensor pullback line bundles along
  etale charts and quasi compact separated projection”. Eight hits concerned
  scheme limits, scheme pullback carriers, and local representability; none
  states this algebraic-space preparation.
- `msearch.py loogle`: `IsAmple, tensorPullback, IsPullback`. Zero hits, with
  `unknown identifier 'IsAmple'` reported by that search index; not evidence
  that the project lacks the notion (the recorded project declaration is used).
- `msearch.py grep`: `ample.*[Pp]reparation|[Ll]ine.*[Dd]escent` in Mathlib's
  `AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and prospective
  declaration names: no existing statement. Concept searches found the existing
  scheme relative-ample base-change theorem, algebraic-space invertible descent,
  normalized comparison theorem, and the parent `representable_and_ample_of_etale_cover`.
  The parent asserts representability and final ampleness, not this node's
  arbitrary-test tensor descent, specified transitions, uniqueness, and comparison.
  Their full signatures and docstrings were read and their interfaces reused.

The item's mathematical statement, proof and mathematical Lean signature are
unchanged; the terminology citation is corrected as recorded below. Its statement dependencies now name the definition owners listed in
the repair section below; the descent and locality theorems remain proof dependencies.
There is no mathematical statement dispute.

## New nodes

`def-trf-tensor-sections-unit-composition` owns the existing plain definitions
`AlgebraicGeometry.Scheme.Modules.tensorSectionsComp` and
`AlgebraicGeometry.Scheme.Modules.tensorSectionsUnit` in
`WeilConjectures.AlgebraicGeometry.EtaleTensorSections`, with `existing: true`
and no new Lean module. The former is the actual natural isomorphism from
successive tensor pullback to pullback along the composite, defined by
conjugating the inverse pushforward composition comparison under the specified
canonical adjunctions. The latter is the actual additive global-section unit,
evaluated at the whole target and transported along preimage-top. Its source is
Stacks 03DR, equation (35.8.1), and the canonical tensor adjunction used there.
The definition covers arbitrary schemes and modules, including zero modules,
empty schemes, identity maps and arbitrary non-etale maps. It asserts no
functoriality theorem. Universes are explicitly those of the existing signatures.

Searches are recorded from the launcher results in its `mathlib_searches`:
LeanSearch returned eight general categorical pullback/unit hits; LeanFinder
returned eight general module pullback/free-module hits; Mathlib grep for the
two exact names returned zero. Project declaration grep found exactly their
existing definitions at EtaleTensorSections.lean lines 45 and 54. Definition-node
text grep found uses, and inspection of all definition-node Lean declaration
lists found no owner of either name. Blueprint searches for both exact names
returned zero matches. `def-weil-pbc-etale-tensor-sections-restriction` owns only
`etaleTensorSectionsRestriction`. The distinct existing
`def-pc-tensor-pullback-composition-iso` owns the reverse-oriented comparison
with a triangle equation; the new node reuses that notion in its source-level
specification and binds the two concrete section-oriented maps requested by
the return. No existing construction is copied or changed.

The formerly proposed `def-trf-algebraic-space-ordinary-etale-identification`
is omitted on rebase: current main now has the exact definition owner
`def-sfb-ordinary-etale-identification`. The item reuses that landed node and
uses its exact declarations through the existing public descent-module import.
A direct import of the extracted module alongside the verified descent build
collided with that build's older copies. Following the duplicate-import repair
instructions, only the descent module is imported; its current source reexports
`Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentification`. The four definitions, their types and data
are unchanged. There is no duplicated ordinary-identification definition node.

## Repair of returned delivery

Baseline: independent return of immutable head `39e4bfa645eb`. I compared the
retained item with the current main node: the mathematical statement and proof
are identical. The current main node has no Lean record. The two requested
qc/separated definition nodes have since landed and are reused unchanged.

- H2, ordinary/etale identifications: add the definition node above, cite it in
  `stmt_deps`, remove `lem-trf-algebraic-space-invertible-descent` from
  `stmt_deps`, and retain that theorem in `proof_deps`.
- H2, qc and separated predicates: replace the statement dependency
  `lem-trf-space-qc-separated-etale-local` with the landed definition owners
  `def-sfb-space-quasi-compact-presheaf-map` and
  `def-sfb-presheaf-map-separated-diagonal`. The locality theorem remains in
  `proof_deps`, with the already reviewed point-cover interface repair retained.
  The direct public import now names the predicates' module; the point-cover
  theorem module is a plain proof import.
- Earlier minor, tensor composition (superseded by the current H2 repair below):
  the previous delivery cited `lem-sc-etale-qcoherent-presheaf-functorial` in
  `stmt_deps` and directly imported
  `WeilConjectures.AlgebraicGeometry.EtaleTensorSections` publicly. I read the
  owner's full statement and the actual `tensorSectionsComp`/`tensorSectionsUnit`
  signatures, docstrings and unit-normalized data.

The helper source module is reused as requested; none of its four declarations
is moved or modified. Apart from the import classification, both delivered Lean
files retain the previously reviewed mathematics.

## Repair of returned head a799091a0d34

H2 is repaired by adding the definition owner
`def-trf-tensor-sections-unit-composition` above and citing it directly in the
item's `stmt_deps` instead of `lem-sc-etale-qcoherent-presheaf-functorial`.
The functoriality theorem appears only in the item's `proof_deps`; the new
pure definition node has empty `proof` and `proof_deps`.

The retained ordinary-identification definition proposal initially had both its
statement citation and `stmt_deps` switched to the new tensor-map owner, as
requested. During dry run the existing-binding check exposed a subsequent
current-main extraction: the four helpers are now owned by the landed
`def-sfb-ordinary-etale-identification` in
`Sheaf.AlgebraicGeometry.OrdinaryEtaleIdentification`, instead of being declared
in the descent module. Following the instruction to use already landed owners,
I removed our redundant unlanded definition proposal and cite that exact landed
owner. No changes to the landed node's metadata are part of this packet. The
new tensor-map owner remains a direct item dependency; its two exact names are
checked by the existing-definition compiler probe. No Lean body or mathematical
hypothesis/conclusion changes. Both the old verified descent build and its
current source expose these same definitions. The direct extraction import
was tested and removed after a duplicate-declaration error, so the existing
descent-module import alone remains.

I compared the retained packet to current main: the item still has no Lean
record, the point-cover repair remains a lean-only dependency repair, and
current main does not contain the new tensor-map definition node. The earlier
qc/separated owners, proof-only descent/locality dependencies, citation
correction and full citer audit are preserved. The first dry-run failure was
repaired by rebasing ownership to the landed extracted declaration, rather than
creating a duplicate or changing any published source.

## Repair of returned head a7da3638c2ff

The return found that `lem-sc-etale-qcoherent-presheaf-functorial` was listed
in `proof_deps` but not in any proof step's `uses`. Step 3 now explicitly uses
its identity/composition laws for ordinary tensor-section restrictions to obtain
naturality of the sectionwise identifications on localized etale tests, including
composite test maps. The step's `uses` includes that theorem and its prose names
the conclusion used. The Lean theorem's proof docstring records the same use.
The theorem remains a proof dependency only; the existing-definition owner of
the two maps remains in `stmt_deps`.

I checked the set equality between `proof_deps` and the union of every proof
step's `uses`; they now agree exactly. The current-main proof is retained
verbatim in `statement_change.old_proof`, because this packet now edits proof
prose as well as the previously recorded metadata. Current main still has no
Lean record for the item, and the prior citation-only correction and its sole
citer audit remain applicable. No theorem signature, definition body,
hypothesis or conclusion changes.

## Statement corrected

This is a reference-only correction forced by the returned H2 request: the final
qc/separated terminology now cites the two landed definition nodes in place of
the locality theorem. No mathematical clause or Lean signature changes. The
`statement_change` records the old statement verbatim and the old statement
dependencies, together with the source and full citer audit. The sole citer is
`lem-trf-algebraic-space-ample-local` (`holds: true`): its first proof step uses
exactly the same arbitrary-test preparation, local ample invertible modules,
qc/separated projection and etale comparison. Its use is unaffected. No citer
is edited. The descent and locality theorems remain in `proof_deps`. The
current ownership repair also records `old_proof` and `old_proof_deps` from main because the
functoriality theorem is now added only for the proof; no existing proof
dependency is removed. This is a continuation of the same unlanded citation
correction, not a new mathematical statement change.

## Dependency modules

`lem-trf-space-qc-separated-etale-local`: section 1(B) repair in
`Sheaf.TraceFormula.SpaceQCSeparatedPointCover`, declaration
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_separated_etaleLocal_pointCover`.
The recorded `IsJointlySurjectiveEtaleFamily` requires every scheme-valued section
to lift globally through one family member. It does not express joint
surjectivity. For example, `Spec ℂ → Spec ℝ` is surjective etale but the identity
section of `Spec ℝ` has no such lift. I read the live server source with
`scompile.py --source` and confirmed that this was not merely a stale local copy.
The new module publicly imports and retains the existing quasi-compact and
separated predicates, and states the node's equivalence for genuinely jointly
surjective etale charts using the published `IsJointlySurjective`. Only the
node's `lean` record changes, with `lean.note` explaining the defect. Sources read:
`spaces-morphisms.tex`, `lemma-quasi-compact-local` (03KG) and
`lemma-separated-local` (03KM). Its docstring spells out the node's four proof
steps. Proof-dependency nodes for closed-immersion cover descent and finite atlas
assembly have no recorded Lean modules, so there are no such imports to add;
the other recorded proof-dependency modules are imported.

## Validation

The corrected proof-step metadata passes direct exact set equality against all
19 `proof_deps`. The archived old proof, old proof dependencies and old statement
match current main; the complete citer audit still contains only
`lem-trf-algebraic-space-ample-local`, with `holds: true`.

Both Lean files compile cleanly via `scompile.py`; the main-file sandbox and
library checks took 14.2 s and 10.0 s. The prescribed `deliver2.py --no-push`
dry run passed server preflight and compilation at commit `8fb19df8e7b`,
including the existing-definition probe. Final dry run and delivery repeat the
checks with this validation report. No errors or unexpected warnings remain.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
