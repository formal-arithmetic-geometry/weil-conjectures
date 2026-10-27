## Worker report

The module `Sheaf.AlgebraicGeometry.CanonicalProjOpenCoverGluing` states
`AlgebraicGeometry.Scheme.Modules.canonical_proj_open_cover_gluing`, with sorry proof.
It reuses the existing `Scheme.Modules.RelativeSectionAlgebra` affine-basis presentation
of the ordinary canonical section algebra. No algebra is chosen from a bare existence
statement and no new tensor, pullback, relative Proj or canonical-map notion is defined.
The two helpers `canonicalSectionOpenPull` and `RelativeSectionAlgebra.OpenComparison`
specify the restriction comparison belonging to this gluing statement.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{Z S : Scheme.{u}} (h : Z ⟶ S)`.
- Quasi-compact and separated: `[QuasiCompact h] [IsSeparated h]`. No finite-type,
  properness, flatness or absolute separatedness assumption is added.
- Invertible module: `(N : Z.Modules) [N.IsInvertible]`.
- Arbitrary affine open covering: `{I : Type v}`, `U : I → S.Opens`,
  `_hU : ∀ i, IsAffineOpen (U i)`, `_hcover : iSup U = ⊤`.
- The inverse-image scheme and restricted map are literally `(h ⁻¹ᵁ U i).toScheme`
  and `h ∣_ U i`. The restricted line module is
  `(tensorPullback (h ⁻¹ᵁ U i).ι).obj N`, the required tensor pullback.
- The given local canonical quasi-coherent graded section algebras are `A_local`.
  `RelativeSectionAlgebra.sectionEquiv` identifies degree n on each affine base
  open with the actual sections of the inverse-image tensor power. Its `smul`,
  `one`, `mul`, `restriction` fields fix the algebra and all restrictions.
  Its `data : GradedAlgebraData` is the existing equivalent quasi-coherent
  affine-basis encoding used by the project's canonical relative Proj.
- Evaluation is the existing `RelativeSectionAlgebra.evaluate`, defined using the
  unit of `tensorPullbackSectionAdjunction` and `boundaryPullbackPowIso`.
  `IsCanonicalMap` uses precisely this evaluation, including degree zero.
- Full local generation: `_hgen : ∀ i, (A_local i).GeneratesEverywhere`.
  This is the existing stalk criterion for the union of the positive-degree
  surjectivity loci to equal the whole source: the target stalk has rank one,
  and a section outside the maximal ideal times that stalk generates it.
- The local canonical maps and their open-immersion hypothesis are `r_local`,
  `_hcanonical` and `_hopen`. These are not arbitrary unconstrained maps.
- Existence of the global quasi-coherent canonical graded algebra is
  `∃ A : RelativeSectionAlgebra h N`. Its homogeneous components, products and
  unit are the actual direct-image tensor-power sections by the same fields.
  The total algebra is encoded on the affine basis by their graded direct sum;
  no assumption A_0 = O_S is made.
- The graded restriction isomorphisms and restricted evaluation identifications
  are `∀ i, ∃ D : A.OpenComparison (U i) (A_local i)`.
  `D.data` is the existing `PullbackData` along the open inclusion. It asserts
  coefficientwise base change, equivalently the isomorphism on restricted
  sheaves. `D.section_eq` fixes every homogeneous map by the actual tensor unit
  `1 ⊗ s`, canonical power comparison and restriction to the smaller open.
  Thus it is the canonical graded comparison, preserving products and unit
  by its graded-algebra maps; it identifies evaluations on every tensor
  generator `a ⊗ s`, since both evaluations send it to `a` times this section.
  This is a full map normalization, not an unspecified isomorphism class.
- The canonical relative-Proj restriction isomorphism is the existing
  `D.data.relProjIsoPullback`; its first projection is
  `D.data.relProjComparison`. The final displayed map equation identifies the
  restricted global map with the given local canonical map under that isomorphism.
- Global full generation is `A.GeneratesEverywhere`. Together with the given
  local full generation this also identifies the restricted generation loci:
  both are the whole inverse-image open. No extra tautological conjunct is added.
- The concluding ordinary scheme canonical open immersion is
  `∃ r : Z ⟶ A.data.relProj, A.IsCanonicalMap r ∧ IsOpenImmersion r`.

Dependencies read and used:

- `def-nagata-relative-proj`: `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`,
  `Scheme.GradedAlgebraData`, `relProj`, `relProjHom`, `relProjι` and
  `relProjRestrictIso`. The affine-basis input, not a second gluing interface, is used.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionAdjunction`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme` and `Scheme.Hom`.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, the existing
  localization tensor; powers use `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `tensorPow`, with zeroth power equal to the structure module.
- `def-sc-invertible-module`: the same Invertible module, `Scheme.Modules.IsInvertible`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  with `QuasiCompact` from Morphisms.QuasiCompact, rather than finite type.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`.
- `def-weil-pbc-graded-sheaf-structures`:
  `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`, `GradedSheafAlgebra`.
- `def-weil-pbc-quasi-coherent-algebra`:
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`,
  `Scheme.IsQuasiCoherentAlgebra` and `QuasiCoherentAlgebra`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  with `IsSeparated` from Morphisms.Separated; properness is not assumed.
- `lem-trf-space-line-module-proj-map`: `Sheaf.TraceFormula.SpaceLineModuleProjMap`,
  `AlgebraicSpace.space_line_module_proj_map`, especially its ordinary-scheme clause.
- Proof dependencies `lemma-nagata-relative-proj-exists` and
  `lemma-nagata-relative-proj-base-change-arbitrary`: RelativeProj.Basic, Universal
  and BaseChange; the latter supplies `PullbackData`, `relProjComparison` and
  `relProjIsoPullback`, actually used in the statement.
- Proof dependency `lem-weil-pbc-open-immersion-injective-local-source`: its exact
  mathlib_match `IsOpenImmersion.of_forall_source_exists` in Morphisms.OpenImmersion.
- Proof dependency `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  exposing the existing affine-local quasi-coherence predicate.

Definition-only helper interface, extracted without changing any definition body:
`Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap`,
`RelativeSectionAlgebra`, `.evaluate`, `.GeneratesEverywhere`, `.IsCanonicalMap`.
The definition node `def-sfb-relative-section-algebra-canonical-map` owns all four
of these definitions, including `GeneratesEverywhere` as its canonical-evaluation
full-generation predicate. The source criterion theorem module now publicly imports
the definitions-only module, and plainly imports this gluing result for its existing
proof dependency. The gluing module no longer imports the criterion theorem, directly
or transitively. This repairs the actual module direction rather than suppressing the
required proof import. The precise move and consumer edit are included in this packet.

Edge cases checked before writing: empty S and Z; empty cover (forces S empty);
empty opens within a nonempty cover; singleton and arbitrary infinite covers;
index universe independent of the scheme universe; degree zero and unit maps;
non-affine overlaps of affine opens; a degree-zero algebra larger than O_S;
no choice of finite cover or positive degree uniform over the whole base.
The assumptions require full positive-degree generation, so zero positive-degree
algebras on nonempty sources are correctly excluded by that assumption alone.

Sources read locally: morphisms.tex, lemma-characterize-relatively-ample,
(3) implies (5), Tag 01VJ; constructions.tex,
lemma-invertible-map-into-relative-proj, Tag 01O9, especially (3) and its proof.
The ordinary Zariski constructions agree with the node's specified source.

Searches:

1. msearch.py leanfinder: "Canonical section algebras of an invertible module restrict
   over an affine open cover and their canonical maps to relative Proj glue as an
   open immersion". Eight hits, including Proj.fromOfGlobalSections,
   fromOfGlobalSections_morphismRestrict, and chart open immersions. None states
   the relative sheaf section-algebra gluing assertion.
2. msearch.py loogle: "AlgebraicGeometry.Proj.fromOfGlobalSections,
   AlgebraicGeometry.IsOpenImmersion". Zero hits.
3. msearch.py grep: "sectionAlgebra|SectionAlgebra|section_algebra|generationLocus"
   in Mathlib/AlgebraicGeometry. Zero hits.
4. rg in both project roots for sectionAlgebra/SectionAlgebra/section_algebra and
   RelativeSectionAlgebra. Found the existing canonical section-algebra interface
   in SchemeAmpleCanonicalProjCriterion and reused it. Other hits concern space
   base change, graded evaluation, or specialized polarizations; no gluing theorem.
5. rg in both roots for the item id: no existing statement. rg in Mathlib,
   WeilConjectures, Sheaf and dag/lean_names_upstream.json for the three delivered
   names: no collisions.

No mathematical statement correction or new DAG notion is needed. No
STATEMENT-DISPUTED flag. This repair includes the dependency interface extraction
and consumer migration detailed below. The only postponed statements are the original
gluing theorem and the existing, unchanged criterion theorem; no new sorry was added.
All definitions have real data.

## Second reading by N9

The dispatcher instructs this worker not to start other agents; an independent
maintainer review follows delivery. This section records the worker's second pass,
not an independent-agent review. I reopened the node and the completed module and
checked the hypothesis and clause correspondence above. In particular I checked
that the local maps are constrained by IsCanonicalMap, the comparisons have their
actual section normalization, the conclusion includes full generation and global
open immersion, and no A_0 = O_S or affineness of overlaps was inserted. The degree-zero
comparison uses boundaryPullbackPowIso and the same normalized unit. No mismatch or
statement change was found in this second pass. The module and ownership defects of the first delivery are repaired below.


## Dependency modules

`def-sfb-relative-section-algebra-canonical-map`: §1(B) repair required by the immutable-head
review of 1fb9beba172e. Its previous Lean record pointed at
`Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`. Although its definitions
were mathematically correct, that module also states the theorem whose proof requires
the assigned gluing result. Using it from the gluing statement prevents the required
reverse proof import. The delivery moves `RelativeSectionAlgebra`, `.evaluate`,
`.GeneratesEverywhere` and `.IsCanonicalMap`, preserving their bodies, to
`Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap`. Their blueprint tags
now name the definition owner. The main record signature is the unchanged structure
signature, and lean.note explains both the unusable former location and the ownership
of GeneratesEverywhere. The latter is an auxiliary definition of this same canonical
evaluation: every point admits a positive-degree homogeneous section whose germ is
outside the maximal ideal times the tensor-power stalk, the existing full-generation
criterion of 01O9 and 01VJ for invertible L. This follows the return's explicit option
to put it in that node's declarations with lean.note. No new definition node is needed.

`lem-trf-scheme-ample-canonical-proj-criterion`: the associated consumer migration explicitly
required by the same return. Its module publicly imports the definitions-only module;
the four moved declarations are removed from its body and declaration-ownership list.
Its coproduct comparison definition and theorem, including their mathematical signatures
and bodies, are unchanged. The gluing module is now an ordinary proof import of this
criterion, so the existing proof dependency can actually be used. Its node differs only
in lean and the note records this narrowly scoped consumer edit. This is a consumer
migration, not a mathematical prerequisite of the gluing theorem; no false DAG edge is
added to make the criterion appear to be a prerequisite.

## Repair of return 1fb9beba172e

1. H2/H12, cycle and GeneratesEverywhere ownership: the four definitions were physically
   extracted into the definition-only owner module, with exactly the same signatures
   and bodies. GeneratesEverywhere now has its definition-node owner recorded and
   explained in that node's declarations and lean.note. The gluing result imports the
   new module and no longer the ampleness theorem module. The theorem consumer now
   reimports the definitions and can import the gluing proof prerequisite.
2. H2, missing owners: the item's stmt_deps gains the two already-landed definition
   nodes `def-sfb-relative-section-algebra-canonical-map` and
   `def-sc-tensor-pullback-power-comparison`, as explicitly required by the return.
   The former is repaired in this packet; the latter's existing upstream declaration
   `boundaryPullbackPowIso` is reused via a direct public import of its recorded module
   `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`.
   This is a substantive interface/ownership repair, not an unchanged re-push.

The prior delivered gluing signature was compared with the sandbox signature and is
unchanged. The source for the theorem consumer was reread from the current server using
`scompile.py --source Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion` before
extraction, so this is based on the current published source. Existing node metadata
were preserved from the current shared read clone; the delivery wrapper rebases the
owned delta on the current server branch. No direct repository Git command was used.


Source import-closure validation of the repaired packet: traversing imports from the
gluing module with all three sandbox replacements examined 4,186 modules and found
no path to SchemeAmpleCanonicalProjCriterion. The consumer's new proof import therefore
has the correct direction. Extraction validation also compared the four moved definition
bodies (ignoring only their updated blueprint docstring tags) and the remaining comparison
and theorem source suffix; both comparisons were identical.

Repair compilation: prescribed scompile.py compiled all three files together as separate
modules in dependency order, including the migrated theorem consumer with its new gluing
proof import. Exit code 0, no errors or non-sorry warnings. The server reported 348.4 s
elapsed for the initial definitions-module overlay job (including slot acquisition),
then 3.9 s for the gluing library module and 2.5 s for the consumer library module;
the actual per-file timeout setting was unchanged at 60 s.

## Delivery-tool refusal

The repaired three-module packet compiles successfully. The required dry run then
refused the consumer migration (exit 1, nothing pushed). It treats the consumer
node as outside the item's prerequisite closure, excludes its ownership record,
and then emits this enforced failure:

`(c) lean/Sheaf/AlgebraicGeometry/SchemeAmpleCanonicalProjCriterion.lean: no node of the delivery has it as lean.file (every module is the module of the item, of a new definition node or of a dependency node)`

The packet DOES contain that module's existing owner node with lean.file pointing
to it. It is excluded because this is a downstream consumer, not a prerequisite,
which is exactly why the return requires extraction. The consumer edit is explicitly
required by the return: "the theorem module re-imports it". Leaving that edit out
would leave duplicate declarations in the library; adding the theorem as a dependency
would create the forbidden DAG cycle. Neither is a valid repair. No launcher or
project tool was changed or bypassed. The completed repair is retained for a tool
update allowing this authorized consumer migration.

## Retained-repair retry

On the dispatcher retry, reread the current server criterion source through the prescribed
scompile.py --source command and compared it with the source used for extraction: identical.
The complete definitions extraction, consumer migration, ownership repair and added stmt_deps
are still present in the sandbox. Reran deliver2.py --no-push; its three-file compilation
passed, but current server preflight again excluded the downstream criterion owner record
and emitted the identical single enforced no-owner finding recorded above. Exit 1;
nothing pushed. The required consumer migration is still not admitted by the delivery
checker. No invalid dependency edge or tool bypass was introduced.

Retry 3: current server criterion source remains identical to the extraction source;
all three module ownership records and both added definition dependencies are retained.
The prescribed deliver2.py --no-push again completed its compilation phase and refused
preflight with the same single enforced (c) no-owner error for the required downstream
consumer module. It still excludes lem-trf-scheme-ample-canonical-proj-criterion from
the admissible node set despite its explicit lean.file record in this packet. Nothing
was pushed. The repair remains ready for a delivery-tool change admitting the consumer
migration explicitly requested by the maintainer's return.

Retry 4: current server criterion source still matches the extraction source. Reran the
prescribed dry run with all three modules and their owner records retained. Compilation
passed; server preflight again rejected only the required downstream consumer module
as having no delivery owner after excluding its node from the prerequisite closure.
The checker printed that the base had advanced and checked against the delivery base;
the enforced failure remains the same (c) no-owner error. Nothing was pushed.

Retry 5: checked current server source again (identical to the extraction source) and
reran deliver2.py --no-push. All three files passed the compilation phase. Preflight
again refused the required downstream consumer migration with exactly the single
(c) no-owner finding for SchemeAmpleCanonicalProjCriterion.lean, after excluding its
existing node from the admissible prerequisite closure. The file and its explicit
owner record are both in the staged packet. Nothing pushed. A tool change admitting
the explicitly authorized consumer migration is required; no tools were patched.


## Maintainer extraction landed; final repair packet

The current live source and owner records were reread on 2026-10-24. Maintenance
N9 1792851621 has now landed the four-definition extraction, GeneratesEverywhere
ownership, and criterion public reimport. The definitions module matches this
repair verbatim apart from the final blank line. The criterion comparison and
theorem remain unchanged; its gluing proof import is explicitly deferred until
the gluing module lands. The previously blocked consumer edits and definition
module/node copies have therefore been removed from the active delivery packet
and retained only in a sandbox archive. The preceding refusal/retry sections
record historical attempts, not the scope of this final packet.

This delivery now consists of the repaired gluing module, the item's lean record,
and its two added statement dependencies. It imports the landed definitions-only
module and the recorded tensor pullback comparison owner. All four helper
definitions have the live definition-node owner, and there is no import of the
criterion theorem module or reverse DAG edge. The mathematical signature remains
that independently reviewed at 1fb9beba172e.
