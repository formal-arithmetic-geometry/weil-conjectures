# Stage-1 report: det-prop-p1-adjunction-rational-unit-counit

## Files written

All files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `det-prop-p1-adjunction-rational-unit-counit.json`: existing parent target retained byte-for-byte in its `statement`; its proof is now a three-step assembly (under 3000 characters) of the extracted statements.
- `lem-sfb-rational-p1-localizing-preservation.json`: statement-only unsplit node, no Mathlib match; former six-step construction proof moved verbatim to `source.note`.
- `lem-sfb-rational-p1-unit-inversions.json`: statement-only unsplit node, no Mathlib match; former three-step construction proof moved verbatim to `source.note`.
- `lem-sfb-projective-normalized-unit-counit-restriction.json`: statement-only unsplit node, no Mathlib match; former seven-step construction proof moved verbatim to `source.note`.
- `citations.json`: verbatim statement quotes for every parent proof citation.
- `searches.jsonl`: the twelve inherited `msearch.py` records (three nodes, each LeanSearch, LeanFinder/Loogle, grep, and the alternate LeanSearch phrasing), retained with their original attribution.

## Lean declarations

- `lem-sfb-rational-p1-localizing-preservation` owns `AlgebraicGeometry.ProEtale.RationalP1.localizingPreservation` (sorried; requested separate module `Sheaf.Paper.RationalP1LocalizingPreservation`).
- `lem-sfb-rational-p1-unit-inversions` owns `AlgebraicGeometry.ProEtale.RationalP1.unitInversions` (sorried; requested separate module `Sheaf.Paper.RationalP1UnitInversions`).
- The recorded module `Sheaf.Paper.RationalP1UnitCounit` and these declarations are absent from the read clone's `lean/WeilConjectures/`; no Lean file was written or compiled.

## Attachments

No attachment is claimed. A search for the blueprint tag, both declaration names, and the relevant notions in `lean/WeilConjectures/` found no exact project declaration. The two ownership assignments above come from the released 2026-10-27 repair order.

## WANTED

None for the statement-level split. The unavailable recorded Lean module is reported above as a source-availability limitation, not treated as a finished proof.

## What was wrong and what changed

The live parent statement is unchanged, but the retained retry had all three extracted nodes marked `split` with proof arrays and had maintainer-owned `lean` fields on the two declaration nodes. The released repair order explicitly requires statement-only unsplit nodes for the two sorried declarations and says that every proof argument must move into `source.note`; it also requires the existing conditional construction node to lose its proof-bearing split status. I applied that order to all three extracted nodes: removed `proof`, `proof_deps`, `proof_origin`, and `lean`, set `status` to `unsplit`, removed stale child split metadata, and preserved every former proof text, cited node list, source place, and elementary flag in the corresponding note.

The parent `statement` was compared byte-for-byte with the live repository copy and was not changed. Its new proof has three short steps: preservation supplies domains and exactness; the fixed-inversion node plus the existing line and projection lemmas supplies the two inversion conditions; and the conditional normalized-construction node, specialized with the diagonal-class and trace statements, supplies the displayed unit, counit, naturality, and exactness. `proof_deps` is exactly the union of those uses. `split_report.lean_declarations` records the two requested declaration-to-node assignments.

## Not duplicates

- `lem-sfb-rational-p1-localizing-preservation` vs `det-proper-image-localizing-proper`: the existing node gives a general proper-image restriction tool; this node states the projective-line geometry, coefficient hypotheses, and simultaneous preservation of every required localizing category.
- `lem-sfb-rational-p1-localizing-preservation` vs `det-proper-base-change-unbounded-pullback`: that node concerns inverse-image behavior; this node includes the projective-line pushforward, twist, tensor, and domain checks.
- `lem-sfb-rational-p1-unit-inversions` vs `det-proper-base-change-unbounded-extension`: the existing extension node assumes generator invertibility; this node proves the canonical exchange and fixed twisted projection are invertible on the rational localizing category.
- `lem-sfb-rational-p1-unit-inversions` vs `def-sfb-rational-p1-unit-inversion-condition`: the latter only defines the conjunction of two `IsIso` predicates; this node proves both clauses for the named maps.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `def-sfb-projective-ambient-unit-counit-composites`: the definition gives ambient component formulas; this node states the conditional support, naturality, fullness, and uniqueness construction on arbitrary full subcategories.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `det-prop-p1-adjunction-rational-unit-counit`: the parent specializes this conditional statement to rational coefficients after proving its hypotheses; the conditional node is strictly more general and does not restate the rational target.

## Review by NI

I read `GOAL.md`, `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `roles/worker.md`, and delivery-errors sections B--E, then read the released repair note before touching the retained sandbox. The specified archive glob returned no prior directories. I compared the sandbox parent against the live repository and verified that its statement strings are identical. I read the chapter and unit records and the latest blueprint proof file. The live Lean search for the blueprint tag, `localizingPreservation`, and `unitInversions` returned no declaration, so there is no attachment.

For `lem-sfb-rational-p1-localizing-preservation`, I read its complete statement and its retained former proof. The statement introduces the primes, field, scheme, coefficients, projective-line fiber product, unbounded module categories, finite-constant-model localizing closures, and every preservation conclusion. The former six steps are copied into `source.note`: properness/Noetherianity, qcqs and the quasi-compact complement, separated finite-type hypotheses, coefficient and Tate conventions, the constant-model domain calculation, and unbounded exactness/localizing preservation. The step dependencies in that note are the exact statements previously cited, including the proper-image, pullback, tensor, Tate, and constructibility nodes. Its inherited searches contain LeanFinder, Loogle, grep, and an alternate LeanSearch query; all report no exact Mathlib theorem.

For `lem-sfb-rational-p1-unit-inversions`, I checked that the statement says precisely that the canonical self-cartesian exchange `β_M` and the fixed normalized twisted projection `Π` are isomorphisms for every object of the stated rational localizing category. The retained note preserves the three former arguments: preservation and coefficient identification, bounded rational proper base change extended to the localizing closure, and the localizing projection formula with the actual shifted Tate comparison. The parent assembly cites this statement only for those two named maps. Its inherited four search records likewise found no Mathlib match.

For `lem-sfb-projective-normalized-unit-counit-restriction`, I checked every hypothesis and conclusion in the statement: exact coefficient inverse images, the diagonal class and trace, the fixed canonical maps, full replete triangulated subcategories, restricted exact functors, both inversion predicates, the diagonal tensor isomorphism, the `Rp_{2*}RΔ_*` identity, normalized component formulas, naturality, and the explicit absence of triangle identities. Its former seven-step proof is preserved in `source.note`, including the open/closed conservativity argument, the adjunction-transpose identification of the actual diagonal map, pushforward composition, class insertion, inverse projection/trace contraction, both naturality equations, and componentwise uniqueness. The inherited searches found only generic category-theory results and no theorem constructing this normalized pair.

I opened the statements of every node used by the new parent proof. The preservation statement supplies the geometric and functor-domain facts claimed in parent step 1. The inversion statement supplies both fixed `IsIso` clauses; `lem-sfb-rational-p1-line-from-preservation` says the shifted line belongs to the localizing category under preservation, and `lem-sfb-rational-p1-localizing-projection` says the exact fixed left projection is invertible, so parent step 2 has both counit and unit hypotheses. The conditional statement supplies the diagonal tensor map, pushforward identity, normalized formulas, naturality, and exactness used in parent step 3; the diagonal coefficient and trace statements supply the rational `δ_Λ` and `Tr_q` and their identities. Every entry in `citations.json` is a verbatim substring of the cited statement.

I checked edge cases against the unchanged statements: empty `Y`, zero complexes, and the base `Y=Spec(k)` reduce the displayed maps to the corresponding zero or identity maps; the preservation statement does not assume `Y` proper; all arguments are degreewise for arbitrary unbounded objects; and the conditional node assumes full subcategories and exactness rather than silently deriving them. No statement dispute was found. No compiler, Lake build, Lean file edit, repository write, or launcher-file edit was made.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-pe-coefficient-origin-closed-direct-image`: the existing node concerns coefficient-origin direct-image support; this node constructs normalized unit/counit transformations under explicit projective-line hypotheses.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-closed-immersion-scalar-change`: the existing node is scalar change for a closed immersion; this node proves a diagonal tensor identification and normalized transformations on full derived subcategories.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-condensed-open-closed-recollement`: the existing node states recollement data; this node uses such data conditionally to construct and normalize projective-line components.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-integral-model-open-closed-pieces`: the existing node concerns integral-model open/closed pieces; this node concerns arbitrary coefficient diagrams, traces, and full subcategory unit/counit construction.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-abelian-closed-counit`: the existing node gives an abelian closed counit; this node gives derived diagonal support, normalized components, naturality, and uniqueness.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-abelian-closed-support`: the existing node gives abelian support vanishing; this node packages it with tensor, trace, and unit/counit formulas.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-closed-underived-projection`: the existing node concerns an underived projection; this node concerns arbitrary unbounded derived modules and normalized transformations.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-immersion-limit-preservation`: the existing node concerns limit preservation for immersions; this node constructs a derived diagonal tensor isomorphism and componentwise unique pair.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-inverse-image-limits-zariski-local`: the existing node is a Zariski-local inverse-image limit fact; this node is a global conditional projective-line construction.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-restriction-preserves-limits`: the existing node gives restriction-limit preservation; this node proves normalized unit/counit naturality and uniqueness after support arguments.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-ringed-closed-counit`: the existing node states the closed counit for ringed pro-etale modules; this node uses that ingredient to establish a diagonal tensor isomorphism and normalized pair.
- `lem-sfb-projective-normalized-unit-counit-restriction` vs `lem-weil-pbc-proetale-ringed-open-closed`: the existing node states open/closed exactness and support sequence; this node applies it in a broader conditional construction with trace and projection data.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sc-affine-noetherian-underlying-space`: the existing node concerns an affine Noetherian underlying space; this node proves all projective-line geometry, coefficient, and localizing-functor preservation clauses.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sc-components-open-injection`: the existing node concerns component openness/injection; this node concerns proper projective-line pushforward and pullback preservation on derived localizing categories.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sc-locnoeth-components-locally-finite`: the existing node concerns local finiteness of components; this node establishes the full projective-line domain and preservation package.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sc-noetherian-finite-irreducible-components`: the existing node concerns finite irreducible components; this node includes Noetherianity only as one part of a larger preservation theorem.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the existing node states Noetherianity of an open subscheme; this node uses that fact while also proving qcqs, coefficients, exactness, and localizing closure preservation.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sfb-noetherian-component-open`: the existing node concerns component openness; this node concerns the separated finite-type projective-line functor package.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sfb-noetherian-connected-components-open`: the existing node concerns connected-component openness; this node proves preservation of all required rational derived categories and functors.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sbc-constant-local-dimension-components`: the existing node concerns local dimensions of constant-model components; this node concerns proper push/pull, tensor, Tate, and unbounded localizing preservation.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-weil-pbc-irreducible-refinement-topological`: the existing node concerns topological irreducible refinements; this node proves a derived categorical preservation theorem with projective geometry.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-trf-normal-topologically-noetherian-components`: the existing node concerns components of a normal topologically Noetherian scheme; this node proves rational projective-line functor domains and preservation.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-sc-separated-over-affine-scheme-separated`: the existing node gives separatedness over an affine base; this node includes separatedness as one geometric check among all preservation hypotheses.
- `lem-sfb-rational-p1-localizing-preservation` vs `lem-dl-a1-locally-closed-stratum-separated-finite-type`: the existing node concerns separated finite-type strata; this node concerns global projective-line geometry, coefficients, and localizing functor preservation.
