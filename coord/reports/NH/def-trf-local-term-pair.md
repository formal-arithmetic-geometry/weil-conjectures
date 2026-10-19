# Worker report: def-trf-local-term-pair

## Files written

- `dag/nodes/sec-trace-formula/def-trf-local-term-pair.json`: definition, split; no Mathlib match. Added the direct coefficient-conventions citation/dependency, completed blueprint search metadata and recorded all six actual Mathlib searches.
- `citations.json`: `[]`. This item is a definition, with no proof steps; its inputs are statement dependencies, as stages/1-dag.md §3.2 requires.
- `report.md`: this report. No new nodes, no Mathlib leaves, no unit or chapter edits.

## Attachments

None. Searches of project Lean by the exact node tag and by `localTerm`, `local_term`, `restricted pairing`, `opposite pair`, and `Lefschetz–Verdier` led to `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Pairing.lean`. `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm` at line 409 requires `[IsProper aE]`, so it does not state the item's definition for nonproper ambient support. `supportedPairing` at line 355 supplies the pairing, not all clauses of this item. The `traceClass` docstring at lines 378–385 explicitly says its comparison with `supportedPairing` along the fixed-scheme/intersection isomorphism is not formalized. No partial declaration is being attached. The upstream master is reference material only.

## WANTED

None for this definitional split. Its source is the available blueprint; no external theorem is newly introduced or attributed to an unread source.

## Problems found and changes

The imported mathematical definition agrees with `literature/blueprint/master/blueprint/sec-trace-formula/sk-d-local-term/def-trf-local-term-pair.md` and with the current `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-local-term/def-trf-local-term-pair.md`. The coefficient conventions were mentioned without a direct reference: added `[def-trf-coefficient-conventions]` and the corresponding `stmt_deps` entry. No coefficient category, admissibility convention, formula or mathematical hypothesis was changed. The other six inputs already exist and suffice; manufacturing separate restriction, integral, or diagonal-specialization nodes would duplicate them or merely restate clauses.

There is a source-version discrepancy worth preserving for the next reader: the recorded unit `dag/units/sk-d-local-term.json` and the master unit explicitly allow nonproper ambient support, as does the current detailed definition. The current main-20261015 `_section.md` instead presents the ambient-proper idempotent formula. This is a restricted presentation, not a reason to impose ambient properness on the detailed node. The recorded unit and the current detailed node give the same restriction-then-integration construction used here. I did not change the unit or route.

## Unfinished work

None in this one-level definition split. The existing dependencies remain their own items. No Lean was written and no compiler, Lake or build tool was run. This sandbox is for the independent second reader; nothing is pushed by this worker.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for `local-term`, `restricted section`, `opposite pair`, `local terms` and the item's title found the existing inputs and nearby statements. `def-trf-local-term` defines the operation on an arbitrary section but not the opposite-pair input. `def-trf-supported-pairing` constructs that input and abbreviates its local term, but does not give this entire restriction/diagonal/point definition. `sk-d-local-term` presents the ambient-proper idempotent formulation in its node statement, whereas this item expressly permits nonproper ambient support. No other blueprint node states exactly the entire item, so `blueprint.same_as` is empty; the imported `from` stays null.

## Review by NH

I read both detailed blueprint versions named above, the master and current main unit texts, the recorded chapter/unit, and the statements of every dependency. This is a definition rather than a theorem, so its audit is by construction clauses rather than numbered proof steps. There are no new statements and no unchecked proof-step citations hidden in `citations.json`.

For the coefficient and input clause, `def-trf-coefficient-conventions` gives the finite ring A = O_E/varpi_E^n and the finite-Tor constructible category. `def-trf-correspondence-between-pairs` specifies the orientations c:C→Y×X and d:D→X×Y, the swap of d, and E=C×_(Y×X)D, so the intersection is over the right product. Its last paragraph explicitly identifies the diagonal specialization with Fix(c). `def-trf-supported-pairing` gives the actual morphism A_E→omega_E and states its exceptional-admissibility assumptions. These hypotheses are inherited by the item's explicit use of its notation; the pairing is not postulated for arbitrary unsupported inputs.

For the restriction clause, I checked `def-trf-local-term`: its restricted-section paragraph gives precisely A_B→Lj_B* A_E→Lj_B* omega_E→omega_B, with open purity and dualizing composition, and explicitly says neither B nor E must be proper. Thus this item applies an existing construction to the pairing section; it neither cites a mere definition for an unstated purity theorem nor needs a new restriction lemma. The necessary dualizing/admissibility conventions are those of that input definition.

For the scalar clause, the same node defines LT_B(sigma) as the integral on B only when B is proper. `def-trf-integration` states the integration map Hom(A_B,omega_B)→A and gives its adjunction-unit/counit composite, under separated finite-type, proper and exceptional-admissibility hypotheses. The item uses exactly those inputs and never integrates over a nonproper E. No global trace formula or component-sum theorem is needed.

For the diagonal clause, `def-trf-correspondence` supplies the endocorrespondence notion, while `lem-trf-trace-class-diagonal-pairing` states exactly the equality of Borel–Moore sections <u,1_K> = Tr_c(u), with no sign or twist and under its stated exceptional-admissibility hypotheses. This is the already-named comparison used by the source, not a new lemma about the present definition. Applying the same restriction and integration operations to that equality gives the displayed specialization; no additional non-elementary fact is used. All diagonal expressions are read under the hypotheses of that explicitly cited comparison, just as in the source. `def-trf-local-term` supplies the resulting endocorrespondence notation and its Frobenius reduced-point convention.

I checked small cases: B=E when E is proper gives the original integral; B empty is allowed and yields the integral of the unique zero section; for E=A^1_k disjoint union Spec k and B=Spec k the definition remains meaningful although E is not proper (one can take diagonal identity correspondences on E). If B=A^1_k the restriction still exists but the scalar integral is not asserted. An arbitrary isolated nonreduced point is not silently identified with Spec k: the final notation refers only to reduced clopen point components, and the input local-term node states the Frobenius fixed-scheme theorem that supplies these components. Thus the empty case, nonproper ambient case and reduced-point qualification have not been lost.

For delivery-errors B–E: no new nodes require standalone statements, Stacks tags, or leaf-file lines; the TeX and import flags were preserved. Each construction operation is supplied by an opened existing statement, so C1/C4 do not hide an uncited fact. There is no relabelled auxiliary clause, no new proof route, and no change to a target. All actual Mathlib searches are recorded verbatim in the node and in `searches.jsonl`. Both semantic phrasings returned ordinary sheaf/open-set facts, LeanSearch returned clopen topology and idempotent facts, Loogle found no localTerm name, and the targeted AlgebraicGeometry grep had no hits. The broad grep hits were Lefschetz principle or Verdier-localization references, not this definition. I corrected only the missing direct coefficient dependency and incomplete split metadata.


## Second reading by NH

I independently opened the item and all seven statement dependencies, both detailed blueprint versions of `def-trf-local-term-pair`, the recorded `sk-d-local-term` unit, both unit sources, the chapter record and current chapter source, and `Pairing.lean` in the read-only slopmaster2 source. The detailed definition is identical in master (order 2336) and main-20261015 (order 2680), apart from front matter; the delivered addition merely names the existing coefficient-conventions input. No Stacks tag is named as this definition's source, and no Stacks theorem or prohibited SGA route is introduced.

- Input clause: checked against `def-trf-coefficient-conventions`, `def-trf-correspondence-between-pairs`, and the current `blueprint_update.statement` of `def-trf-supported-pairing`; PASS: finite coefficients with n >= 1, finite-Tor coefficients, separated finite-type schemes, the swapped opposite map, and the pairing's exceptional-admissibility data are the cited inputs. The coefficient field E in the conventions and the support E(C,D) are distinguished by context, as in the source.
- Restriction clause (there is no numbered proof step): checked against the restricted-sections paragraph of `def-trf-local-term`; PASS: its actual statement gives A_B -> Lj_B* A_E -> Lj_B* omega_E -> omega_B, including open purity and dualizing composition, with no properness requirement. Thus no theorem is inferred just from the name of a definition.
- Scalar clause: checked against `def-trf-local-term` and the current integration statement; PASS: only the clopen B is integrated, and it is proper, separated of finite type, with the dualizing/admissibility data of those inputs. Ambient E is not integrated. This also agrees with the recorded unit; the current unit's ambient-proper idempotent presentation is a restriction, not a replacement for the unchanged detailed definition.
- Diagonal clause: checked against the final paragraph of `def-trf-correspondence-between-pairs`, `def-trf-correspondence`, and the complete statement of `lem-trf-trace-class-diagonal-pairing`; PASS: swapping the diagonal fixes it and the fiber product is Fix(c); the comparison supplies equality in Hom(A_F,omega_F), with no sign or twist, under its explicitly required exceptional-admissibility data. Restriction sends equal morphisms to equal morphisms, and application of the same integration map preserves equality; these are elementary operations on that cited equality, not a new comparison claim.
- Point clause: checked against the point-components paragraph of `def-trf-local-term`; PASS: the notation uses a reduced clopen Spec k component of a Frobenius fixed scheme. It does not replace an arbitrary nonreduced isolated point by Spec k.
- Formal proof steps: none, correctly, because the item defines the composite of existing operations (stages/1-dag.md section 3.2). `proof`, `proof_deps`, and `citations.json` remain empty; there are no step citations requiring quotes.
- New nodes: none; B1–B7 and pruning of proposed auxiliary nodes have no instances. I independently searched all DAG node titles for local-term/restricted-pairing variants and opened the relevant existing definitions. The general local-term definition, supported-pairing definition, and ambient-proper unit do not duplicate this entire definition; no extra node or Mathlib leaf is warranted.

Small cases checked: B empty admits restriction and has the zero scalar composite through the zero sections on the empty scheme; B=E is allowed when E is proper; E=A^1_k disjoint union Spec k with B=Spec k shows why proper ambient support must not be added; B=A^1_k permits restriction but not the asserted scalar operation. Zero coefficient morphisms give zero through the pairing recipe's tensor/composition maps. For n=1 the coefficient ring is the residue field and all maps retain their stated types; n=0 is excluded by the coefficient conventions. For X=C=D=Spec k the diagonal is the identity and restriction to the full point is the identity restriction, consistent with the displayed specialization. No counterexample or type fault was found.

Independent source inspection confirms `supportedPairing` at `Pairing.lean:354` returns only the Borel–Moore section, while `localTerm` at line 409 assumes `[IsProper aE]`; neither is an exact declaration of the full definition here. The trace-class docstring at lines 378–386 says its comparison along the fixed/intersection isomorphism is not formalized, so no source declaration is being treated as a finished proof.

Changes made in this reading:

- Added three actual independent Mathlib-search records, with the queries and outcomes also logged by `msearch.py`: dualizing-complex integration, Borel–Moore homology restriction/counit, and a source grep using those terms. The first semantic search returned scheme structure-sheaf facts; the second returned profinite/clopen locally constant-function facts; the grep had no hits. None states this definition.
- Added this clause-by-clause second-reading record and edge-case audit. The mathematical statement, dependencies, source, original worker sections, and empty citation list are correct and were preserved.
