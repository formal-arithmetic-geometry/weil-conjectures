# Worker report: lem-sfb-qc-space-schematic-strata

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-qc-space-schematic-strata.json`: statement split in eleven source-based steps, with no new nodes and no Mathlib leaves. The inherited searches remain; five searches actually run by Q129 are appended.
- `citations.json`: one verbatim statement quotation for every node used by every numbered proof step.
- `report.md`: this report and signed review.

No other repository file is delivered. All work is in the designated sandbox. `searches.jsonl` records the actual searches. `write_split.py` is sandbox preparation only.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, schematic stratification, 0BBN, algebraic spaces, unordered configurations and distinct tuples found no declaration of this assertion. The hits on stratifications concern schemes or sheaves, and those on distinct tuples concern Cech complexes. No Mathlib declaration is a project attachment.

## WANTED

None. Every mathematical source used is in the read clone's Stacks source.

## Corrections and route

The statement is mathematically correct and is unchanged. I repaired doubled TeX backslashes in the inherited statement. This is a serialization/rendering correction, not a change of hypotheses or conclusion. The proof, proof dependencies, document proof origin, status and split report are now populated.

I read Stacks `decent-spaces.tex`, Tag 0BBN (`lemma-filter-quasi-compact`), including its entire configuration-space proof. The proof uses symmetric quotients of the distinct-tuple schemes, rather than bounded degree or a finite splitting filtration. The existing `lem-sfb-qcqs-space-splitting-filtration` and `lem-sfb-etale-atlas-distinct-tuple-geometry` both assume quasi-separatedness; I did not apply either to this unrestricted item. The restricted Chow-configuration node also assumes separated finite type over an affine base and cannot serve here.

I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` section and direct-image proof (3). The inherited auxiliary chain remains below that direct-image input; no unit step is replaced. `tools/blueprint_refs.py ancestor` returns a null ancestor for this item, so its existing null `from.node` and `via` chain are retained. Whole-blueprint searches for `schematic`, `0BBN`, `unordered`, and `configuration` found no equivalent blueprint statement. The configuration hits concern blowups of surfaces, not algebraic-space atlas configurations.

The Q129 Mathlib searches were LeanFinder with two different phrasings, Loogle `"AlgebraicSpace"`, a grep for `AlgebraicSpace|schematic.*strat|strat.*schem` in AlgebraicGeometry, and LeanSearch for schematic strata covering quasi-compact field points. I read all returned hits: they concern scheme covers, scheme quasi-compactness, affine charts, etale schemes and the algebra etale locus. Loogle and grep returned zero hits. The local Mathlib `Morphisms/QuasiCompact.lean` definition (line 43) and its permanence statements concern schemes and provide neither the unrestricted algebraic-space filtration nor its schematic differences. Therefore this item is not a Mathlib leaf. No new node or unperformed search was recorded.

## Not duplicates

No new nodes. Existing statements provide every geometric input. In particular the finite qcqs filtration is a different, more restricted assertion and is not used to restate the present item.

## Review by Q129

I checked the proof against delivery-errors B--E with the item and every cited node's statement open. Each citation is to the statement, not to a construction hidden in that node's proof. `citations.json` copies the statements verbatim so that both the needed assertion and its hypotheses remain inspectable. All steps have explicit uses and source places. No new statement-only nodes, new definitions, new source requests or compiler activity occur.

Step 1 uses `lem-a1-space-point-open-calculus` for continuity and surjectivity of the given scheme atlas, then `lem-sfb-qc-space-affine-etale-atlas` for an affine surjective etale atlas with no separation assumption. The first hypothesis supplied to that lemma is topological quasi-compactness, obtained by pulling an open cover back to the given quasi-compact atlas. I read Tag 03H6 (`spaces-properties.tex`, `lemma-quasi-compact-affine-cover`).

Step 2 uses affine-source separation for the absolute diagonal of U, closed-immersion base change, and exactly the open-and-closed diagonal clause of `lem-sfb-space-separated-etale-diagonal-complement`. The displayed scheme-test equality proves separatedness of U -> X; it does not assume X separated. This is the separation argument in the first paragraph of 0BBN, with Tag 03HK for the diagonal.

Step 3 uses scheme-test representability and etale permanence to build all F_p and their etale maps to X, separated base change/composition to prove their absolute separation, and the already closed/open atlas diagonal to construct the pairwise loci. Closed base change and the definition of open subspace supply their pullbacks; an open immersion is etale by `lem-weil-pbc-etale-composition-cancellation`. I checked p=1 explicitly, where no equality locus is removed.

Step 4 is a stated induction, not an invocation of the qcqs distinct-tuple node. The comparison lemma `lem-sfb-space-fibre-product-comparison` supplies separated local quasi-finiteness without its optional quasi-compactness clause: Stacks Tag 03KN(1), read in `spaces-morphisms.tex`. Scheme separated/lqf base change and `lem-a1-scheme-lqf-composition` carry the successor; `lem-sfb-space-separated-fp-composition` carries separated composition. `lem-a1-etale-space-locally-quasi-finite` covers the identity at the base. The affine tensor-product lemma makes U^p over Z affine. `lem-a1-space-separated-lqf-permanence` permits restriction to W_p, and `lem-sfb-separated-lqf-affine-finite-set` gives affine neighborhoods of finite subsets, without source quasi-compactness. I read Tag 07S0 (`more-morphisms.tex`, `lemma-separated-locally-quasi-finite-over-affine`). These are routine finite-product and restriction operations; no independent configuration theorem is being assumed.

Step 5 proves freeness on test schemes, including locally constant permutations, before applying `lem-sfb-admissible-free-finite-quotient`. Its statement supplies a separated scheme quotient, finite surjective etale quotient map, factorization into any fppf sheaf, and the algebraically closed point-orbit formula. The hypotheses are absolute separation from step 3 and affine neighborhoods of each finite orbit from step 4. I read Tags 07S6 (`proposition-finite-flat-equivalence-global`) and 0BBM (`lemma-quotient-separated`) in `spaces-properties.tex`. No invertibility of p! is imposed or used.

Step 6 checks representability using `lem-trf-space-representable-etale-scheme-tests`. On every scheme test, the surjective etale source cover W_H -> V_H and its etale composite to H satisfy `lem-sfb-scheme-etale-source-target-properties` for P=etale. That statement explicitly permits the surjective source chart and the identity target chart. The open factorization is exactly the conclusion of `lem-a1-etale-scheme-map-open-image`; no open-image existence is inferred from a definition. I checked the cited places 03EC, the etale-locality clauses of descent Tag 04R3 and `spaces-properties.tex` `lemma-etale-image-open` against their statements.

Step 7 uses `lem-weil-pbc-etale-fibre-discrete-separable-points`, read against Tag 02GL (`morphisms.tex`, `lemma-etale-over-field`), and the quotient node's explicit geometric orbit clause. Every finite separable extension of an algebraically closed field is that field, so the geometric fibre is a disjoint union of copies of Spec Omega. Ordered distinct tuples are the fibre-product definition; their permutation orbits are p-element subsets. The orbit formula is applied to the fibre at a fixed X(Omega)-point because the action is over X. Infinite fibres are allowed.

Step 8 uses the same etale fibre description to turn nonempty geometric fibres into Omega-points, and the statement of `lem-a1-space-point-open-calculus` to turn support inclusions into open-subfunctor inclusions. It does not infer any factorization through a reduced closed subset just from containment of point images. The resulting decreasing chain is the one in the second paragraph of 0BBN.

Step 9 uses exactly `lem-sfb-space-reduced-closed-support`: existence, reducedness, specified support, and representable closed base change. The latter proves that Z_p is a closed scheme in V_p. Scheme-test etale base-change permanence proves that Z_p -> T_p is surjective etale. The geometric membership computation gives exactly p sheets and therefore one p-element subset at every geometric point of T_p. The reduced support source is Tag 03IQ, read in `spaces-properties.tex`.

Step 10 checks separatedness on scheme tests by the closed absolute diagonal of V_p, then uses separated base change and the singleton-fibre clause of `lem-sfb-space-separated-etale-diagonal-complement`. The node really states the needed isomorphism, not merely an open-immersion criterion. I read Tag 05W5 in `spaces-morphisms.tex`. The resulting scheme is Z_p; reducedness follows from its isomorphism with the already reduced T_p. I made no assertion that arbitrary closed pullbacks are reduced.

Step 11 uses `lem-sfb-space-quasicompact-affine-tests` to pull the *given field map* back to the affine U. `lem-weil-pbc-affine-scheme-qcqs` supplies quasi-compact U and the quasi-separated affine field spectrum; `lem-weil-pbc-qcqs-morphism-permanence` supplies source quasi-compactness, the scheme map to Spec K being quasi-compact, and base change to an algebraic closure. I checked the underlying source places 03HD/03HF, 01K5 and the scheme permanence results. Thus the resulting etale geometric fibre is quasi-compact. Its singleton-component open cover is finite, giving a positive integer p by atlas surjectivity. No quasi-compactness of U -> X is used. This is the final paragraph of 0BBN, expressed through scheme pullbacks to avoid assuming a composition lemma not cited.

Small cases: for X empty, the affine atlas and every configuration and stratum can be empty; there are no field points to cover. For the identity atlas of an affine scheme, p=1 gives its reduction and all p>1 configurations are empty, so the schematic claim does not require X itself reduced. For a split n-sheet atlas, W_p is empty for p>n and the quotient fibre at p=n is a singleton. For infinitely many sheets over a geometric point, the point may remain in all U_p; the statement requires coverage only for quasi-compact field representatives, and step 11 proves why those have finitely many sheets. The argument never replaces 'quasi-compact field representative' by an unrestricted point or assumes X quasi-separated/Noetherian. Positive characteristic dividing p! is harmless: the free constant-group torsor is etale without an invertibility hypothesis.

The B checklist is satisfied by preserving the item statement and notions, correcting TeX serialization, and using exact Stacks places. The C checklist is satisfied by the explicit statement-level inputs above; no definitions are cited in place of a theorem. For D, the proof constructs configurations, takes actual quotients, proves their geometric fibre formula, constructs strata and proves coverage: no new node is a relabelled conclusion. For E, the restricted qcqs/Chow inputs were excluded, every application has its stated hypotheses, all fibre products and bases are identified, and there is no assertion that a map factors through a reduced closed subspace from image containment alone. Every proof step is below 2000 characters, and I checked that none conceals an additional non-elementary lemma absent from its uses.

## Unfinished work

None in the mathematical split. Server checks and the required delivery are recorded below when they complete.
