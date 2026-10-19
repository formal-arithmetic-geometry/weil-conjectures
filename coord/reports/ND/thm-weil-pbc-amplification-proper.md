# Stage-1 report: thm-weil-pbc-amplification-proper

## Files written

- `dag/nodes/sec-proper-base-change/thm-weil-pbc-amplification-proper.json`: split item; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-uniform-perfect-quotient-bound.json`: statement-only commutative-algebra tool; unsplit, no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-normalized-constructible-local-effectivity.json`: statement-only local-effectivity tool; unsplit, no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-exchange-tensor-coherence.json`: statement-only ringed-topos coherence tool; unsplit, no Mathlib match.
- `citations.json`: full verbatim statements for each citation, indexed by proof step.

## Attachments

None. Searching the target id/tag and amplification, witness and tower terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration giving this conjunction. Upstream master is reference material, not attachment evidence.

## WANTED:

WANTED: a published bounded finite-type (not finite-Tor) extension of the local-model argument of Stacks 09C3/09C6/09C7, for `lem-weil-pbc-normalized-constructible-local-effectivity`. The local Stacks sources are present and read, but their finite-Tor assumption must not be silently dropped; the new node records the required extension explicitly as an agent assembly and remains unsplit.

## Source error

The imported proof (b) calls $P_n$ perfect for tensoring over $P_{n+1}$. The datum only supplies perfectness over $A$. For $A=\mathbf Z_\ell$, $I=(\ell)$, $P_1=\mathbf F_\ell$ is not perfect over $P_2=\mathbf Z/\ell^2$: the periodic free resolution with maps multiplication by $\ell$ yields nonzero $\operatorname{Tor}_i^{P_2}(P_1,P_1)$ for every $i\geq0$. The replacement uses the proper torsion projection formula, existing `lem-kun-0f0g`, whose statement and actual Stacks source 0F0G allow arbitrary coefficient complexes. Neither the item statement nor its coefficient datum is weakened.

The imported proof (c) also does not justify its conclusion: levelwise constructibility and etale origins alone give neither a common stratification nor a common bounded local complex. Those extra data are precisely what the already-reviewed tower definition requires. The revised split exposes local effectivity as a separate generic statement with a normalized derived tower and a common cohomological interval as hypotheses. It is a dictionary theorem about one tower, without a morphism or a functor, not a restatement of proper tower preservation.

## Not duplicates

lem-weil-pbc-normalized-constructible-local-effectivity vs lem-weil-proetale-dbc-triangulated: the existing statement only proves closure of intrinsic finite-level constructible cohomology under triangles and shifts; it asserts neither etale origin nor common integral local-model effectivity for normalized coefficient towers.
lem-weil-pbc-normalized-constructible-local-effectivity vs lem-sf-proetale-constructible-origin: the existing node is a finite-level comparison restricted to finite extension residue rings over the fixed finite-field datum; the new criterion constructs common integral local models for general normalized adic-datum towers.

lem-weil-pbc-uniform-perfect-quotient-bound vs thm-weil-pbc-amplification-proper: a bound on projective resolutions of finite quotient rings is independent of schemes and all four functors; it is strictly smaller than AMP/WIT/TOW.
lem-weil-pbc-normalized-constructible-local-effectivity vs thm-weil-pbc-amplification-proper: the new node turns normalized finite-level data with a common interval into common local models on a single Noetherian scheme; it asserts no preservation by any functor.
lem-weil-pbc-normalized-constructible-local-effectivity vs lem-weil-pbc-reconstruction-uniform-tower: reconstruction starts with common local models and takes their limit, whereas the new node constructs the missing common models from normalized uniformly bounded constructible levels.
lem-weil-pbc-normalized-constructible-local-effectivity vs lem-coef-normalized-dvr-effectivity: the existing node only identifies reductions of the inverse limit for DVR coefficients and explicitly asserts no constructibility or boundedness; it supplies no common stratification or local complexes.
lem-weil-pbc-normalized-constructible-local-effectivity vs def-weil-pbc-bounded-constructible-tower: the existing definition names the required model data but does not assert their existence from finite-level hypotheses.
lem-weil-pbc-normalized-constructible-local-effectivity vs prop-weil-pbc-preservation-constructible: the existing proposition asserts preservation of a complete constructible category and depends on this item, so citing it would be circular.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lemma-weil-pbc-completed-exchange-coherence: the existing node concerns naturality and pasting of the completed exchange, not tensor compatibility in a square of ringed topoi.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lem-weil-pbc-finite-level-rectangle: the existing node concerns the four particular finite-level corners, not the etale-to-proetale comparison square or a general coefficient complex.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing node only asserts the scheme-cartesian-square case with the blueprint projection arrows; the new node allows arbitrary commutative squares of ringed topoi, needed for the comparison morphisms.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lem-kun-proj-formula-natural: the existing statement is restricted to a cartesian square of schemes on small etale sites. The comparison square has proetale and etale topoi and is not that square.

lem-weil-pbc-normalized-constructible-local-effectivity vs prop-weil-pbc-levelwise-truncations: the existing DVR theorem starts with local models and discusses truncations under Tor compatibility; it does not produce local models from a normalized bounded tower.
lem-weil-pbc-normalized-constructible-local-effectivity vs def-weil-pbc-tower-preservation: TOW is a predicate requiring functorial preservation, whereas the new node is a criterion for the existence of local models for one tower, with no functor.
lem-weil-pbc-normalized-constructible-local-effectivity vs lem-weil-pbc-pullback-preserves-bounded-constructible: the existing lemma concerns one finite coefficient ring and finite-level pullback only.
lem-weil-pbc-normalized-constructible-local-effectivity vs def-weil-pbc-qbar-category: the existing definition forms a category of finite extension coefficient stages after rationalization; it gives no integral local models.
lem-weil-pbc-normalized-constructible-local-effectivity vs prop-weil-pbc-restriction-direct-image: the existing statement restricts a finite-level direct image under FIN, without tower effectivity.
lem-weil-pbc-normalized-constructible-local-effectivity vs prop-weil-pbc-amplification-consequences: the existing statement gives amplitude and constructibility at each finite level under AMP, but not common local models across levels.
lem-weil-pbc-normalized-constructible-local-effectivity vs prop-weil-pbc-descent-functors: the existing statement concerns descent of scalar-compatible finite-extension functors to the rational algebraic-closure coefficient category, not effectivity over ideal powers.
lem-weil-pbc-normalized-constructible-local-effectivity vs def-weil-pbc-finite-level-amplification: the existing definition gives the finite-level predicate AMP and asserts no common tower models.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the latter asserts the tensor pullback isomorphism, not its compatibility with the projection and exchange maps of a square.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lem-kun-inverse-image-monoidal: the latter asserts only monoidality of a scheme inverse image on etale sites, not the exchange/projection square for general topoi.
lem-weil-pbc-ringed-exchange-tensor-coherence vs lem-pur-derived-pullback-tensor-iso: the existing statement is tensor pullback coherence for the specified l-adic coefficient stages; it does not assert the projection/exchange diagram for general ringed topoi.

## Review by ND

I read the item, chapter and unit records, the blueprint's full proof (a)-(c), and the cited node statements. I read the finite-type adic-sheaf statements 09BU/09BV/09BW/09BX, including the preceding non-Noetherian counterexample explaining why the Noetherian hypothesis matters, and Stacks 095U (proper torsion cohomological dimension), 0GL0 (constructibility of shriek), 0F0G (proper torsion projection formula), 0E48 (projection/exchange tensor diagram), 09C1/09C2/09C3/09C6/09C7 (constructible and adic local-model statements), 099N (direct image and completion), 09AV (pseudo-coherent normalized coefficient systems), and 090V (Auslander-Buchsbaum). The sources for the three new tools distinguish a literal source statement from an assembly or extension. In particular I did not label the finite-type local-effectivity extension as the finite-Tor theorem 09C7 itself.

Step 1 uses the actual statement of `lem-sc-fibre-dimension-after-base-change` for locally finite-type maps, not the curve-only dimension node. Properness supplies locally finite type; taking the supremum uses the general local-dimension node, including empty fibres. The annihilator calculation is evaluation on 1 in A/I and passage to I^n; no extra torsion hypothesis is added.

Step 2 takes exactly FIN with bound 2e from the proper finiteness node for both maps, and exact triangulated interval preservation from the pullback node. The AMP definition says exactly these two things, so this step is only the assembly of its two clauses.

Step 3 uses the torsion-ring projection formula over P_{n+1}, the qcqs comparison theorem and the general derived tensor pullback isomorphism. It explicitly uses the new 0E48 ringed-topos coherence statement to make reduction compatible with comparison, rather than inferring coefficient naturality from same-ring naturality in L. Properness supplies the comparison theorem's qcqs assumption. Step 4 uses the general tensor pullback isomorphism for the two ordinary finite pullbacks, the comparison-pullback isomorphism for witnesses, and writes the normalization/cocycle formula out. Together these steps realize WIT, without claiming that compatibility of the special four corner maps alone suffices for arbitrary towers.

Step 5 uses the full current tower definition, including completed coefficient local terms. The new uniform projective-resolution bound is needed to give all reductions one interval even though the terms are not assumed flat. Flat constant-to-completed scalar extension is cited separately; the proof does not identify their ambient categories. AMP's consequences then give common output intervals and constructibility for all levels.

Step 6 uses the derived direct-image-limits node for strict evaluations. It separately checks completed-coefficient tower pullback on arbitrary supplied quotient-level objects: its K-flat construction and flat finite-quotient coefficient identities yield the displayed scalar-extension calculation. This fills the gap left by the completed-pullback definition, whose evaluation sentence only discusses reduction towers. Naturality makes this calculation a calculation on the given transition maps. The new local-effectivity node then supplies exactly the extra common local-model data that finite-level bounds do not supply. Its hypotheses are normalization, cocycle, constructibility and the common interval already obtained, so no preservation theorem is applied circularly.

The common-resolution tool can be checked locally at the finitely many maximal ideals containing I: nonzero localized P_n have finite length, depth zero, and finite projective dimension. Auslander-Buchsbaum makes their dimensions equal to the corresponding depth of A, independent of n. Away from V(I) the quotients vanish. The local-global criterion for finite modules gives the global finite projective-resolution bound. The zero-ring/unit-ideal case is vacuous with r=0; I=0 gives projective quotients in degree zero. The actual Mathlib search found the local-global criterion as an ingredient, not the depth calculation or the whole conclusion.

For the local-effectivity tool, 09BU/09BX provide finite-type adic sheaf stratification and local constancy without the finite-Tor restriction. The intended next split is to choose a constructibility stratification at finite level, pass to weakly contractible proetale covers and lift finite generators and relations compatibly through nilpotent coefficient quotients, using the pseudo-coherent system construction of 09AV rather than asserting projectivity of the terms. Uniform cohomological bounds allow a bounded truncation with a finite-type end syzygy; this is the non-finite-Tor extension left explicitly to that node. Small cases checked are the zero tower, a constant finite-ring tower (I=0), the reduction tower of a finite module over a completed DVR including torsion modules, and free towers. The criterion explicitly retains both uniform bounds and derived normalization, so it does not claim that arbitrary independently constructible levels have common local models. The general coherence tool reduces to the identity diagram for identity maps and does not require any exchange arrow to be invertible.

## What remains

The three new tools are intentionally statement-only and unsplit. No Lean file, compiler or Lake tool was used. Only the sandbox contains authored project files; the delivery helper is used solely for its authorized dry run. The first tentative citation run rejected short quotes; they have been replaced by complete verbatim statements after the mathematical repair.

## Final citation review by ND

I checked the canonical direct-image comparison node as well as the existence comparison: its explicit counit equation identifies the comparison with the exchange morphism needed by the generic tensor diagram. Step 3 now cites that named map, the finite-level etale-origin definition, derived full faithfulness and exact conservative sheaf comparison. These justify lifting normalization to the bounded etale witnesses, including when the quotient is not perfect over the preceding quotient.

I also read Stacks 09AL in proetale.tex, lines 5356-5385. It states the constructible derived comparison for any Noetherian coefficient ring. The existing lem-sf-proetale-constructible-origin assumes coefficients O_E/varpi_E^n and the global finite-field datum, so it cannot justify arbitrary P_n here. The generic local-effectivity tool now states its finite-level etale-origin consequence explicitly, starting with intrinsic constructible cohomology, and names 09AL for this part. Step 5 invokes it on the normalized input tower before applying AMP; step 6 invokes its common-model conclusion on the output towers. This removes an implicit change between two meanings of bounded constructible.

lem-weil-pbc-normalized-constructible-local-effectivity vs lem-sf-proetale-constructible-origin: the existing statement has specific finite extension residue coefficients and a finite-field datum, and asserts only the finite-level comparison. The new criterion has general adic-datum quotients and constructs compatible common integral local models across a normalized tower; its finite-level comparison consequence is the general Noetherian-coefficient theorem 09AL.

## Second reading by ND

- Item statement: checked against the blueprint node and its proof source, clause by clause; the cartesian square, Noetherian finite-dimensional hypotheses, properness, annihilator invertibility, fibre bound, and AMP/WIT/TOW conclusions agree.
- Step 1: checked against the adic-datum, scheme-convention, fibre-dimension, and dimension-supremum statements; the annihilator calculation and the empty-fibre case are explicit and use no extra hypothesis.
- Step 2: checked against proper FIN, pullback preservation, and the AMP definition; both maps use the common bound $2e$ and both AMP clauses are accounted for.
- Step 3: checked each cited comparison, projection-formula, tensor, and witness statement; the argument uses the arbitrary-coefficient proper projection formula and the ringed-topos coherence node, so it does not assume quotient perfectness over the preceding quotient.
- Step 4: checked tensor pullback, comparison pullback, and witness-compatibility statements; the balancing formula and the three-level cocycle are written out rather than hidden behind “transports”.
- Step 5: checked the bounded-tower definition, the uniform quotient bound, AMP consequences, and the local-effectivity criterion; the interval shift and the finite-lisse/etale-origin bridge are stated explicitly.
- Step 6: checked strict evaluation, completed pullback, coefficient comparison, tensor reassociation, and tower-preservation statements; the scalar-extension calculation on supplied quotient objects and transition naturality are included.
- New node `lem-weil-pbc-uniform-perfect-quotient-bound`: statement-only and self-contained; tested on $I=0$, the unit ideal, the zero quotient, and finite-length localizations, with source 090V recorded as an assembly ingredient and searches recorded.
- New node `lem-weil-pbc-normalized-constructible-local-effectivity`: statement-only and self-contained; retains normalization, cocycle, common interval, and constructibility hypotheses, distinguishes the finite-Tor sources from the claimed extension, and records all searches.
- New node `lem-weil-pbc-ringed-exchange-tensor-coherence`: statement-only and self-contained; checked on the identity square and on the comparison square, with naturality and no unwarranted cartesianness assumption; all searches are recorded.

Changes made in this second reading: none to the mathematical statements or proof steps. I verified the existing source-error repair (removing the false $P_n$-over-$P_{n+1}$ perfectness claim), the complete citation quotes, duplicate distinctions, blueprint metadata, and the dry-run preflight.
