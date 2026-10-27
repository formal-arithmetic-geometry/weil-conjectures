## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-section-value-closure-dimension-specialization.json — statement, split into five steps; no Mathlib match for the whole assertion.
- citations.json — one literal quotation for every use in every proof step.
- report.md — this report.

No new nodes and no new Mathlib leaves. prepare.py is a sandbox-only preparation helper, not a delivered project file.

## Attachments

None for the item. Searched lean/WeilConjectures by the exact blueprint tag, section-value closure terminology, and specialization/dimension terminology. The sorry-free AlgebraicGeometry.exists_trait_of_strict_specializes in AlgebraicGeometry/NoetherianSpecializationTrait.lean:33 belongs to the already existing lem-sbc-noetherian-specialization-trait, which the proof cites. It proves the DVR reduction only, not this item. No attachment is proposed in place of the whole item.

## Sources and wanted documents

WANTED: literature/bosch-lutkebohmert-raynaud-neron-models.pdf, BLR 5.3 Lemma 7, printed p.126 (PDF p.132), for lem-sfb-section-value-closure-dimension-specialization. The primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf was read online. It states the dimension inequality and uses a DVR reduction, schematic closure of the generic closure, and its flatness. The local BLR PDF is absent. The proof is accordingly marked agent-written, with its explicit affine calculation.

Read locally EGA IV_3 Corollaire 11.10.7, printed p.172, including its assertion on reduced closures after a field extension, and Lemma 14.3.10 / Proposition 14.3.11, printed pp.207–208. The latter explains why components missing the special fibre yield an inequality rather than equality for the whole closure. Read the Stacks source statements of 054F (properties-lemma-locally-Noetherian-specialization-dvr), 00P3 (algebra-lemma-dimension-preserved-field-extension), 00E5 (algebra-lemma-spec-closed), 0539/0AUW (more-algebra-lemma-valuation-ring-torsion-free-flat / lemma-dedekind-torsion-free-flat), and 0H3X (more-morphisms-lemma-relative-dimension-support-flat). These support the existing DAG tools; no SGA source is used.

## Corrections and limitations

The statement is unchanged and no hypothesis is disputed. The imported node had no proof. Its explicit empty-family convention is retained. No flatness hypothesis on the original algebra B is introduced: only the constructed quotient Q over the auxiliary DVR is proved flat. The dimension comparison is one-sided, allowing components of the generic closure to miss the special fibre.

The inherited blueprint.from.node is null: blueprint_refs.py ancestor confirms it. Its existing from.place already identifies the BLR first assertion and is retained. Searched all imported blueprint nodes using Hilbert, closure of section, specialization, section value, closure dimension, section-value, 0H3X, 0D4H and 02FY. Read the current latest chapter and sk-thm-sf-ctf-stability unit at ef6f9619. This is a lower-level general algebraic-geometry input, not a replacement for a step of that unit. Chapter, unit, source and inherited metadata are untouched.

No unfinished subargument remains in the item's natural-language proof. This is stage 1 only; no Lean file, compiler, Lake or build tool was run.

## Mathlib searches

The five existing searches were retained, and the new actual searches for the item were appended from searches.jsonl with the exact query text and service result. Both new semantic phrasings, LeanSearch, Loogle and the prescribed grep were run and read. Results provide generalization maps, ordinary topological specialization, affine topology and flatness statements, not dimension monotonicity of the closure of values of a specified set of sections. The earlier search for fibre-dimension lower semicontinuity was exploratory: the DAG already has both the algebraic-space semicontinuity statement and the simpler generic-dimension bound. No new node was created for either.

## Not duplicates

There are no new-node/existing-node pairs. In particular I did not create a scheme version of lem-sfb-flat-space-fibre-dimension-lower-semicontinuous (0D4P), a new DVR-specialization node, or a new torsion-free-flat node. The direct scheme bound lem-trf-flat-family-generic-dimension-bound (0H3X), the existing rational-density-field-extension node, lem-pc-dim-base-change, and the existing PID flatness leaf are reused.

## Review by Q39

I checked B–E against the actual node statements and the source passages above. There are no new statements requiring separate small-case tests or splitting. Every non-elementary fact in the item is a cited node; citations.json quotes the statements verbatim, rather than borrowing an argument from their proofs.

Step 1 uses pqf-def-locnoeth only to recognize the single affine Noetherian cover of Spec A. The trait lemma says exactly that a strict specialization on a locally Noetherian scheme admits a DVR with the required two images. The equality case is handled first, so its distinctness hypothesis holds. def-sc-discrete-valuation-ring supplies the domain/PID and local-ring properties; def-pc-base-change explicitly defines the induced sections. These statements were read, as was the project declaration for the trait lemma.

Step 2 uses the affine fibre-product statement with its projection formulas to obtain the correct fibre rings and evaluations. The quotient-spectrum homeomorphism identifies the closure with V(intersection of the evaluation kernels): a closed V(L) contains the points exactly when every element of L evaluates to zero. The quotient-closed-immersion node, and its base-change stability node, say exactly that the scalar-extended quotient has closed image. The rational-density statement is applied to the quotient scheme itself with the specified family, not to all rational points of the ambient scheme. Its hypotheses do not require smoothness, separability or reducedness. The dimension-invariance node is an assertion about finite type algebras, so I explicitly identify the quotient coordinate ring as finite type and cite the ring dimension definition for equality with the topological dimension of its spectrum. This repairs the potential C4 error of citing an algebra dimension result directly for an arbitrary closed topological subset.

Step 3 is the elementary affine calculation. It uses the affine-spectrum anti-equivalence to obtain the actual maps D to R, and the affine fibre-product formula and quotient-spectrum identification already read in step 2. The common-denominator calculation is written out: Q embeds in H, the map Q tensor K to H is surjective by fractions and injective because d/a in J implies d in P. It does not claim that tensor products commute with an infinite intersection. Torsion-freeness is proved from that injection. No schematic-closure existence or flatness assertion is hidden in this elementary step.

Step 4 uses the PID torsion-free-flat statement for the possibly infinitely generated R-module Q: that node has no finite-generation hypothesis. The affine flatness comparison then gives the required scheme flatness. The finite list of algebra generators gives the finite type condition. Every equation in P vanishes on every section already over R because R injects into K; this establishes the closed-fibre containment, without confusing topological containment with a factorization through an arbitrary nonreduced closed subscheme. The cited quotient and base-change statements give the closed subset needed to take the closure.

Step 5 applies precisely the statement of lem-trf-flat-family-generic-dimension-bound, with integral base Spec R and the morphism proved flat and locally finite type in step 4. No properness or equidimensionality is used. The infinite-dimension case is treated separately; for a nonempty generic closure any remaining dimension is a finite nonnegative integer by the dimension convention, so the bound node's integer r is legitimate without adding a dimension-finiteness theorem. The final closed-subspace inequality is the explicit chain argument from the dimension definition. This avoids using an open-subspace monotonicity node for a closed subset.

I tested the empty family, equal base points, a singleton section (both closures are points), finite families, and the strict-drop example A=k[t], B=A[x], a_c(x)=ct with c ranging over an infinite field k: at the generic point the values are dense in an affine line, while at t=0 they coincide at the origin. Nilpotents in A or B cause no problem: the initial fibre vanishing ideals are intersections of field kernels, and the auxiliary DVR is a domain. Components disappearing from the special fibre are allowed by the upper bound, so no equality is silently asserted. All five steps are below 2000 characters. No elementary fact or clause of the item was promoted to a new node.

The off-unit statements are declared as generic tools in split_report.tool_uses with their purpose; no alternate cohomological route is taken. Independent maintainer review remains to be performed after delivery.
