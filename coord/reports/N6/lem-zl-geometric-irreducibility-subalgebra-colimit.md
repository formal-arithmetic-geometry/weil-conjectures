# Stage-1 report: lem-zl-geometric-irreducibility-subalgebra-colimit

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-geometric-irreducibility-subalgebra-colimit.json`: statement, split into seven steps; no exact Mathlib match for the two geometric closure assertions together or separately was found.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-spectrum-irreducible-nilradical-prime.json`: statement-only Mathlib leaf, `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`, `Mathlib/RingTheory/Spectrum/Prime/Topology.lean:276`. Its general commutative-semiring statement specializes immediately to commutative rings.
- `citations.json`: one exact statement quotation for every cited node in every step.
- `report.md`: this report. `searches.jsonl` is the search command's retained output log; existing item searches were retained. `prepare.py` is sandbox-local preparation code, not project code.

## Attachments

None. I searched the project declarations under `WeilConjectures/` by the item's blueprint tag and by geometric irreducibility, subalgebra, colimit and nilradical terminology. The project has geometric-irreducibility and domain results, but none found asserts both clauses with the item's hypotheses. The exact nilradical equivalence is a Mathlib declaration, not an attachment of a declaration of this project. The upstream master checkout is reference material only; no sorry declaration there was treated as completed evidence.

## WANTED

None: the Stacks source, the current blueprint and Mathlib source needed here are locally available.

## Problems found and corrections

The imported statement agrees with Stacks Tag 037N(1),(3). It already allows noninjective transition maps and omits reducedness and finite generation correctly; I changed no statement or statement dependency. Its proof was empty. The source's last sentence, that the colimit clauses follow because tensor commutes with colimits, needs both detection of a nilpotence relation at a finite stage and a nonemptiness argument. These are now explicit rather than implicit. I also supplied the underlying-module colimit universal property before applying the existing module tensor/colimit theorem; the cited algebra-colimit theorem states only the ring colimit and element representatives, so it was not incorrectly quoted as already supplying the module colimit.

For assertion (1) I expanded the source's tensor-injectivity reduction and used the equivalent prime-nilradical argument in place of its minimal-prime/dense-image argument. This stays below the same elementary-algebra lemma and the same blueprint route. The expansion is honestly marked `proof_origin.by = agent`; no change to a unit's proof route or a chapter is involved. The chapter and unit records remain unedited because this item is not the unit's key node.

One exploratory grep used an extra `Mathlib/` prefix in its subdirectory argument; its empty output is not evidence of absence. The later whole-Mathlib and `RingTheory/Spectrum/Prime` searches used the correct paths. All searches recorded for the new leaf were actually run through the prescribed command and appear in this item's `searches.jsonl`; the focused grep supplies the exact declaration and line. The item's preexisting searches were retained, and the current task added two concept phrasings and a whole-source search. The geometrically reduced hits are about a different property, and the new ordinary-spectrum criterion does not itself state either geometric closure assertion.

## Unfinished work

None in the mathematical split. The only new node is an exact Mathlib leaf with no proof to split further. Delivery validation and the push are performed after writing this report.

## Review by N6

I read `literature/stacks-project/algebra.tex`, the definition immediately preceding Tag 037N and the whole proof of Tag 037N (lines 11207–11257). This verifies that geometric irreducibility quantifies over every field extension, includes nonemptiness, and imposes neither reducedness nor finite generation. I read the current blueprint `main-20261015` proof of `lem-zl-bertini-finite-cover-curve`, paragraph 3: the application of Tag 0G4F to X and T leads through `lem-zl-bertini-irreducible-member` and `lem-zl-generic-point-geometric-irreducibility` to this item. The new leaf's `blueprint.from.via` retains those intermediate items, preceded by this item. Blueprint searches for the geometric closure statement and the nilradical criterion found no equivalent blueprint node.

For the new leaf I read Tag 00ES(2) and its proof (lines 4665–4695) and the radical/intersection and vanishing statements in Tag 00E0 (lines 2987 onward). Applying the radical-ideal/closed-set correspondence to the zero ideal gives exactly the claimed prime-nilradical criterion, including properness. I read the actual Mathlib equivalence at `RingTheory/Spectrum/Prime/Topology.lean:276` and its neighboring irreducible-zero-locus statements. The theorem is for a commutative semiring and hence has no stronger hypothesis than our commutative ring. Its `IrreducibleSpace` includes nonemptiness and its `IsPrime` includes properness. I searched the whole DAG by nilradical, nilpotence and irreducibility, the exact declaration name and Tag 00ES. The existing closed-subset/prime correspondence does not identify the whole spectrum's defining prime with the ideal of nilpotent elements in its statement, and the source's radical correspondence is a further fact: the new Mathlib leaf records that complete equivalence explicitly. It is not a restatement of either clause of the item.

Step 1 uses the affine-fibre-product theorem, whose statement explicitly identifies the fibre product with Spec of the algebra tensor product. The geometric-irreducibility definition really quantifies over arbitrary field extensions, and the new criterion really includes properness. All rings here are commutative and the base is the fixed field k. Thus the reduction does not silently substitute a field-only or reduced-only version of geometric irreducibility.

Step 2 uses the field-extension faithful-flatness theorem with D=k, which meets its field-extension and commutative-algebra hypotheses. The faithfully-flat definition explicitly includes flatness, and the flat-module definition explicitly says that tensoring an injective linear map is injective; I do not take exactness preservation from an unrelated definition. The displayed mutually inverse maps identify k tensor K with K by bilinearity. The algebra-tensor theorem supplies its multiplication and unit formula, and the module-tensor definition supplies linear functoriality and generation by pure tensors. These quoted statements justify that the induced tensor injection is also a unital ring map; the remaining checks are the displayed bilinear identities.

Step 3 uses the nilradical criterion in both directions. Injectivity, already established in step 2, reflects the equality v(x^n)=0, so the inverse-image identification of nilradicals is proved rather than assumed. Properness follows from preservation of the unit and primality follows from the product test. The final return to geometric irreducibility uses exactly the definition and the affine identification already proved in step 1. This is an elementary argument from the cited criterion, not a new node restating the item's subalgebra clause.

Step 4 uses both clauses of the algebra-filtered-colimit node: the underlying ring colimit and representatives. I opened the ring-colimit equality node and checked that it assumes a small filtered category and concludes equality at a common later stage. The given small nonempty directed poset is such a category: parallel arrows are unique. This is exactly what makes the explicitly constructed linear map independent of representatives. Its additivity and scalar compatibility are checked at a common stage. The module-colimit comparison is thus constructed here and not claimed as a clause missing from a cited statement.

Step 5 uses the module tensor/colimit theorem only after step 4 supplies its module-colimit hypothesis. Its arbitrary small category hypothesis is satisfied. The elementwise module-colimit theorem then supplies representatives, common-stage equality and eventual zero; it does not require transition injections. The tensor algebra and module tensor statements supply the formulas used to check that all structural maps preserve products and the unit. A module-colimit theorem is sufficient: the subsequent argument needs only representatives and detection of zero in the tensor ring, not an unproved assertion that a forgetful functor preserves some unrelated colimit.

Step 6 applies the nilradical criterion to each tensor algebra B_i, with irreducibility supplied by the given geometric hypotheses. The module-colimit zero criterion says exactly that an element which vanishes in the limit vanishes later. Since I is nonempty, one may choose i and apply that statement to 1 in B_i. All transitions preserve 1, so vanishing later contradicts the properness of the later nilradical. This repairs the nonemptiness gap that would arise from checking just the product test.

Step 7 uses the representative and zero clauses of the module-colimit node. Directedness moves x and y to one stage; the structural ring maps carry their product power to the product power. A single nilpotence relation is witnessed at a later stage, where the already-known prime nilradical gives one factor nilpotent. A ring map preserves that power-zero identity. The nilradical criterion and geometric definition then conclude exactly clause (2). No injectivity is inferred for a transition map, and no boundedness on nilpotence exponents is imposed.

I tested the statement and the new leaf on the zero ring (empty spectrum, excluded by properness), a field (zero ideal prime), the dual numbers over a field (irreducible despite a nonzero nilpotent), and k times k (zero nilradical not prime, reducible spectrum). For the colimit argument I checked a one-object diagram, and the two-object directed diagram k[t] to k by evaluation at zero: both algebras are geometrically irreducible, the transition is noninjective, and the colimit is k. An infinite chain of polynomial rings whose maps kill one variable at a time also illustrates why one only needs eventual vanishing of each fixed relation, not a single stage killing all elements. None of these checks needs an additional hypothesis. All seven proof steps are shorter than 2000 characters; I reread their arguments for hidden non-elementary claims rather than treating their length as the check. The new leaf, not an inline claim, carries the non-elementary nilradical criterion; the tensor and colimit facts are existing cited nodes. The other explicit constructions are routine consequences of those precise statements.

I checked delivery-errors B–E against the files: every new statement introduces its own ring, the new leaf has the exact source and Mathlib match, the statement notion dependencies exist, every cited use has an actual verbatim quotation in `citations.json`, the proof dependency list is exactly the union of step uses, and the blueprint references point to the current ancestor and its exact passage. No SGA source, Lean edits, compiler command, live-project edit, or project git command is involved.

## Not duplicates

lem-zl-spectrum-irreducible-nilradical-prime vs lem-zl-finite-type-fibre-component-lower-bound: the existing statement concerns a lower dimension bound for components of a fibre between finite-type algebras, whereas the new criterion characterizes ordinary irreducibility using nilpotent elements.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-zl-linear-incidence-irreducible: the existing statement concerns a height-dependent irreducibility result for a linear-incidence hypersurface over a finite-type domain, whereas the new criterion is for every commutative ring.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-closed-point-dimension-local-ring: the existing statement concerns closed-point/local-ring dimension equality, rather than the prime-nilradical criterion.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-dimension-at-point-components: the existing statement concerns dimension at a point in a finite-type algebra, rather than an equivalence between irreducibility and prime nilradical in an arbitrary ring.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra: the existing statement concerns a dimension bound for quasi-finite polynomial-algebra maps, rather than the prime-nilradical equivalence.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-generic-fibre-localization-domain-irreducible: the existing statement concerns irreducibility of a particular localization of a domain, whereas the new criterion allows arbitrary nonreduced rings and is an equivalence.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-spec-irreducible-closed-subsets-primes: the existing statement concerns the classification of irreducible closed subsets as V(p), without identification of the ideal of nilpotent elements with the prime defining the whole spectrum; that identification is part of the new exact Mathlib equivalence.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-spec-irreducible-components-minimal-primes: the existing statement concerns the classification of irreducible components by minimal primes, without identification of the ideal of nilpotent elements with the intersection of all primes needed for the new equivalence.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-weil-pbc-spec-topological-krull-dimension-ring: the existing statement concerns equality of ring and topological Krull dimensions, rather than the irreducibility criterion.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-sfb-finite-type-noetherian-spectrum: the existing statement concerns Noetherianity of a finite-type spectrum, rather than irreducibility or the nilradical.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-pur-a1-pullback-endomorphism-rigidity: the existing statement concerns rigidity of an endomorphism of a pulled-back locally constant sheaf, rather than a ring-spectrum criterion.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-trf-dnc-principal-generic-smooth-reduction: the existing statement concerns a local smooth-parameter reduction on a normal scheme, rather than a prime-nilradical characterization of an affine spectrum.

lem-zl-spectrum-irreducible-nilradical-prime vs lem-zl-geometric-irreducibility-subalgebra-colimit: the new leaf characterizes ordinary irreducibility of one arbitrary ring by its nilradical; the item proves preservation of geometric irreducibility under injections and directed algebra colimits. Neither preservation assertion is a clause of the new leaf.
