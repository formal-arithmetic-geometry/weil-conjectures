## Files written

- `dag/nodes/sec-trace-formula/lem-trf-closed-immersion-finite-presentation-ideal.json`: statement item, now split into five steps; no exact Mathlib match for the item. All twelve proof dependencies already exist. No new nodes and no new Mathlib leaves.
- `citations.json`: all sixteen step/node citations, with verbatim statements copied from the cited files.
- `searches.jsonl`: actual searches run with the prescribed search command; the item retains its inherited six search records and adds the four searches made for this delivery.

## Attachments

None for this item. Searches for the exact blueprint tag and for closed-immersion/finite-presentation terminology in `lean/WeilConjectures/` found no declaration stating the equivalence. The existing declaration `AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine` belongs to the already attached node `lem-weil-pbc-quasi-coherent-finite-type-affine`; it supplies a supporting affine module criterion, not this item.

## Wanted sources

None. All sources used are in the supplied literature checkout.

## Problems found and changes

The imported statement agrees with Stacks 01TV and is unchanged. Its proof was empty. I supplied the two implications by the source's affine-quotient argument, and supplied the otherwise implicit justification that a closed immersion is always quasi-compact and quasi-separated. I did not add a Noetherian, globally quasi-compact, or separated-base hypothesis.

The inherited search verdicts mention the parent's smooth-pair blowup comparison as well as this item's actual question; I preserved these historical records and added searches with verdicts specific to the present equivalence. Mathlib search returned closed-immersion finite-type/finite instances, the definition of local finite presentation, open-immersion finite presentation, and general finite-presentation sheaf data. I read the relevant morphism and sheaf declarations. These do not identify the ideal's finite type with the immersion's finite presentation. The existing ring-kernel Mathlib leaf, by contrast, gives exactly the algebraic input, specialized to zero polynomial variables.

I read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and `.proof.md`, as well as the chapter/unit records and this item's parent. The long `blueprint.from` chain records a historical resolution/blowup branch. The current ancestor proof uses the normal cone; it does not itself state this closed-immersion equivalence. This delivery proves the existing generic geometric input faithfully from its stated Stacks source, without changing that historical provenance, the unit realization, or the ancestor's route.

## Unfinished work

None for this stage-1 item. No Lean was written and no compiler, Lake command, local DAG checker, or build tool was run.

## Not duplicates

No new nodes were created. Existing nodes were reused for every non-elementary input, including the affine finite-type criterion, the polynomial-presentation kernel criterion, the all-affine-pairs local-finite-presentation criterion, separatedness of closed immersions, and quasi-compactness of affine schemes. The exact-tag blueprint search for 01TV found no imported blueprint node stating this item; the more specific equivalence searches also found no alternate statement.

## Review by Q71

I read `morphisms.tex`, Tag 01TV (`lemma-closed-immersion-finite-presentation`), including its full proof. Its affine-quotient and ideal-sheaf identifications are recorded in the existing definition nodes, so these are used explicitly rather than citing a source as if it were a proof. I also read `properties.tex`, Tag 01PB (`lemma-finite-type-module`), and `algebra.tex`, Tag 00R2 (`lemma-finite-presentation-independent`), which substantiate the two substantive auxiliary criteria. There are no new nodes needing separate source or small-case reviews.

For step 1 I opened all seven cited statements. The closed-immersion definition explicitly gives affine inverse images, and the affine-scheme node explicitly gives quasi-compactness. Thus the quasi-compact morphism definition applies to every closed immersion. Clause (a) of the closed-immersion permanence node explicitly gives separatedness; the proper-morphism definition explicitly defines this by a closed diagonal. Applying the same quasi-compactness argument to that diagonal gives precisely the quasi-separatedness definition. The local-finite-presentation definition explicitly records that finite presentation additionally asks for these two properties. None of this assumes the target scheme is quasi-compact or separated.

For step 2 the two cited definitions explicitly give, on an arbitrary affine target open, the inverse-image quotient spectrum, the kernel ideal as its sections, and its associated quasi-coherent ideal sheaf. I checked that the ideal used is J, not J/J^2. This is an elementary unpacking of the cited definitions, not an uncited theorem about affine sheaves.

For step 3 the surjection-kernel node explicitly quantifies over every n >= 0, including n = 0, and every surjective polynomial presentation. Taking S = R/J and the quotient map verifies every hypothesis and gives finite generation of exactly J. In the reverse direction the finite-presentation definition itself permits zero variables and finitely many constant relations. Equality of the ideal span and the module span is written out; no new algebraic lemma is hidden here.

For step 4 I read `morphisms.tex`, Tag 01TQ (`lemma-locally-finite-presentation-characterize`), and the cited node's full statement. It gives finite presentation on every affine source/target pair, so it applies to the full inverse image of an affine target open, which step 2 proves affine. I read the affine module criterion's full statement: clause (c) concludes finite type from finite generation on an affine open cover, with quasi-coherence as a hypothesis. Step 2 verifies quasi-coherence; step 3 supplies the finite generation. The criterion is already Lean-closed according to its existing audit. It is used as a generic tool, with its existing attachment, rather than a replacement of the unit's geometric route.

For step 5 clause (a) of that same affine criterion gives finite generation of sections on each affine open once the quasi-coherent ideal is of finite type there. Restricting the finitely many local generators gives the needed finite-type restriction. The zero-variable ring calculation in step 3 then makes the quotient algebra finitely presented. For each source point, the inverse image of an affine target neighbourhood is an affine source neighbourhood containing that point. These are exactly the witnesses in the cited pointwise local-finite-presentation definition. Step 1 supplies the remaining two global morphism conditions.

I tested the identity immersion (J = 0, zero relations), the empty immersion (J = R, relation 1), the zero ring/empty base, and an arbitrary infinite disjoint union of affine bases. All arguments remain local and allow these cases. As a non-Noetherian negative test, take R = k[x_1,x_2,...] and J = (x_1,x_2,...). The ring-kernel theorem rules out finite presentation of R/J over R since J is not finitely generated; the affine module criterion simultaneously rules out finite type of the associated ideal sheaf. This confirms the argument does not conflate finite type of the immersion with finite presentation.

I checked delivery-errors B through E against these files: all objects and hypotheses are present; source tags and labels were read in their actual TeX files; all non-elementary inputs are existing cited nodes with statements that supply the precise facts used; the two implications contain the argument rather than restating the item under a new name. Every proof step is shorter than 2000 characters. I generated every citation quote from the actual cited statement without changing its wording. I preserved the imported statement and metadata and corrected only the missing proof and its dependency/search/report fields.
