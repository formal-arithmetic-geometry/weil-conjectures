## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cm-closed-point-flat-quasifinite-slice.json`: item, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-fibre-regular-element-flat-hypersurface.json`: one new statement-only node, Stacks 056Y; no Mathlib match.
- `citations.json`: verbatim statements for every step/node citation.

## Attachments

None. Searched the project `WeilConjectures/` for the item id, slice-CM, and flat/quasi-finite slicing terminology. `Morphisms/SlicingFlat.lean` treats smooth/etale slices and connected fibres, not this Cohen–Macaulay slice. `RelativeEffectiveCartier.lean` and `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean` contain related algebraic inputs; their fibre hypothesis is regularity on the entire affine fibre, not regularity merely in the designated fibre stalk, so they are not exact attachments for either node.

## WANTED

None. All mathematical source text used is in the supplied Stacks checkout.

## Corrections and route

No statement change or dispute. The globally flat hypothesis implies flatness at the specified point, precisely the condition in Stacks 0570 after expanding its Cohen–Macaulay terminology (more-morphisms definition-CM). The item intentionally omits the regular-immersion conclusion of 0570. Its inherited statement and statement dependencies are retained.

The previous item was statement-only. The split follows 0570, with one harmless change of induction parameter: use the finite dimension of the fibre local ring directly rather than first equating it with the topological local dimension at the closed fibre point. The induction claim uses depth at least dimension, so that the existing quotient node gives exactly the hypotheses for induction. This strengthens the induction claim only; it changes no delivered statement. The base case explicitly uses the affine closed-point dimension theorem and the pointwise ring version of 0397. I did not cite the scheme node `lem-trf-locally-quasi-finite-relative-dimension-zero` for a pointwise implication, since its statement only gives the global equivalence.

The ancestor is `lem-trf-local-term-locality`, via the already recorded 055W/0570 input in the elementary-etale structure route. The unit/chapter records were read and left untouched. The off-unit citations are generic dimension, quotient, fibre-stalk, and quasi-finite-locus tools, declared individually in `split_report.tool_uses`; no unit step is replaced. No SGA source is used.

## Search record and Not duplicates

The complete logged searches are in `searches.jsonl`. Five new Q19 searches for the item and five for the new node were run with the prescribed `msearch.py` command: LeanFinder, Loogle, grep, LeanSearch, and a second LeanFinder phrasing. The original Q09 item searches are retained. I read the results: flatness and smooth-chart declarations, quasi-finiteness definitions, and `Module.Flat.isSMulRegular_of_nonZeroDivisors` do not state the local flat hypersurface existence theorem. The latter says regular scalar multiplication on an already-flat module; it does not prove flatness of the quotient. The grep hits in ConstantSheaf and Flat concern quotient maps of spaces, not quotient algebras. No service was unavailable in these Q19 searches.

Before adding the hypersurface node I searched all DAG node statements/sources by 056Y, slice-given-element, slice-once, nonzerodivisor, flat hypersurface, and Cohen–Macaulay quotient, and searched the whole blueprint with `blueprint_refs.py search` for slice, Cohen, 056Y, hypersurface, nonzerodivisor and quasi-finite. No existing node states 056Y. The existing 02JN quotient, 00OU dimension, 01TI open-locus and fibre-stalk nodes are reused. The new node is a one-equation local cutting lemma, with neither a zero-dimensional fibre nor local quasi-finiteness in its conclusion; it is not a clause of the item, and it does not move the induction into a new node.

## Not duplicates

No existing node has source Tag 056Y. The distinct source 0570 is the item itself. The 02JN ring quotient theorem gives dimension/depth after a nonzerodivisor; the new 056Y scheme theorem gives relative flatness on a neighbourhood and does not assert that dimension/depth conclusion. The related Cartier criterion `lem-pc-cartier-criterion` assumes a smooth relative curve and starts with flatness of the closed subscheme; it does not give the fibre-stalk slicing theorem.

## Review by Q19

I read Stacks more-morphisms.tex Tag 0570 (`lemma-slice-CM`), including the whole base case and induction; Tag 056Z (`lemma-slice-once`); and the statement and proof of Tag 056Y (`lemma-slice-given-element`). For 056Y I checked that only flatness at the designated point and local finite presentation are assumed, with no Noetherian base or separability condition. The new node is exactly the explicit affine hypersurface conclusion, forgetting the unused effective-Cartier assertion. It introduces its schemes, point, germ, maximal ideal, nonzerodivisor, affine neighbourhood and quotient subscheme; the nonzerodivisor is defined inline and the scheme/morphism notions cite existing definitions. It has no proof or proof dependencies.

I also read algebra.tex Tag 02JN (`lemma-reformulate-CM`) and Tag 00OU (`lemma-dimension-closed-point-finite-type-field`), morphisms.tex Tags 0397 (`lemma-locally-quasi-finite-rel-dimension-0`) and 01TI (`lemma-quasi-finite-points-open`), and all statements quoted in citations.json. The item and new node are faithful to those sources. Here is what each step actually takes from its citations:

1. The Noetherian-local dimension node gives a finite nonnegative dimension, so strong induction has a natural-number parameter. The strengthened depth inequality is stated before the induction is used and includes the original equality hypothesis.
2. The finite-presentation definition supplies a finite-type affine pair. The affine fibre-product node supplies the fibre ring, which is finite type over the residue field by its displayed algebra generators. The closed-point dimension node applies to its maximal ideal, not an arbitrary prime. The ring 0397 node gives quasi-finiteness at this point, and the definition node turns exactly this affine pair into the scheme pointwise condition. This avoids taking a pointwise assertion from a node that states only a global one.
3. The open-locus node gives local quasi-finiteness on W; the isolated-fibre-point node gives the open singleton. The fibre definition explicitly includes the subspace-topology assertion, so O with O_s = {y} exists. The open restriction node gives local quasi-finiteness on O intersect W. Flatness is unchanged on stalks. The displayed polynomial presentation proves finite presentation on a basis of principal charts; no uncited openness-of-flatness theorem is used. There is no claim that all fibres of the original g are zero-dimensional.
4. Positive depth gives a nonempty regular sequence by the actual supremum definition, and the regular-sequence definition gives injectivity of multiplication by its first element. The fibre-stalk quotient node really is surjective. A lift lies in the maximal ideal because a unit maps to a unit. Thus all hypotheses of the new 056Y node hold, including flatness at y; its conclusion really gives global flatness of D over S after shrinking.
5. The closed-immersion node supplies the affine quotient description; the fibre-stalk node supplies quotient by the base maximal ideal. The explicit fraction maps prove that localizing the hypersurface quotient gives T/(h); then taking the fibre gives A/(h-bar). Tensoring the quotient equation gives the same closed-subscheme description on the fibre, so the point remains closed. This is an elementary quotient computation, not a theorem about an unknown immersion's image.
6. The existing 02JN node assumes depth at least d and supplies exactly Noetherianity, dimension d-1 and depth at least d-1. No equality stronger than its statement is taken from it. These are the strengthened induction hypotheses, while 056Y supplies flatness and local finite presentation and Step 5 supplies closedness. The composite map to Y does not alter Z to S or its fibre, so all four required conclusions follow.

For the mathematical edge checks, d=0 includes Artinian nonreduced local rings; no reduction or smoothness is assumed. For positive dimension, a regular element in the maximal ideal cannot make the quotient zero, and the quotient node applies to a nonzero local ring. In the example k[t,eps]/(eps^2) at (t,eps), cutting by t retains a nonreduced zero-dimensional fibre, which the item permits. For f the identity, the point fibre has dimension zero and the open slice construction applies. Inseparable residue extensions cause no difficulty, since neither the dimension node nor 056Y assumes separability. An empty source cannot satisfy the specified-point hypothesis. I checked that no new node is elementary, duplicate, a restatement of a conclusion, or a Mathlib specialization. Every proof step is below 2000 characters. citations.json quotes each cited statement verbatim, and the union of step uses is exactly proof_deps.

The substantive corrections made while preparing the split were to use the pointwise ring 0397 interface instead of the global scheme one, to make the strengthened induction claim explicit so that the quotient node's depth inequality suffices, and to write the fibre-local quotient maps and finite-presentation-on-open computation rather than hide them behind an identification or permanence assertion. Nothing remains mathematically unfinished at this splitting level; the new 056Y lemma is intentionally left unsplit for the next worker.

## Unfinished work

None for this item at stage 1. One statement-only child remains for later splitting.
