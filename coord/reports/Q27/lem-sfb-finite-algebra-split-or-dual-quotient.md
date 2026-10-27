# Stage-1 report: lem-sfb-finite-algebra-split-or-dual-quotient

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-algebra-split-or-dual-quotient.json`: item, statement, split; no exact Mathlib match. Seven proof steps cite six existing Mathlib leaves. Statement, statement dependencies, chapter, unit, source, creation provenance and imported blueprint fields are retained.
- `citations.json`: six entries, each quoting the entire verbatim statement of the existing node used in its numbered step.
- `report.md`: this report. `searches.jsonl` was generated only by the prescribed msearch command.

New nodes: **0**. New Mathlib leaves: **0**. Existing Mathlib leaves used: **6**.

## Attachments

None. Exact blueprint-tag and conceptual searches of `lean/WeilConjectures/` found no declaration stating the full dichotomy. The project's `AlgHom.toDualNumber` and its coefficient identities in `WeilConjectures/Mathlib/RingTheory/Ideal/Cotangent.lean` construct maps from cotangent functionals, but do not give the whole item or its surjectivity alternative. They are not an attachment. The connected reduced finite-algebra theorem in `WeilConjectures/Mathlib/RingTheory/Artinian/Ring.lean` covers a more restricted assertion.

## WANTED

None. Milne's Algebraic Groups and all Stacks material used are present locally. Milne's reference CA 16.7 is not needed separately: the already available Stacks 06RS and 00JA statements supply its finite-local-product input.

## Problems corrected

The item was statement-only, with no proof or proof dependencies. Its statement is correct, including the zero algebra, and was not changed. Milne Theorem 12.18, printed p.237, says that a nonfield local factor gives a surjection to the dual numbers without giving the construction. Steps 4--7 supply that argument rather than restating this clause as a new lemma. Step 2 also supplies the reason the local factors are finite-dimensional: the product projections are surjective and carry a finite spanning family to a spanning family. This avoids an unjustified inference that arbitrary localizations preserve finite dimension.

The proof_origin is agent: it follows Milne's route but expands the omitted local argument. The source for each step distinguishes the Stacks product and residue-field inputs from this expansion. No unit or chapter route is replaced. The latest blueprint's direct-image proof and its unit/chapter records were read; the item is an algebraic tool below the recorded supporting chain, and its full blueprint.from.place and via are retained. `tools/blueprint_refs.py ancestor` reports a null ancestor for this already imported supporting chain; no new node requiring an ancestor is created.

## Not duplicates

There are no new nodes. Searches by concept and by Stacks tags reused the existing finite-spectrum/product-localization nodes, finite-algebra Artinianity, local radical nilpotence, triviality of finite extensions of an algebraically closed field, and separation by linear duals. Blueprint searches for `Artinian`, `dual number`, `finite algebra`, `product of fields` and `dual-number` found no equivalent statement of the item's dichotomy. In particular the existing reduced-Artinian residue-product node assumes reducedness, which the item does not.

## Review by Q27

I read Milne, *Algebraic Groups* (2017), Theorem 12.18, proof (b) => (c), printed p.237, directly from the local PDF. The passage first writes the dual finite algebra as a product of local Artinian rings with residue field the algebraically closed ground field, then invokes a dual-number quotient for a nonfield factor. The split follows these two cases. I also read the latest blueprint direct-image proof, the chapter record and the unit record; this supporting commutative-algebra argument changes none of their steps.

For C4, I opened all six cited nodes and checked the statements, not just their titles or proofs. The six full verbatim statements are in citations.json. Here is the hypothesis and use audit by step:

1. The zero algebra has a unique isomorphism to the empty product. This uses the convention already in the item. It does not incorrectly assert existence of a map from the zero ring onto a nonzero ring.
2. `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum` applies to the structural map F -> A because a field is local with only prime (0), and A is finite-dimensional over F. Its statement actually gives finitely many primes, all maximal, and a nil intersection. `lem-weil-pbc-product-of-localizations-at-maximal` therefore applies with precisely its two hypotheses, and actually gives a canonical F-algebra product isomorphism and local factors. I read Stacks algebra.tex, Tag 06RS (`lemma-local-dimension-zero-henselian`), proof, and Tag 00JA (`lemma-product-local`), including their proof texts. The coordinate preimage with the other coordinates zero proves surjectivity of each factor projection; images of generators prove finite dimension. These short arguments need no new lemma. The empty product is explicitly covered.
3. `lem-weil-pbc-alg-closed-finite-extension-trivial` applies to each quotient field because the images of the factor's finite spanning family span the quotient and F is algebraically closed. Its statement says the structural map is bijective, exactly what is needed to construct rho_i, rather than an arbitrarily chosen ring map. I read Stacks fields.tex, Tag 09GR (`lemma-algebraically-closed`), its equivalent conditions and proof. A quotient by a maximal ideal is a field by the definition of maximality; kernel and quotient operations are defined in the item's existing definition dependency. With every maximal ideal zero the factor maps really are F-algebra isomorphisms.
4. `lem-weil-pbc-finite-dim-algebra-artinian` applies to the chosen finite-dimensional commutative F-algebra B and gives the Artinian hypothesis of `lem-weil-pbc-artinian-local-noetherian-nilpotent`. B is local by step 2. That node's statement gives the actual ideal-power equality m^N=0 with N >= 1, not merely elementwise nilpotence. I read algebra.tex, Tags 00J6 (`lemma-finite-dimensional-algebra`), 00J8 (`lemma-artinian-radical-nilpotent`), and 00KH (`lemma-Noetherian-dimension-0`); the corresponding Mathlib nilpotent-maximal-ideal criterion was also read. The nonzero quotient m/m^2 follows by the explicit ideal-power induction in the step, so no unrecorded use of Nakayama is hidden.
5. `lem-weil-pbc-vector-space-dual-separates` applies to the F-vector space V=m/m^2 and its chosen nonzero v. It states existence of a functional nonzero on this v; neither finite-dimensional duality nor an unproved cotangent comparison is assumed. I also read the recorded Mathlib `Module.Projective.exists_dual_ne_zero` source (LinearAlgebra/Dual/Lemmas.lean, lines 196 onward). Scaling the representative by the inverse of its nonzero coefficient gives lambda([u])=1. The map in step 6 is constructed directly, so no geometric tangent-vector node is being misused as a ring-algebra theorem.
6. The formula b -> rho(b) + lambda([b-s(rho(b))]) epsilon is checked directly. The class exists since rho s=id and ker rho=m. The displayed product expansion shows that the only discarded term is xy in m^2. Additivity, F-linearity and the value at 1 follow directly from the formula. This is an elementary ring calculation, not a hidden quotient-existence theorem. It uses exactly the multiplication the item defines for the dual numbers.
7. The displayed preimage s(a)+d u has coefficients (a,d), using rho(u)=0 and lambda([u])=1. It proves surjectivity for every a+d epsilon and composition with the already surjective projection gives the required map from A. No additional assumption on characteristic is used.

For C1 and D1/D2, the six non-elementary inputs above are explicit cited statements; all remaining reasoning is written out in short steps. No argument has been moved into a new node restating the item. All seven steps are under 900 characters, so there is no step above the 2000-character long-step threshold. The proof dependency list equals the union of step uses. Every cited node is already a Mathlib leaf, so no undeclared off-route non-Mathlib theorem is being used.

For the small-case audit in E: the zero algebra chooses n=0; A=F and A=F^r choose the product alternative; B=F[t]/(t^2) gives the identity dual-number quotient after selecting lambda([t])=1; B=F[t]/(t^3) gives the truncation modulo t^2. For F[x,y]/(x,y)^2 a functional picking one coordinate gives a surjection. The proof works in characteristic 2 as well, since the product formula has no division by 2. In a product with both field and nonfield factors the latter's surjective projection is used, rather than an unjustified inclusion of a factor.

For B, no new node requires a self-contained statement, a Mathlib-leaf classification, or a duplicate-pair explanation. The existing item's statement introduces all its objects and has unchanged definition dependencies. Search records were appended only from the real msearch log. All four prescribed search tools were run, the hits were read, and the second phrasing sought general Artinian decomposition. Reduced/etale/semisimple hypotheses in those hits do not imply the item's arbitrary-algebra dichotomy. The supporting facts that do exist in Mathlib were already nodes and were reused.

## Unfinished work

None in the split. No Lean files were written and no compiler, Lake or build was run. Required server-side dry run and delivery are performed after this report.
