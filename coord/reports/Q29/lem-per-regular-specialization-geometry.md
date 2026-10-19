## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-specialization-geometry.json`: split into six steps; statement unchanged; Mathlib no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-strict-local-regular-integral-fibres.json`: statement-only supporting lemma, unsplit; Mathlib no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-dimension-function-calculus.json`: statement-only supporting lemma, unsplit; Mathlib no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-dimension-function-pullback.json`: statement-only supporting lemma, unsplit; Mathlib no match.
- `citations.json`: verbatim statements used by Steps 1, 2 and 5, including the dimension-function difference formula and the strict-local-model fibre-dimension equality.

## Attachments

None. Searches for the blueprint tag and for regular specializations, fibre-generic lifting and dimension functions in the project Lean source found no declaration stating this item. The hits about valuative criteria and generic fibre dimensions do not state it. No Lean was written or compiled.

## WANTED

None.

## What was checked and corrected

Continued the saved attempt, keeping its item proof, supporting nodes, sources, recorded Mathlib searches and search outputs. The required initial dry run passed at 819c1b5e0a. Its old report described a different four-step split with no new nodes; this report replaces that stale account. The current repository's reviewed `lem-per-regular-specialization-rectangle` already depends on this item, so the old reverse citation cannot be restored. The retained six-step argument avoids that cycle.

Read Illusie–Laszlo–Orgogozo, `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Expose XVII 4.3.2.3–4.3.2.6 (printed pp.284–285) and Expose XIV 2.1.2–2.2.5 and 2.5.4 (printed pp.209–213 and 217–218), using the saved full text. The source's generic-lift lemma has a typographical occurrence of X where its point eta must be in Y; the item's statement already has the correct domain, so no statement correction was needed. No SGA source is used.

The same-chapter existing `lem-per-regular-strict-local-model` already supplies regularity, excellence and preservation of fibre local dimension under strict localization. I removed those duplicated clauses from the new integral-fibres node and made Step 1 cite the existing node explicitly. The remaining new integral-fibres assertion is precisely XVII 4.3.2.3, for local regular maps between Noetherian strictly local schemes. The other two nodes expose the non-elementary dimension-function inputs rather than hiding them in the codimension calculation. All three remain statement-only.

DAG and whole-blueprint searches covered integral fibres, strictly local schemes, regular morphisms, dimension functions, the source numbers, and the ancestor returned by `tools/blueprint_refs.py ancestor`. The item remains under the existing master-blueprint Step 3 of `lem-per-artin-gabber-affine-curve`, through the regular potential-dualizing pullback. Read the chapter and unit records and that ancestor proof; no unit statement or route is changed. This item is not a unit key node, so no unit record is written.

The saved `searches.jsonl` and `repair-search-output.json` were read and reused. For each new node they contain LeanFinder, Loogle, source grep and LeanSearch, followed by a second semantic phrasing. The Loogle integral-fibre candidate assumes a geometrically integral morphism; it does not deduce that property from strict locality and regularity. The generic-point and flat-generalization candidates do not assert integral fibres or dimension-function pullback. A further logged exact-name grep for `instIsIntegralFiberOfGeometricallyIntegral` also returned zero hits. No candidate proves the node, and no new Mathlib leaf is claimed.

## Not duplicates

lem-per-strict-local-regular-integral-fibres vs lem-per-regular-strict-local-model: the existing node gives strict-local regularity, excellence and preservation of local fibre dimensions; the new node only states integrality of geometric fibres of an already local regular strictly local morphism. Step 1 reuses the existing model node.

lem-per-strict-local-regular-integral-fibres vs lem-per-regular-specialization-rectangle: integral geometric fibres are the supporting input XVII 4.3.2.3, whereas the rectangle node states a square, chain lifting and codimension comparison and depends on this item. Neither implies the required integral-fibre assertion by specialization.

lem-per-local-dimension-function-calculus vs lem-per-finite-type-dimension-function: the new node gives local existence and computes arbitrary geometric codimensions by differences; the existing node instead assumes a base dimension function and pulls it back along a locally finite-type map using residue transcendence degree.

lem-per-regular-dimension-function-pullback vs lem-per-finite-type-dimension-function: the new node treats arbitrary regular morphisms without a finite-type hypothesis and uses negative local fibre dimension; the existing node requires locally finite type and uses residue transcendence degree.

lem-per-regular-dimension-function-pullback vs lem-per-regular-potential-pullback: the latter requires finite coefficients, invertibility and an existing pinned putative dualizing complex, and its proof depends on this item. The new node is the coefficient-free XIV 2.5.4 theorem for every base dimension function, with no dualizing-complex existence assumption.

lem-per-regular-dimension-function-pullback vs lem-per-regular-pullback-pinnings: the latter similarly assumes a pinned potential dualizing complex and proves pinning compatibility as well as a dimension-function clause. It cannot provide the coefficient-free assertion, and its geometry route passes through this item.

## Review by Q29

I read the complete statements of all three new nodes and the existing strict-local-model node, with the cited ILO passages open. The item matches XVII 4.3.2.4–4.3.2.6, and its extra numerical identity follows from XIV 2.5.4. The generic-points convention is the category of strict localizations, so uniqueness up to isomorphism does not assert equality of arbitrary algebraically closed residue overfields. No global geometric-fibre connectedness is assumed.

Step 1 now uses `lem-per-regular-strict-local-model` exactly for its induced regular map, Noetherian excellence and displayed local fibre-dimension equality. Excellence gives universal catenarity by its definition. `lem-per-local-dimension-function-calculus` supplies a dimension function on the local base and the codimension difference formula on both schemes. `lem-per-regular-dimension-function-pullback` applies because both strict local schemes are excellent and the map is regular; subtracting the fibre local dimension gives the displayed formula with sign b(v)-b(u). These are full statements of the cited nodes, not facts extracted from their proofs.

Step 2 uses the integral-fibres node on the strict-local map at the chosen fibre-generic eta, supplied by the Step 1 reduction. Flatness and locality ensure nonempty fibres; XVII 4.3.2.3 gives integrality. The integral geometric fibre has a unique generic underlying point. Choosing a geometric representative and separable closures produces the lift and identifies any other generic lift up to a possibly nonunique isomorphism. Fibre-genericity is local fibre dimension zero; preservation of that dimension was established in Step 1. Step 3 substitutes zero at the two generic endpoints into Step 1, giving equality with base codimension. This is elementary arithmetic from earlier steps.

Step 4 is the finite backward construction from the already proved unique lift: at stage i apply Step 2 to x_i towards x_(i+1), then Step 3 makes that arrow immediate. The composite is identified with the originally prescribed lift by Step 2 uniqueness. This spells out the argument of XVII 4.3.2.5 and uses no additional theorem. Step 5 applies integral fibres twice, above x and x', in the same strict-local total scheme. Choosing generic points supplies both vertical arrows; identifying the two geometric representatives above the generic point over x' supplies the left arrow. The maps are over the fixed strict localization, so their composites to its closed point are the structural map. This is the commutative square construction in XVII 4.3.2.6, with its agreement of geometric arrows made explicit. Step 6 substitutes identity base arrows into Step 1 to compute the two vertical codimensions, and applies Step 1 to the bottom and common composite. Both path sums equal c_X(x',x)+b(t). These last calculations are elementary, not an uncited additivity theorem.

The new integral-fibres node does not need excellence, matching XVII 4.3.2.3; the existing model node retains the excellence hypotheses needed for strict localization. The dimension-calculus node follows XIV 2.2.1/2.2.4 for local existence and 2.1.4 plus the saturated-chain calculation in 2.2.5 for geometric codimension. On a local scheme an open containing the closed point is the entire scheme, so local existence suffices. The regular-pullback node matches XIV 2.5.4, including the absence of finite-type assumptions. All definitions used are either inline or named in statement dependencies. New nodes have no proof sketches or proof dependencies; all blueprint references and genuine searches are preserved.

Small cases checked: identity regular morphisms give b=0 and unchanged codimension; a regular scheme over a field has delta=-dim(local ring) and c(t',t)=b(t)-b(t'); a closed point and generic point of a smooth curve over a field give 1=0+1-0. On a plane and line glued at a point one must not use minus absolute local dimension as a global dimension function; the local-existence theorem used here allows normalization on components instead. For a disconnected global regular fibre, strict localization selects the relevant branch and makes no connectedness claim about the original fibre. Empty schemes have no specified points and give vacuous assertions. Identity arrows, codimension-zero geometric isomorphisms and the empty factorization obey the same formulas. No proof step exceeds 2000 characters, and the only longer constructions are the source's explicit generic-point and square arguments, with their non-elementary input cited.

The remaining unfinished work is precisely the three new unsplit supporting lemmas; this delivery intentionally splits only one level. No statement is disputed, and no blocking mathematical gap remains in the item.
