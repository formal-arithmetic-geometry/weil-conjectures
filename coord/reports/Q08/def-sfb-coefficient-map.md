# Stage-1 worker report: def-sfb-coefficient-map

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-coefficient-map.json` — existing definition, split; no complete Mathlib match. Retains the three existing statement dependencies, gives the construction as an elementary application of the existing ring-object functor, records seven actual searches, and corrects the proof-source path.
- `citations.json` — the verbatim part of the sole cited statement that supplies the transported ring structures and the functor.
- `searches.jsonl` — appended only by the prescribed `msearch.py` commands.

There are zero new nodes and zero Mathlib leaves.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for `def-sfb-coefficient-map`, `coefficientMap` and coefficient-map/change terminology found no declaration of this construction. The blueprint name is likewise absent there. The broad terminology search found trace-formula coefficient maps and a polynomial coefficient-map lemma; they do not have this statement. The upstream-master reference has `AlgebraicGeometry.ProEtale.coefficientMap` in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:95`, an abbreviation for `(upperStarFromPoint X).map a`, under `MonObj` and `IsMonHom` hypotheses. I read its surrounding variables and definition. Master is reference material, not a completed slopmaster2 attachment.

## WANTED

None. The current blueprint supplies the definition and proof, and all cited statement interfaces exist locally. No SGA source is used.

## What was wrong in the node, blueprint, or earlier attempt

The earlier sandbox attempt left `mathlib_searches` empty despite a search log. It also attributed the proof to `def-sfb-coefficient-map.md`, which contains only the statement. I recorded the seven new searches actually run in this pass and changed the proof source to the adjacent `def-sfb-coefficient-map.proof.md`. The definition's mathematical statement is unchanged. No statement dispute was found.

The old proof repeated the general assertion that a monoidal functor preserves monoid morphisms. The existing dependency already states the requisite functor on ring objects. I replaced that repetition by the explicit construction: apply that functor to the given morphism, identify its source, target and underlying map, and name the resulting morphism `a_X`. This is elementary relative to the cited interface and needs no new theorem node.

The current imported node has no `chapter`/`unit` fields, and `dag/chapters/sec-proetale-coefficients.json` and `dag/units/sk-prop-sfb-cartesian-coefficients.json` do not exist. I therefore read the current blueprint chapter and unit `_section.md` files directly, as well as the unit's `.proof.md`; I did not invent or edit maintainer-owned metadata or unit records. This item is a subsidiary definition, not the unit's key statement, so no realization record changes are required.

## What I could not finish, and why

No mathematical work remains for this one-level definition split. Delivery awaits the required fresh second reader; this worker runs only `deliver.py --no-push`.

## Not duplicates

No nodes were created. The whole-DAG keyword search and `tools/blueprint_refs.py search 'coefficient change'` found `sk-def-sfb-coefficient-change`. I opened its statement and proof: it assumes commutative condensed rings, includes derived extension/restriction of scalars and two naturality squares, and its proof explicitly cites this item. It cannot replace the present construction for arbitrary ring objects and is not equivalent to the whole item, so `blueprint.same_as` remains `[]`. The subfield coefficient-map definitions specialize this item; the identity, composition and square lemmas concern properties of it. None supplies a replacement definition without this dependency. The search for `ring objects` also found the already cited pulled-back-coefficients interface; no new node for its functor was introduced.

## Review by Q08

I read the current chapter `sec-proetale-coefficients/_section.md`, the parent unit `sk-prop-sfb-cartesian-coefficients/_section.md` and its proof, and both the statement and proof files for this item under `literature/blueprint/main-20261015/blueprint/`. The source permits a morphism of arbitrary condensed rings and any scheme; neither commutativity nor finiteness, properness, nonemptiness or an admissible coefficient list is needed. The unchanged statement keeps exactly that generality and exactly the map `p_X^*a`. I also read the existing condensed-ring and pullback-from-point node statements: they supply the source category of ring objects and the strong monoidal inverse image for each scheme. These are the notions named by the statement dependencies.

For step 1 I opened `sk-def-sfb-pulled-back-coefficients.json` and its current blueprint `_section.md`. Its statement gives the transported ring structures on `p_X^*Λ` and explicitly says that `Λ ↦ Λ_X` is a functor from ring objects on the point to ring objects on `X_proét`. Thus the given ring-object morphism `a` has an image with precisely source `Λ_X` and target `Λ'_X`; its underlying sheaf map is the image under `p_X^*` in the transported-structure construction. A morphism in the target category is, by definition, a ring-object morphism. This is the entire step, marked elementary relative to that statement. It does not cite the dependency's proof or reconstruct its monoidal coherence argument. `citations.json` quotes the transported structures and functor clause verbatim, rather than merely a definition of an object. This checks C1, C3 and C4 without hiding a further non-elementary fact.

I checked the search hits by reading Mathlib `CategoryTheory/Monoidal/Mon.lean`, especially `map.instIsMonHom` at line 850 and `mapMon` at line 867. These are the general categorical machinery behind the already existing dependency; they do not construct the project-specific `p_X^*` or `Λ_X`. The first semantic search concerned the full pro-etale construction; the second used the more general lax-monoidal formulation. Both are recorded with the exact query text, along with Loogle, LeanSearch and source grep. A single-file grep call exposed a wrapper formatting defect (line numbers printed in the file field); its search is recorded as returned, then I repeated it on the containing directory and read the actual file. No unavailable search is claimed to have found nothing, and no unexecuted query is recorded.

For the mathematical edge cases I checked `X = ∅`, the zero ring as either coefficient object when a unital ring morphism exists, and noncommutative coefficients. The cited functor is stated for every scheme and every ring object, so all these cases are covered; the construction never chooses a section, divides by a coefficient or assumes a ring map exists where it does not. At the identity morphism it returns the identity by the already stated functor structure. No extra edge-case theorem is asserted. Because there are no new nodes, B1–B8 and the new-statement small-case tests are vacuous; the existing item remains self-contained with all three notions cited, its TeX preserved, and no proof content moved to a child. I preserved all imported flags and blueprint metadata apart from the worker-owned `same_as` search result. The split uses no descendant or off-route statement and introduces no cycle.


## Second reading by Q08

- Item statement: independently compared every hypothesis and the displayed definition with `main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/def-sfb-coefficient-map.md`; the statement is exactly the source body. PASS: arbitrary scheme, arbitrary unital condensed ring objects, and a given ring-object morphism; no commutativity, invertibility or geometric restrictions added. The definition and its claimed ring-map property match the adjacent `.proof.md`.
- Step 1: independently opened the statement of `sk-def-sfb-pulled-back-coefficients` and its source `_section.md`. It supplies both transported ring structures and the functor between ring-object categories. Applying that functor to the given `a` gives source `p_X^*Λ`, target `p_X^*Λ'`, and underlying map `p_X^*a`; being a morphism in the target category gives the ring-map property. PASS: elementary application of the cited statement, with no appeal to its proof and no missing non-elementary fact. The sole `citations.json` quote is literally a substring of that statement and includes the functor clause.
- New nodes: none. PASS: no elementary child, duplicate, restatement, or new-node form to repair; zero new nodes and zero Mathlib leaves.

I read the current chapter and parent-unit statement and proof, as well as the condensed-ring, pullback-from-point and ring-object definition statements. They define every notion used here, and the one-step construction stays on the prescribed route. The source is a blueprint definition, with no Stacks tag to verify; no SGA source enters the split. Checked the empty scheme (all coefficient sheaves and maps are zero), the zero coefficient ring whenever the stipulated unital ring morphism exists, a discrete field with its identity map on `Spec k`, and a noncommutative ring object. In each case the image under the stated functor is defined without an extra hypothesis; the identity case follows from functoriality. There is no integer parameter in this statement.

Independent whole-DAG and whole-blueprint searches for coefficient change confirmed the existing larger `sk-def-sfb-coefficient-change` interface is restricted to commutative rings and depends on this definition, so it cannot replace it without losing generality or creating a cycle. Exact-name and concept searches in the read-only slopmaster2 source found no attachment. I read upstream master's `ChangeOfCoefficients.lean:88-97`: its `MonObj`/`IsMonHom` inputs and `(upperStarFromPoint X).map a` body agree with the definition, but this reference is not an attachment to a finished proof.

I ran a fresh, more general LeanFinder query, “A monoidal functor induces a functor between categories of internal monoids with underlying map given by the functor map”. It returned `CategoryTheory.Functor.mapMon` and related machinery. Reading Mathlib `CategoryTheory/Monoidal/Mon.lean:850-852,867-869` confirmed the generic map preserves the unit and multiplication and that its underlying morphism is `F.map f.hom`. This supports the already cited functor interface; it does not define this project's pro-étale inverse image or coefficient objects. No additional node is warranted.

Changes made in this second reading:

- Added the actual independent search and its source-checked verdict to `mathlib_searches`; its raw result was appended by `msearch.py` to `searches.jsonl`.
- Appended this independent review, preserving `## Review by Q08` and all earlier report sections. No mathematical, source-path, dependency or citation repair was needed; the existing split and verbatim citation were correct.

Required dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q08 def-sfb-coefficient-map --no-push` printed `OK (not pushed)` at `09c5c6af36`: preflight passed.
