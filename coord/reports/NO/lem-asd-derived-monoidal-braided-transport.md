# Stage-1 delivery: lem-asd-derived-monoidal-braided-transport

## Files written

- `dag/nodes/sec-smooth-purity/lem-asd-derived-monoidal-braided-transport.json`: item, statement; split into nine explicit steps. No complete Mathlib match.
- `dag/nodes/sec-smooth-purity/def-asd-derived-monoidal-comparison-data.json`: new definition, unsplit; specifies binary and ternary universal properties and compatibility of the supplied associator. No complete Mathlib match. It contains conditions on given data, no existence assertion or proof sketch.
- `citations.json`: one verbatim statement excerpt for the comparison-data node cited by each of the nine steps.
- `searches.jsonl`: actual msearch log, retained. `write_split.py` is a sandbox-only writing script, not part of the delivery.

One new node, zero Mathlib leaves. No Lean file, compiler, Lake, local preflight, repository write, or direct git command was used.

## Attachments

None. The exact audited declaration `CategoryTheory.DerivedMonoidal.braidedCategory` at `lean/WeilConjectures/CategoryTheory/DerivedCategory/Monoidal/Braided.lean:304` still has two `sorry` hexagon arguments. I read its complete abstract section, lines 250–305, and its file-level explanation. The existing inverse construction is closed but does not prove the hexagons. Searches in `lean/WeilConjectures/` by the blueprint tag and by braided transport did not find an exact closed declaration.

`CategoryTheory.DerivedMonoidal.braidedCategory'` in `CategoryTheory/Monoidal/DerivedBraided.lean` is a different, closed result: its KFlat section assumes `W.RespectsIso`, `W.localizerMorphismKFlat.IsLeftDerivabilityStructure`, and `W.HasTwoOutOfThreeProperty`, absent from this abstract item. I read that section and did not attach it, add its extra hypotheses, or replace the prescribed ternary-universal-property route with its resolution argument. The concrete `DerivedCategory.braidedCategory'` also has stronger Grothendieck and flat-resolution assumptions.

## WANTED

None. The relevant current blueprint and upstream source files are available. The proof is marked `proof_origin.by = agent`: the source's abstract transport docstring states that ternary extensionality gives the hexagons, and this delivery supplies the omitted calculations. It does not claim a human-written proof of those calculations.

## Source error

STATEMENT-DISPUTED: the imported statement identifies a derived monoidal structure with the binary derived tensor alone. That does not determine the associator and is insufficient for the asserted hexagons. This is an ambiguity/error in the natural-language import, not an error in the actual Lean declaration's hypotheses.

Here is an explicit counterexample to the binary-only reading. Over a field of characteristic different from 2, let C be the category of Z/2-graded vector spaces with the usual tensor, usual associator, and ordinary unsigned flip. Let D have the same underlying category, tensor bifunctor, unit and unitors, but multiply its associator on homogeneous degrees i,j,k by (-1)^(ijk). This is monoidal: the pentagon scalar condition is

`jkl + i(j+k)l + ijk = ij(k+l) + (i+j)kl` in Z/2,

which follows by expansion, and the unit conditions hold because an exponent with a zero entry is zero. Take L to be the identity localization at isomorphisms, and q to be the identity binary comparison. The tensor is its own binary left derived functor along the identity; the transported braiding is the unsigned flip. On a triple of one-dimensional degree-one spaces, the forward hexagon's first path has scalar (-1)(+1)(-1)=+1, while its second has (+1)(-1)(+1)=-1. The asserted transported braiding fails a hexagon.

The repair explicitly requires the ternary derived comparisons and the associator induced from C. These conditions are already present in the upstream `Functor.HasDerivedMonoidalCategory` and construction: `lean/WeilConjectures/FromJoel/CategoryTheory/Monoidal/Derived.lean:143–156` supplies both ternary universal properties, and lines 170–183 construct the associator and its comparison equation. Its additional unary/four-variable conditions construct the unitors and monoidal coherence, already assumed for D in this statement. The repaired statement uses only the binary/ternary portion needed for braiding and covers every instance of the audited declaration. The twisted counterexample fails the repaired associator equation, as it should. No target statement was changed.

The imported `stmt_deps` cited `def-weil-abstract-derived-category`, which defines derived categories of abelian categories and does not define this arbitrary localization's monoidal comparison data. I replaced it with the appropriate existing monoidal/localization notions and the new precise data definition.

The supplied chapter and unit are retained. `sk-prop-sf-cbc` has no proof steps and this ancillary audit node is not its key statement, so no unit realization file is changed. The current blueprint places the ancestor's proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`. I read it, the imported master source, and the current `lem-sfb-derived-monoidal.proof.md` paragraph about two-, three- and four-variable tensors and descended constraints.

The ancestor helper returns `None`: this maintainer-created item's `created.item` is null despite its supplied `blueprint.from.node = thm-asd-smooth-tensor`. I left its maintainer-owned origin record unchanged. The new node records the helper's null ancestor, with the actual supplied blueprint origin and its precise opening tensor-transposition place written in `from.place`, and `via` containing the item. This preserves both pieces of information without inventing a creation history.

## Searches and Mathlib decisions

I searched the entire DAG by braided/derived transport, binary and ternary derived functors, multivariable universal properties, and the expected source declaration names. Whole-blueprint searches included `braid`, `left derived`, `multivariable`, `Kan extension`, `derived monoidal`, and `derived tensor`. I read the statements of the closest existing nodes rather than relying on their titles.

All newly recorded Mathlib searches are actual msearch invocations, whose exact tool/query and output metadata are in `searches.jsonl`. The comparison-data definition was searched with both phrasings: a derived monoidal structure with binary/ternary/quaternary iterates, and right Kan universal properties applied to the tensor and its associator. Loogle and source grep confirmed the absence of `HasDerivedMonoidalCategory`, `DerivedMonoidal`, and multivariable derived API from pinned Mathlib. The class is in the project's `FromJoel` sources. Searches found ordinary braided monoidal localization, Tor, Day convolution, and individual right Kan extension APIs. I read `Mathlib/CategoryTheory/Functor/KanExtension/Basic.lean:74–113` and the ordinary localization braided structure at `Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean:124–139`. The former supplies the individual universal bijection; the latter requires a tensor-stable class and invertible tensor comparisons. Neither states the combined derived comparison datum or the item under its hypotheses.

For the item, the second semantic phrasing asked directly about hexagon coherence transported through a right Kan extension tensor with derived triple iterates. Its hits were the generic trifunctor hexagon API, not the derived transport. No unavailable service was recorded as a negative search result.

## Not duplicates

- `def-asd-derived-monoidal-comparison-data` vs `lem-sfb-multivariable-derived-calculus`: the existing theorem constructs derived functors under chosen left derivability structures and counits invertible on resolving objects. The new definition imposes universal properties directly on given binary/ternary tensor data and requires the particular associator equation; no resolving subcategory or invertibility is assumed.
- `def-asd-derived-monoidal-comparison-data` vs `lem-sfb-braided-monoidal-localization`: ordinary monoidal localization has tensor-stable W and invertible comparison maps; the new data allow noninvertible q and do not assert a braiding.
- `def-asd-derived-monoidal-comparison-data` vs `lem-pur-derived-tensor-additive-constraints`: that node concerns K-flat module-sheaf models, shifts, additive constraints and tests on resolving tuples, not abstract localizations and their supplied right Kan counits.
- `def-asd-derived-monoidal-comparison-data` vs `lem-sfb-derived-monoidal`: that blueprint theorem constructs a derived tensor for Grothendieck abelian categories with flat resolutions; it does not define the abstract binary/ternary comparison predicate.

There is no shared Stacks tag in the new definition's source record. The definition records hypotheses that the item needs, not a clause of its conclusion. The inverse equations, reindexing argument, and each hexagon calculation are retained as steps, not new lemma nodes.

## Review by NO

I checked delivery-errors B–E with the actual node statements and sources open. For the item I read the entire abstract section of upstream Braided.lean and the full derived-monoidal hypothesis and associator construction in FromJoel's Derived.lean. For the new definition I used the current blueprint's paragraph on iterated tensors and checked each displayed comparison against Derived.lean's `counit₁₂_app`, `counit₂₃_app` and `associator_hom_fac_app_app_app`. Its universal bijection has the right direction: maps *into* the derived tensor are detected after the counit. It asserts neither pointwise invertibility nor a resolving-subcategory criterion.

In step 1 the cited definition provides the binary universal bijection. Reindexing both sides by the involution interchanging the arguments produces the flipped target, so both b and c exist as natural transformations. Step 2 uses its injectivity, twice; I checked the indices of the inverse: c(U,V) lifts beta(V,U)^(-1), and the inverse of b(U,V) is c(V,U). This remains valid for genuinely braided, nonsymmetric categories. These are immediate uses of the stated hypothesis, not unnamed theorems about derivability.

In step 3 the cited definition states both ternary bijections and the associator equation. I wrote the permutation and inverse-permutation operations on a test functor explicitly; they commute with L in every coordinate. The inverse associator equation is obtained by multiplying by inverse isomorphisms, not by cancelling q. Steps 4 and 5 each use that same cited equation, the binary factorization from step 1, and naturality of b and q. I checked domains and codomains: both forward paths start at (x star y) star z and end at y star (z star x), and are postcomposed with q^r(Y,Z,X). The resulting source-category paths are precisely the forward hexagon for the given beta. Step 6 applies the permuted right-parenthesized ternary injectivity. The definition's statement gives exactly this universal property; no existence theorem with a small-index or flatness hypothesis is being substituted.

Steps 7 and 8 repeat the full calculation with inverse associators. Their paths start at x star (y star z), end at (z star x) star y, and are postcomposed with q^l(Z,X,Y). I checked that the source-category expressions are exactly the reverse hexagon, with alpha(X,Y,Z)^(-1) on the first path and alpha(X,Z,Y)^(-1) on the second. Step 9 applies the left-parenthesized ternary injectivity from the cited definition and assembles the braiding. All extra equalities used in these calculations are the written naturality equations, functorial composition, or inverses, rather than an unstated coherence theorem. This is why the individual steps are marked elementary: each is a short substitution into a universal property assumed in the statement, or a displayed calculation from the preceding equations. They do not smuggle in the whole transport as a lemma. Every step is under 2000 characters.

Small cases checked include the identity localization with the canonical associator (the lift is beta), the terminal monoidal category (all maps and diagrams are identities), and the twisted Z/2-graded associator above (excluded by precisely the repaired condition). The abstract proof never requires q to be epic or invertible; equality is obtained by universal injectivity on *natural transformations*, not componentwise cancellation. The definition makes no claim that arbitrary binary derived tensors have derived triple iterates, so no unproved existence fact is hidden inside its data. Citations were extracted verbatim from its statement and matched locally, one for every step/use pair. Definitions and existing Mathlib leaves are notions, not off-unit replacement proof routes. No SGA source was used.

## Unfinished work

None in the authorized one-level split. The one new definition remains unsplit as required; it will receive its own independent stage-1 handling. Delivery is subject to the required server dry run and subsequent push.
