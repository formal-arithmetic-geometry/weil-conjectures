# Stage-1 delivery: pur9-dg-def-tangent

## Files written

- `dag/nodes/sec-smooth-purity/pur9-dg-def-tangent.json`: definition, split using existing constructions; no full Mathlib match.
- `citations.json`: empty list because this definition has no proof steps.
- `report.md`: this report.

There are 0 new nodes and 0 new Mathlib leaves. The original formula, projection, augmentation and zero section are retained, with their previously implicit construction dependencies made explicit. No Lean or repository files were written and no compiler was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, relative tangent bundle, tangentBundle and tangent_bundle found no exact declaration. The tangent-bundle discussion in `EtaleCohomology/Purity/Smooth/Basic.lean:195` is explanatory text above a sorry, not a construction or attachment. The existing sheaf of differentials, symmetric algebra and relative-spectrum interfaces are reused through their existing nodes.

## WANTED

None.

## Corrections and omissions in the imported item

The imported definition had no statement dependencies at all. Added the existing scheme and smoothness definitions, the relative differential sheaf, quasi-coherence, the explicit symmetric-algebra sheaf, its affine quasi-coherence and universal property, relative Spec and affine Spec. This elaborates the original definition without changing its hypotheses or mathematical meaning. The source is the current main-20261015 blueprint, not the older master snapshot. Its blueprint identity and import_flags are preserved; same_as is now the searched empty list.

A generic vector-bundle definition with Noetherian base and constant rank (`def-asd-vector-bundle-zero-section`) and the finite-field purity-setting definition (`def-pur-vector-bundle-zero-section`) cannot be applied to every smooth morphism here. They are not dependencies of this general definition. The scheme relative spectrum and symmetric-algebra interfaces have the needed unrestricted base hypotheses. No new lemma restates a clause of the item.

## Blueprint and duplicate searches

Read the chapter record and `dag/units/sk-lem-diag-reg.json`: the unit proves diagonal regularity and identifies its normal bundle with this tangent bundle. This supporting definition changes neither that unit's route nor its key statement. Whole-blueprint searches were `tangent`, `relative spectrum`, `symmetric algebra`, and `differential`, together with the ancestor query. Read DAG matches by title, concept, and Stacks tags 01LW, 01LX, 01UM and 08S2, and searched all node statements for tangent bundle and T_{X/Y}. Only this item defines the relative tangent bundle; the diagonal regularity node asserts an identification, not this construction. There is no new id and no same-tag new/existing pair requiring a Not duplicates comparison.

## Mathlib searches

Every entry in mathlib_searches is copied from the query text in this sandbox's actual searches.jsonl. Read all printed results. The first Loogle pattern was rejected for an unknown identifier; its entry is explicitly unavailable, and the successful replacement query `SymmetricAlgebra` was read. The two semantic phrasings return ring cotangent modules, formal unramifiedness, affine schemes and affine space, while LeanSearch also returns manifold tangent bundles. None is the scheme tangent bundle. The two Mathlib/AlgebraicGeometry greps find no relative Spec or relative differential-sheaf construction. Read the local `Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean` construction and lift: these are ordinary ring/module algebra constructions, not the entire item. Therefore this item is split, not marked mathlib. No searches are invented or recorded as successful absence evidence when unavailable.

## Review by NI

I read the current blueprint file `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-diag-reg/pur9-dg-def-tangent.md` in full. It defines precisely Spec_X Sym(Omega_{X/Y}) and its augmentation section. I checked the actual local Stacks text: morphisms.tex definition-sheaf-differentials (01UQ), lemma-differentials-affine (01UT), and the neighbouring affine gluing explanation; modules.tex section-symmetric-exterior (01CF), lemma-local-tensor-algebra (01CG), and lemma-whole-tensor-algebra-permanence (01CL); constructions.tex definition-relative-spec (01LW), lemma-spec-properties (01LX), and definition-vector-bundle (01M2). Tag/label pairs were verified against tags/tags. There are no new nodes whose sources require a separate review.

This is a definition, so there are no numbered proof steps or non-elementary proof steps to quote. I instead checked every construction clause against the full statement of each dependency. `def-pc-scheme` supplies schemes and `def-sbc-smooth-morphisms` the smoothness predicate. `def-sc-relative-differential-sheaf` explicitly gives the associated-module description on affine charts mapping into affine charts of the target. Those neighbourhoods cover X, so it meets exactly the affine-local definition of quasi-coherence in `pqf-def-coherent`; no extra theorem asserting coherence, finite presentation or constant rank is used. `lem-weil-pbc-symmetric-algebra-sheaf-construction` gives the actual sheafification construction P^# and its map j, not merely an arbitrary algebra satisfying an unproved existence assertion. `lem-weil-pbc-quasi-coherent-symmetric-algebra-affine` applies to that same constructed algebra and a quasi-coherent F, and supplies both quasi-coherence and its affine-section identification. `lem-weil-pbc-quasi-coherent-symmetric-algebra-core` applies even to an arbitrary module sheaf and explicitly gives the unique extension of every linear map; taking the zero map into O_X therefore uniquely determines epsilon. `lem-weil-pbc-affine-morphism-relative-spec` gives the affine scheme for every quasi-coherent algebra and the contravariant morphism correspondence, including its affine-chart formula. Apply it to A, to O_X, and to epsilon: the identity X -> X has direct image O_X, so the source of the resulting section is X. Its being an X-morphism gives pi z = id; equivalently epsilon fixes scalars. The affine formula uses `def-weil-affine-spectrum` and the actual chart correspondence in that relative-Spec statement. Thus none of these citations is a mere definition used for a theorem it does not state.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against those sources. Definitions of the constituent notions and all non-elementary construction interfaces are named, there are no new nodes or hidden inline lemmas, and the definition retains empty proof/proof_deps. No existing proof internals are used. In particular the sheaf algebra is not confused with the naive presheaf of sectionwise symmetric algebras. The augmentation direction is A -> O_X, so its spectrum direction is X -> T, as required. No separation, finite-type-over-a-field, Noetherian or global relative dimension condition is smuggled in.

As small cases, for f=id_X the differential sheaf is zero and Sym(0)=O_X, giving T=X and the identity zero section. For affine space A^d_Y -> Y the affine formula is Spec B[v_1,...,v_d] over Spec B and the augmentation sets each v_i to zero, agreeing with the tangent bundle and its zero section. For d=0 this reduces to the identity. Empty schemes cause no nonemptiness requirement. A disjoint union of smooth morphisms with different relative dimensions still uses the same sheaf construction without demanding constant rank. These tests confirm the variance and the intended generality. There are no proof steps over 2000 characters.

## Unfinished work

None at this one-level definition split. The existing construction dependencies are reused with their own recorded proof status; no claim is made that this delivery proves them in Lean.
