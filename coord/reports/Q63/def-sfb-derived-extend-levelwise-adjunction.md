# Q63: def-sfb-derived-extend-levelwise-adjunction

## Files written
- dag/nodes/sec-proetale-coefficients/def-sfb-derived-extend-levelwise-adjunction.json: existing definition, split; no exact Mathlib match for the derived module-object construction.
- citations.json: verbatim statements supporting every step citation.
- No new nodes and no Mathlib leaves.

## Attachments
None. Searches of WeilConjectures in the current read-only slopmaster2 checkout by blueprint id, recorded declaration name and scalar-change adjunction names found no matching declaration. The recorded ModuleObjects/DerivedExtendScalars.lean file is absent there. The upstream master file does contain CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction at lines 135-137, but depends on the sorry at preservesKFlatQuasiIso, lines 107-110, and is reference material only.

## WANTED
None.

## Corrections and unfinished work
The imported proof had no uses or proof_deps despite naming two constructions. I added precisely those dependencies and the ambient-situation node, and replaced the bare instruction to transport with the maps, inverse and naturality calculation. The statement is unchanged. No statement dispute or departure from the unit route. All blueprint and import metadata is retained.
The dependency nodes remain responsible for construction of the derived adjunction and comparison; this item does not reprove them. The stale slopmaster2 audit record was retained as instructed rather than rewritten from an unavailable file.

## Blueprint and duplicate search
Read the chapter record and the unit sk-def-sfb-derived-extension-of-scalars, its current main-20261015 statement and the item's statement and proof. Ran blueprint_refs ancestor and searches for adjunction, levelwise restriction, and derived extension of scalars, and searched the DAG for transport and right-adjoint isomorphisms. The key unit node contains this adjunction together with existence and computation of derived extension. It is recorded in same_as, but not cited, since its construction must not be used circularly. No new node is needed for elementary postcomposition with an isomorphism. The unit's realized record is already populated; this item is not its key node.

## Mathlib searches
Read searches.jsonl, including the completed searches whose tool sessions disappeared during provider interruptions. All six recorded queries actually ran: LeanFinder twice with distinct phrasings, Loogle for ofNatIsoRight, two grep patterns, and LeanSearch. The ordinary ModuleCat.extendRestrictScalarsAdj and scalar-change hits concern ordinary modules, not derived module objects in a general closed monoidal category. Read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean lines 134-151: the general derived theorem requires composite derivation compatibility, so does not supply the present construction in one specialization. Read Mathlib/CategoryTheory/Adjunction/Basic.lean lines 485-531: ofNatIsoRight supplies only transport after its two inputs have been constructed. Its Hom formulas agree with step 3. It is not a Mathlib leaf for this item. No unperformed search or unavailable service is recorded as a negative match.

## Not duplicates
No new nodes.

## Review by Q63
I read the item's current blueprint source and its one-paragraph proof, the parent unit and chapter, the full statement of lem-sfb-extend-scalars-kflat, and the statements of both construction nodes. I also read the upstream master DerivedExtendScalars.lean lines 95-137 as a comparison of the intended hypotheses and the final ofNatIsoRight definition, without treating it as a finished proof.

Step 1 uses lem-sfb-extend-scalars-kflat only to identify the ambient hypotheses of the imported statement. Its statement explicitly assumes closed symmetric monoidal Grothendieck abelian C with additive tensor, functorial flat resolutions and a morphism of commutative ring objects. The statement of def-sfb-derived-extend-restrict-adjunction explicitly gives LE adjoint to RU under exactly those hypotheses and defines their source and target derived module categories. I checked it gives the adjunction itself, rather than only the ordinary adjunction or a definition of a derived functor. Its natural Hom bijection is the defining data of that adjunction.

Step 2 cites def-sfb-derived-restrict-levelwise, whose complete statement explicitly gives the canonical isomorphism RU to D(U), with direction from S-modules to R-modules. I checked both ends and orientation before using its component as a postcomposition map. No assertion that restriction preserves K-injectives is used.

Step 3 uses only the inputs of steps 1-2, category composition, inverses and naturality. I wrote the two inverse maps and the complete naturality equation for arrows in both variables, instead of hiding these behind 'transport'. Its unit and counit formulas have the correct types: K to H(FK) and F(HN) to N. Each proof step is below 2000 characters, and no standalone comparison or identification is hidden in a long step.

I checked identity scalar change (rho equal to identity returns the original bijection), zero objects and the zero ring, and the ordinary example Z to Z/n, where extension need not be exact but its derived version is allowed. The argument places no boundedness condition on K or N and does not assume S is flat over R. It is a purely categorical operation on the two already supplied constructions, so these cases change none of its inputs.

Against delivery-errors B-E: no statement-only child is incorrectly split, no missing definition is introduced, no source tag is used as a substitute for a statement, no off-route result is used, no new clause is merely renamed, and every non-elementary input is an explicit citation with a verbatim statement in citations.json. The source itself is blueprint/agent material, so proof_origin remains agent. No SGA source, Lean write, compiler, Lake, local gate, or shared-repository mutation was used.
