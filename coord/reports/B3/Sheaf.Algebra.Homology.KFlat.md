## What changed

Completed the two remaining proofs in `Sheaf.Algebra.Homology.KFlat`.
`SheafOfModules.isMonoidal_W_separateHomUniverse` now tests localized maps by
precomposition into sheaves and uses the sectionwise tensor–Hom equivalence.
Private, fully proved helpers generalize the source library's TensorHom construction
from an equal-universe site to objects in `u`, morphisms in `v`, and coefficients
and modules in `max u v`. The internal Hom still lies in that coefficient universe,
since `max u v (max u v) = max u v`. No source module was changed.

`SheafOfModules.preservesZeroMorphisms_curriedTensor` uses the tensor/sheafification
comparison isomorphism. The underlying presheaf of the zero sheaf is zero; tensoring
it with a presheaf preserves zero morphisms sectionwise in ModuleCat and hence
preserves its zero object. Sheafification preserves zero objects as a left adjoint.
Thus the tensor of the zero sheaf with any sheaf is zero. Factor a zero morphism
through the zero sheaf and apply functoriality of right whiskering.

The second-variable proof already present is retained. All existing public
signatures, definitions, docstrings, attributes, and imports are unchanged.
No new public statement, definition, node, or sorry was introduced.
The second reading records the actual infrastructure proof route and its origin in
`dag/nodes/sec-picard-framework/def-pc-kflat-complex.json`; `proof_deps` remains empty.
The conservative command-level interface check is documented in
`coord/changes/kflat-proof-local-commands.md`; downstream modules need no adaptation.

## Proved and sorry left

Proved both original remaining sorries:

- `SheafOfModules.isMonoidal_W_separateHomUniverse`
- `SheafOfModules.preservesZeroMorphisms_curriedTensor`

Both belong to `def-pc-kflat-complex`. No sorry remains in the delivered module,
and none is added elsewhere. The existing
`SheafOfModules.preservesZeroMorphisms_curriedTensor_obj` remains proved.
The private curry, uncurry, inverse, naturality, and localization helpers are all
proved. Compilation and the required delivery dry run check all declarations.

## No longer needed

None. No proof imports were added or removed. The node is a definition with no
planned proof dependencies to prune. Its four statement dependencies (complexes,
acyclicity, total tensor complexes, and quasi-isomorphisms) remain needed.
The existing public imports provide the monoidal structure, abelian and colimit
instances, total tensor complex, and quasi-isomorphism infrastructure; their
public visibility is preserved for importers.

## Where the brief, the DAG or earlier work was wrong

The existing source library's `SheafOfModules.isMonoidal_W` and its tensor–Hom
adjunction are restricted to equal object, morphism, and coefficient universes.
They cannot be applied directly to the item's separate-universe signature.
Their sectionwise proofs generalize without new assumptions, as checked here
by Lean. This also treats empty sites and zero sheaves without extra hypotheses.

Searches read the source monoidal and internal-Hom modules, Mathlib's presheaf
monoidal structure and zero-object preservation lemmas, and the source tree for
the two theorem names. The prescribed Loogle query for
`Functor.PreservesZeroMorphisms` returned an unknown identifier; LeanFinder's
monoidal localization/zero-morphism query returned general monoidal preadditive
and presheaf monoidal ingredients, but no exact sheaf theorem.

The DAG records no proof plan for this definition. No unit statement or unit
proof step is bypassed: the unit's realized statement and step lists are empty.


## Second reading by B3

1. **Public interface: pass.** Compared the delivered module with the repository
   using `diff` and the delivery declaration parser. All five existing declaration
   statements, attributes and docstrings are identical; the two public definition
   bodies and the already-proved second-variable theorem are unchanged. The only
   additions are private proof helpers and their local context. The existing change
   record explains the conservative command-level interface classification.
2. **Proof and trust: pass.** Independently compiled the module with `lcompile.py`
   (exit 0, no warnings). A scratch copy with `#print axioms` for all five public
   declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No sorry or prohibited declaration mechanism occurs in the delivered Lean file;
   private data constructions are fully defined and their proof obligations closed.
3. **Split statements: pass, none.** There are no split-off statements or new public
   statements to audit. Read the source TensorHom constructions and the sheaf
   monoidal localization proof, checking the universe enlargement and the inverse
   and naturality calculations. Empty sites cause no missing evaluation: evaluation
   is only made when an object U is supplied. Zero sheaves and zero rings cause no
   exception to the bilinear construction or zero-object argument.
4. **Route and pruning: pass.** The upstream tensor-Hom and localization theorems
   require equal site universes and cannot directly replace these private helpers.
   A separate LeanFinder search for zero-object preservation recovered Mathlib's
   map_isZero and preservesZeroMorphisms_of_map_zero_object; the latter uses the
   same factorization through zero as this proof and supplies no missing sheaf
   tensor comparison. Tested removal of each Mathlib import in scratch copies:
   Abelian is needed for homology/zero objects, Colimits for HasMapBifunctor,
   Grp.FilteredColimits for sheafification/local-bijectivity instances,
   BifunctorShift for mapBifunctor, and QuasiIso for the resolution definition.
   The source Monoidal import supplies the tensor structure used by the public
   statements and definitions. Thus all imports remain public for those uses.
   No old proof dependency is omitted (the old list is empty). The unit
   sk-thm-picard-semicon has empty realized statement and step lists, unchanged.
5. **DAG agreement: repaired.** The definition node correctly names all five public
   declarations and has the same statement and four statement dependencies.
   Recorded the sectionwise adjunction, localization and zero-object arguments in
   its proof and proof_origin fields so the node now describes the proofs actually
   delivered. No DAG-node theorem is used as a proof dependency; proof_deps stays
   empty. No new nodes are needed for fully proved private implementation helpers.

Second reading changed only the report and the existing node's proof metadata.
No Lean repair was required. Scratch compilation experiments are not delivered.
