## What changed

Completed both proofs in `lean/Sheaf/CategoryTheory/ProperFaceMatchingObject.lean`,
following the existing seven-step plan of
`lem-weil-pbc-matching-object-proper-faces`. The existing public declarations,
signatures, definitions and docstrings are unchanged. The second reading replaces
the public Sheaf matching-object import with its upstream definition module and
updates the node's proof, proof dependencies and proof origin to match the proof.

Added proved private helpers for face factorization, computation and extensionality
of natural families, extension of compatible face tuples, independence of the
factorization, and restriction compatibility. `extendFamily` is a private
noncomputable construction from the fully proved factorization theorem: it chooses
a missing vertex and a factor through its face. Its naturality and independence
are proved. It uses no unproved existence theorem or postponed proof.

For degree one, morphisms to `[0]` are unique and epimorphic; cancellation and
injectivity of the face indexing show two factorizations use the same vertex.
For higher degrees, two distinct missing vertices yield a common factor through
the double face, by `SimplexCategory.eq_comp_δ_of_not_surjective'` and
`SimplexCategory.δ_comp_δ'`. Applying the tuple equation proves independence.
Naturality gives the restriction equations. These constructions give the requested
bijections, with naturality by componentwise computation. Extending the original
boundary projections gives the proper-face cone; the original product/multifork
limit supplies its lift and uniqueness. The matching-map formulas follow from
functoriality, and uniqueness follows by restricting to codimension-one faces.

Source read: [Stacks Project, Tag 0186](https://stacks.math.columbia.edu/tag/0186),
the factorization, independence and compatibility argument, restricted to injective
proper faces as in the existing node. The local literature source is absent in
this clone, so the official online lemma was read. The unit record
`dag/units/sk-prop-h2.json` has no realization attached to this item. The existing
seven-step mathematical route is retained. The second reading updates Steps 2,
6 and 7 to describe the supplied cone and limit witness rather than invoking the
unfinished matching-object existence theorem.

Searches: LeanFinder for compatible families on proper simplex faces returned
simplicial-set face/subcomplex results, with no matching arbitrary-category limit
theorem. Loogle confirmed `SimplexCategory.eq_comp_δ_of_not_surjective`.
Ripgrep of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found the existing
simplex factorization/face identity and the boundary diagram definitions, but no
existing proof of either target declaration.

## Proved and sorry left

Closed both original holes, under
`lem-weil-pbc-matching-object-proper-faces`:

- `CategoryTheory.SimplicialObject.matching_object_proper_faces_one`.
- `CategoryTheory.SimplicialObject.matching_object_proper_faces_succ_succ`.

No `sorry` remains in the item, and none was added elsewhere. No split-offs or new
nodes were introduced. This is two proofs, not a decomposition.

Single-file compilation succeeds. Explicit `#print axioms` checks of both theorems
report exactly `propext`, `Classical.choice`, and `Quot.sound`. Those temporary
checks were removed from the final source. The proof covers degree one separately
and every degree at least two, including `n = 0` in the successor-successor theorem;
the equal-index and both strict-order cases of independence are all proved.

## No longer needed

Removed the import of `Sheaf.CategoryTheory.SimplicialMatchingObject`; replaced
it with `public import WeilConjectures.CategoryTheory.SimplicialMatchingObject`,
where `matchingBoundaryShape` and `matchingBoundaryIndex` are actually defined.
The Over and ObjectProperty imports remain public because the existing public
definitions use their data. No proof-only import is public.

The proof does not use the holed existence theorems `matching_object_zero`,
`matching_object_one`, or `matching_object_succ_succ`. It applies Mathlib's
`Fan.IsLimit` and `Multifork.IsLimit` APIs to the supplied witnesses directly.
Removed `lem-weil-pbc-simplicial-matching-object` and
`def-galois-finite-limits-colimits` from the node's `proof_deps` and from the
corresponding proof steps: existence and finite completeness are not invoked.
Both remain unchanged as statement dependencies. The former still supplies the
mathematical boundary diagram specification; the latter is an unchanged
hypothesis. No whole module leaves the target closure: other modules still import
the Sheaf matching-object module independently. The removed import is an edge
pruning, not a claim of whole-module progress.

The public re-export change is recorded in
`coord/changes/proper-face-matching-object-diagram-import.md`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG's factorization and face identity are
available as Mathlib lemmas. The earlier report incorrectly said the Sheaf wrapper
was necessary for the boundary definitions; the definitions belong to its upstream
import. The DAG also attributed Steps 6 and 7 to existence theorems, while these
Lean statements already supply the cone, limit witness and matching-map equations.
Those steps and the dependency union have been corrected. No definition or
statement needed correction, and no consumer adaptation was made.

## Second reading by D3

1. **Existing interface: pass.** Read the entire repository module and sandbox
   diff. All six existing declaration signatures are byte-for-byte identical;
   all four definition/abbreviation bodies and existing docstrings are unchanged.
   Ten added helpers are private. The only public import change is explicitly
   recorded above. Source-only `downstream.py` found 45 downstream modules and
   zero uses of the three existence theorems removed from the re-export; no
   consumer statement changes and no adaptation is needed.

2. **Proof and data: pass.** Compiled the original worker module, then the edited
   source with explicit axiom checks in `scratchpad/ProperFaceAudit.lean`.
   Both theorems compile without warnings and depend exactly on `propext`,
   `Classical.choice`, and `Quot.sound`. There is no `sorry`, forbidden declaration,
   or unproved construction. `extendFamily` chooses a factorization using the
   fully proved `face_factor`; its hypothesis `hx` proves independence for every
   factorization and `family_ext` proves uniqueness of the resulting family.
   Thus no arbitrary object is chosen from an unproved existence statement.
   Closed holes are exactly the two declarations listed above; holes added: none.

3. **Split statements and edge cases: pass.** There are no split-offs or new
   nodes. Independently checked the private intermediate statements. In degree
   one the proper face has source `[0]`, the factors to `[0]` are unique and
   epimorphic, and cancellation forces equal missing vertices. In degree two
   (`n = 0` in the second theorem), two distinct omitted vertices meet at a
   vertex; the proof factors through exactly this double face. Equal indices use
   mono cancellation, and reversed strict order uses symmetry. No degree-zero
   matching theorem is assumed. Fresh LeanFinder, Loogle and Mathlib grep searches
   with different queries found simplicial-set horn results and the simplex
   identities, but no arbitrary-category shortcut; repository grep located the
   upstream boundary definitions. No large proof rewrite was warranted.

4. **Route and pruning: pass after repair.** Read
   [Stacks Tag 0186](https://stacks.math.columbia.edu/tag/0186), its factorization,
   independence and compatibility proof. Step 1 is `face_factor`; Step 2 is
   `restrict_compatible` via the double-face object; Step 3 is
   `factor_independent_lt` plus the equal/reversed-index cases; Step 4 is
   `extendFamily.naturality`; Step 5 is `family_ext` and `extendFamily_face`,
   with precomposition naturality computed definitionally. Step 6 uses the given
   Fan/Multifork limit's lift, fac and hom_ext; Step 7 uses `hμ`, functoriality and
   hom_ext. The source's restriction to injective proper faces retains each
   factorization and commuting triangle used. The unit `sk-prop-h2` has empty
   `realized` statement and step arrays; neither matching-object node is a
   realized unit step anywhere in `dag/units`. No unit route is bypassed.
   Removed the unnecessary Sheaf wrapper import and listed every removed proof
   dependency under No longer needed; no whole-module pruning is asserted.

5. **DAG/Lean agreement: pass after repair.** Read the node and all six old proof
   dependencies. The factorization and face identity agree with Mathlib's
   `eq_comp_δ_of_not_surjective'`/`eq_comp_δ_of_not_surjective` and `δ_comp_δ'`;
   mono cancellation gives uniqueness. The simplicial-object and simplex-category
   definitions supply exactly the functor and indexing operations used. Updated
   Steps 2, 6 and 7 and `proof_origin` to describe the actual supplied witnesses.
   `proof_deps` is now exactly the union of the four remaining step dependencies;
   statements, statement dependencies, unit and all unrelated node fields stay
   unchanged. No new-node obligations arise.

Changed in this reading: the diagram import, the existing node's proof metadata,
the import change record and this report. The worker's proof bodies are retained.
