## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedBasisBinaryExtension` states
`AlgebraicGeometry.derived_basis_binary_extension`. Its only theorem has proof `sorry`.
Four real-data helpers package notions explicitly introduced in this item's own statement:
`DerivedBasisBinary.System`, `DerivedBasisBinary.Solution`,
`DerivedBasisBinary.restrictHom`, and `DerivedBasisBinary.IsComparison`.
These are item-owned helpers under the human's helper authorization, not independent
new mathematical assumptions or new independent notions. Every helper is listed in
`lean.declarations`. Nothing is proved, and no definition contains `sorry` or an
arbitrarily chosen map.

Source read in full: Stacks `cohomology.tex`, Situation 0D67 and its solution paragraph,
Lemma 0D68, Remark 0D69, the two-open construction of Lemma 0D6A, and the successor step
of Theorem 0D6C. The theorem docstring carries all seven proof steps of the DAG node,
including the crossing-member construction and the empty-cover argument.

Hypotheses and objects, clause by clause:

- A scheme X: `(X : Scheme.{u})`, Mathlib's recorded scheme declaration.
- The set of opens B: `(B : Set X.Opens)`; covering X: `hcover : sSup B = ⊤`.
- Intersection refinement: `hrefine` quantifies over every U,V in B and equates
  `sSup {T | T ∈ B ∧ T ≤ U ⊓ V}` with `U ⊓ V`. No topological-basis or finite-cover
  assumption replaces this weaker intersection-refinement condition.
- Local derived objects: `D : DerivedBasisBinary.System X B`, with `D.K U` in
  `DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U.val))`.
  This is exactly the localized-open-site encoding used by both existing basis-descent
  statements. `Scheme.Modules.overEquiv U` canonically identifies it with module sheaves
  on the open subscheme U; it imposes no quasi-coherence or boundedness condition.
- Every inclusion V ≤ U in B has `D.rho U V h`, an isomorphism from the actual derived
  `SheafOfModules.overMap` restriction of `D.K U` to `D.K V`.
- Identity transition: `D.rho_id`. Its right side is the sectionwise identity natural
  isomorphism, transported by `Functor.mapDerivedCategoryNatIso` and
  `Functor.mapDerivedCategoryIdIso`. This is the same canonical normalization as the
  existing BBD module's helper, written as a term rather than defining it a second time.
  Importing that downstream BBD module would obstruct its future proof import of this
  binary-extension module, so the downstream declaration is not used as an import.
- Transition cocycle: `D.rho_comp`, using `derivedModuleOpenMapCompIso` to put
  the iterated restriction in the same category as the direct restriction.
- Negative self-Hom vanishing: `hnegative`, for every basis member and every integer
  `i < 0`, asserts `Subsingleton (D.K U ⟶ (D.K U)⟦i⟧)`. Since this is an additive
  Hom group, subsingleton is exactly vanishing, including its zero morphism.
- Derived-category universes: the explicit instance family for all opens fixes the
  same morphism universe w throughout. The object universe u and morphism universe w
  are independent. These are the usual localization existence/size parameters, not
  additional geometric or cohomological hypotheses.
- Unions O1,O2: `O₁ O₂ : X.Opens`; `hO₁`, `hO₂` say each is the supremum of all
  B-members contained in it. This is equivalent to being a union of a subcollection.
- Supplied solutions: `S₁ : Solution X D O₁`, `S₂ : Solution X D O₂`. A `Solution`
  contains its derived object `F`, isomorphisms `s U hU` for EVERY U in B with U ≤ O,
  and `compatible` for every inclusion between these members. The source's
  `rho_V^U ∘ (s_U|V) = s_V` is the field `compatible`; the displayed inverse
  canonical comparison changes direct restriction to iterated restriction.

Conclusions, clause by clause:

- `∃ c₁₂` gives an isomorphism between the two restrictions on `O₁ ⊓ O₂`.
- `IsComparison X S₁ S₂ c₁₂` is precisely, for every U in B contained in the overlap,
  `s₂,U ∘ (c₁₂|U) = s₁,U`. Its `restrictHom` is the actual restricted morphism
  conjugated by the two canonical composition comparisons, not a freely supplied map.
- `(∀ c, IsComparison X S₁ S₂ c → c = c₁₂)` gives uniqueness among all such
  isomorphisms, without also requiring the cocycle or extension from its competitors.
- The next conjunct quantifies over EVERY third union O3, its supplied solution S3,
  and ANY similarly characterized comparisons c13 and c23. It asserts the equality
  of c13 restricted to the triple overlap with restricted c12 followed by restricted
  c23. The triple open is `(O₁ ⊓ O₂) ⊓ O₃`. The common intermediate object is the
  direct restriction of S2.F, because `restrictHom` normalizes both endpoints.
  Existence and uniqueness of the similarly characterized comparisons are given
  by the universally quantified first clause of this same theorem applied to the
  pairs (O1,O3) and (O2,O3); the triple clause quantifies over all such comparisons.
- The final existential supplies `S : Solution X D (O₁ ⊔ O₂)` and the required
  restriction isomorphisms `f₁`, `f₂` to S1.F and S2.F.
- Its first conjunct is exactly `f₂|W = c₁₂ ∘ (f₁|W)`, where W is the overlap;
  both sides start at the direct restriction of S.F through the inverse canonical
  composition comparisons.
- Its last two conjuncts say `s_U = s_j,U ∘ (f_j|U)` for EVERY basis U inside
  O_j, j=1,2, with the same canonical normalization.
- Because S is a `Solution` on the full union, its `s` and `compatible` fields
  also supply all crossing-member isomorphisms and ALL their inclusion equations.
  There is no disjunction requiring U to lie in one of the two pieces.
- There is no quasi-compactness, affine, finite, nonempty or cohomological-bound binder.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Scheme.Opens`, read at their full definitions/docstrings.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (the shared unbounded derived-category
  construction), read with its carrier/universe explanation. The local categories are
  its open-site model already used by the recorded basis-descent dependencies.
- `Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion`:
  `AlgebraicGeometry.moduleOpenMapCompIso` and
  `AlgebraicGeometry.derivedModuleOpenMapCompIso`, read at their full signatures,
  docstrings, and real-data bodies. The new definition node
  `def-trf-derived-module-open-map-comp-iso` owns exactly these two existing
  definitions, recorded with `existing: true` on their unchanged published module.
  The increasing-union theorem node is not a statement dependency.
- Proof-only `Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue`:
  `AlgebraicGeometry.derived_basis_local_hom_glue`, read with its full source proof
  docstring and signature, including its empty-cover clause.
- Proof-only `WeilConjectures.AlgebraicGeometry.DerivedOpenGluingObjects`:
  `AlgebraicGeometry.derived_open_gluing_objects`, read with its full signature and
  cone-construction proof docstring. It supplies objects only, as required by step 4.
- `SheafOfModules.overMap` and its shared exactness/additivity instances come from
  the imported module interfaces; no restriction or exactness structure is replaced.

Edge cases checked before writing and again against the final signature: empty X and
B; B containing the empty open; an empty piece; disjoint pieces; equal/repeated pieces;
O3 empty or repeated; zero local objects; unbounded objects; a basis member crossing
both pieces; and every possibly empty restricted indexing family. All occur in the
signature without an extra premise. For an empty B, `hcover` forces X to be empty.
The `Solution` definition still permits an empty family of s-maps. Empty overlaps
remain derived categories with zero objects, and no nonemptiness is required.

Searches for an existing statement or packaging:

- `msearch.py leanfinder`, query "Glue derived descent solutions on two open unions
  with negative self Hom vanishing and compatible identifications on every basis open":
  8 results, including scheme gluing and ordinary sheaf-section gluing; none states
  the derived binary extension with original-family equations.
- `msearch.py loogle`, query `DerivedCategory, "glue"`: 0 results.
- `msearch.py grep`, query
  `(derived|DerivedCategory).*(glue|gluing|descent)|(glue|gluing|descent).*(derived|DerivedCategory)`
  in Mathlib/AlgebraicGeometry: 0 results.
- `msearch.py leansearch`, query "Derived category descent solutions over a basis of
  opens and unique compatible overlap comparisons": 8 results, including abstract
  derived categories and pseudofunctor descent; none gives this statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for derived/basis/descent and
  exact item/declaration/module names: found the BBD, local-Hom and increasing-union
  modules read above, but no binary-extension theorem. The BBD theorem concerns a
  global solution, not extension of two supplied solutions and its triple cocycle.
- Further `rg` in project and Mathlib module-sheaf sources for overMap composition
  found the shared comparison helpers; reused them. Searches for a named derived-basis
  solution/system packaging found no existing declaration.
- Exact item/name search of `dag/lean_names_upstream.json` and upstream sources found
  no match. No repair note for the item was present.

No statement correction or disputed claim. The item's original statement and proof are
unchanged. The added statement dependency is now the new definition node owning the
two existing canonical restriction-composition definitions.

Validation: required scompile.py checked this module both as a sandbox file and under
its library module name, with no errors or warnings (57.4 s and 50.5 s respectively).
The only postponed proof is the named main theorem.


## Repair of returned delivery 743e33f8097e

H2/H12: the returned packet cited the increasing-union theorem node solely to access
its two plain definitions. Added `def-trf-derived-module-open-map-comp-iso`, with the
required stage-2 definition-node fields, and replaced that theorem node in the item's
stmt_deps by this definition node. The new node cites exactly `def-pc-scheme` and
`def-pc-derived-category`. Its `existing: true` record owns both published declarations,
with the derived comparison's signature copied verbatim from the source. It owns no theorem.
The unchanged Lean module still imports the module containing those definitions.

The current read clone's item has no Lean record and only the two original statement
dependencies. Relative to that base this packet changes only lean and adds the new
definition dependency. Relative to the returned packet it replaces the incorrect
ownership edge and adds its definition-node record. The delivery wrapper constructs
the repaired commit on the refreshed current server main branch.

## New nodes

`def-trf-derived-module-open-map-comp-iso` specifies the ordinary sectionwise identity
comparison from successive to direct open module restrictions and its precise derived
comparison. Source: Stacks cohomology.tex, Situation 0D67, Remark 0D69 and Lemma 0D6B,
whose cocycle equations use these canonical identifications. The exact existing definitions
are `AlgebraicGeometry.moduleOpenMapCompIso` and
`AlgebraicGeometry.derivedModuleOpenMapCompIso` in
`Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion`; no Lean definition is copied or moved.
The ordinary signature has a scheme X, opens T,V,U and inclusions i,j; its target is the
natural isomorphism `overMap j ⋙ overMap i ≅ overMap (i ≫ j)`. Its body is the
sectionwise identity. The derived signature adds only the three explicit derived-category
size instances and applies the canonical exact-functor composition comparison followed
by the derived ordinary identity. Empty opens and identity inclusions are included;
universes u and w stay independent. Searches of DAG nodes found only the two theorem
nodes that mention these names, with no definition node owning them. Blueprint search
for "successive restriction" returned two unrelated coefficient nodes. LeanSearch found
8 ordinary restriction results, Loogle `"overMap"` found 12 general slice/sheaf results,
and Mathlib module-sheaf grep found overMap and overMapUnitIso but no exact comparison.
Upstream WeilConjectures grep found no matching definition; project Sheaf grep found
these exact two definitions, which are reused. The new node records each search and
its actual result. Its import_flags is empty, retaining the item's target reach metadata.
The live server source was read with `scompile.py --source` and confirmed the same
signatures and bodies. No independent second reader was started; the maintainer's
independent review remains the review specified by the dispatch brief.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
