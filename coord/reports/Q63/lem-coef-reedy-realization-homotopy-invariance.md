## Worker report

Item: `lem-coef-reedy-realization-homotopy-invariance`, group Q63, stage 2,
2026-10-17. The module
`Sheaf.CategoryTheory.ReedyRealizationHomotopyInvariance` states
`CategoryTheory.reedy_realization_homotopy_invariance`. Its proof is `sorry`.
The item statement, proof and proof dependencies are unchanged. Its statement
 dependencies gain the new definition node `def-coef-simplicial-realization-map`.
No statement correction or disputed statement is needed.

The main statement renders every hypothesis and clause as follows:

- A simplicial model category is `{M : Type u} [Category.{v} M]
  [ModelCategory M] [HasLimits M] [HasColimits M]`, both prescribed
  `MorphismProperty.HasFunctorialFactorization` instances, `[SimplicialCategory M]`,
  `T : SimplicialTensorCotensor M`, and
  `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`. These are exactly the
  model hypotheses in the recorded nerve-localization theorem: Mathlib's model
  axioms give retract closure, two-out-of-three and the two lifting-characterized
  weak factorization systems, while completeness, cocompleteness and functorial
  factorization are supplied explicitly. `SatisfiesSM7` is the actual enriched
  pre/postcomposition corner-map Kan-fibration and triviality condition.
- `A B : SimplicialObject M` are functors from `SimplexCategoryᵒᵖ` to `M`.
  `_hA` and `_hB` assert `Reedy.leftClass
  (MorphismProperty.epimorphisms SimplexCategory).op (cofibrations M)` of their
  initial arrows. Positive maps in the opposite simplex category are opposite
  surjections. Thus these are precisely the relative-latching tests for Reedy
  cofibrancy in the recorded model structure. Neither diagram is assumed fibrant.
- The object `|C|` is the existing `SimplicialModelRealization.realization T C`.
  Its `summand T C n` is `T.tensor (SSet.stdSimplex.obj n) (C.obj (op n))`.
  `Operator` ranges over every triple `(m,n,α : m ⟶ n)`. `relationLeft` applies
  `C.map α.op`; `relationRight` is the tensor transpose of the standard-simplex
  map followed by the universal tensor element. Their coequalizer is exactly the
  displayed all-operator formula, with the node's `C_n ⊗ Δ^m` convention written
  using the dependency's `Δ^m ⊗ C_n` tensor notation. No realization is redefined.
- `f : A ⟶ B` is the given simplicial morphism and `g : B ⟶ A` its homotopy inverse.
  Lean uses diagrammatic composition, so `f ≫ g` means the node's `gf`, and
  `g ≫ f` means `fg`.
- `_hgf` is the disjunction of `Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 A))`
  and the reversed homotopy. `_hfg` is the independently oriented disjunction for
  `g ≫ f` and `𝟙 B`. `Nonempty` merely forgets the choice of the supplied prism
  data, so these express existence of the two homotopies without choosing either
  orientation. All four combinations of orientations are included.
- Mathlib's `SimplicialObject.Homotopy.h` is `A_n ⟶ B_(n+1)` indexed by
  `Fin (n+1)`. Its first and last face identities are respectively
  `h 0 ≫ δ 0 = g_n` and `h (Fin.last n) ≫ δ (Fin.last (n+1)) = f_n`.
  Its remaining five fields are exactly the node's other prism face and degeneracy
  identities, with `castSucc`/`succ` spelling out the valid index ranges.
  This is the combinatorial homotopy of the Mathlib dependency; it is not replaced
  by a degreewise family of tensor-cylinder maps.
- The conclusion is `WeakEquivalence (SimplicialModelRealization.map T f)`.
  The new `map` is the canonical map on the recorded coequalizer objects, given
  on each summand by `T.tensorMap (SSet.stdSimplex.obj n) (f.app (op n))` and the
  target summand inclusion. Its definition is `coequalizer.desc`, with the named
  relation-equality theorem; no arbitrary realization map or noncanonical choice
  is an assumption of the statement.
- There is no fibrancy binder, basepoint, nonemptiness, degree bound or restriction
  equating the object and morphism universes. Both universes are explicitly bound;
  the enrichment/tensor universe is `v`, following the recorded dependency API.

Dependencies read and used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.simplicial_model_nerve_localization` (full signature and proof
  docstring read), `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7` and
  its `cornerMap`. These fix the precise model-category hypothesis.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor` and `.tensorMap`. The latter uses the
  inverse enriched representing isomorphism of the given tensor universal element.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.model_structure` (full signature and docstring read),
  `.relativeLatching`, `.leftClass` and `.simplex_reedy_structure`. Their use gives
  the exact simplicial Reedy-cofibrancy predicate without an assumed Reedy model
  instance on diagrams.
- `Mathlib.AlgebraicTopology.ExtraDegeneracy`:
  `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopy`, the recorded
  `mathlib_match` for `lem-coef-simplicial-extra-degeneracy-prism`, together with its
  structure and section construction. The Homotopy signature and all its fields
  were read in `Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`.
- `Mathlib.AlgebraicTopology.SimplicialSet.Basic`: `SSet`; the other recorded
  `def-weil-pbc-simplicial-set` clauses were also read (`degenerate`, `nonDegenerate`,
  `Subcomplex`, `Finite`). `SSet.stdSimplex` supplies the representables `Δ^n`.
- `Sheaf.CategoryTheory.SimplicialModelRealization`: `summand`, `Operator`,
  `relationSummand`, `relationLeft`, `relationRight`, `realization`; the complete
  module and its augmentation helpers were read. This module has no general map
  on a simplicial morphism, which is the precise missing helper supplied here.
- Proof-only import `Sheaf.CategoryTheory.ModelLocalizationDetectsWeakEquivalences`:
  `HomotopicalAlgebra.modelLocalization_weakEquivalence_iff_isIso`, read with its
  arbitrary-endpoint signature and proof docstring.
- Proof dependency `lem-coef-reedy-realization-prism` currently has neither a Lean
  module nor a declaration in its node record, so no import is available for it.
  It is a proof dependency, not a missing notion needed for the statement. Its
  cylinder and endpoint conclusions are retained explicitly in the theorem's
  complete five-step natural-language proof docstring.

Edge cases checked before writing: in degree zero the only prism map has both
endpoint face conditions, exactly as Mathlib's `Homotopy` specifies; the degree-one
interior gluing equation uses the same face and index range on both prisms. The two
homotopy disjunctions allow opposite orientations independently. The identity map
and its constant homotopies are included. Constant diagrams on a cofibrant object
satisfy the stated latching condition; no constant noncofibrant object is silently
admitted as Reedy cofibrant. The initial diagram and an initial augmentation object
require neither a chosen point nor nonemptiness; all the tensor coproduct and
coequalizer maps are still defined. No zero object or additive structure is assumed.
No fibrancy is used in the cylinder endpoint argument or localization detection.
For the new map, the degree-zero summand and every identity operator are included,
and naturality is imposed through `f` on all simplex operators, not only faces.

Searches for the main statement (all via `msearch.py`, Q63 and this item):

- LeanFinder: `Tensor realization of Reedy cofibrant simplicial objects preserves
  combinatorial simplicial homotopy equivalences` returned eight hits, including
  the preadditive `ExtraDegeneracy.homotopyEquiv`, truncated homotopy-category
  products and Dold--Kan; none is a realization theorem in a simplicial model category.
- Loogle: `"realization", "homotopy"` returned zero hits.
- Mathlib grep: `Reedy|realization|coend` in `AlgebraicTopology` returned 17 hits,
  including the Reedy model-structure TODO and the space-specific `SSet.toTop`.
- `rg` searched the upstream `WeilConjectures` tree and `lean/Sheaf/CategoryTheory`
  for realization-map names and Reedy-cofibrancy combinations; the item-id search
  in upstream returned no match. The existing realization object and downstream
  extra-degeneracy theorem were read; neither states this homotopy-invariance theorem.
- LeanSearch and the further map-specific searches are recorded verbatim in the new
  node's `mathlib_searches`. The general Mathlib `coend.map` was read: it requires a
  natural transformation of curried bifunctors and acts on Mathlib's multicoequalizer
  coends, rather than the recorded tensor realization coequalizers. It therefore
  supplies no existing declaration for the present specialized map.

Source verification: opened
[Dugger's primer](https://pages.uoregon.edu/ddugger/hocolim.pdf), formula (3.2),
printed p.9, and Section 19.1, printed p.90, and read the current blueprint ancestor
`main-20261015/.../sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph beginning `For K`. The item's general prism proof remains explicitly
agent-written, as recorded in its source; no claim of a verbatim theorem of Dugger
is made.

Validation: `scompile.py Q63 lem-coef-reedy-realization-homotopy-invariance` with both
modules compiled each file separately in dependency order, including the private
side overlay, and returned no errors or warnings. The two library checks took
1.8 and 1.9 seconds. Every delivered theorem is `by sorry`; all definitions contain
real data. The only postponed helper is `SimplicialModelRealization.map_condition`,
the relation equality stated explicitly in its owning definition node, with the
full natural-language naturality/coequalizer proof in its docstring.

## New nodes

`def-coef-simplicial-realization-map` defines the canonical induced arrow between the
existing tensor coequalizer realizations. Its module is
`Sheaf.CategoryTheory.SimplicialModelRealizationMap`, with definitions `mapLeg` and
`map` and the named well-definedness theorem `map_condition`. The definition node
explicitly states the relation equality needed for descent. Its dependencies are
the existing simplex/simplicial-set, tensor and tensor-realization nodes. Its source
is Dugger (3.2) and Section 19.1; the map follows the coequalizer universal property.
`map` is uniquely specified by its summand restrictions, so its data do not depend
on an undetermined choice from a sorry existence proof. The searched general
`coend.map` is on another existing categorical presentation, and none of the source
or project declarations gives this specialized map. Both blueprint-reference
searches (`realization map`, `tensor realization`) returned zero blueprint nodes;
DAG searches located the existing realization object/augmentation node but no
separate induced-map node. The new node retains the item's chapter, unit and
blueprint ancestor/via and records the actual search outputs.

## Second reading by Q63

I read the sandbox copy of the item node, the source place in Dugger, and every
recorded declaration behind the statement dependencies. Dugger's formula (3.2)
is the coequalizer of the coproduct over all maps `[m] → [n]`, with the two legs
given by the simplicial operator and the simplex map; Section 19.1 supplies the
chosen tensor and SM7 context. The source does not state this exact general
homotopy-invariance theorem, so the node honestly records the prism/localization
argument as agent-written.

The item statement matches the Lean theorem item by item:

- `M : Type u`, `Category.{v} M`, `ModelCategory M`, `HasLimits M`,
  `HasColimits M`, both functorial-factorization instances, `SimplicialCategory M`,
  `T : SimplicialTensorCotensor M`, and `_hSM7` are exactly the simplicial-model
  hypotheses supplied by `simplicial_model_nerve_localization`; no properness,
  combinatoriality, fibrancy, pointedness, or finiteness assumption is added.
- `A B : SimplicialObject M` are the two `Δᵒᵖ` diagrams. The hypotheses
  `Reedy.leftClass (epimorphisms SimplexCategory).op (cofibrations M)
  (initial.to A/B)` are the recorded relative-latching/Reedy-cofibrancy tests.
  Neither diagram is made fibrant.
- `SimplicialModelRealization.realization T C` is the existing tensor
  coequalizer. Its operators range over every `α : [m] ⟶ [n]`, so the displayed
  node formula, including all faces, degeneracies, identities, and degree zero,
  is present rather than a restricted skeletal formula.
- `f : A ⟶ B` and `g : B ⟶ A` have the required two composite homotopies. Since
  Lean composition is diagrammatic, `f ≫ g` is the node's `gf` and `g ≫ f` is
  its `fg`. The two `Nonempty` disjunctions retain both possible orientations.
- `SimplicialObject.Homotopy` is the dependency's degree-raising prism family;
  its endpoint, interior-face, and degeneracy fields give exactly the node's
  combinatorial homotopy, including the valid `Fin` ranges.
- The conclusion is `WeakEquivalence (SimplicialModelRealization.map T f)`,
  where the added definition node supplies the canonical coequalizer-descended
  map on all tensor summands. This is the node's `|f|`; no arbitrary map or
  choice is assumed. There is no hidden fibrancy or universe equality.

The initial simplicial diagram and initial object are admitted by the coproduct and
coequalizer constructions. Degree zero has the unique prism index and both
endpoint faces. Identity maps with constant homotopies are included. A constant
diagram is required to be Reedy cofibrant through its initial latching map, so a
noncofibrant constant object is not silently admitted. No characteristic,
basepoint, nonemptiness, zero-object, or degree bound is present or needed.

I reran the three required kinds of search with realization-map and weighted
coend wording. LeanFinder returned abstract model homotopy, product-simplex,
and Dold--Kan declarations; Loogle `"coequalizer", "Homotopy"` returned zero
hits. LeanSearch returned general natural-transformation, limit/colimit, and
chain-complex maps. Grep of Mathlib `AlgebraicTopology/SimplicialObject`,
the upstream `WeilConjectures` tree, `lean/Sheaf`, and the blueprint index found
no declaration of this theorem or of the specialized tensor-realization map.
The existing `SimplicialModelRealization.realization` declaration was read in
full, as were the model-localization, tensor/cotensor, Reedy, simplicial-set,
and prism declarations. `coend.map` has the wrong bifunctor presentation and
does not provide this coequalizer map.

The worker had already supplied the missing canonical realization map under the
stage-2 extra-node rule as `def-coef-simplicial-realization-map`, with real
definitions `mapLeg` and `map` and the named postponed naturality theorem
`map_condition`. Its statement, source, searches, dependencies, and
`lean.statement` were checked against the existing realization node. The item
node copy adds exactly this definition to `stmt_deps`; the theorem statement and
all other node fields are unchanged. No existing declaration was duplicated.
I found no mismatch requiring a Lean or node repair and retained both modules.
The second reading changes only this audit report and adds independent searches.

Both sibling modules compile cleanly through `scompile.py`, with only the
intentional `sorry` proofs and no warnings (library checks 2.2 and 1.7 seconds).
Both `lean.statement` fields are verbatim substrings of their declarations;
all variables and universes are explicitly bound and every Lean line is at most
100 characters. The new node has the required definition-node fields, empty
proof/proof-dependency lists, its own owning module and the item's ancestry.
No dependency module or statement correction is delivered.

The required `deliver2.py --no-push` completed successfully: commit `3963db2ae2`
passes the server preflight and compiles, with nothing pushed. The final delivery
uses the same modules and node records with this validation result added.
