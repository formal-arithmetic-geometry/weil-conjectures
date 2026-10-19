## Worker report

This is the stage-2 statement delivery for `lem-trf-finite-coproduct-topos-coherent`.
The NF delivery already on the base is its stage-1 natural-language split, not a Lean
statement: that node has no `lean` record. This delivery adds that record and the module
`Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent`, retaining all the node's existing fields.
No theorem is proved. The main theorem has `sorry`; the auxiliary definitions and structure
have real predicate and field data, with no choice from an unspecified existence theorem.

Clause-by-clause correspondence:

- A finite index set is `{I : Type w} [Finite I]`; it need not be inhabited and no finite
  enumeration is imposed.
- The sites are `C : I → Type w`, with `SmallCategory (C i)` and component topologies `JC`.
  The containing set universe is `Type w`. The categories `E i` have independent object
  universe `uE` and morphism universe `w`; `p i : E i ≌ Sheaf (JC i) (Type w)` supplies the
  small-site presentations, and hence the Grothendieck-topos hypothesis itself. There is
  no additional coherence assumption on the construction or universal property.
- The disjoint-union category is Mathlib's actual `(Σ i, C i)` with its sigma-category
  instance: objects are pairs, arrows within a component are exactly component arrows,
  and there are no cross-component arrows. `Sigma.incl i` is its actual inclusion.
  `Witness.topology` characterizes the topology on EVERY sieve by its actual functor
  pullback along that inclusion. Thus the existential topology cannot be an arbitrary
  replacement. This is the Grothendieck-topology encoding of precisely the given site;
  the site/topology passage is Stacks 00ZC, as in the recorded site convention.
- The total topos is literally `Sheaf J (Type w)`. `Witness.equivalence` identifies it with
  the dependent product `∀ i, E i`; `Witness.restriction` normalizes this equivalence by
  a natural isomorphism to precomposition by `(Sigma.incl i).op` on presheaves, using the
  given `p i`. It is therefore specifically restriction to components.
- `limits_componentwise` and `colimits_componentwise` quantify over every small diagram
  and cone/cocone, with an iff between the total universal property and all component
  universal properties. These concern all limits and colimits, not only finite ones.
  `epimorphisms_componentwise` is the iff for every arrow.
- `inclusion i` is the recorded `GeometricMorphism`. `inclusion_inverse` specifies its
  inverse image as the component projection. `inclusion_direct_same` identifies its right
  adjoint at component i, naturally, with the identity; `inclusion_direct_other` says all
  other components are terminal. The right adjoint is not an arbitrary extra map.
- `universal` quantifies over every target Grothendieck topos, in its independent object
  universe `uF`, and every family `a i`. It supplies `b` with the NATURAL inverse-image
  formula `b.inverse ⋙ equivalence.functor ≅ Functor.pi' ...`, and for every tuple the
  product cone computing `b.direct`. The direct-image isomorphisms `β i` identify
  `b j_i` with `a i`. For EVERY other extension and compatible component isomorphisms,
  the `∃! γ` clause requires their unique compatible natural isomorphism, with the
  compatibility equation written using `Functor.isoWhiskerLeft`.
- `presentation_independent` allows entirely different component sites and topologies,
  with presentations of the same `E i`, and proves equivalence of the resulting total
  sheaf categories.
- `coherent` has the conditional hypothesis that every `E i` is coherent, and concludes
  coherence of the total topos AND the iff between coherence of a tuple and of every
  component. The total-topos predicate is exactly the dependency's repaired declaration.
  The auxiliary `IsCoherent` only packages the coproduct and finite-limit structures
  around the dependency's existing `CategoryTheory.IsCoherentObject`; it introduces no
  alternate compactness or separatedness notion.
- `empty_case` explicitly gives equivalence to `Discrete PUnit` when I is empty. This is
  the degenerate one-object, one-arrow topos, including the empty product in the direct
  image formula.

Dependency declarations read and used:

- `def-weil-size-convention` is the recorded metatheoretic convention, with no Lean object.
  The universes above implement it directly; site and sheaf object universes are not forced
  equal, and `uE` and `uF` are independent.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: read the full signature and docstring.
  The node's set-sheaf convention is Mathlib's `GrothendieckTopology` and `Sheaf`; no
  cohomology, coefficient, or continuous-functor clause is needed in this statement.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`, `CategoryTheory.GeometricMorphism` and
  `CategoryTheory.GeometricMorphism.comp`: the inverse/direct functors, adjunction,
  left exactness, and composite are precisely that dependency's interface.
- `Sheaf.CategoryTheory.Sites.CoherentToposRepair`,
  `CategoryTheory.CoherentToposRepair.IsCoherentTopos`; and the underlying module
  `Sheaf.CategoryTheory.Sites.CoherentTopos`, `CategoryTheory.IsCoherentObject`.
  Both full definitions and docstrings were read. The object helper packages exactly
  the existing predicate, matching the repaired ambient-topos convention.
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`, `CategoryTheory.IsGrothendieckTopos`,
  is imported through the geometric-morphism and coherent-topos dependencies; it is used
  for the universal property's target topoi.
- The proof-only node `lem-trf-set-sheaf-finite-extensivity` is a Mathlib leaf, matched by
  `CategoryTheory.SheafOfTypes.finitary_extensive` in
  `Mathlib.CategoryTheory.Sites.LeftExact`; that module is imported without `public`.
  Its signature and full match record, including strictness, monicity, disjointness and
  universal finite coproduct clauses, were checked.

Sources read: the complete node and its six proof steps; the full statements and Lean
records of all four statement dependencies; their declaration modules and docstrings;
Stacks `sites.tex`, Definition 00VH, Definition 00VM, Lemma 00W2 and Lemma 00WI; Mathlib's
sigma-category objects, Hom constructors and inclusions; Mathlib's sheaf-limit/colimit
and finite-extensivity declarations returned by the searches.

Edge cases checked: empty I, a singleton I, `Set × Set` with `(1,∅)`, initial components,
and components which are degenerate topoi. No positivity, inhabitedness, nondegeneracy,
or coherence hypothesis is added to the unconditional construction. Quasi-compactness
uses finite subfamilies and finiteness of I, with initial-supported generators as in the
reviewed split. The universal property includes the empty product, a terminal direct image.

Searches made (the exact service output is retained in `searches.jsonl`):

- `msearch.py leanfinder`: “A finite coproduct of Grothendieck topoi is sheaves on the
  disjoint union site; coherent objects are componentwise coherent”. Eight hits, including
  `CategoryTheory.Sheaf.instHasFiniteCoproducts` and
  `CategoryTheory.SheafOfTypes.finitary_extensive`. Their full source signatures were read:
  these give coproducts of objects inside one topos, not coproducts of topoi.
- `msearch.py loogle`: `"Sheaf", "Sigma"`. Five hits, including
  `CategoryTheory.Presieve.isSheafFor_sigmaDesc_iff`; this concerns an internal coproduct
  covering in one category, not a sigma category of sites or componentwise coherence.
- `msearch.py grep`: `coproduct.*[Tt]opos|disjoint.*union.*site|[Ss]igma.*[Ss]heaf`
  in `CategoryTheory/Sites`: zero hits.
- Direct `rg` of `finite_coproduct_topos_coherent|FiniteCoproductTopos|disjoint.*union.*site`
  in upstream `WeilConjectures` and project `lean/Sheaf`: no existing declaration of the
  node. The unrelated project hits concern topological cylinders, module comparison, and
  the finite disjoint union of objects of one pro-etale site. Searching the item id in
  upstream `WeilConjectures` gave no hit.
- `msearch.py leansearch`: “Finite coproduct of topoi sheaves on sigma category coherent
  objects componentwise”. Eight hits on internal coproducts, limits, and spaces; none states
  the finite-coproduct-of-topoi theorem.
- Direct source search found and reused Mathlib's `CategoryTheory.Sigma` category and
  `Sigma.incl`, `Pi.eval`, `Functor.pi'`, `Sieve.functorPullback`, and `Fan.mk`.

No new independent notion, dependency repair, or statement correction is required. There
is no `STATEMENT-DISPUTED` issue. The only postponed theorem is the main theorem, whose
blueprint tag matches this DAG node and whose docstring contains the six-step proof.

Validation: the final source has explicit binders and universes, lines of at most 100
characters, real auxiliary definitions, and exactly one postponed theorem. The node
copy differs from the shared base only in `lean`; its statement signature is copied
verbatim from the module. The final module is checked through `scompile.py`, followed
by the required `deliver2.py --no-push` preflight and delivery.

The final `scompile.py` run succeeded for both the sandbox check and the library module,
with no errors or warnings. The required `deliver2.py --no-push` dry run also passed the server preflight and
compilation, printing `OK (dry run)` for the complete three-file delivery packet.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
