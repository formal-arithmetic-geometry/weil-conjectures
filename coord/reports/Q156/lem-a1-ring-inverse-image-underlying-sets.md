## Worker report

The module `Sheaf.Topology.RingInverseImageUnderlyingSets` states
`TopCat.Sheaf.ringInverseImage_underlyingSets`, with one `sorry` and no new definitions.
The node's statement, dependencies, proof and other fields are unchanged; only `lean` is added.
No dependency repair or new node is needed.

Hypotheses and conclusions, clause by clause:

- The arbitrary continuous map is `{T Z : TopCat.{u}} (h : T ⟶ Z)`.
  `G : Z.Sheaf CommRingCat.{u}` is an arbitrary commutative-ring sheaf.
  The underlying set sheaf is `sheafCompose (Opens.grothendieckTopology Z)
  (CategoryTheory.forget CommRingCat.{u})` applied to `G`.
- The existential natural isomorphism `β` compares two functors from ring sheaves on
  Z to presheaves of sets on T. Its source first forgets to sets and then takes
  `TopCat.Presheaf.pullback (Type u) h`; its target takes
  `TopCat.Presheaf.pullback CommRingCat.{u} h` and then forgets. Thus each component
  `(β.app G).app (op W)` is exactly the bijection between the two neighbourhood
  colimits, and both its inverse and bijectivity are part of the isomorphism type.
- The neighbourhood condition is `(i : W ≤ (Opens.map h).obj B)`, equivalently
  h(W) ⊆ B. The first conjunct quantifies over every W, B, i and section
  `s : G.obj.obj (op B)`. On each side the presheaf adjunction unit at B followed
  by restriction along `(homOfLE i).op` is the colimit coprojection indexed by B.
  It is the same canonical coprojection of the pointwise left Kan extension
  (the equivalent `CostructuredArrow` neighbourhood index). The displayed equation
  sends the set-colimit representative of s to the ring-colimit representative of s.
- Compatibility with restrictions in W is the naturality of `β.hom.app G`, which
  is a morphism of presheaves. Naturality in G is the naturality of `β.hom`, which
  is a morphism of functors on ring sheaves. These properties are carried by the
  natural-isomorphism type, not omitted from the conclusion.
- The existential natural isomorphism `α` has source set inverse image of the
  underlying set sheaf and target underlying set sheaf of ring inverse image.
  Both inverse-image functors are the explicit
  `Functor.sheafPullbackConstruction.sheafPullback`, as prescribed by the dependency's
  `mathlib_match`. This is the sheafification of the recorded presheaf pullback.
- The second conjunct states exactly
  `toSheafify P ≫ (α.hom.app G).hom = β.hom.app G ≫ whiskerRight (toSheafify Q) forget`.
  Thus α is induced by sheafifying this very β, rather than being an arbitrary
  isomorphism with the correct endpoints. The representative equation determines
  β uniquely; this sheafification equation determines α uniquely. Together they
  express the word 'canonical' in the node without choosing arbitrary data.
- Naturality of α in G is built into its natural-isomorphism type.
- The final conjunct quantifies over every G, open B and s and states the node's
  displayed element equation at `op ((Opens.map h).obj B)` verbatim. Both η terms
  are the units of `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`.
  These are the actual units belonging to the explicit sheafification construction,
  not arbitrary maps and not units for an unnormalized abstract left adjoint.
- There are no compactness, separation, nonemptiness, surjectivity or nonzero-ring
  hypotheses. All universes and term variables are explicitly bound. The common
  universe is the conventional one already used by the recorded topological
  inverse-image interface; it is arbitrary, not a fixed small universe.

Dependency declarations read and used:

- `def-weil-pbc-topological-inverse-image`: `Mathlib.Topology.Sheaves.Functors`,
  `TopCat.Sheaf.pullback`, `pushforward`, `pullbackPushforwardAdjunction`, and the
  associated `TopCat.Presheaf.pullback` and `pullbackPushforwardAdjunction` from
  `Mathlib.Topology.Sheaves.Presheaf`. Its recorded match explicitly allows and
  recommends `Functor.sheafPullbackConstruction.sheafPullback` and
  `sheafAdjunctionContinuous` from `Mathlib.CategoryTheory.Sites.Pullback` to retain
  the specified sheafification and unit. No dependency redefinition is introduced.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `Cocone`,
  `IsColimit`, coprojections and canonical maps from
  `Mathlib.CategoryTheory.Limits.HasLimits`. Here these colimits are accessed through
  the dependency's existing pointwise left-Kan-extension pullback, not a new model.
- `lem-pc-filtered-colimit-commrings-elementwise`: its recorded
  `Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists`
  (`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`) and
  `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`
  (`Mathlib.Algebra.Category.Ring.FilteredColimits`). These supply proof steps 1–3.
- `lem-weil-pbc-filtered-colimit-sets-elementwise`: its recorded
  `Types.jointly_surjective`, `Types.FilteredColimit.isColimit_eq_iff` and
  `isColimit_eq_iff'` in `Mathlib.CategoryTheory.Limits.Types.Colimits` and `Filtered`.
- `lem-pc-sites-sheafification-underlying-sets`: its recorded `sheafifyComposeIso`,
  `sheafComposeIso_hom_fac`, and `GrothendieckTopology.PreservesSheafification`
  (`Mathlib.CategoryTheory.Sites.PreservesSheafification`). These are proof inputs.
- `def-weil-pbc-sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction` (`Mathlib.CategoryTheory.Sites.Sheafification`).
  `toSheafify` appears explicitly in the middle conjunct; `presheafToSheaf` is the
  final functor in the chosen inverse-image construction. Sheafification's module
  is publicly imported by the stated topological inverse-image dependency.

Source checked directly: `literature/stacks-project/sheaves.tex`, proof of
`lemma-pullback-presheaves` (Tag 008F), including the presheaf unit and restriction
construction, and `lemma-sheafify-presheaf-structures` (Tag 0087), clauses (1) and (2).
The six-step natural-language proof in the declaration docstring follows all six
DAG proof steps and names their inputs.

Edge cases checked before writing:

- W empty: every open B is an index and the empty open is a final index. For a
  ring sheaf G, G(empty) is the one-element zero ring. Its underlying set and the
  set colimit agree; no exclusion of the zero ring is hidden in the binders.
- T empty, and T = Z = empty: all terms still exist. No point of either space is
  used, and the indexing poset always contains the whole open.
- A nonsurjective h: the containment condition is h(W) ⊆ B, with no equality or
  image-surjectivity requirement. In particular h(h⁻¹B) ⊆ B suffices for the unit.
- Identity map: the representative of s at B is the same on both sides and the
  sheafification equation normalizes the comparison with the chosen units.
- Arbitrary W' ⊆ W: the same B remains a neighbourhood; naturality of the
  presheaf comparison expresses precisely the restriction clause.

Searches for an existing full statement (all run through the prescribed msearch tool,
with local source searches in addition):

- LeanFinder: 'For a continuous map inverse image of sheaves of commutative rings
  commutes with forgetting to sets compatibly with presheaf colimit coprojections
  and adjunction units'. Eight hits: pushforwardForgetIso/pushforward_forget,
  scheme structure-presheaf comparison, gluing, restrictions, and componentwise
  limits. None states inverse image together with all normalization clauses.
- Loogle: `TopCat.Presheaf.pullback, CategoryTheory.forget`. One hit,
  `TopCat.Sheaf.pullbackIso`, comparing abstract sheaf pullback with the
  sheafification construction at unchanged coefficients. It does not compare rings
  with underlying sets.
- Mathlib grep: `pullback.*[Ff]orget|[Ff]orget.*pullback` in `Topology/Sheaves`.
  Two hits, both the same unchanged-coefficient pullback/sheafification interface.
- Local rg of `lean/WeilConjectures` and `lean/Sheaf` using the same pattern and
  the node id: module-pullback comparisons and site-specific constructions were
  found, but no existing full topological ring/set statement. The exact proposed
  declaration name was also searched in Mathlib, both project roots and
  `dag/lean_names_upstream.json`, with no collision.
- LeanSearch: 'The forgetful functor from sheaves of commutative rings to sheaves
  of sets commutes with topological inverse image and preserves its adjunction unit'.
  Eight hits include `sheafForget`, module-sheafification unit and Hom formulas,
  `Scheme.ringCatSheaf`, `SheafOfModules.forget`, and spectrum structure-sheaf
  comparisons. None states the combined inverse-image comparison and normalizations.

Validation: the complete module compiled through `scompile.py` in both sandbox
and library mode (approximately 2 seconds per mode), with no errors or warnings.
The required dry run and final delivery are run after the record and report are written.
No disputed statement or source correction was necessary.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
