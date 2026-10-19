## Worker report

The new module `Sheaf.Paper.CoefficientFiniteDescentSections` states the node in three
named theorems, all with whole proofs `by sorry`. It defines no new notion. The node
copy changes only `lean`; its statement, dependencies, and proof remain unchanged.

Hypotheses and clauses, checked against the current DAG node rather than the older,
unrestricted quasi-compact assertion in the blueprint:

- The scheme is `X : Scheme.{u}`. A site object is `V : X.ProEt`, the recorded Mathlib
  small pro-etale site of weakly etale X-schemes with the fpqc topology
  `Scheme.ProEt.topology X`. `V.left` is its underlying scheme. Quasi-compactness is
  exactly `[CompactSpace V.left]`, with no separation convention.
- The indexing category for clause (1) is `I : Type v` with `[SmallCategory I]` and
  `[IsFiltered I]`. This permits a filtered category, including parallel arrows,
  rather than only a directed poset. The sheaf values are in universe
  `max (u + 1) v`, which contains both the site and the small indexing diagrams.
  Both universes are arbitrary. There is no equality imposed between the site's
  object universe `u+1` and its morphism universe `u`.
- `set_sections_filtered_colimit` takes an arbitrary diagram `F` of set sheaves.
  `c : Cocone F` with `hc : IsColimit c` supplies an arbitrary chosen sheaf colimit,
  exactly the colimit datum of the recorded category-colimit dependency. The map
  `colimit.desc _ (((sheafSections ...).obj (op V)).mapCocone c)` is the canonical
  map from the colimit of section sets to `c.pt(V)`. Its composite with every
  source coprojection is the evaluated coprojection of c. This is Mathlib's
  `colimit.post` formula when c is `colimit.cocone F`, but also permits every other
  chosen colimit. Supplying its universal property is colimit data, not an extra
  geometric or preservation assumption. It avoids the upstream abelian
  sheafification instance that otherwise forces the value universe to u+1; no
  such universe equality is imposed on this statement.
- The first conjunct is `Function.Injective` of this map. The second conjunct says
  that `QuasiSeparated (toSpecZ V.left)` OR sectionwise injectivity of every
  transition, quantified over all `(i j : I) (f : i ⟶ j) (U : X.ProEt)`, implies
  `Function.Bijective` of the same map. The first disjunct is the node's absolute
  quasi-separated scheme condition, not quasi-separatedness over X. The second
  imposes no overlap compactness or quasi-separatedness.
- `abelian_sections_filtered_colimit` repeats exactly that statement for
  `AddCommGrpCat.{max (u + 1) v}`-valued sheaves. Its `colimit.desc`, using an arbitrary
  sheaf-colimit cocone `c` with `hc : IsColimit c`, is an actual abelian-group
  homomorphism between the abelian colimit of section groups and the sections
  of the abelian sheaf colimit c.pt. Injectivity/bijectivity concern its
  underlying function, as in the node. Both alternatives are unchanged.
- For clause (2), the prime is `(l : ℕ) [Fact l.Prime]`. The fixed algebraic closure
  is the existing `PadicAlgCl l`, as in the recorded coefficient definitions;
  `PadicAlgCl.FiniteIntermediateField l` is exactly the subtype of intermediate
  fields of `ℚ_[l]` with finite-dimensional extension. Its topology is induced
  from that algebraic closure. The chosen algebraic closure is the one used by
  the dependency interface; no new algebraic closure or coefficient object is
  introduced.
- `coefficient_finite_descent_sections` uses the exact recorded `padicSubfieldRingObj`
  and `padicAlgClRingObj` via the existing canonical map
  `padicSubfieldRingObjToPadicAlgCl X l E`. Its component `.hom.app (op V)` is the
  section map `E_X(V) → Qbar_X(V)`.
- The first conjunct quantifies over EVERY finite subextension E and asserts
  `Function.Injective` of that section map. The second is the set equality
  `Set.univ = ⋃ E, Set.range ...`, giving precisely the union inside Qbar_X(V).
- The third conjunct quantifies over a set `S` of Qbar_X(V) sections with `S.Finite`,
  and supplies ONE finite E with `S ⊆ Set.range ...`. No nonemptiness is required.
- The fourth quantifies over an arbitrary finite type K of matrices, arbitrary
  dependent row and column index types `rows : K → Type w`, `cols : K → Type z`,
  each finite, and the actual matrices M. It supplies ONE E for ALL k, rows i and
  columns j, with `M k i j` in the section-map range. The family, row and column
  universes are explicit and independent. There is no fixed rank or square-matrix
  assumption. Coefficient descent assumes only quasi-compactness of V.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.precoverage`, `Scheme.ProEt.topology`;
  read the exact object and topology definitions and their fpqc refinement interface.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, exactly the dependency's convention.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, whose field is quasi-compactness of the diagonal;
  `quasiSeparated_iff_quasiSeparatedSpace` verifies the absolute formulation.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`, `colimit.post`,
  together with `IsFiltered` from `Mathlib.CategoryTheory.Filtered.Basic`.
  `sheafSections` is Mathlib's evaluation functor, not a private copy.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `AlgebraicGeometry.ProEtale.padicSubfieldRingObj`, `padicAlgClRingObj`,
  `padicSubfieldRingObjMap`, `padicSubfieldRingObjToPadicAlgCl`. These are actual
  pullbacks under `upperStarFromPoint X` of the continuous-map inclusions.
- The closed upstream dependency `sk-def-sfb-qlbar-condensed` has no `lean` record;
  its closed audit names `Profinite.padicAlgClCondensedRing` and
  `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Their definitions
  and docstrings were read in the shared published overlay: sections are continuous
  functions valued in a SINGLE finite subextension, not arbitrary continuous
  functions into the algebraic closure. `FiniteIntermediateField` is in the
  imported `WeilConjectures.CategoryTheory.RingObjects.EllAdic`; its nonempty and
  directed instances were read too.
- The module also imports the stated proof dependencies, without `public`, as the
  stage rules require: sectionwise presheaf colimits, sheafification, covering
  axioms, local sheafification sections, affine pullbacks, exact filtered sheaf
  colimits, underlying-set sheafification, forgetting abelian filtered colimits,
  condensed rings, point pullback, exact site inverse image, scheme inverse image,
  and the completed-coefficient comparison. The proof docstrings name every step
  and the supporting DAG nodes. In particular the coefficient argument uses only
  the finite-subextension colimit of `sk-prop-sfb-qlbar-colimit-x`.

Edge cases checked mathematically before writing: V can be empty; sheaves then
have their unique empty-cover section. No nonempty V or nontrivial section group is
assumed. An empty set of coefficients, empty finite matrix family, and empty row
or column index types are included, with the base field as an available finite E.
Filtered I is correctly nonempty; an empty indexing category is not filtered.
A quasi-compact non-quasi-separated V is included in the injectivity statement and
in bijectivity for injective transitions. Arbitrary transitions on such a V are
not claimed bijective. The original blueprint's stronger assertion was already
corrected in the reviewed DAG; this delivery does not alter that correction.

Searches for reuse (2026-10-18):

- `msearch.py ... leansearch "On a quasi compact site object sections of filtered
  sheaf colimits are injective and bijective for injective transitions"`: eight
  hits, including `Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered`,
  `Sheaf.hasFilteredColimitsOfSize`, and AB5 facts; no exact statement of this node.
- `msearch.py ... leanfinder "Sections of filtered colimits of sheaves on quasi
  compact pro etale objects and finite coefficient subfield descent"`: eight hits
  on condensed locally constant sections and affine transition scheme limits;
  none states either the general pro-etale comparison here or coefficient descent.
- `msearch.py ... loogle "CategoryTheory.Sheaf, CategoryTheory.IsFiltered"`: zero hits.
- `msearch.py ... grep "colimit.*[Ee]val|[Ff]iltered.*[Ss]ection" CategoryTheory/Sites`:
  six hits, in general sheafification left exactness and local surjectivity;
  none gives this node.
- Local `rg` over `WeilConjectures` in the slopmaster2 checkout, the published
  pro-etale overlay, and `lean/Sheaf` for finite descent and section/filtered-colimit
  patterns found existing coefficient constructions and qcqs-only section calculus.
  In particular `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus` assumes
  quasi-separatedness and evaluates on the site of V; it does not give this node's
  set case, injective-transition case without quasi-separatedness, or coefficient
  union and finite-matrix assertions. It is not an exact existing match.
- `grep -rn "det-lem-coefficient-finite-descent-sections"` in slopmaster2
  `WeilConjectures` returned no occurrence. A name search in
  `dag/lean_names_upstream.json`, Mathlib, upstream and side sources found no
  collision with the three new theorem names. The existing Mathlib `sheafSections`
  and `colimit.desc` eliminate any need to define auxiliary evaluation/comparison
  notions. No new node or dependency repair is needed.

Sources checked: the current DAG statement and its reviewed proof; the blueprint
statement/proof at the node's source; Stacks `sites.tex`,
`lemma-directed-colimits-sections` (Tag 0738), all four cases and proof; and the
published framework explanation `coord/pefw-upstream-framework.md`.

Validation: compilation and delivery preflight results are recorded below after
running the prescribed wrappers. There is no new statement dispute or node fault.

## Second reading by Q78

No second worker was started: the dispatcher brief requires direct delivery and
reserves independent review to the maintainer. A separate final self-reading checked
the three Lean signatures against each hypothesis and clause above. It verified the supplied sheaf-colimit cocones and their universal properties,
then retained absolute quasi-separatedness, all-object injective transitions, both value
categories, and all four coefficient conclusions. Matrix indices were generalized
from `Fin n` to arbitrary finite row/column types in independent universes, so no
choice of enumeration or fixed matrix shape is part of the statement.

Validation results: the prescribed `scompile.py Q78
 det-lem-coefficient-finite-descent-sections ...CoefficientFiniteDescentSections.lean`
passed for all three theorem signatures, both sandbox and module-path checks (34.4 s
and 34.6 s respectively), with no errors or warnings. Earlier failures were repaired:
the matrix definition is `Mathlib.LinearAlgebra.Matrix.Defs`; `toSpecZ` belongs to
`AlgebraicGeometry.ProEtale`; and supplying the sheaf colimit as `c`/`hc` avoids the
specialized abelian sheafification universe constraint without restricting the
statement's site or coefficient universes. A final reread found no added/dropped
hypothesis or conclusion. The JSON comparison found exactly the `lean` field changed,
and the Lean file has no line longer than 100 characters. The final direct dependency
imports and docstrings are also checked by the delivery dry run and delivery compile.

Final dry run: `deliver2.py Q78 det-lem-coefficient-finite-descent-sections --no-push`
printed `OK (dry run): commit e90c7a76e0 passes the preflight and compiles; nothing pushed`.
Its exact staged paths were this report, the item's node JSON, and the one Lean module.
