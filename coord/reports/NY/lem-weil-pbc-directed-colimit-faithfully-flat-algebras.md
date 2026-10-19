## Worker report

The module `Sheaf.RingTheory.DirectedColimitFaithfullyFlatAlgebras` states
`CommAlgCat.directedColimit_faithfullyFlat`, with its sole proof `sorry`.
Source read: literature/stacks-project/algebra.tex,
`lemma-colimit-faithfully-flat` (Tag 090N), including the entire proof.
No statement correction, new notion, or dependency replacement was needed.

Clause-by-clause reading:

- A commutative ring R is `(R : Type u) [CommRing R]`.
- A nonempty directed set I is `{I : Type v} [Preorder I]
  [IsDirectedOrder I] [Nonempty I]`. Its thin category has a morphism precisely
  for each inequality. The Mathlib instance
  `CategoryTheory.isFiltered_of_directed_le_nonempty` supplies filteredness.
- A directed system of commutative R-algebras with R-algebra transition maps
  is `(F : I ⥤ CommAlgCat.{v, u} R)`. `CommAlgCat.Hom.hom` is an `AlgHom`,
  so transitions preserve both the unit and the fixed R-algebra structure.
  Functor laws encode identity and composite transition laws.
- The assumed colimit S is `[HasColimit F]`, with S represented by
  `(colimit F : CommAlgCat.{v, u} R)`. This is the dependency's chosen colimit
  in the category of commutative R-algebras. An arbitrary colimit is uniquely
  R-algebra isomorphic to this one, and faithful flatness is invariant under
  that isomorphism, so the chosen representative loses no case.
- Each structural map R to S_i is faithfully flat is
  `(hfaithful : ∀ i : I, Module.FaithfullyFlat R (F.obj i))`.
- The conclusion R to S is faithfully flat is
  `Module.FaithfullyFlat R (colimit F : CommAlgCat.{v, u} R)`.
  For both occurrences, Mathlib's `RingHom.faithfullyFlat_algebraMap_iff`
  identifies the module predicate with faithful flatness of the structural
  ring map, exactly as the recorded definition node specifies.
- The final sentence imposes no transition-map condition. The Lean has no
  injectivity or faithful-flatness hypothesis on any `F.map`.

Dependencies read and used:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit` and `HasColimit`; also read the signatures of
  `Cocone`, `IsColimit`, and the filtered-category definitions in Mathlib.
- `def-weil-pbc-faithfully-flat-ring-map`:
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`.
  Read its class definition and docstring, and `RingHom.FaithfullyFlat` and
  `RingHom.faithfullyFlat_algebraMap_iff` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`.
- Proof import `Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise`,
  `CommAlgCat.filteredColimit_tensorProduct_elementwise`, with its universal
  and ring-homomorphism companion declarations, was read in full.
- Proof import `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`,
  `ModuleCat.filteredColimit_flat`, was read in full.
- The two remaining proof leaves have Mathlib matches in the already public
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`:
  `Module.FaithfullyFlat.submodule_ne_top` and `Module.faithfullyFlat_iff`.
  No additional project module is recorded for those leaves.

The declaration docstring follows all three node proof steps: flatness of the
underlying module colimit; nonvanishing modulo a maximal ideal using the
stagewise criterion and elementwise tensor-colimit description; the final
maximal-ideal faithful-flatness criterion.

Edge cases checked before writing:

- Empty I is excluded explicitly, as in the source. No chosen stage is assumed.
- A singleton I recovers faithful flatness of that one stage.
- R may be the zero ring. No `Nontrivial` assumption is imposed on R or S;
  its unital algebras and modules are trivial and the conclusion is consistent.
- Over a field k, a two-stage diagram k[X] to k by evaluation at zero has
  faithfully flat stages over k and a noninjective, non-faithfully-flat
  transition. The theorem accepts it, as required.
- No linear order or chosen upper bound is required, only directedness.
- Universes u (R) and v (I and underlying algebras) are independent, following
  the project convention that index and stage carriers share a universe.
  Larger set-sized diagrams can be placed in a common larger universe.

Searches made (2026-10-15):

- `msearch.py ... leansearch "Directed colimits of faithfully flat commutative
  algebras over a ring are faithfully flat"`: service unavailable, Internal
  Server Error; this is recorded as unavailable.
- `msearch.py ... leanfinder "A directed colimit of faithfully flat commutative
  R-algebras is faithfully flat over R"`: eight hits, including
  `Module.FaithfullyFlat.directSum`, `.trans`, `.toFlat`,
  `RingHom.faithfullyFlat_algebraMap_iff`, and descent results. None states
  the requested directed-colimit result with this signature.
- `msearch.py ... loogle "Module.FaithfullyFlat,
  CategoryTheory.Limits.colimit"`: zero hits.
- `msearch.py ... grep
  "FaithfullyFlat.*[Cc]olimit|[Cc]olimit.*[Ff]aithfully|FaithfullyFlat.*[Dd]irectLimit|[Dd]irectLimit.*[Ff]aithfully"`:
  zero Mathlib hits.
- `rg` with the same pattern and the item id over upstream
  `WeilConjectures/` and project `lean/Sheaf/`: one relevant upstream hit,
  `WeilConjectures.RingTheory.ProEtale.FaithfullyFlat`,
  `RingHom.FaithfullyFlat.of_isColimit`. The other hit concerns strict
  henselization, not this statement. Read the upstream file and its related
  `CommAlgCat.faithfullyFlat_of_colimitPresentation` and
  `Module.FaithfullyFlat.of_colimitPresentation` signatures. These express
  the underlying mathematical result but require R, all algebras and the
  index category to lie in one universe u; the present node's signature
  keeps R in an independent universe. They are useful proof ingredients,
  but cannot serve as the exact existing declaration for this signature.
- Name collision search for `directedColimit_faithfullyFlat` and
  `directed_colimit_faithfullyFlat` across upstream `WeilConjectures/`,
  project `lean/Sheaf/`, and `dag/lean_names_upstream.json`: no matches.

Validation: `scompile.py` compiled the delivered module on the server in 1.0 s,
with nice 19, two threads, and a 60 s per-file limit, without diagnostics.
No local compiler or library build was run. The second reader will add their
independent reading before delivery.

## Second reading by NY

Independently read the node, the sandbox module, Stacks Algebra Tag 090N
(`lemma-colimit-faithfully-flat`, statement and whole proof), and the chapter's
Conventions: rings are commutative with 1 and the zero ring is allowed.
The independent maintainer review found an extra antisymmetry assumption in the
original delivery. The complete replacement module and node record use `Preorder I`
instead of `PartialOrder I`, agreeing with Stacks Categories Tag 00D3.
This delivery has no new definition nodes,
no dependency replacement modules, and no statement correction.

Object/hypothesis/conclusion checklist against the node:

- Base ring R: `(R : Type u) [CommRing R]`. Verdict: exact, including the
  source's unit and commutativity conventions; no field or finiteness assumption.
- Nonempty directed set I: `{I : Type v} [Preorder I]
  [IsDirectedOrder I] [Nonempty I]`. Verdict after the maintainer correction: exact.
  Mathlib's thin category
  on this preorder and `isFiltered_of_directed_le_nonempty` give the intended
  filtered indexing category, with arrows corresponding to inequalities.
- System of commutative R-algebras S_i: `(F : I ⥤ CommAlgCat.{v, u} R)`.
  Verdict: exact. Opened `CommAlgCat` and its `Hom` in Mathlib: carriers are
  `Type v` with `CommRing` and `Algebra R` instances, and morphisms are
  `R`-algebra homomorphisms. Functor laws give the directed-system identities
  and composition law; the structural map is `algebraMap R (F.obj i)`.
- Colimit S of that system: `[HasColimit F]` and
  `(colimit F : CommAlgCat.{v, u} R)`. Verdict: exact chosen colimit in
  R-algebras. Opened the recorded `HasLimits` module: `HasColimit` asserts
  existence of a universal cocone, and `colimit` chooses its vertex. This
  agrees with `def-weil-pbc-category-colimit`; replacing any specified
  colimit by the chosen one transports along the unique algebra isomorphism.
- Faithful flatness of every R to S_i: the explicit hypothesis
  `(hfaithful : ∀ i : I, Module.FaithfullyFlat R (F.obj i))`.
  Verdict: exact, before the conclusion, with no assumption about transitions.
- Faithful flatness of R to S: conclusion
  `Module.FaithfullyFlat R (colimit F : CommAlgCat.{v, u} R)`.
  Verdict: exact and complete. Opened the recorded dependency's
  `Module.FaithfullyFlat` class (flat plus the maximal-ideal condition) and
  `RingHom.FaithfullyFlat`, and checked
  `RingHom.faithfullyFlat_algebraMap_iff`. Thus both module predicates mean
  exactly faithful flatness of the structural ring maps in the node.
- Final clause allowing arbitrary transition algebra maps: no injectivity,
  flatness, or faithful-flatness assumption on any `F.map`. Verdict: exact.

Edge cases: empty I is excluded by the node and Lean alike; a singleton
system is included. Zero R and zero algebras are not excluded by a hidden
`Nontrivial` instance. All characteristics are covered. Over a field the
system k[X] to k by evaluation at zero is admitted despite its noninjective
and nonfaithfully-flat transition. Schemes and n do not occur in this node.
Universes u and v are explicitly bound and independent for the base ring and
stage carriers; the index and stage carriers share v as required by the
project's colimit convention. No variable is left auto-implicit.

Independent H4 searches (2026-10-15):

- LeanSearch, `A filtered colimit of faithfully flat commutative algebras is
  faithfully flat over the base ring`: unavailable, Internal Server Error.
- LeanFinder, `The colimit of a nonempty directed diagram of faithfully flat
  R algebras is faithfully flat`: eight hits, including descent,
  `Module.FaithfullyFlat.directSum`, `.trans`, `.toFlat`, and
  `RingHom.faithfullyFlat_algebraMap_iff`; none is this theorem.
- Loogle, `Module.FaithfullyFlat, CategoryTheory.Limits.colimit`: zero hits.
- Independent case-insensitive rg of `faithfully.?flat.*(colimit|directlimit)`
  and its reverse through pinned Mathlib, upstream `WeilConjectures`, and
  project `lean/Sheaf` found the upstream ProEtale/FaithfullyFlat results
  and an application in WLocalization. Opened the entire upstream
  `FaithfullyFlat.lean`, including
  `CommAlgCat.faithfullyFlat_of_colimitPresentation`,
  `Module.FaithfullyFlat.of_colimitPresentation`, and
  `RingHom.FaithfullyFlat.of_isColimit`. Their base, stages and index all
  share one universe u. They do not directly supply this statement with
  independent base universe u and carrier/index universe v. Retaining this
  generalization is consistent with the existing independent-universe
  flat-colimit dependency, whose module explicitly lifts universes before
  applying the upstream same-universe result. No second definition is added.

Read both proof-import modules, including the signatures of
`CommAlgCat.filteredColimit_tensorProduct_elementwise`, its universal and
ring-hom companions, and `ModuleCat.filteredColimit_flat`. They supply the
stated proof ingredients with the required independent base universe.
The docstring faithfully carries all three node proof steps: flatness,
nonzero maximal-ideal fibres via eventual vanishing and preservation of 1,
then the faithful-flatness criterion. Module and declaration docstrings have
the source and blueprint identifier. There are no definitions, local copies,
local instances, or auxiliary proofs; the sole delivered theorem has `sorry`.
The node's `lean.statement` is verbatim the theorem signature in the module.

Second-reader validation: `scompile.py NY
lem-weil-pbc-directed-colimit-faithfully-flat-algebras` compiled the sole module
on the server in 1.1 seconds, nice 19, two threads, 60-second per-file limit,
with no errors or warnings. No local compiler or library build was run.

## Independent maintainer correction

H3 (and the directed-set convention of the standing brief): the immutable
delivery used `[PartialOrder I]`, whereas Stacks Categories, Tag 00D3,
`definition-directed-set`, defines directed sets as nonempty directed preorders.
Antisymmetry is not assumed by Algebra Tag 090N. The complete replacement uses
`[Preorder I]` in the theorem and in the node's verbatim `lean.statement`.
The mappings above reflect this correction; all other binders and the conclusion
are unchanged. In particular, distinct mutually comparable indices are now
included. The natural-language node statement needs no correction.

The original immutable module reproduced cleanly with server-only `scompile.py`
in 1.0 s, nice 19, two threads, limit 60 s. The corrected module also compiled cleanly through the same server-only
compiler in 1.0 s, nice 19, two threads, limit 60 s, exit status 0, without
errors or warnings. No local compiler, global build, or live library write was used.
