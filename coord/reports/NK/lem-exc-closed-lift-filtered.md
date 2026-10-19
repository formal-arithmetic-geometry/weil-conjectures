## Worker report

Existing declaration attachment; no new module, definition, theorem, dependency module,
or statement correction. `Algebra.ClosedLift.isFiltered_index` belongs to
`lem-exc-closed-lift-filtered`. Its source is
`WeilConjectures/RingTheory/ProEtale/ClosedLift.lean`, lines 140–144, in both the
slopmaster2 source and the group clone's current framework. Its docstring explicitly names
this blueprint lemma and the definition it uses. Its proof is `sorry`: this delivery records
an existing stage-2 statement and does not claim a proof or closed axiom audit.

Read the item's complete JSON, its blueprint source (order 1839), and the complete
statement and Lean record of its sole statement dependency
`def-exc-ind-etale-closed-lift`. Read that dependency's module
`Sheaf.RingTheory.ProEtale.ClosedLiftMap` in full, and the underlying upstream
`WeilConjectures.RingTheory.ProEtale.ClosedLift` in full. Also read
`coord/pefw-upstream-framework.md` and the stage rules and example CompactObject module.

Hypothesis and conclusion correspondence:

- A is a commutative ring: upstream section binders `(A : Type u) [CommRing A]`.
- The input algebra is `(C : Type u) [CommRing C] [Algebra A C]`.
  In the dependency's application C is the given ind-etale A/I-algebra, with this
  A-action induced by the quotient. Neither the category's objects nor its morphisms
  use I or ind-etaleness. The existing declaration is valid for every input A-algebra
  and specializes directly to every input of the cited definition. No alternate category
  or extra hypothesis is introduced. Universe `u` is arbitrary; both carriers can be
  placed in a common universe.
- The category N_A(C) is exactly the dependency's reused `Algebra.ClosedLift.Index A C`.
  Its fields are `n`, `rel`, `etale`, `toC`. The underlying algebra is
  `MvPolynomial (Fin n) A ⧸ rel`; `etale` supplies `Algebra.Etale A` and hence finite
  presentation. The recorded dependency already explains the small model: a finitely
  generated ideal of relations replaces a redundant finite generating list. All
  compatible algebra maps are retained; no injectivity or surjectivity is imposed.
- Its morphisms are `Index.Hom`, with `hom : X.alg →ₐ[A] Y.alg` and
  `comp_toC : Y.toC.comp hom = X.toC`. The existing SmallCategory instance uses
  identities and composition of these algebra maps.
- The sole conclusion, “is filtered”, is `IsFiltered (Index A C)`.
  Mathlib `CategoryTheory/Filtered/Basic.lean`, lines 82–97, defines this as
  common successors, coequalization of parallel arrows, and nonemptiness.

Dependency declarations used: the recorded module
`Sheaf.RingTheory.ProEtale.ClosedLiftMap` reexports upstream
`Algebra.ClosedLift.Index`, `Index.Hom`, `diagram`, `ClosedLift`, and `toAlgHom`, and
adds `Algebra.ClosedLift.map`. The attached instance uses precisely that upstream Index
and its category instance. No declaration is copied or reconstructed.

Mathematical checks against all six proof steps: the zero-variable presentation of A
provides an object; tensor products provide common successors; the multiplication map
B tensor_A B → B models the diagonal; quotienting B' by the finitely many generator
differences models its base change; compatibility with the map to C lets this quotient
map to C and equalizes the arrows; these three properties give IsFiltered. The quotient
remains etale by base change and composition, with the displayed finite presentation.
These are the node's proof steps, not newly supplied Lean proofs.

Edge cases checked: zero A and C; zero C with arbitrary A; I = bottom or top;
zero variables and zero relations; identical objects and identical parallel arrows;
noninjective maps to C. The factorization through A still gives nonemptiness, including
when C is zero, and quotienting by differences is allowed to give the zero ring.
No nonzero or connectedness hypothesis is required. No statement dispute or node fault
was found.

Searches actually run using msearch.py for NK and this item:

- leanfinder: “The category of finitely presented etale A algebras mapping to an A algebra
  C is filtered”. Eight hits, including `Algebra.Etale.finitePresentation`, tensor descent
  and finite-presentability lemmas; none states this whole category result.
- loogle: `Algebra.Etale, CategoryTheory.IsFiltered`. Zero hits.
- grep: `ClosedLift|Etale.*[Ff]iltered|[Ff]iltered.*Etale`. One Mathlib hit,
  `AlgebraicGeometry/Sites/EtalePoint.lean:56`, concerns etale neighborhoods of a point,
  not the general input algebra indexing category.
- leansearch: “category of etale algebras mapping into a fixed algebra is filtered”.
  Service unavailable (Internal Server Error); not treated as a negative result.
- Direct rg of ClosedLift/closedLift/closed_lift and the node id in the source
  WeilConjectures tree found `ClosedLift.lean:140–144`, the exact existing instance.
  Direct rg in lean/Sheaf found the dependency ClosedLiftMap, with no second statement.
  Search in dag/lean_names_upstream.json found no indexed name for this item.

Validation: the scratchpad server probe imports the dependency's recorded module,
checks the full existing instance signature and prints its axioms. The delivery dry run
also performs its own existing-declaration server probe. No local compilation is used.

## Second reading by NK

Independent second reading: opened the item's complete node, its six proof steps,
its blueprint source at order 1839, the dependency's complete statement and Lean record,
the blueprint definition at order 1838, the complete ClosedLiftMap module, and the
complete upstream ClosedLift module in the group clone. Also checked the corresponding
source declaration in slopmaster2 and the framework/isolation note. This delivery has
no new definition nodes, dependency modules, statement correction, or delivered Lean files.

Object/hypothesis/conclusion checklist, extracted before comparing the signatures:

- Commutative ring A: upstream `(A : Type u) [CommRing A]`; exact ring notion,
  with no domain, field, Noetherian, characteristic or nontriviality assumption.
- Ideal I and ind-etale A/I-algebra C-bar, viewed through A -> A/I: these are the
  inputs of the cited definition. Its recorded construction deliberately uses only
  `[CommRing C] [Algebra A C]`; the dependency module explicitly says it applies to
  arbitrary input algebras. `isFiltered_index` is the matching generic existing
  declaration, applied to that induced action. I and ind-etaleness do not enter Index
  or its morphisms, and no alternative action is chosen. This is the same reusable
  construction and its filteredness, including all the source's inputs.
- Objects are finitely presented etale A-algebras with maps q to C-bar:
  `Index.n`, `Index.rel`, `Index.etale`, `Index.toC`, with
  `Index.alg X = MvPolynomial (Fin X.n) A / X.rel`. Mathlib's `Algebra.Etale`
  includes `Algebra.FinitePresentation`, as checked in RingTheory/Etale/Basic.lean.
  Thus the arbitrary relation ideal is finitely generated; replacing a finite list
  of generators by its ideal is precisely the small-model convention already recorded
  and reviewed on the dependency node. It introduces no additional algebra objects
  or restricted maps. Scheme etaleness here is the usual equivalent affine condition.
- Morphisms are all A-algebra maps f with q' composed with f equal to q:
  `Index.Hom.hom : X.alg →ₐ[A] Y.alg` and
  `Index.Hom.comp_toC : Y.toC.comp hom = X.toC`. The SmallCategory instance
  uses algebra-map identity and composition. It imposes neither injectivity nor
  surjectivity nor a condition on polynomial presentations. Verdict: exact.
- The single conclusion is filteredness of this very category:
  `instance isFiltered_index : IsFiltered (Index A C)`. Opened Mathlib's
  CategoryTheory/Filtered/Basic.lean: `cocone_objs`, `cocone_maps`, and
  `nonempty` are exactly common successors, equalization of parallel arrows, and
  existence of an object. Read Stacks categories.tex, definition-directed (002V),
  including its distinction between a filtered diagram and a filtered index category.
  Verdict: exact category filteredness, with no clause omitted.

Source/proof check: read the blueprint proof and the Stacks statements
lemma-open-immersion-etale (02GP), lemma-base-change-etale (02GO),
lemma-composition-etale (02GN), and lemma-etale-permanence (02GW).
None assumes a field, nonzero ring, or Noetherian base. Matched all six node steps:
(1) zero-variable presentation of A gives nonemptiness;
(2) tensor product, with multiplication into C, gives common successors;
(3) multiplication B tensor_A B -> B is etale by cancellation;
(4) quotient by finitely many generator differences realizes the diagonal base change;
(5) base change and composition give an etale finitely presented quotient, and
compatibility makes its map to C descend and equalize the arrows;
(6) these are exactly IsFiltered's three requirements.
The attached upstream instance has a `sorry` proof, not a closed-proof claim.
Its existing docstring identifies this blueprint lemma and the indexing definition;
the full proof plan remains in the node and this report. No upstream file was edited
and no duplicate theorem was introduced merely to alter existing documentation.

Edge cases: zero A (hence zero C for a unital A-action), zero C with arbitrary A,
I = bottom or top, zero polynomial variables and zero relations, arbitrary
characteristic, identical objects and arrows, and noninjective q are all included.
The index category is not allowed to be empty: its A-object exists even in the zero
case. Empty schemes correspond to the permitted zero rings; there is no additional
scheme hypothesis. The arbitrary universe u can be chosen as a common upper universe
for the input carriers; finite polynomial presentations and compatible maps remain
small there. No independent low test universe or unbound variable occurs.

Independent searches used different wording from the first reader:
`msearch.py ... leanfinder "Filtered category of finite presentation formally etale
commutative algebras equipped with a morphism to C"` found Etale.finitePresentation
and related etale algebra facts, but no alternate category result.
`msearch.py ... leansearch "Finite presentation etale algebras over A mapping to C
form a filtered category"` returned Internal Server Error; recorded as unavailable,
not as evidence of absence. Direct rg for `isFiltered_index`, filtered/ClosedLift,
and filtered/etale in the source WeilConjectures tree, Mathlib's Etale directory,
and lean/Sheaf independently found the exact upstream instance. Inspected the nearby
candidate results: Mathlib EtalePoint is a cofiltered category of geometric-point
neighborhoods; PointedEtaleFiltered requires a local ring and separable-closure field;
PairHenselizationFiltered requires trivial reduction; EtaleResidueTriplesFiltered
has residue-field triples. None is this unrestricted category. ClosedLiftMap reuses
Index and adds functoriality rather than restating its filteredness.

Mismatches and changes: none found. Kept the existing attachment and its verbatim
signature unchanged; appended this independent review only. Server validation uses
scompile.py on scratchpad/ExistingChecks.lean, importing the dependency module and
checking the full instance and its axioms, followed by deliver2.py's own existing
attachment probe and preflight. No local Lean compiler or library build was run.
