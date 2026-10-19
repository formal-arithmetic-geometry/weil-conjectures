## Worker report

The module `Sheaf.CategoryTheory.ProperWordColimitInvariance` states
`SSet.SignedWord.proper_colimit_invariance`, with its proof `by sorry`.
It defines the signed-word category and properness explicitly, as the item itself
introduces them. These helpers belong to this node and are listed in
`lean.declarations`; they are not statements of any other DAG node. There are no
hollow definitions, extra hypotheses, postponed helper theorems, or private notions.

Source checked: Dwyer--Kan, *Calculating simplicial localizations*, Section 4.1
(printed page 22, PDF page 6), Definition 4.4 and Proposition 4.5 (printed page 23,
PDF page 7), at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf.
The paper's pair of disjoint subsets partitioning the first n positive integers is
exactly a word of n signs; shifting positions from 1..n to `Fin n` preserves the
order and all sign-preserving maps. Definition 4.4 has precisely the two conditions
in `IsProper`, and Proposition 4.5 has precisely the theorem's hypotheses/conclusion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small category I: `SSet.SignedWord` has `length : ℕ` and
  `sign : Fin length → Bool`, with true = plus and false = minus. It contains all
  finite words, including the length-zero word. There is no restriction to
  alternating words, no positive-length assumption, and no excluded word shape.
- Its morphisms: `SignedWord.Hom w v` has a map `toFun` of positions,
  `monotone : Monotone toFun`, and `sign_eq` at every source position. Thus maps
  are weakly order-preserving, not necessarily strictly order-preserving or
  injective. The global `SignedWord.instCategory` has identity maps and ordinary
  composition of these functions. The category laws are construction fields,
  verified directly, rather than additional theorem statements.
- An injection means `Function.Injective f.toFun`, with no assumption that the
  induced simplicial map is an isomorphism or that f is a surjection.
- The intersection subword h: the second conjunct of `SignedWord.IsProper E`
  quantifies over f, g and h with their common codomain v, requires each to be
  injective, and requires
  `Set.range h.toFun = Set.range f.toFun ∩ Set.range g.toFun`.
  This describes exactly the h in the node. The finite ordered intersection has
  its increasing enumeration and hence such a word and injection; its sign
  function is inherited from v by `h.sign_eq`. Conversely an injective monotone
  map is the unique increasing enumeration of its image, so this quantification
  is equivalent to using that intersection subword, not a weaker conditional
  claim about an arbitrary map whose existence was assumed as extra data.
- The functors E and E': the binders
  `(E E' : SignedWord ⥤ SSet.{u})` use the recorded simplicial-set notion,
  and `(η : E ⟶ E')` is an ordinary natural transformation.
- Properness of E: `(hE : IsProper E)`. The first conjunct requires, for every
  injection f and every `n : ℕ`, injectivity of
  `(E.map f).app (Opposite.op (SimplexCategory.mk n))`. The second requires
  equality of the image of E(h) and the intersection of the images of E(f) and
  E(g), in every degree, inside exactly the common target E(v).
- Properness of E': `(hE' : IsProper E')` supplies both of the same conditions
  for E', with no condition omitted for the second functor.
- Every component is a weak homotopy equivalence:
  `hη : ∀ w : SignedWord, Enhanced.IsWeakHomotopyEquivalence (η.app w)`.
  The reused definition is bijectivity on path components of `SSet.toTop` and
  bijectivity on all positive based homotopy groups at every point of the source
  realization. Its `componentsMap` and `homotopyGroupMap` are the induced maps,
  not unspecified bijections. The maps on positive homotopy groups preserve
  concatenation; bijectivity is exactly the group-isomorphism requirement.
- The induced map on ordinary colimits is Mathlib's `colimMap η`, whose defining
  coprojection equation is
  `colimit.ι E w ≫ colimMap η = η.app w ≫ colimit.ι E' w`.
  The conclusion is `Enhanced.IsWeakHomotopyEquivalence (colimMap η)`.
  These are the chosen universal-property colimits of the recorded colimit node.
  Pointwise colimits in the functor category compute their simplex sets as the
  ordinary Type colimits, i.e. the disjoint-union/diagram-relation quotients.
  There is no use of homotopy colimits and no extra `HasColimit` assumption.

Dependency declarations read and reused:

- `def-nagata-category`: `CategoryTheory.Category`, including its CategoryStruct
  fields and laws, in `Mathlib.CategoryTheory.Category.Basic`.
- `def-weil-pbc-simplicial-set`: `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`; its morphisms are natural
  transformations and its n-simplices are evaluation at the opposite of `[n]`.
  The other recorded clauses (`SSet.degenerate`, `SSet.nonDegenerate`,
  `SSet.Subcomplex`, `SSet.Finite`) were read in their recorded source files;
  they are not needed in this theorem's signature and are not copied.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit` and `colimMap`
  in `Mathlib.CategoryTheory.Limits.HasLimits`; also read its Cocone,
  IsColimit, colimit.desc and IsFiltered interfaces. Filteredness is not a
  hypothesis here: the node concerns this particular nonfiltered category.
- `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`,
  `componentsMap`, and `homotopyGroupMap` in
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its recorded declaration and
  source were read. This already landed node is added to `stmt_deps` under the
  standing rule allowing added landed statement dependencies, so the existing
  weak-equivalence notion is explicitly cited rather than duplicated.
- Stated proof dependency `lem-coef-kan-quillen-right-proper`: imports
  `Sheaf.AlgebraicTopology.KanQuillenRightProper` non-publicly; read
  `SSet.KanQuillen.right_proper_kan_quillen` and its proof-plan docstring.
- Stated proof dependency `lem-coef-reedy-model-structure`: imports
  `Sheaf.CategoryTheory.ReedyModelStructure` non-publicly; read
  `HomotopicalAlgebra.Reedy.model_structure` and its hypotheses/docstring.
- The remaining proof-only dependencies `lem-coef-brown-split-factorizations`
  and `lem-coef-signed-word-boundary-pushout` have no Lean record in the base
  read for this delivery, so there is no module to import yet. Their proof uses
  are retained in the theorem's complete eight-step docstring. They are not
  statement prerequisites and are not restated in this delivery.

Edge cases checked before finalizing the statement:

- The empty word is present: `length = 0`, with the unique function `Fin 0 → Bool`.
  Its maps into every word are the unique empty maps, hence injections. Properness
  therefore genuinely includes the images of E(empty word), even for disjoint
  images of f and g; it does not silently replace such an image by the empty set.
- For an empty target word there are maps precisely from the empty word. This
  also gives valid intersection data and imposes no impossible extra assumption.
- Repeated signs, all-plus/all-minus words, constant monotone maps, identities,
  and noninjective sign-preserving maps are allowed in the category. Properness
  only imposes injectivity on the actual injections of positions.
- Degree zero is included by `∀ n : ℕ`; no face or degeneracy condition has been
  dropped, since all maps being evaluated are actual simplicial maps.
- Empty simplicial sets and empty realizations remain allowed. The existing weak
  equivalence predicate retains path-component bijectivity even when the
  basepoint quantifier is empty, so empty-to-nonempty maps are not weak equivalences.
- No fibrancy, Kan condition, cofibrant-diagram assumption, or nonemptiness of
  the simplicial values was added to the theorem. `u` is arbitrary; the fixed
  Type-zero category of finite words is small in every such universe.

Searches (all performed through the required msearch.py wrapper where indicated):

- LeanFinder: "An objectwise weak homotopy equivalence of proper simplicial set
  diagrams indexed by finite signed words induces a weak homotopy equivalence
  on colimits". Eight hits included `HomotopicalAlgebra.ModelCategory.cm1b`,
  `SSet.horn.isColimit`, weak-factorization-system and Whitehead facts. None
  states this theorem or defines this signed-word category/properness.
- Loogle: `"colimMap", "WeakEquivalence"`: zero hits.
- Mathlib grep: `SignedWord|[Pp]roper[Dd]iagram|colimMap.*[Ww]eak` in
  AlgebraicTopology: zero hits.
- LeanSearch: "Homotopy invariance of ordinary colimits of proper diagrams of
  simplicial sets indexed by signed words". Eight hits included
  `CategoryTheory.MorphismProperty.colimitsOfShape_eq_of_equivalence`,
  `CategoryTheory.SimplicialObject.instHasColimits`, `SSet.hasColimits`, and
  finite-colimit dimension/finiteness statements. These supply ordinary
  colimits or shape transport, not the node's weak-equivalence invariance.
- Additional semantic/search queries for the signed-word category were run;
  the exact theorem-name and word-pattern searches below establish that the
  returned generic order/category constructions are not a pre-existing copy.
- `rg` over the upstream `WeilConjectures` and side-project `lean/Sheaf` for
  `SignedWord`, signed words and proper signed diagrams: no existing definition
  or theorem match. The downstream
  `Localization.HomotopyFractionsHammockComparison` mentions this item only in
  its proof plan; it does not supply this category or theorem.
- `grep -rn lem-coef-proper-word-colimit-invariance` over the upstream source:
  no match. `tools/lean_names_upstream.py show` has no binding for this item;
  the upstream-name JSON has no signed-word/category declaration match.
- `rg` over dag/nodes for the signed-word notion found the present statement,
  its boundary-pushout proof input, and the downstream hammock-comparison proof,
  not a separate definition node giving this category or properness.
  `tools/blueprint_refs.py search 'signed word'`: zero blueprint-node matches.

No statement correction, disputed statement, new definition node, or dependency
interface repair was needed. The node differs only in `lean` and the addition of
one already landed statement dependency. No other node is delivered. The module's
sole theorem has `sorry`; category-law proofs are the real construction fields.

Validation: scompile.py compiled the module separately in both its sandbox and
library-path checks with no errors or warnings. The required deliver2.py dry run
is run after writing this record; the second reader supplies independent review
and performs the actual delivery.

## Second reading by Q55

I read the node, its source place (Dwyer--Kan, Section 4.1, pages 22--23), the
dependency records, and `Sheaf/CategoryTheory/ProperWordColimitInvariance.lean`.
The item-by-item correspondence is as follows.

- The node's indexing category is rendered by `SSet.SignedWord`, with
  `length : ℕ` and `sign : Fin length → Bool`; the empty word is therefore
  included.  `SSet.SignedWord.Hom` has a weakly order-preserving position map
  and the pointwise sign-preservation equation.  `instCategory` supplies the
  stated identities and composition.
- An injection is rendered by `Function.Injective f.toFun`.  `IsProper` first
  quantifies over every such map and every `n : ℕ`, requiring injectivity of
  the degree-`n` component.  Its second conjunct quantifies over the two
  injections and an injection `h` with the prescribed intersection range, and
  equates the three degreewise ranges in `E(v)`.  This is the node's
  intersection-image clause; the source's induced image map is degreewise
  bijective because the first clause makes `E(h)` injective.
  Every finite intersection of position ranges has an increasing enumeration
  by `Fin` of its cardinality, with signs pulled back from `v`.  Thus such `h`
  always exists, including when the intersection is empty; the conditional
  quantification does not make this clause vacuous.
- The functors, natural transformation, and properness hypotheses are exactly
  `(E E' : SignedWord ⥤ SSet.{u})`, `η : E ⟶ E'`, `hE : IsProper E`, and
  `hE' : IsProper E'`.  There are no Kan, cofibrancy, finiteness, or
  nonemptiness hypotheses.
- The objectwise hypothesis is
  `∀ w, Enhanced.IsWeakHomotopyEquivalence (η.app w)`, using the recorded
  realization-based notion from `def-cbc-enhanced-diagrams-cones`.
- The conclusion is exactly
  `Enhanced.IsWeakHomotopyEquivalence (colimMap η)`, with Mathlib's chosen
  ordinary colimits of the two diagrams.  The colimit and degreewise quotient
  convention is supplied by the recorded `colimit` dependency.

The source's pairs of disjoint subsets of the positive integers whose union is
an initial segment are equivalent to the finite signed words used here; the
source's weakly order-preserving, sign-preserving maps are exactly `Hom`.  I
checked the empty word and empty target, repeated and constant signs, identity
and noninjective maps, degree `n = 0`, empty simplicial sets, and arbitrary
`u`; all are covered without an extra restriction.  No characteristic,
Noetherian, or universe assumption is present or needed.

I repeated the existing-definition searches with `rg` over the source and
side-project Lean, `tools/lean_names_upstream.py`, and DAG searches, and used
LeanSearch, LeanFinder, Loogle, and Mathlib grep for signed-word categories,
proper diagrams, and weak-equivalence colimit theorems.  They found only the
generic Mathlib category, simplicial-set, colimit, and weak-equivalence
primitives; no duplicate signed-word notion or theorem exists.  The recorded
`def-cbc-enhanced-diagrams-cones` declaration is the exact existing weak
equivalence predicate and is correctly added to `stmt_deps`.

The independent search queries and results were:

- LeanFinder: "A natural transformation of simplicial sets indexed by finite
  sequences of signs induces a weak equivalence on ordinary colimits if both
  diagrams preserve intersections and embeddings". Eight hits: the Quillen
  generating horn property, Dold--Kan summand maps, `SSet.hasColimits`,
  `SSet.horn.isColimit`, and `SSet.Subcomplex.MulticoequalizerDiagram`.
  These are general primitives, not this category or its invariance theorem.
- Loogle: `"colimit", "weakEquivalences"`. Zero hits.
- LeanSearch: "Finite ordered sets partitioned into two subsets form an index
  category for proper simplicial diagrams and their homotopy invariant colimits".
  Eight hits, including `SSet.hasColimits`, simplicial splitting index sets,
  `SimplicialObject`, and ordered-set colimits. No exact match.
- Mathlib grep through `msearch.py`:
  `signed.?word|proper (functor|diagram)|colimMap.*weak` in AlgebraicTopology.
  Zero hits. Direct `rg` using "finite words", "proper diagrams", and
  "proper functors" over upstream and project sources found no definition;
  the hammock-comparison hit is only a downstream proof-plan mention.
- `tools/lean_names_upstream.py show` gave no item binding;
  `tools/blueprint_refs.py search 'signed word'` gave zero matches. The DAG
  contains the present item and its boundary-attachment proof input, rather
  than another definition of this category and properness.

I also checked the eight proof steps in the theorem docstring against the
current node. The two unstated proof inputs (Brown split factorization and the
signed-word boundary pushout) still have no Lean record, so their omitted
imports are correct. No new node or dependency module needs a separate review.

I found no mismatch, statement correction, hollow definition, unbound
variable, or unusable dependency interface, so no Lean source or node field
was changed.  `scompile.py` was rerun on the module and passed both sandbox and
library-path compilation with only the permitted `sorry` proof.
