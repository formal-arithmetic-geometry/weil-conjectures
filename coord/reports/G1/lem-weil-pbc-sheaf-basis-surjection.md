## Worker report

The module `Sheaf.Topology.SheafBasisSurjection` states
`TopCat.exists_epi_extensionByEmptyConstant`. Its sole theorem has proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and clause correspondence:
- Topological space X: `(X : TopCat.{u})`.
- Basis B of its topology: `(B : Set (Set X)) (hB : IsTopologicalBasis B)`.
  This is Mathlib's actual topological-basis predicate, with no finiteness or
  quasi-compactness condition.
- Sheaf F of sets on X: `(F : X.Sheaf (Type u))`, the category of sheaves for the
  open-cover Grothendieck topology on `Opens X`.
- A set I and opens U_i: `∃ (I : Type u) (U : I → Opens X)`.
- Each U_i belongs to B: `∀ i : I, (U i : Set X) ∈ B`.
- Finite sets S_i: `(S : I → Type u)` and `∀ i : I, Finite (S i)`.
- One may take every S_i to be a one-point set: `∀ i : I, Nonempty (Unique (S i))`.
  Together with the other conjuncts this asserts that the same witnesses have
  singleton coefficients, as the node's parenthetical sentence and source proof say.
- Extension by empty of the locally constant S_i-valued sheaf:
  `TopCat.extensionByEmptyConstant (U i) (S i)`, exactly the dependency declaration.
- Coproduct in sheaves of sets on X:
  `∃ c : Cofan (fun i : I ↦ extensionByEmptyConstant (U i) (S i)),
  Nonempty (IsColimit c) ∧ ...`. A cofan is a cocone on the discrete diagram;
  `IsColimit c` asserts its coproduct universal property. The coproduct object
  is `c.pt`. This uses the node's colimit notion rather than assuming a
  `HasCoproduct` instance on the bundled `TopCat.Sheaf` category. The initial
  attempt to use chosen-coproduct notation had no such instance available;
  explicitly quantifying the colimit supplies its existence in the conclusion.
- Morphism to F and categorical epimorphism: `∃ φ : c.pt ⟶ F, Epi φ`.
  Neither objectwise surjectivity nor an arbitrary cocone replaces these conditions.

Dependency declarations read and used:
- `def-weil-pbc-sites-and-cohomology`: its record includes
  `CategoryTheory.Sheaf` (`Mathlib.CategoryTheory.Sites.Sheaf`), used through
  `TopCat.Sheaf` (`Mathlib.Topology.Sheaves.Sheaf`). The topological specialization
  supplies exactly the sheaves of sets needed here; the record's cohomology and
  continuous-functor declarations are irrelevant to this node.
- `def-weil-pbc-sets-extension-by-empty`: `TopCat.extensionByEmptyConstant`,
  in `Sheaf.Topology.SetsExtensionByEmpty`. Its full definition applies
  `extensionByEmpty` to `sheafToTop` with the discrete topology on S, hence the
  sheaf of locally constant S-valued maps. `extensionByEmpty` sheafifies
  `extensionByEmptyPresheaf`, whose object is G(V) for V ⊆ U and empty otherwise.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit` from its recorded declaration list;
  `CategoryTheory.Limits.Cofan` (`Mathlib.CategoryTheory.Limits.Shapes.Products`)
  abbreviates `Cocone (Discrete.functor ...)`. The signatures and universal-property
  fields were read in `Limits.Cones`, `Limits.IsLimit`, and `Limits.HasLimits`
  (the latter generates `colimit` and its interfaces by duality).
- `TopologicalSpace.IsTopologicalBasis` in `Mathlib.Topology.Bases` renders
  the basis hypothesis directly; no extra definition node is required.

Source check: the local Stacks TeX was absent on this machine, so the full
statement and proof were read at https://stacks.math.columbia.edu/tag/0CAH.
It asserts the finite-constant basis-open surjection and explicitly proves it
with singleton coefficients. The module docstring follows the node's five proof
steps: representative of each germ on a basis open, extension-by-empty adjunction,
coproduct and total map, stalk surjectivity, and the stalkwise criterion for epi.

Edge cases checked before writing:
- Empty X and even an empty basis are allowed. The family I may be empty;
  its coproduct is initial, and all set sheaves on the empty space are terminal
  and isomorphic, so the requested morphism is epi.
- The initial sheaf on a nonempty X may also use an empty I. No `Nonempty I`
  or nonempty-space assumption was inserted.
- Empty basis opens may occur and contribute initial extension-by-empty sheaves.
  No restriction U_i ≠ ∅ was inserted.
- No stalks or coefficient sets are required to be finite; only the chosen S_i
  are finite, and their singleton choice covers arbitrarily large sets of germs.
- X and section values both lie in universe u, as the dependency API specifies.
  The disjoint union of all stalks lies in Type u, so I : Type u can index the
  germ construction. The theorem is polymorphic in u, not restricted to a fixed
  concrete size. No independent smaller index universe excludes an example.

Searches for existing declarations:
- `msearch.py leansearch`: “Every sheaf of sets is an epimorphic coproduct of
  extensions by empty of finite constant sheaves on basis opens”. Service
  unavailable, Internal Server Error; no verdict inferred from the outage.
- `msearch.py leanfinder`: “A sheaf of sets is a quotient of a coproduct of
  extensions by empty of singleton sheaves on basis opens”. Eight hits on
  `typesGlue`, sheaf gluing conditions, and `existsUnique_gluing`; none states
  this basis-open coproduct epimorphism.
- `msearch.py loogle`: `TopCat.Sheaf, CategoryTheory.Epi`. Two hits:
  `TopCat.Sheaf.isLocallySurjective_iff_epi` and
  `TopCat.Sheaf.IsFlasque.epi_of_shortExact`; neither gives this presentation.
- `msearch.py grep`: `basis.*(surject|epi)|extensionByEmpty|fromFreeYonedaCoproduct`
  in `Topology/Sheaves`: zero hits.
- `rg` in `WeilConjectures` and `lean/Sheaf` for
  `basis.*(surject|epi)|extensionByEmptyConstant|lem-weil-pbc-sheaf-basis-surjection`:
  the extension-by-empty definition is present; other hits concern unrelated
  module bases or finite-free sheaf quotients. No matching theorem.
- `rg` in the source `Topology`/`CategoryTheory` directories for
  `extensionByEmpty|basis.*(surject|epi)|sheaf.*basis`: no matching theorem.
- Full declaration name and blueprint id checked against
  `dag/lean_names_upstream.json`, `WeilConjectures`, and `lean/Sheaf`: no match.

Validation: `lcompile.py` compiles the final module cleanly. All universes and
variables are explicitly bound. The final server compile and preflight are run
by `deliver2.py --no-push`; the independent second reading remains for its reader.
No disputed statement or node fault was found.

## Second reading by G1

I independently compared the node, its dependency signatures, and
`Sheaf/Topology/SheafBasisSurjection.lean`.

Object and hypothesis list, with Lean rendering and verdict:

- A topological space `X` is `(X : TopCat.{u})`; verdict: exact.
- A basis is `B : Set (Set X)` with `hB : IsTopologicalBasis B`; verdict: exact,
  with no separation, finiteness, or nonemptiness assumption.
- The sheaf of sets is `F : X.Sheaf (Type u)`; verdict: exact topological-site
  sheaf of sets from the sites-and-cohomology dependency.
- The witnesses are `I : Type u`, `U : I → Opens X`, and `S : I → Type u`;
  verdict: exact, with the index universe matching the sheaf universe.
- `∀ i, (U i : Set X) ∈ B`; verdict: exact basis-open condition.
- `∀ i, Finite (S i)`; verdict: exact finite-coefficient condition.
- `∀ i, Nonempty (Unique (S i))`; verdict: the permitted parenthetical
  strengthening that all coefficients may be chosen one-point sets.
- `∃ c : Cofan (fun i : I ↦ extensionByEmptyConstant (U i) (S i)),
  Nonempty (IsColimit c)`; verdict: exact coproduct existence and universal
  property in sheaves of sets, using Mathlib's `Cofan`/`IsColimit`.
- `∃ φ : c.pt ⟶ F, Epi φ`; verdict: exact epimorphism clause, with the map
  having the coproduct object as source.

The quantifier and conjunction order is unchanged. The source is Stacks,
Modules, Lemma 0CAH (lemma-surjection), line 2992: it assumes only a
topological space, a basis, and a sheaf, and chooses basis representatives of
all germs; it explicitly allows singleton coefficients. Empty `I`, empty
basis, empty basis opens, the empty space, and zero/initial sheaves remain
allowed by the Lean statement. Universe `u` is shared by `X`, the sheaf, the
index, and coefficient sets, so no case is excluded.

Searches repeated for the second reading: `rg` over Mathlib, the source
`WeilConjectures`, and `lean/Sheaf` found no theorem with this statement and
only the dependency `TopCat.extensionByEmptyConstant`; the existing
declarations `CategoryTheory.Sheaf.isLocallySurjective_iff_epi` and related
stalk criteria are not this presentation. The recorded LeanSearch,
LeanFinder/Loogle, and grep searches likewise found no duplicate notion.

No mismatch was found and no source or node correction was needed. The module
compiles cleanly with `lcompile.py`; all variables and universes are explicit,
and the only proof placeholder is the theorem's required `sorry`.
