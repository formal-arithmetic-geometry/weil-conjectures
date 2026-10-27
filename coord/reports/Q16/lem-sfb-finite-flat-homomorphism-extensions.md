## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FiniteLocallyFreeExtensions` states
`AlgebraicGeometry.finiteLocallyFree_surjective_of_extension_diagram`, with its whole
proof `by sorry`. It defines no new notion. The node is unchanged outside `lean`.

Hypothesis and conclusion correspondence:

- The arbitrary base scheme is `(B : Scheme.{u})`.
- The six commutative B-group schemes are the three families
  `(K E Q : Fin 2 → Over B)`, each with `GrpObj` and `IsCommMonObj` instances.
  Indices 0 and 1 encode the source's rows 1 and 2. These are the existing internal
  group objects in the category of schemes over B, with their actual multiplication,
  inverse and identity morphisms and group laws. Multiplicative notation makes the
  additive zero section of the node the section `1`.
- The row homomorphisms are `j` and `q`, with `IsMonHom (j i)` and `IsMonHom (q i)`.
- For EACH row and EACH B-scheme U, `hkernel` asserts injectivity of postcomposition
  by `j i`, and `e ≫ q i = 1 ↔ ∃ k, k ≫ j i = e`. Together these say precisely
  that K(U) identifies with the kernel, including that every j(k) lies in the kernel.
- For EACH row, U and section `x : U ⟶ Q i`, `hlift` supplies a family of B-schemes
  V with arrows p to U. The underlying family belongs to `Scheme.fppfPrecoverage`:
  it is jointly surjective, flat, and locally of finite presentation. For EACH
  member, a section e satisfies `e ≫ q i = p a ≫ x`. This is local lifting, not
  global surjectivity on sections. All arrows in `Over B` are B-morphisms.
- The covering index has `I : Type u`, the same universe as scheme points. This
  loses no covers needed for local lifting: any jointly surjective covering can
  be reduced by choosing a member and a point above each point of U; the selected
  subfamily is still jointly surjective and all its members remain fppf. The
  empty cover is permitted for empty U.
- The vertical homomorphisms are `u`, `v`, `w` and their three `IsMonHom` instances.
- `hleft : j 0 ≫ v = u ≫ j 1` is v j₁ = j₂ u;
  `hright : v ≫ q 1 = q 0 ≫ w` is q₂ v = w q₁.
- `hu` and `hw` are the recorded `Scheme.Hom.IsFiniteLocallyFree` on u.left and
  w.left. `hsu` and `hsw` are `AlgebraicGeometry.Surjective` on those scheme maps,
  which means surjectivity on underlying points.
- The conclusion is precisely `Scheme.Hom.IsFiniteLocallyFree v.left ∧
  Surjective v.left`.
- There is no smoothness, reducedness, connectedness, or characteristic hypothesis.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; the full signatures and docstrings were read locally.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `fppfTopology`. We use the recorded
  covering families explicitly; their slice arrows are encoded by `Over B`, so
  no separate slice-topology construction or sheafification is needed.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`. Its full server signature
  is a Prop class extending `IsFinite f`, `Flat f`, and
  `LocallyOfFinitePresentation f`, exactly the node's definition.
  The older local file lacks it, but `scompile.py --source` confirmed the recorded
  definition in the live server module; no duplicate or record repair was made.
- Group notions use `CategoryTheory.GrpObj`, `CategoryTheory.IsCommMonObj`,
  `CategoryTheory.IsMonHom` and `CategoryTheory.Hom.group` from the existing
  Cartesian group-object API. `Over` uses the scheme pullback monoidal structure.
- The proof-dependency records were read. Their modules are imported: Yoneda;
  scheme morphism permanence via Finite, Flat, FinitePresentation, Proper and
  QuasiSeparated; fppf base-change and fppf-to-fpqc via Sites.Fpqc; and
  `WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover`,
  `WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover`,
  `WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent`.
  The three descent declarations' full signatures and proof docstrings were read.

Source and edge cases:

Read `literature/stacks-project/descent.tex`, the complete lemma and proof at
`lemma-descending-property-finite-locally-free` (Tag 02VO), together with all six
steps of the item's agent-written group-extension argument. The module docstring
carries those six steps, including the translation inverse, Yoneda identification,
descent of all three finite locally free properties, and the point argument for
surjectivity. The statement agrees with this argument.

Checked: empty base and empty test schemes (no nonemptiness assumption, empty
cover allowed); trivial kernel or quotient groups; identity vertical maps;
nonreduced groups and positive-characteristic infinitesimal kernels (none are
excluded); local lifts that do not descend to global sections; and arbitrary
scheme universe u. No rank or positivity condition was inserted. A non-surjective
finite locally free map of degree zero cannot be used over a nonempty target,
as required by the separate surjectivity assumptions. No statement dispute or
node fault was found.

Searches for existing statements (2026-10-24):

- `msearch.py ... leansearch "A homomorphism of extensions of commutative group
  schemes is finite locally free and surjective if its maps on the kernel and
  quotient are finite locally free and surjective"`: 8 hits, including
  Algebra.Extension.Hom, GroupExtension, AddGroupExtension and IsFinite.recOn;
  none states the scheme-theoretic extension result.
- `msearch.py ... leanfinder "A morphism of extensions of commutative group
  schemes is finite locally free surjective if the kernel and quotient maps are
  finite locally free surjective"`: 8 hits, concerning algebra cotangent maps,
  IsFinite.of_comp, Module.Finite.of_exact and abstract five lemmas; no match.
- `msearch.py ... loogle '"GrpObj", "IsFiniteLocallyFree"'`: 0 hits.
- `msearch.py ... grep "(extension|exact).*(finite locally free|finite flat)|
  (finite locally free|finite flat).*(extension|exact)"`: 2 irrelevant hits in
  RingTheory/RamificationInertia/Basic.lean about extensions of domains.
- `rg` with that same expression in `lean/WeilConjectures` and `lean/Sheaf`:
  only three unrelated prose hits about locally free modules and pairings.
- `rg` for the node id in `lean/WeilConjectures`: no hit.
- `rg` for `finiteLocallyFree_surjective_of_extension_diagram` in Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json`: no hit.
- `rg` for group-scheme / group-object names located the existing Over/GrpObj/
  IsCommMonObj/IsMonHom conventions and their full source definitions, used here.

Validation: `scompile.py Q16 lem-sfb-finite-flat-homomorphism-extensions <file>`
passed both the sandbox compile (4.1 s) and final module compile (7.1 s), with no
errors or warnings. Every universe and variable is explicitly bound.

## Second reading by Q16

Performed a separate clause-by-clause rereading of the node and the completed
module in this dispatcher-started single-worker session; no second agent was
started, as the brief forbids it. The maintainer's independent review remains
the independent reading.

The two Fin 2 rows cover exactly the six supplied group schemes. Checked both
halves of kernel identification, including injectivity rather than just equality
of images, both local lifting clauses, the directions of the two composition
equations, all seven homomorphisms (four row maps and three vertical maps), both finite locally free hypotheses,
both point-surjectivity hypotheses, and the two-part conclusion. The multiplicative
`1` is the identity SECTION in `Hom(U,Q i)`, not the identity scheme map. Cover
membership is tested on the underlying family over U.left, while p and e remain
B-morphisms. No local instance, private notation, hollow data, or extra geometric
assumption occurs. No mismatch was found and no statement correction was made.
