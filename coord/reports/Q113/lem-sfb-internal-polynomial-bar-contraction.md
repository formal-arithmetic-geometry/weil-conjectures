## Worker report

The module `Sheaf.Paper.InternalPolynomialBarContraction` states
`InternalPolynomialBar.contraction` and defines the actual finite sum
`InternalPolynomialBar.finiteColumn`. Every theorem has a sorry proof; the definition
contains only `Finsupp.sum` and categorical composition, with no postponed data or proof.
No node statement was changed and no new or dependency nodes were needed.

The source read was the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), together with this node's explicit agent-origin finite-matrix proof.
The current blueprint paragraph uses the coefficient/open-image theorem and does not
itself contain the polynomial contraction, as the node's proof_origin already records.
The module docstring preserves this attribution rather than claiming a quoted theorem.

Hypotheses and clauses, in the order of the node:

- The arbitrary commutative condensed ring is `A : Profinite.CondensedRing.{u}` with
  `[IsCommMonObj A.X]`, not a ring of continuous functions on a topological coefficient
  ring. The unital rational global-section map is `φ : ℚ →+* ...obj (op (⊤_ Profinite))`.
  `sectionRings` reconstructs the actual section ring from the tensor ring object.
- The internal category is the recorded `Profinite.CondensedAction.Modules A`, transparently
  Mathlib's `Mod (Sheaf (coherentTopology Profinite) AddCommGrpCat.{u+1}) A.X`.
  The profinite objects are in universe u, their site in u+1, and section groups in u+1.
  Ordinary derived localization uses `HasDerivedCategory.{u+2}` and `DerivedCategory.Q`.
  The derived clause quantifies over every choice of this localization interface.
- `r : ℕ` covers every nonnegative rank. The polynomial degree-n object `P.X n` has
  injections `ι n` indexed by `(Fin n × Fin r) →₀ ℕ`, with `IsColimit (Cofan.mk ... )`.
  Thus it is precisely the internal coproduct of copies of the regular module indexed
  by all monomials, with no polynomial-degree bound.
- `K.X n` has injections `κ n` indexed by the recorded `ExteriorIndex r n` (subsets
  of cardinality n). Its coproduct universal property and `K.d n (n+1)=0` express
  the exterior sum and its zero differential. `K.extend embeddingUpNat` and the
  corresponding P extension put both complexes zero in negative integer degrees.
- The generator equation for `P.d` uses the exact
  `RationalPolynomialBar.differential ℚ r n`, whose definition has both outer cofaces
  and the signs (-1)^(a+1) for zero-based interior coface a. It therefore renders the
  displayed differential clause by clause. The cochain-complex structure also carries d²=0.
- `i` is pinned on every subset injection to the exact dependency's `inclusion` column:
  the ordered product of its coordinates, including the empty product 1 in degree zero.
- The given rational homotopy `h` is universally quantified. `hzero` and `hsucc` express
  its rational contraction identities separately at zero and at positive degrees.
  The inclusion and projection are the fixed monomial formulas of the rational dependency,
  whose theorem supplies the other rational identities. Each h-column is a genuine
  polynomial, hence finitely supported, so no separate support hypothesis is necessary.
- The scalar endomorphism `s c` is pinned at every profinite S and every coefficient
  section a to `φ(c)|S * a`, using `sectionRings.map (terminal.from S).op`.
  `p` and `H` are pinned on every monomial injection to `finiteColumn` of the exact
  rational projection/homotopy column. `AddMonoidAlgebra.coeff` accesses the stored
  finitely supported coefficients (Mathlib now wraps these coefficients in a structure).
  These are actual internal morphisms and their underlying natural transformations
  commute with every restriction; this is stronger than checking ordinary points only.
  Evaluating the finite-column equation on any coefficient section gives exactly the
  node's finite sum of rational coefficients times that section. No sectionwise
  direct-sum identification is assumed.
- The next conjuncts explicitly say `di=0`, `pd=0`, `i ≫ p = 𝟙 K`, and the homotopy
  identity at degree zero and at every successor degree. The order of categorical
  composition reverses the printed function-composition notation: `i ≫ p` is p i.
- The `HomotopyEquiv` existential on the integer extensions fixes both `e.hom` to
  `extendMap i` and `e.inv` to `extendMap p`. The final isomorphism in the ordinary
  derived category likewise fixes both arrows to the images under `DerivedCategory.Q`.
  An arbitrary unrelated isomorphism cannot witness these clauses.
- The statement has no nonzero, completeness, topology-on-A, or flatness hypothesis.
  Its finite sums operate on each source injection and not on all sections at once.

The coproduct models and their maps are existentially specified together with their
universal properties and all generator equations. These properties determine the
models up to their coproduct identifications and determine every arrow uniquely.
This states existence of the constructions and their asserted properties without
introducing a choice-based definition of an unknown complex or map.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`, `Mod.Hom`, `Mod.regular`.
  `Sheaf.CategoryTheory.CondensedActionModule.Modules` specializes exactly this category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`; `HasDerivedCategory.standard` gives the default u+2 choice.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; the dependency module's
  `MvPolynomial.aeval` renders the substitutions and its monomial basis fixes the columns.
- `Sheaf.Paper.RationalPolynomialBarContraction`: `P`, `K`, `ExteriorIndex`, `differential`,
  `inclusion`, `projection`, `extendHomotopy`, `contraction`; full definitions and signatures read.
- `def-weil-size-convention` is metatheoretic, with no Lean declaration to import.
- Proof imports for the stated nodes `def-sp-grothendieck-abelian` and
  `def-weil-pbc-category-colimit` are respectively
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` (`IsGrothendieckAbelian`)
  and `Mathlib.CategoryTheory.Limits.HasLimits` (`colimit`, `IsColimit`).
  `lem-sfb-condensed-action-injective-infrastructure` has no recorded Lean declaration,
  so there is no module to import for that proof dependency. Its needed generic
  module-abelian infrastructure is publicly supplied by the upstream
  `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` and sheafification
  module; no additional hypothesis or restatement of that unstated infrastructure is used.

Edge cases checked before writing: the zero ring admits a unital map from ℚ and every
coefficient endomorphism is zero; no injectivity is required. At r=0 all monomial index
sets are singleton, exterior index is singleton in degree zero and empty otherwise;
the constant polynomial complex alternates d=0 in even and d=identity in odd degrees.
The ordered empty product is 1, so i is the degree-zero constant inclusion. At n>r the
exterior indexing type is empty. Degree zero has its own homotopy equation, so there
is no missing predecessor or unintended degree -1 term. In rank one at degree one,
the differential is f(y)-f(x+y)+f(x), matching the recorded dependency.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Extend rational polynomial additive bar contraction to
  internal condensed modules by finite monomial matrices"`: eight unrelated hits,
  including `LinearMap.polyCharpolyAux`, `PolynomialLaw.lifts`, `PolynomialModule.comp`;
  no internal contraction or matching theorem.
- `msearch.py ... loogle '"MvPolynomial", "Homotopy"'`: OK, zero hits.
- `msearch.py ... leansearch "A rational polynomial bar contraction extends by finite
  matrices to sheaves of modules"`: eight hits, including general module-sheaf colimits
  and unrelated polynomial contraction; none states the specified contraction.
- `msearch.py ... grep 'polynomial.*(homotop|contract)|(homotop|contract).*polynomial'`:
  only separable-degree and polynomial-expand hits, no relevant statement.
- `msearch.py ... grep 'InternalPolynomialBar|finiteColumn|polynomial.*(homotop|contract)'
  CategoryTheory`: OK, zero hits.
- `rg -n` of polynomial/bar/contraction names in `lean/WeilConjectures` and `lean/Sheaf`
  found the rational dependency and the polynomial derived-bar comparison. Their complete
  relevant declarations were read. The latter's `Complex` is a coproduct specification
  only and its theorem concerns continuous topological coefficients and evaluation
  into a lattice bar construction, not extension of arbitrary rational contractions.
  The rational dependency works in ordinary modules over an ordinary ring, not internal
  modules. Neither supplies the item. A search for this exact blueprint id under
  `lean/WeilConjectures` found no match.

Validation: the prescribed `scompile.py Q113 lem-sfb-internal-polynomial-bar-contraction`
compiled the file both as a sandbox module and under its library module name, with no
errors or warnings beyond the allowed sorry. The initial coefficient-wrapper mismatch
was repaired using `AddMonoidAlgebra.coeff`; no assumptions or conclusions changed.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
