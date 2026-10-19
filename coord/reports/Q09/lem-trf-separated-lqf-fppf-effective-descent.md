## Worker report

The module `Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent` states
`AlgebraicGeometry.separated_lqf_fppf_effective_descent`. It uses the existing
covering-family interface `AlgebraicGeometry.SchemeCoverDescentDatum` and its
`SchemeCoverDescentDatum.IsEffective` predicate from
`Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum` (the family form of the recorded
`def-pd-descent-datum` notion). The fppf covering is rendered by
`Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`.

The Lean signature renders the statement clause by clause as follows:

* `T : Scheme.{u}` is the base scheme.
* `I : Type (u + 1)`, `U : I → Scheme.{u}`, and `f : ∀ i, U i ⟶ T` are the
  size-bounded indexed covering family.
* `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T` says that every member
  is flat and locally of finite presentation and that the family is jointly
  surjective, exactly the fppf covering condition.
* `D : SchemeCoverDescentDatum f` supplies the local schemes over the `U i`, their
  overlap transition isomorphisms, and the triple-overlap cocycle. This is the
  existing Yoneda encoding of the scheme descent datum in the node statement.
* `hsep : ∀ i, IsSeparated (D.localScheme i).hom` states separatedness of every
  local structure morphism.
* `hlqf : ∀ i, Scheme.Hom.IsLocallyQuasiFinite (D.localScheme i).hom` states local
  quasi-finiteness of every local structure morphism in the project's Stacks-01TD
  convention (including its local finite-type clause).
* The conclusion `D.IsEffective` is the existing geometric effectivity predicate:
  there is a scheme over `T`, Cartesian squares with every local scheme, and
  invariance of the composites under all overlap transports. It therefore renders
  the requested global `X` and the isomorphisms `X ×_T U_i ≅ X_i` inducing the
  given transitions.

The declarations used are:

* `AlgebraicGeometry.SchemeCoverDescentDatum` and
  `AlgebraicGeometry.SchemeCoverDescentDatum.IsEffective`, module
  `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum` (the existing covering-family
  datum and effectivity interface corresponding to the dependency
  `def-pd-descent-datum`).
* `AlgebraicGeometry.Scheme`, `CategoryTheory.Presieve.ofArrows`, and
  `AlgebraicGeometry.Scheme.fppfPrecoverage` from Mathlib's scheme and fppf-site
  modules (`def-pc-scheme`, `def-pc-fppf-site`).
* `AlgebraicGeometry.IsSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` (the separatedness clause of
  `def-weil-proper-morphism`).
* `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` from
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` (the recorded `pqf-def-quasifinite`
  declaration).

The statement has no quasi-compactness or local-finite-presentation hypothesis on
`D.localScheme i`; local finite presentation occurs only in the fppf covering
hypothesis, as required by Tag 02W8. Empty indexing families and empty schemes are
allowed by the unrestricted `I : Type (u + 1)` and scheme binders. The local
quasi-finite predicate is checked on the empty scheme vacuously, and no nonempty
cover assumption was added.

Searches performed:

* `msearch.py ... leanfinder "Effective fppf descent of separated locally quasi-finite schemes"`:
  no exact theorem; hits were generic separated/locally-quasi-finite permanence and
  fpqc descent declarations.
* `msearch.py ... loogle "SchemeCoverDescentDatum, IsEffective, fppfPrecoverage"`:
  unavailable for the project identifier (`unknown identifier`), hence no match.
* `msearch.py ... grep "SchemeCoverDescentDatum|separated_lqf_fppf_effective_descent|effective.*descent" AlgebraicGeometry`:
  no match in the searched Mathlib subdirectory.
* `rg` over `WeilConjectures` found no theorem with this item; `rg` over the project
  found the existing `SchemeCoverDescentDatum` interface and no theorem with this
  name. The full source and docstrings of that interface were read before use.

The file compiled cleanly with `scompile.py`; the only postponed proof is the
required theorem `sorry`.

## Second reading by Q09

(Written by the maintainer's independent reader. It replaces the one-line placeholder that the
delivery carried.) Node, Stacks Tag 02W8 (`more-morphisms.tex`, lemma
`lemma-separated-locally-quasi-finite-morphisms-fppf-descend`), every stmt_dep and the module
were read against each other.

Clause list of the node and its Lean:

1. Scheme $T$ [def-pc-scheme]: `T : Scheme.{u}`. Correct.
2. The family $\{T_i\to T\}_{i\in I}$ in the size-convention universes: `{I : Type (u + 1)}`,
   `U : I → Scheme.{u}`, `f : ∀ i, U i ⟶ T`. Index universe `u + 1` is the one fixed by the
   landed family interface `SchemeCoverDescentDatum` (def-trf-scheme-cover-descent-datum); it
   contains every `Type u` family up to `ULift`, so no case is lost. Correct.
3. fppf covering [def-pc-fppf-site]: `Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`;
   Mathlib's `fppfPrecoverage = precoverage (@Flat ⊓ @LocallyOfFinitePresentation)`, i.e.
   each member flat and locally of finite presentation, jointly surjective. Correct.
4. Descent datum $(X_i,\phi_{ij})$ with triple-overlap cocycle, "covering-family form of
   [def-pd-descent-datum]": `D : SchemeCoverDescentDatum f`, the landed family-form declaration
   of def-trf-scheme-cover-descent-datum (local schemes `D.localScheme i : Over (U i)`,
   transition isomorphisms and cocycle through Mathlib descent data and Yoneda). The recorded
   declaration of def-pd-descent-datum, `Over.DescentDatum`, is for a single morphism only, so
   the family declaration is the right object. One definition per notion: no private copy.
5. $X_i\to T_i$ separated [def-weil-proper-morphism]: `hsep : ∀ i, IsSeparated (D.localScheme
   i).hom`. Correct.
6. $X_i\to T_i$ locally quasi-finite [pqf-def-quasifinite]:
   `hlqf : ∀ i, Scheme.Hom.IsLocallyQuasiFinite (D.localScheme i).hom`, the recorded Stacks-01TD
   predicate (quasi-finite at every point, with the local finite-type clause). Correct, not
   Mathlib's weaker `LocallyQuasiFinite`.
7. No quasi-compactness or local finite presentation of $X_i\to T_i$: none is assumed. No
   extra instance. Correct.
8. Conclusion, effective: `D.IsEffective`, i.e. an `X : Over T` and maps $q_i$ with Cartesian
   squares and transport-invariance (the isomorphisms induce the given $\phi_{ij}$). Correct,
   neither weaker nor stronger.

Edge cases: empty `I` (no cover hypothesis excludes it; then the cover forces $T$ empty), empty
schemes and empty local schemes are all allowed. No nonemptiness or finiteness assumption.

Searches: the worker's LeanFinder, LeanSearch, Loogle and grep searches were repeated in
substance (`rg` for `SchemeCoverDescentDatum`, `effective`, `fppf` in lean/Sheaf and Mathlib
`AlgebraicGeometry/Sites`, `Morphisms/FlatDescent.lean`). There is no existing theorem; Mathlib's
`DescendsAlong` results are about properties of morphisms, not about effectiveness of scheme
descent data.

Compile: `nt_compile.py` on the module was clean (rc 0, no error, only the theorem's `sorry`).

Observation, nothing changed: the module uses the declarations of
def-trf-scheme-cover-descent-datum, which is not in the item's stmt_deps. The node text renders
the notion inline as the "covering-family form of [def-pd-descent-datum]", and the import records
the dependency. A later bookkeeping pass may add that landed node to stmt_deps.
