## Worker report

The node is already implemented by the pinned slopmaster2 declaration
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` in
`WeilConjectures/SixFunctors/ProEtale/Derived/LowerShriek.lean` (source line 96).
No module is added. Its signature is
`noncomputable abbrev rightDerivedLowerShriekOfCompactification :
DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)`, with an explicit
compactification argument `c : Compactification f` in the surrounding section.
The declaration body is
`D((c.i)_!open[A]) ⋙ R((c.g)_*[A])`, which is the node's
`R\\bar f_{*,n} j_!` after specializing the coefficient category to
`ModuleCat.{u + 1} (A_{E,n})`.

The node's hypotheses are rendered by specialization/context: `X` and `Y`
are the schemes in the source declaration; a finite-type `K_0`-scheme and a
separated finite-type map `f` supply the compactification context; the prime
`ell`, its invertibility in `K_0`, finite extension `E`, and level `n >= 1`
select the finite coefficient ring `A_{E,n}`; and `c` is the source
`Compactification f`. These assumptions do not add data to the functor, so
the more general source declaration is the exact same definition. The
statement's composition clause is rendered by the source body: `D((c.i)_!`
is the derived extension by zero and `R((c.g)_*[A])` is the total derived
proper direct image. The node's etale-origin restriction, refinement
comparison, identity and transitivity laws, independence of `c`, cocycle
condition, and triangulated-functor assertion are properties/scope clauses,
not extra data in this definition; they are supplied by the separately cited
nodes `def-sf-etale-origin-subcategory`, `def-sf-refinement-comparison-isomorphism`,
`prop-compactification-coherence-detailed`, and
`lem-compact-support-direct-image-triangulated` (the last is a pointer in the
node).

Dependency declarations consulted:

- `def-weil-compactifications-refinements`: `AlgebraicGeometry.Compactification.Refinement`
  and `AlgebraicGeometry.Compactification.category`,
  `WeilConjectures.Compactification.Refinement`.
- `def-weil-l-adic-coefficient-extension`: `Padic.coefficientExtensionRing`
  and the finite coefficient construction in
  `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `def-weil-finite-torsion-constructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` in
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `def-weil-pbc-proetale-site`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` in
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `def-weil-derived-direct-image`:
  `WeilConjectures.SfIntegralDirectImage` and its finite-level derived-image
  declarations in `Sheaf.Paper.SfDerivedDirectImage`.
- `def-weil-extension-by-zero`:
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriek` in the source
  `FiniteCoefficient.LowerShriek.Open.Defs` module.
- `def-weil-pbc-etale-origin-witness`:
  `AlgebraicGeometry.ProEtale.EtaleOriginWitness` in
  `Sheaf.Paper.EtaleOriginWitness`.
- `def-weil-scheme-morphism-properties` is a convention node and has no
  declaration of its own; its named property nodes provide the classes.

Edge cases checked: the formula is defined for every chosen compactification
(including the identity compactification of a proper map), for arbitrary
objects of the unbounded derived category, and for every finite coefficient
ring instance; no nonempty, boundedness, constructibility, or witness
assumption is silently added to the definition. The source documentation also
warns that this is the composite of derived functors, not the derived functor
of the underived composite, matching the node's formula.

Searches made:

- `msearch.py ... leanfinder "compact support direct image derived functor compactification extension by zero pro-etale"`: eight generic condensed/sheaf hits; no compact-support direct-image declaration.
- `msearch.py ... loogle "rightDerivedLowerShriekOfCompactification, Compactification, DerivedCategory"`: no hits; the identifier is source-specific.
- `msearch.py ... grep "compactification|rightDerivedLowerShriek|lowerShriek"`: no Mathlib match.
- `rg` over the slopmaster2 source and project Lean found
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` at
  `WeilConjectures/SixFunctors/ProEtale/Derived/LowerShriek.lean:96`, with the
  exact body and documentation described above.

No statement discrepancy or `STATEMENT-DISPUTED` finding.

## Second reading by Q34

I read the complete node statement, the source place
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-compact-support-direct-image-detailed.md`,
and the source declaration at
`WeilConjectures/SixFunctors/ProEtale/Derived/LowerShriek.lean:96`.
The item-by-item match is:

* The field `K_0`, finite-type schemes `X` and `Y`, and separated finite-type
  morphism `f` provide the source context `X Y : Scheme.{u}`, `f : X ⟶ Y`, and
  `c : Compactification f`; the source declaration is polymorphic in this
  context, so specializing it to the node's geometric hypotheses introduces no
  stronger assumption.
* The prime `ell`, its invertibility in `K_0`, the finite extension `E/Q_ell`,
  and `n ≥ 1` determine the node's finite coefficient ring `A_{E,n}`. The
  source variable `A` is an arbitrary category with `[Category] [Abelian]
  [IsGrothendieckAbelian]`; taking `A := ModuleCat` over `A_{E,n}` is exactly
  the node's coefficient specialization.
* The node's `c = (j, \bar f) ∈ Comp(f)` is the source
  `AlgebraicGeometry.Compactification f`, whose fields are `c.i` (open
  immersion), `c.g` (proper map), and the factorization of `f`.
* The displayed functor and its domain and codomain are rendered by
  `rightDerivedLowerShriekOfCompactification`:
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
  DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)`.
* The composition clause is definitionally
  `D((c.i)_!open[A]) ⋙ R((c.g)_*[A])`, i.e. derived extension by zero followed
  by the total right-derived proper direct image, in the same order as
  `R\bar f_{*,n} j_!`.
* The finite-torsion/constructibility wording, the etale-origin subcategory
  and witness, refinement comparison, identity and transitivity laws,
  compactification independence, cocycle condition, and triangulated-functor
  assertion are scope/property clauses in the node. They are not extra fields
  of this definition and are supplied by the cited dependency nodes, exactly as
  the source documentation distinguishes the definition from later properties.

No mismatch was found. The only delivery change is the node's `lean` record:
it now records the existing source declaration
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` with
`existing: true`; no duplicate module is written.

Edge cases checked: `c` may be the identity compactification of a proper map;
the empty scheme and zero coefficient/module objects are allowed by the source
functor; the derived categories are unbounded, so no boundedness or nonempty
hypothesis is added; `n = 0` is excluded exactly by the node's `n ≥ 1`; and no
universe equality beyond the source's shared scheme universe is imposed.

Searches: `leanfinder` for “compact support direct image derived functor
compactification extension by zero pro-etale” returned only unrelated
condensed/sheaf declarations; `loogle` for
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` returned
no Mathlib hit; grep over Mathlib's algebraic-geometry, sheaf, and category
directories returned no compact-support direct-image declaration. The required
LeanSearch service was unavailable during this reading. `rg` over the source
repository found the exact declaration at the line cited above. The same
declaration is already recorded for dependency node
`def-weil-compact-support-candidate`, confirming that this item reuses it under
the one-definition-per-notion rule.
