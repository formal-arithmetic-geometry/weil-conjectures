## Worker report

The node already has an exact upstream declaration, so no Lean module is added.  The
recorded declaration is
`AlgebraicGeometry.Scheme.Hom.IsFrobenius.isUniversalHomeomorphism` in
`WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius`.  Its source theorem is
proved (not `sorry`) and has the signature
`theorem isUniversalHomeomorphism : IsUniversalHomeomorphism F`.
The theorem's surrounding binders quantify a finite field `k`, a scheme `X`, an
endomorphism `F : X ⟶ X`, a proof that `F` is the `Nat.card k`-power Frobenius,
and a structure morphism `f₀ : X ⟶ Spec (CommRingCat.of k)`; its conclusion is
`IsUniversalHomeomorphism F`.  Taking `k = k₀`, `X = T`, `f₀` to be the given
`k₀`-scheme structure morphism, and `F` to be the absolute q-power Frobenius
(`q = Nat.card k₀`) gives exactly the node statement.  The theorem has no
finite-type or separatedness assumption.

The node's clauses render as follows.  The fixed finite-field datum supplies
`p`, `a`, `q = p ^ a`, the finite field `k₀` with `Nat.card k₀ = q`, and its
chosen algebraic closure `k`; these are the fields and cardinality assumptions
used by the upstream theorem after specializing its finite field parameter to
`k₀`.  A `k₀`-scheme `T` is a scheme `X` together with its structure morphism
`f₀ : X ⟶ Spec (CommRingCat.of k₀)`, using Mathlib's `Scheme.Over` convention
from `def-weil-scheme-over-base`.  The absolute q-power Frobenius
`F_T^(q)` is the a-fold iterate of the absolute Frobenius from
`def-weil-absolute-frobenius-scheme`; its affine action is `s ↦ s ^ q` and its
underlying-space map is the identity.  The upstream predicate
`Scheme.Hom.IsFrobenius F (Nat.card k₀)` is precisely the affine-chart
characterization of this q-power action.  The conclusion
`AlgebraicGeometry.IsUniversalHomeomorphism F` is the project's universal
homeomorphism class (integral, universally injective, and surjective), which
is equivalent in the imported upstream module to the usual all-base-changes
homeomorphism formulation.

Dependency declarations read and used:

* `def-weil-finite-field-fiber`: `WeilConjectures.FiniteFieldDatum` in
  `Sheaf.Paper.FiniteFieldFiber`; its fields `p`, `a`, `q`, `k₀`, `k`,
  `prime`, `exponent_pos`, `cardinality_eq`, and `card_base` provide the fixed
  finite-field datum.
* `def-weil-scheme-over-base`: Mathlib's `AlgebraicGeometry.Scheme.Over` in
  `Mathlib.AlgebraicGeometry.Over`, with `Scheme.Hom.IsOver`/`Scheme.asOver`
  expressing the structure morphism and maps over the base.
* `def-weil-absolute-frobenius-scheme`: the existing
  `AlgebraicGeometry.Scheme.iterateFrobenius` declaration in
  `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`, whose `n = a` case is
  the absolute q-power Frobenius.
* `def-weil-universal-homeomorphism`: the existing
  `AlgebraicGeometry.IsUniversalHomeomorphism` class from
  `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`; the
  same module records `isUniversalHomeomorphism_eq` and the theorem relating
  this class to the universally-base-changed `IsHomeomorph` property.

I checked edge cases before accepting the existing declaration: the empty
scheme (the affine-cover argument and the universal-homeomorphism class remain
valid), the empty base change in the definition, a one-point finite field, and
q = p (a = 1).  No argument uses finite type, quasi-compactness, separatedness,
or nonemptiness of `T`; arbitrary schemes and arbitrary base changes remain
allowed.  The theorem's finite-field assumption excludes the zero-cardinality
case, since `Nat.card k` is positive for a field.

Searches for an existing definition or theorem were repeated with the required
tools.  `msearch.py ... leanfinder "absolute q-power Frobenius of any scheme over a
finite field is a universal homeomorphism"` returned only ring-level Frobenius
and perfect-ring results, with no scheme theorem.  `msearch.py ... loogle
"IsFrobenius, IsUniversalHomeomorphism"` returned no hit because the project
predicate is not in Mathlib.  `msearch.py ... grep "isUniversalHomeomorphism"
AlgebraicGeometry/Morphisms` returned no Mathlib hit.  Direct `rg` over the
upstream `WeilConjectures` tree found the exact theorem in
`AlgebraicGeometry/Morphisms/Frobenius.lean:151` and the universal-homeomorphism
class/equivalence in `Morphisms/UniversalHomeomorphism.lean`; direct `rg` over
`lean/Sheaf` found no duplicate declaration for this item.  The required search
for the item id in the upstream source also found no duplicate node-specific
statement.  The full source module and docstrings were read, and the exact
server source was fetched with `scompile.py --source
WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius`.

A probe importing the upstream module and checking both
`@AlgebraicGeometry.Scheme.Hom.IsFrobenius.isUniversalHomeomorphism` and
`@AlgebraicGeometry.isUniversalHomeomorphism_le_universally_isHomeomorph`
compiled cleanly with `scompile.py`.  No new nodes, dependency modules,
statement correction, or `STATEMENT-DISPUTED` issue is present.


## Second reading by NO

I read the node statement, Tag 0CC8 in `literature/stacks-project/varieties.tex`, the four
statement dependencies, and the Lean declaration independently.  The item has the following
objects and clauses.

* The finite-field datum is `(p, a, q, k₀, k)`, with `p` prime, `1 ≤ a`, `q = p ^ a`,
  `k₀` a field of cardinality `q`, and `k` its fixed algebraic closure.  These are rendered
  by `D : WeilConjectures.FiniteFieldDatum.{u}`; its fields are `D.p`, `D.a`, `D.q`,
  `D.prime`, `D.exponent_pos`, `D.cardinality_eq`, `D.k₀`, `D.card_base`, and `D.k`.
  Verdict: all datum fields are present, including the closure and the cardinality equation.
* A `k₀`-scheme `T` is rendered by `T : Scheme.{u}` and
  `[T.Over (Spec (CommRingCat.of D.k₀))]`; its structure morphism is
  `T ↘ Spec (CommRingCat.of D.k₀)`.  Verdict: the object and its base structure are present,
  with no finite-type, separatedness, quasi-compactness, or nonemptiness hypothesis.
* The absolute `q`-power Frobenius is rendered exactly as
  `T.iterateFrobenius D.prime
  (D.model_characteristic (T ↘ Spec (CommRingCat.of D.k₀))) D.a`.  By the dependency
  declaration `Scheme.iterateFrobenius`, it is the identity on the underlying space and
  sends every section `s` to `s ^ p ^ a = s ^ q`.  Verdict: the map is the dependency's
  canonical absolute iterate, rather than an arbitrary endomorphism; the characteristic
  proof is supplied by `model_characteristic` for every `k₀`-scheme.
* The conclusion that this map is a universal homeomorphism is rendered by
  `IsUniversalHomeomorphism (...)`.  Verdict: the full bundled predicate is retained,
  including integrality, universal injectivity, and surjectivity, hence the equivalent
  all-base-change homeomorphism formulation.

The original worker recorded `AlgebraicGeometry.Scheme.Hom.IsFrobenius.isUniversalHomeomorphism`
as an exact existing declaration.  Its actual signature is
`theorem isUniversalHomeomorphism : IsUniversalHomeomorphism F` in a context containing the
extra parameters `hF : F.IsFrobenius (Nat.card k)` and
`f₀ : X ⟶ Spec (.of k)`.  It therefore states the generic conditional theorem, not the node's
absolute `iterateFrobenius` map, and cannot be recorded as an exact existing realization under
H4.  I replaced that record with the statement-only declaration
`WeilConjectures.FiniteFieldDatum.absoluteFrobenius_isUniversalHomeomorphism` in
`lean/Sheaf/AlgebraicGeometry/AbsoluteFrobeniusUniversalHomeomorphism.lean`; its signature is
verbatim in the node's `lean.statement`.  The upstream theorem remains the planned proof input.
No hypothesis or conclusion was added or removed.

I also read each dependency declaration.  `FiniteFieldDatum` supplies the global datum;
`Scheme.Over` supplies exactly the structure morphism; `Scheme.iterateFrobenius` supplies the
canonical identity-on-points, section-power map; and `IsUniversalHomeomorphism` is the
project's integral/universally-injective/surjective class.  No dependency module was needed.

Edge cases checked: `T` may be empty, have a zero ring on an affine chart, be nonreduced,
be an infinite disjoint union, or be non-separated; `a = 1` gives the ordinary p-Frobenius;
`q = p` is included; the characteristic proof also covers zero section rings.  The finite
field hypotheses exclude `q = 0`, as required.  No universe is introduced below the datum's
universe, and the scheme and all ring objects remain in `Type u`.

Searches repeated: `rg` over `WeilConjectures/` and `lean/Sheaf/` found the generic upstream
`IsFrobenius.isUniversalHomeomorphism` but no theorem for `iterateFrobenius`; Loogle and
LeanFinder found only ring-level Frobenius and bijectivity results; Mathlib grep found no
scheme-level absolute-Frobenius universal-homeomorphism theorem.  The upstream source module
and Stacks Tag 0CC8 were read in full.  The new statement module compiles cleanly with
`scompile.py`; its only permitted diagnostic is the postponed `sorry` proof.
