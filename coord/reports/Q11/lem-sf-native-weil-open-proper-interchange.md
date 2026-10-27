## Worker report

The module `Sheaf.WeilSheaf.NativeOpenProperInterchange` states
`AlgebraicGeometry.WeilComplex.nonempty_extensionByZero_rightDerivedLowerStar_iso`.
Its only proof is `sorry`; it adds no definitions or axioms. The node's mathematical
statement, statement dependencies, and proof plan are unchanged. The node already has a
reviewed stage-1 split by NV, but no `lean` attachment on the supplied base; this packet is
stage 2, not a re-delivery of that split.

Hypothesis and clause correspondence:

- Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime different from the characteristic: `(l : ℕ) [Fact l.Prime]`
  and `[Fact (ringChar k₀ ≠ l)]`. The existing native framework uses `PadicAlgCl l`
  and the chosen `AlgebraicClosure k₀`; neither is replaced by an arbitrary coefficient ring.
- The four finite-type schemes: `{U' X' U X : Scheme.{u}}`, four `Over (Spec k₀)`
  structures, and `LocallyOfFiniteType` and `QuasiCompact` for each structure morphism.
  These are precisely finite type; no absolute separatedness is imposed.
- Four morphisms over that field: `j'`, `p'`, `p`, `j` with their four `IsOver` instances.
- Commutative square: `hcomm : j' ≫ p = p' ≫ j`. There is no pullback assumption.
- Proper vertical arrows: `[IsProper p] [IsProper p']`.
- Quasi-compact open horizontal arrows: `[IsOpenImmersion j] [QuasiCompact j]`
  and the same two instances for `j'`.
- Bounded constructible source and full native derived realization:
  `(WeilComplex.objectProperty k₀ l U').ι` includes the full subcategory
  `WeilComplex k₀ l U'` into `DerivedCategory (ProEtaleWeilSheaf k₀ l U')`.
  The property is boundedness intersected with constructibility of all cohomology.
- The left functor is that inclusion, followed by
  `(ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor`, then
  `(ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory`.
- The right functor is that same inclusion, termwise extension along `j'`, then the total
  right derived functor of the actual native sheaf direct image along `p`.
- `Nonempty (left ≅ right)` states existence of a natural isomorphism of functors,
  with target the ambient `DerivedCategory (ProEtaleWeilSheaf k₀ l X)`.
  Its hom and inv have native derived morphisms as components; Frobenius compatibility
  is included in that category, rather than appended to underlying nonequivariant maps.
- Only the source inclusion restricts the theorem: no assertion is made for unbounded
  arbitrary module complexes. All universes and variables are explicitly bound.

Dependency declarations used:

- `def-sf-native-weil-derived-framework`: public import
  `WeilConjectures.WeilSheaf.LowerShriek`, the recorded public entry module.
  `WeilConjectures.WeilSheaf.Category` supplies `AlgebraicGeometry.ProEtaleWeilSheaf`,
  `AlgebraicGeometry.WeilComplex`, and `AlgebraicGeometry.WeilComplex.objectProperty`.
  `WeilConjectures.WeilSheaf.LowerStar` supplies
  `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar`.
  `WeilConjectures.WeilSheaf.OpenImmersion` supplies
  `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero` and its exactness instances.
  `CategoryTheory.Functor.rightDerivedFunctor` and `mapDerivedCategory` are the actual
  ordinary derived constructions used by the framework itself.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.

Recorded, stated proof prerequisites are imported privately. The native constructible
abelian, native basic comparisons, and continuous-adic proper-base-change-restriction
nodes have no recorded module on the supplied base; their future modules cannot yet be
imported. They are proof prerequisites, and no new statement dependency is needed here.
The theorem docstring contains all eleven proof steps, including their bounded truncation
argument and native-morphism construction.

Sources read: the entire node and its four statement dependencies, the recorded native
framework modules and ordinary operation definitions, Mathlib's morphism classes, and
`literature/stacks-project/more-etale.tex`, lemma-shriek-proper-and-open, Tag 0F7B.
The source tag gives the proper/open geometric pattern, not an identification of these
native coefficients with torsion etale coefficients; the node's native proof is retained.

Edge cases checked before writing:

- Empty `U'` and empty other schemes are permitted; no `Nonempty` scheme hypothesis occurs.
  `Nonempty` in the conclusion quantifies over natural isomorphisms only.
- Identity opens are allowed, as are the identity proper maps and zero complexes.
- A non-Cartesian square is allowed: the clopen factor in the proof can be a proper
  component of `X' ×_X U`. No missing-component surjectivity is assumed.
- Non-separated finite-type schemes over the field are allowed; relative properness of
  `p` and `p'` is the only separatedness input of the geometric argument.
- Finite cohomological support may be empty, a single degree, or any finite range.
  The source is not restricted to nonnegative degrees.
- `Scheme.{u}` and the finite field share the framework universe; no equality between
  the object's universe and the higher site/sheaf universes has been imposed.

Searches made for an existing exact statement:

- msearch LeanFinder: “proper direct image commutes with extension by zero along a
  commutative square of open immersions on bounded constructible Weil complexes”. Eight
  Mathlib hits, including `Scheme.Modules.restrictFunctorComp`, concern ordinary open
  restriction, not this native derived comparison.
- msearch Loogle: `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero,
  CategoryTheory.Functor.rightDerivedFunctor`. Zero hits; the service did not recognize
  the project-specific first identifier.
- msearch Mathlib grep: `proper.*[Oo]pen|[Oo]pen.*proper|extensionByZero.*[Ii]so`.
  Twenty-five returned hits concern scheme morphism properties and open immersions;
  none is the native theorem.
- Project `rg` searches for the item id and for the same proper/open and extension-by-zero
  patterns in `lean/WeilConjectures` and `lean/Sheaf` found no module owning this item.
  The framework's `LowerShriekFunctoriality` states compact-support composition rather
  than the needed interchange of an arbitrary proper/open square. Its proper clopen
  extension comparisons do not state the present theorem.

No statement correction, dependency repair, or new node is needed. No disputed statement
was found. The prescribed `scompile.py` compiled both sandbox and library module modes cleanly
(8.3 s and 6.4 s), with no warnings or errors.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
