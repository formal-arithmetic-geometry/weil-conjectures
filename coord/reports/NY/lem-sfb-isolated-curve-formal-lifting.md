## Worker report

The module `Sheaf.AlgebraicGeometry.IsolatedCurveFormalLifting` states
`AlgebraicGeometry.exists_isolatedCurve_formal_lifting`, with its sole theorem proof
`sorry`. The six helper definitions have real data. They belong to this node's
coefficient-ring and reduction notation and are listed in `lean.declarations`.
No node statement or dependency was changed, and no new node is introduced.

Sources read: `examples-defos.tex`, Tag 0DZP (`lemma-curve-isolated`, statement and
proof), Tag 0DZF (`lemma-isolated`, statement and proof), and `formal-defos.tex`,
Tag 06HN (`lemma-smooth-morphism-essentially-surjective`, including its recursive
commuting square). The theorem is the formal-system consequence recorded by the
node, for the proper case. The docstring follows all eight node proof steps,
including the compatibility equations, properness reflection, and finite presentation.

Hypotheses and conclusion, clause by clause:

- Field and proper curve: `(k : Type u) [Field k]`, `(X : Scheme.{u})`,
  `(f : X ⟶ Spec (.of k)) [IsProper f]`. The explicit structure map is used for
  base change and its induced scalar maps on stalks.
- Dimension at most one: `hdim : topologicalKrullDim X ≤ 1`.
- Distinct finite closed points: `r : ℕ`, `p : Fin r → X`, `hp : Function.Injective p`,
  and `hclosed : ∀ i, IsClosed ({p i} : Set X)`.
- Smooth away from the marked set: for every `x ∉ Set.range p`, `hsmooth` gives
  an open neighbourhood `U` with `Smooth (U.ι ≫ f)`. This is pointwise smoothness
  on the complementary open, without choosing that open's implementation.
- The paper's level n ≥ 1 is Lean's level `n - 1`: `isolatedCurveLevelRing k n`
  is `k[t]/(t^(n+1))`, using the equal ideal `(span {X - C 0})^(n+1)`.
  This uses Mathlib's quotient, polynomial, and ideal-power constructions directly.
  `isolatedCurveLevelReduction` is `Ideal.Quotient.factor` for the canonical ideal
  containment. `isolatedCurveLevelZero` is evaluation at zero, composed with the
  equality of the first ideal power. `isolatedCurveLevelParameter` is the class of X.
- The local algebras are `C : Fin r → ℕ → Type v`, with commutative-ring,
  `IsLocalRing`, coefficient `Algebra`, `Module.Flat`, and `Algebra.EssFiniteType`
  instances separately at every pair of indices. Their universe v is independent
  of the scheme and coefficient universe u; no size restriction on the supplied
  local algebras is imposed.
- The given adjacent quotient isomorphisms are represented by their composite
  quotient maps `c i n : C i (n+1) →+* C i n`, with `hcsurj`, prescribed kernel
  `hcker = span {t^(n+1)}`, and the scalar equation `hcscalar`. A surjective ring
  homomorphism with exactly this kernel is precisely the given isomorphism from
  the indicated quotient, by the first isomorphism theorem. The scalar equation
  says the induced isomorphism is over R_n. This presentation retains the actual
  chosen isomorphisms, rather than retaining only their existence. Longer
  transitions are composites of adjacent maps; their iterated compatibility is
  associativity. There are no additional independent longer transition choices
  in the node's data.
- The prescribed special-fibre local identifications are `eC i : C i 0 ≃+*
  X.presheaf.stalk (p i)`; `heC` is their k-linearity through evaluation at zero.
- The conclusion supplies the actual schemes `Y n` and structure maps `g n`,
  and properness, flatness, and local finite presentation at every level. Properness
  already implies quasi-compactness and quasi-separatedness, so together with local
  finite presentation this is finite presentation, as the dependency defines it.
- The isomorphism `e : X ≅ Y 0` with the displayed structural equation identifies
  the level-one scheme with X over the canonical R_1 ≅ k identification. The
  orientation of the isomorphism is immaterial and gives the node's inverse.
- `j n : Y n ⟶ Y (n+1)` and the `IsPullback` square express the chosen base-change
  isomorphism `Y(n+1) × Spec R_n ≅ Y n`. This is the universal-property encoding
  of that specified isomorphism, and supplies its map to the larger level.
  Each j is a nilpotent closed immersion, since it is the base change of the
  canonical nilpotent quotient immersion. Longer base changes are obtained by
  pasting the adjacent cartesian squares; coherence follows from uniqueness.
- `isolatedCurveSpecialMap Y j e` is defined by recursion as `e.hom` followed by
  the j maps. It is the nilpotent special-fibre map at each level and identifies
  the underlying spaces. It defines the marked point at that level, without any
  arbitrary selection of points or homeomorphisms.
- `h i n` gives the required ring equivalence from the stalk at that marked point
  to `C i n`. Its first equation intertwines the canonical scalar maps
  `(StructureSheaf.toStalk _ _ ≫ (g n).stalkMap _).hom` and `algebraMap`; therefore
  these are R_n-algebra isomorphisms. Ring equivalences between local rings are
  automatically local.
- The second equation is the actual commuting square with `c i n` and the stalk
  map of `j n`, so it specifies reduction compatibility of the chosen local
  isomorphisms. The recursive special-fibre map makes the two point expressions
  definitionally equal; no arbitrary cast or stalk transport is introduced.
- The final equation says `h i 0` is the inverse of the prescribed `eC i` after
  the stalk identification induced by `e`. Thus the chosen special-fibre
  identification and all reductions respect the originally supplied data.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (class and docstring).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` is exactly `Module.Flat` for
  the induced algebra. The statement uses `Module.Flat` for its given algebras;
  its defining signature and tensor-injectivity equivalence in
  `Mathlib.RingTheory.Flat.Basic` were also read.
- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  its projections and universal lift, available with scheme pullbacks through
  `Mathlib.AlgebraicGeometry.Pullbacks`. The equivalent `IsPullback` square is
  used to avoid choosing independent maps for the same reduction.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.

Recorded proof dependencies already stated are imported: properness, Noetherian
finite-type/finite-presentation and separated/quasi-separated facts from Mathlib,
`AlgebraicGeometry.isAffine_of_isThickening` from
`WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme`, and
`AlgebraicGeometry.Flat.of_field` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`. The affine-open stalk
facts are in Mathlib's affine/open-immersion framework imported by these modules.
The four new stage-1 inputs (two-affine cover, affine local lifting, smooth-open
lifting, proper nilpotent reflection) have no recorded Lean module yet, so there
is no module to import for them. They remain named in the proof docstring.

Edge cases: r = 0 imposes no local data; the theorem still constructs the tower.
X empty and r = 0 admits the empty scheme at every level. For r > 0 points rule
out X empty. Dimension zero and the empty dimension −∞ satisfy the bound.
The initial level is exponent one, never exponent zero; the first adjacent step
is exponent two to exponent one. No characteristic or perfectness hypothesis is
imposed. The points are allowed to be smooth; no lci or singularity hypothesis
has been added. The coefficient scalar conditions exclude arbitrary unrelated
ring isomorphisms. The recursion retains the chosen maps, so it also covers
nontrivial prescribed automorphisms of local deformation data.

Searches actually run (recorded by msearch in searches.jsonl):

- LeanFinder: `Compatible formal deformations of isolated curve singularities
  lift to proper flat schemes over k[t]/t^n`: eight hits on smoothness and flatness,
  no formal local-to-global theorem.
- LeanSearch: `Compatible infinitesimal deformations of local rings at isolated
  points lift to formal deformations of a proper curve`: eight formally smooth
  ring lifting hits, no same statement.
- Loogle: `Ideal.Quotient, Polynomial.X, IsLocalRing, Scheme.Hom.stalkMap`:
  no results, unknown identifier `Ideal.Quotient`; this was not a valid exact-name
  query. Follow-up `"stalk", "algebra"` found the canonical
  `StructureSheaf.toStalk` and its stalk algebra/localization declarations,
  which are reused.
- msearch grep `Truncated|deformation|Deformation` in Mathlib AlgebraicGeometry:
  zero hits. Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for deformation
  and truncated-polynomial names found deformation-to-normal-cone and power-series
  material, not this statement or a compatible isolated-curve formal system.
- Direct node-id search in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json`: no match. Direct rg for every proposed helper
  prefix `isolatedCurveLevel` and scalar-to-stalk name in both Lean libraries:
  no collision. DAG search found sibling smoothing/algebraization statements,
  no duplicate definition of this coefficient tower. `blueprint_refs.py search
  'truncated polynomial'` found zero blueprint units; ancestor returned null.

Validation: scompile.py compiled the module both as a sandbox probe and at its
recorded library path, cleanly. The first compile requested noncomputable markers
for three helpers; these were added and both compiles passed. All binders and
universes are explicit, with `set_option autoImplicit false`. No diagnostic command
is retained. There is no statement dispute or correction.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
