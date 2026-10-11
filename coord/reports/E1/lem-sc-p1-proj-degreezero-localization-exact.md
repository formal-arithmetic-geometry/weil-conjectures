## Worker report

The delivery states `LocalizedModule.proj_degreeZero_localization_shortExact` in
`Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`. Its only proof is `sorry`.
The companion module supplies an actual definition of the equal-degree fraction subset.
No statement correction, disputed mathematics, or dependency replacement is required.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the ring is literally
  `MvPolynomial (Fin 2) k`, with its total-degree `homogeneousSubmodule (Fin 2) k`.
  Thus neither another ring nor an arbitrary standard graded algebra is substituted.
- The three modules are `M₀`, `M₁`, `M₂`, with `AddCommGroup` and `Module` structures.
  Their integer-indexed additive subgroups `𝓜₀`, `𝓜₁`, `𝓜₂`, together with
  `DirectSum.Decomposition`, express their direct-sum Z-gradings. The three `hsmul`
  hypotheses state `S_n M_z ⊆ M_(n+z)` for every natural ring degree and integer module
  degree. There is no finite generation or boundedness hypothesis.
- The maps `f`, `g` are linear over the specified polynomial ring; `hf`, `hg` say that
  each preserves every integer degree. `hinj`, `hex`, `hsurj` express the three parts
  of the original short exact sequence using `Function.Injective`, `Function.Exact`,
  and `Function.Surjective`.
- `p` is an ideal of that ring, `[p.IsPrime]` makes it prime, `hp` makes it homogeneous,
  and `hproj` says the irrelevant ideal is not contained in `p`.
- `T := homogeneousSubmonoid 𝒜 ⊓ p.primeCompl` is exactly all homogeneous elements
  outside the prime, including nonzero constants. `H := HomogeneousLocalization 𝒜 T`
  is Mathlib's ring of equal-degree homogeneous fractions, the node's `S_(p)`.
- The three explicit `Module.compHom` structures restrict the ordinary localized
  module action along `algebraMap H (Localization T)`. They introduce no assumption
  and implement the action of `S_(p)` through its inclusion into `T⁻¹S`.
- `degreeZeroFractions` says that a localized element equals `mk y h` for some degree
  `n`, numerator in `𝓜ᵢ n`, and denominator in `𝒜 n`. Here `n : ℕ`, embedded in ℤ for
  module degrees: a nonzero denominator has nonnegative degree, so this includes all
  equal-degree fractions of the node and imposes no lower bound on the modules.
- The existential submodules `N₀`, `N₁`, `N₂` have carriers exactly `Z₀`, `Z₁`, `Z₂`.
  This packages the displayed subsets with their inherited module operations rather
  than assuming their closure or choosing arbitrary substitute localized modules.
  Submodule structure is uniquely determined by its carrier and the ambient action.
- The existential `H`-linear maps `f₀`, `g₀` agree at every element with
  `IsLocalizedModule.map T (mkLinearMap T _) (mkLinearMap T _) f` and the analogous
  map for `g`. `IsLocalizedModule.map_mk'` and `map_LocalizedModules` identify these
  precisely with `y/h ↦ f(y)/h`, `y/h ↦ g(y)/h`. Inclusion into the ambient modules is
  injective, so these equations uniquely specify the maps.
- The conclusion `Function.Injective f₀ ∧ Function.Exact f₀ g₀ ∧
  Function.Surjective g₀` is exactly short exactness over `H`, including both end
  clauses. Existential packaging of uniquely specified inherited structures changes
  neither the strength nor the objects of this conclusion.
- Fraction equality is Mathlib's `LocalizedModule.mk_eq`: some `t : T` satisfies
  `t • h' • y = t • h • y'`. In additive groups this is exactly the node's
  `t • (h' • y - h • y') = 0` relation, not a new quotient.

Dependency declarations read and used:

- `def-sc-p1-standard` records `AlgebraicGeometry.ProjectiveLine.TwistData` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`, lines 202–224.
  Its full definition describes generating sections and gluing of a twist. This
  lemma uses only the node's identification of the homogeneous coordinate ring,
  which is directly Mathlib's `MvPolynomial (Fin 2) k` and its canonical grading;
  it has no twisted sheaf or affine chart as an object. Consequently no twist data
  is introduced and its module is not imported merely for an unused declaration.
  The dependency is kept unchanged; its twist declaration is not redefined.
- `def-pc-standard-graded-algebra` records `GradedAlgebra.IsStandard` in
  `WeilConjectures.RingTheory.GradedAlgebra.Standard`, lines 86–95: finite generation
  in degree one and generation of the algebra. The present lemma fixes the polynomial
  ring rather than quantifying over standard algebras, so there is no new standardness
  hypothesis or private copy of this class. Its homogeneous ideals and irrelevant
  ideal are Mathlib's `Ideal.IsHomogeneous` and `HomogeneousIdeal.irrelevant`; its
  degree-zero ring is Mathlib's `HomogeneousLocalization`, all imported and used.
- The new dependency `def-sc-degree-zero-module-fractions` records
  `LocalizedModule.degreeZeroFractions` in `Sheaf.Algebra.Module.DegreeZeroFractions`.
  It uses the Mathlib leaf `def-weil-pbc-module-localization`, whose match is
  `LocalizedModule` in `Mathlib.Algebra.Module.LocalizedModule.Basic`; its quotient,
  `mk`, and `mk_eq` were read in full. No private ordinary localization is defined.
- `DirectSum.Decomposition` and the graded-module description were read in
  `Mathlib.Algebra.Module.GradedModule`; homogeneous polynomial submodules and the
  locally installed `MvPolynomial.gradedAlgebra` were read in
  `Mathlib.RingTheory.MvPolynomial.Homogeneous`.

Edge cases: zero modules and the zero sequence are included; identity sequences are
included; no module finiteness or restriction on negative components appears. Degree-zero
constant denominators are allowed. Every characteristic is allowed by `[Field k]`.
The primes `(0)`, `(x₀)`, and `(x₁)` are allowed, while the irrelevant prime `(x₀,x₁)` is
excluded exactly by `hproj`. Since `p` is prime, zero is never a denominator. Each module
has its own universe; there is no same-universe or finite-dimensional restriction.

Searches (all performed before defining the subset):

- msearch leanfinder, `degree zero localization of graded modules preserves short exact
  sequences`: eight hits, including ordinary `LocalizedModule.map_exact` and
  `IsLocalizedModule.map_exact`, but no degree-zero restriction theorem.
- msearch loogle, `HomogeneousLocalization, LocalizedModule.map`: zero hits.
- msearch grep, `HomogeneousLocalization|degree.?zero`, `Algebra/Module`: zero hits.
- msearch leansearch, `degree zero submodule homogeneous localization graded module`:
  service unavailable, HTTP Internal Server Error; no evidence inferred from failure.
- msearch leanfinder, `graded module homogeneous fractions numerator denominator same
  degree`: eight ring-fraction hits (`HomogeneousLocalization.NumDenSameDeg` and its
  fields, numerator/denominator membership), no module-fraction definition.
- msearch grep, `graded.*localization|degree.?zero.*localization|degreeZeroFractions`:
  five hits, in ProjectiveSpectrum files and HomogeneousLocalization, all ring APIs.
- rg of the source `WeilConjectures`, the project `lean/Sheaf`, and Mathlib: no declaration
  matching the item or the new definition, including both proposed full names. Source
  matches for homogeneous localization are ring dehomogenization and projective charts.
  Search for the exact item id in `WeilConjectures` returned no match.
- DAG search (`rg -l` for homogeneous localization / degree-zero localization) and
  `tools/blueprint_refs.py search 'degree-zero localization'` (zero blueprint matches)
  found only existing ring-away and module-away notions, not arbitrary-submonoid module
  fractions. In particular `def-nagata-homogeneous-localization-degree-zero` is the
  ring-away definition; `def-weil-pbc-proj-twisting-sheaf` describes module fractions
  away from one positive-degree element and the sheaf, not localization at a prime.

Source checked online because the local literature checkout is absent:
[Stacks 00JL](https://stacks.math.columbia.edu/tag/00JL) specifies Z-graded modules,
nonnegative ring degrees, and degree-preserving maps;
[Stacks 01M7](https://stacks.math.columbia.edu/tag/01M7), clauses (4),(5) and its exactness
paragraph, gives the ring/module prime localizations and exactness. The docstring preserves
all three proof steps of the node. The theorem remains a statement with `sorry`.

Validation: the two modules compiled together on the server with scompile.py, exit 0,
no warnings (2.0 seconds). Every variable and universe is explicitly bound.

## New nodes

`def-sc-degree-zero-module-fractions` names the subset of ordinary module localization
consisting of fractions with numerators and denominators in corresponding degree subsets.
Its data is the displayed existential set predicate, never `sorry`. It is generic in the
index set; in this delivery the index is ℕ and the numerator subgroups are the nonnegative
components of the full Z-grading. It cites `def-weil-pbc-module-localization` and reuses that
Mathlib leaf. Source: Stacks Algebra Section 00JM, `M_(p)`, used in Constructions 01M7 (5).
The three search kinds and DAG/project scans above show that the available declarations
cover the ring version or localization away from one element, not this module subset.
The new node's searches record the actual service outputs, including unavailable LeanSearch.

## Second reading by E1

I independently read the node statement, its source place, the dependency records, and both Lean
modules. The correspondence is as follows.

- The field binder is `{k : Type u} [Field k]`; the polynomial ring is exactly
  `MvPolynomial (Fin 2) k`, with the canonical total-degree grading
  `homogeneousSubmodule (Fin 2) k`.
- The three graded modules are `M₀`, `M₁`, and `M₂`, each with `AddCommGroup` and the indicated
  polynomial-module instance. Their `ℤ` components are the explicit `𝓜₀`, `𝓜₁`, `𝓜₂` with
  `DirectSum.Decomposition`; `hsmul₀`, `hsmul₁`, and `hsmul₂` express the required degree shift
  for every natural polynomial degree and integer module degree. No finiteness or boundedness
  assumption is present.
- `f` and `g` are the two polynomial-linear maps; `hf` and `hg` preserve every integer degree,
  while `hinj`, `hex`, and `hsurj` are exactly injectivity, exactness, and surjectivity.
- `p : Ideal (MvPolynomial (Fin 2) k)` has `[p.IsPrime]`; `hp` makes it homogeneous and `hproj`
  excludes containment of the irrelevant ideal.
- In the nested `let`s, `𝒜` is the homogeneous submonoid grading, `T` is precisely the intersection
  of homogeneous elements with `p.primeCompl`, and `H` is `HomogeneousLocalization 𝒜 T`.
  The three `Module.compHom` instances are the induced H-actions through
  `algebraMap H (Localization T)`.
- `Z₀`, `Z₁`, and `Z₂` are exactly `degreeZeroFractions` with numerator components `𝓜ᵢ n` and
  denominator components `𝒜 n`; this is the node's equal-degree fraction subset, including the
  ordinary localization equivalence relation supplied by `LocalizedModule.mk`.
- The conclusion existentially supplies submodules whose carriers are exactly `Z₀`, `Z₁`, `Z₂`,
  then H-linear maps whose ambient values are the ordinary localized maps on every element, and
  concludes `Function.Injective f₀ ∧ Function.Exact f₀ g₀ ∧ Function.Surjective g₀` in the same
  order as the node.

The source assumptions (field, homogeneous prime, non-containment of the irrelevant ideal,
Z-graded modules, and degree-preserving maps) are all represented, with no extra hypotheses or
restricted universe. Zero modules and zero/identity sequences are admitted; degree-zero constants
are allowed as denominators; all characteristics and the primes `(0)`, `(x₀)`, and `(x₁)` are
covered, while the irrelevant prime is excluded. The arbitrary universes `u`, `v₀`, `v₁`, `v₂`
leave no case out.

I searched Mathlib and the project/source with LeanFinder/Loogle and grep for degree-zero module
localization, homogeneous module fractions, and the exact theorem name. Only ordinary
`LocalizedModule` APIs and ring homogeneous-localization APIs exist; no duplicate statement or
definition was found. The LeanSearch attempt was unavailable, as recorded in the worker report.
The dependency declarations were opened: `AlgebraicGeometry.ProjectiveLine.TwistData` records
the standard affine-cover twist notion for `def-sc-p1-standard`, `GradedAlgebra.IsStandard` is the
standard grading notion, and Mathlib's `LocalizedModule` supplies `mk`, `mk_eq`, and localization
maps. The new `LocalizedModule.degreeZeroFractions` definition is data-free and has no hollow
proof. No mismatch was found, so no source, node, or Lean text required repair.

Both delivery modules compile together with `scompile.py` (exit code 0; no warnings beyond the
allowed `sorry` theorem proof), and the node's `lean.statement` is verbatim the theorem signature.
