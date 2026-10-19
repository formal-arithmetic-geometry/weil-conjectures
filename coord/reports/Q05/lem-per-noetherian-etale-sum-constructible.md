## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianEtaleSumConstructible` states
`AlgebraicGeometry.Scheme.exists_noetherian_etale_sum_constructible`, with `sorry` as its
entire proof. It adds no definitions or assumptions to the node. Its conclusion expands
constructibility directly using the node's recorded finite locally closed stratification,
rather than using the stronger upstream constructibility predicate that also requires
constructible subsets. The node explicitly gives its own constructibility criterion.

Hypotheses and clauses, checked against the node and Stacks 03S8(3),
`etale-cohomology.tex`, lines 12185--12212:

- The schemes `X` and `U` are `{X U : Scheme.{u}}`.
- Quasi-compactness is `[CompactSpace X]` and `[CompactSpace U]`; quasi-separatedness is
  `[QuasiSeparatedSpace X]` and `[QuasiSeparatedSpace U]`.
- The given morphism is `(j : U ⟶ X)` with `[Etale j]`.
- The commutative Noetherian ring is `(R : Type (u + 1)) [CommRing R]
  [IsNoetherianRing R]`.
- The finitely generated coefficient module is `(M : ModuleCat.{u + 1} R)
  [Module.Finite R M]`. Bundling supplies its additive group and scalar action.
- The small etale sites are the arguments `U.smallEtaleTopology` and the sites used by
  `Etale.etaleLowerShriek` and `Etale.upperStar`. The coefficient category `ModuleCat R`
  is the project's established constant-ring-module encoding on these sites. Its objects
  and arrows are modules and linear maps; no new ring or module-sheaf category is defined.
- The constant module sheaf is exactly
  `(constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M`.
- The specified sheafified sum-extension is precisely the recorded
  `Etale.etaleLowerShriek (ModuleCat.{u + 1} R) j inferInstance` applied to that sheaf.
- The finite partition into locally closed subschemes is
  `∃ S : FiniteLocallyClosedStratification X`. Its fields give `Fin S.n`, locally closed
  subsets, disjointness, covering, schemes, immersion maps and their images.
- The inverse-image restriction to each stratum is the application of
  `Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)`.
- Locally constant with finitely generated module values is
  `IsFiniteLocallyConstantSheaf` on every such restriction (`∀ i : Fin S.n`). This is the
  etale ModuleCat presentation explicitly exposed by the recorded dependency module:
  local constancy plus finitely generated geometric stalks. The values may vary between
  trivializing cover members; no constant rank or connectedness assumption is added.
- There is no `Finite R` or `Finite M` binder. The coefficient universe is the established
  `u+1` convention for the small etale site of `Scheme.{u}`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (ideals finitely generated).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the recorded
  general ringed-site module interface (imported; the constant-ring ModuleCat encoding
  follows the constructible-module dependency's existing etale specialization).
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` and its exposed etale interface
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf` from
  `WeilConjectures.ConstructibleSheaf.Defs`. The recorded note explicitly permits that
  interface for the different object and morphism universes of the small etale site.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- The scheme-conventions node fixes no separate declaration; the listed scheme properties
  use the recorded Mathlib predicates.

The proof-dependency modules already stated are imported without `public`:
`Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`,
`WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale`. The constant-pullback
isomorphism is in the already public imported `WeilConjectures.ConstructibleSheaf.Defs`.
`lem-per-finite-etale-pushforward-finite-type` has no Lean record, so no module can yet be
imported for that proof dependency. It is not needed to type this statement. Its role in
the future proof is given in the theorem docstring.

Edge cases checked: `X` empty admits `S.n = 0` with a vacuous restriction condition;
`U` empty gives the zero sheaf; the zero coefficient module is permitted; no nonempty
stratum, nonzero ring, connectedness, separation, finite ring, or finite set of module
elements is required. In particular `R = Z` and `M = Z` satisfy the intended coefficient
hypotheses despite their infinite underlying sets. A constant locally finite-type sheaf
has finitely generated stalks, and conversely its locally constant values are identified
with stalks at geometric points; thus the exposed etale predicate adds no condition.

Searches for an existing statement (2026-10-18 UTC):

- `msearch.py`, LeanFinder: "Etale sum extension of a constant finitely generated module
  over a Noetherian ring is constructible" returned eight declarations about etale
  algebras and finite presentation, with no sheaf-constructibility match.
- `msearch.py`, Loogle: `AlgebraicGeometry.Etale.etaleLowerShriek, Module.Finite` returned
  zero hits (the upstream shriek identifier is not in its Mathlib index).
- `msearch.py`, grep: `etaleLowerShriek|IsConstructibleSheaf` in Mathlib/AlgebraicGeometry
  returned zero hits.
- `msearch.py`, LeanSearch: "extension by zero of constant finite type module is
  constructible" returned eight unrelated extension-by-zero and finitely supported
  function declarations.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the item id,
  `noetherian.*etale`, `etale.*[Cc]onstructible`, and the proposed declaration name:
  no exact theorem found. The item id has no source occurrence. Reading upstream
  `ConstructibleSheaf/FreeLifting.lean:484` found `isConstructibleSheaf_freeYoneda`, but
  that requires finite coefficients, a Noetherian underlying scheme and affine etale
  source, and concerns the free rank-one sheaf. It is not this statement.
- `dag/lean_names_upstream.json` has no binding for this node or proposed declaration.

Compilation initially diagnosed that the live local finite-type dependency imports the
upstream etale predicate privately. Adding a direct public import of
`WeilConjectures.ConstructibleSheaf.Defs` exposes that same recorded declaration without
changing its interface.

No statement correction, new node, dependency replacement or STATEMENT-DISPUTED flag.
The existing Q99 review is the stage-1 split review, not a Lean statement record; the
item's shared node has no `lean` or `reviewed_lean` record.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
