## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToEllUniformizationStandardForm` states
`AlgebraicGeometry.primeToEll_uniformization_standard_form`, with its whole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The source is ILO,
Travaux de Gabber, IX Theorem 1.1, II Theorem 3.2.3, and the finite commutative diagrams of
XIII 3.2.1 (printed p. 199; PDF p. 205), which I read from the local PDF. The theorem's
proof docstring contains all four proof steps of the node. Neither proof prerequisite
currently has a recorded Lean module, so there is no proof-only import to add for them:
`lem-per-gabber-prime-to-ell-regular-cover` and
`lem-per-alteration-cover-standard-refinement`.

Hypotheses, in order:

- `X : Scheme.{u}` is the input scheme; `[IsIntegral X]` includes nonemptiness, reducedness
  and irreducibility; `[IsNoetherian X]` is the scheme's finite-affine-cover Noetherianity.
  Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top` verifies the finite-cover interpretation.
- `hX : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V.1)` says every affine coordinate ring
  is quasi-excellent, using the dependency's actual quasi-excellent predicate rather than
  its stronger excellent predicate.
- `ell : ℕ` and `hell : ell.Prime` express the prime; `hinv : ∀ x : X,
  IsUnit (ell : X.presheaf.stalk x)` expresses invertibility on all local rings of `X`.
- `U : X.Opens` is the open subscheme with its canonical open immersion `U.ι`, and
  `hU : Dense (U : Set X)` is its density. No separate scheme or arbitrary immersion
  replaces that open subscheme.

Conclusion, clause by clause:

- `∃ (X' : Scheme.{u}) (p : X' ⟶ X), ... IsIntegral X' ∧ IsProper p` gives the integral
  modification and proper map.
- `∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (p ∣_ V)` says that the map from the *entire*
  inverse image of a dense open onto that open is an isomorphism, exactly the node's
  isomorphism over a dense open.
- `n : ℕ`, `E W : Fin n → Scheme.{u}`, `e : ∀ i, E i ⟶ X'`, and `a : ∀ i, W i ⟶ E i`
  provide the finite indexed family and its two layers of schemes and maps.
- `∀ i, IsSeparated (e i) ∧ Etale (e i) ∧ LocallyOfFiniteType (e i) ∧ QuasiCompact (e i)`
  gives separated étale morphisms of finite type.
- `r : Fin n → ℕ` and `∀ i, (a i).IsFiniteLocallyFreeOfDegree (r i) ∧ Surjective (a i) ∧
  0 < r i ∧ Nat.Coprime (r i) ell` give precisely finite locally free surjections with
  specified positive constant prime-to-ell ranks. The upstream degree class includes the
  finite, flat and locally finitely presented conditions and the fibre-dimension equality
  at every point of `E i`; it is not a degree at just a generic point.
- `m : ℕ`, `Y : Fin m → Scheme.{u}`, `q : ∀ b, Y b ⟶ X` give the finite family of schemes
  with their structure maps to `X`. The clause `∀ b, IsRegularScheme (Y b) ∧
  IsNoetherian (Y b) ∧ LocallyOfFiniteType (q b) ∧ QuasiCompact (q b)` includes regularity,
  Noetherianity and finite type over `X`.
- `LocallyOfFiniteType p ∧ QuasiCompact p`, the corresponding conjunctions for `e i ≫ p`
  and `a i ≫ e i ≫ p`, and the preceding conjunction for `q b` express all four required
  finite-type-over-`X` assertions. Finite type means locally of finite type and quasi-compact.
- `∀ x' : X', ∃ (i : Fin n) (z : E i), e i z = x' ∧ IsIso ((e i).residueFieldMap z)`
  is complete decomposition: the induced map has source the residue field at `e i z`,
  identified with `κ(x')` by the preceding equality. This demands the *induced* field map
  be an isomorphism, rather than merely an abstract isomorphism of fields.
- `h : ∀ i, W i ⟶ ∐ Y` gives maps to the actual scheme coproduct. `Sigma.desc q` is its
  canonical structure map to `X`. `∀ i, h i ≫ Sigma.desc q = a i ≫ e i ≫ p` makes these
  maps `X`-morphisms. The theorem does not require the `W i` to be connected or to factor
  through just one summand, which the item's statement does not demand.
- `∀ b, ∃ H : (Y b).IdealSheafData, IsStrictNormalCrossingsBoundary H ∧
  (q b) ⁻¹' (U : Set X) = (H.support : Set (Y b))ᶜ` gives the strict normal crossings
  boundary on each `Y b` and identifies the inverse-image open subscheme with its open
  complement. Equality of open supports identifies these canonical open subschemes, so
  there is no change of the underlying schemes or of their structure sheaves.

Dependency declarations read and used (including their source docstrings/signatures):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity uses
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (the recorded module also supplies
  `IsExcellent`; the quasi-excellent component is the one the statement calls for).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`; the open
  subscheme is the existing `Scheme.Opens` construction and its canonical map.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`, on `Scheme.IdealSheafData`.
  Its published source was also checked with `scompile.py --source`.
- `def-weil-pbc-scheme-conventions` is a convention-only node with no declaration. Its
  proper and separated meanings are the existing `IsProper` and `IsSeparated` of
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `...Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, included by
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`; the integral-morphism clause is unused here.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, likewise included
  by that exact finite-locally-free degree predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, via the
  boundary module; this includes local Noetherianity and stalkwise regularity.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` and its parent
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, exactly the recorded node's classes.
  I checked both the read-only source and the current published source through `scompile.py`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from `...QuasiCompact`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Limits`: the scheme coproduct and its `Sigma.desc` structure map.

Edge cases checked before writing:

- Integral includes nonempty, so the empty base is excluded by the node itself. An empty
  open cannot be dense in this base. `U = X` is allowed and calls for the empty boundary;
  the recorded strict-normal-crossings predicate explicitly permits it.
- The finite families use `Fin n` and `Fin m` with no additional positivity hypothesis on
  their cardinalities. Complete decomposition over nonempty `X'` forces an actual member
  of `Fin n`; the `h` maps and positive ranks likewise prevent spurious empty target data.
  Individual `E i` and `W i` are not assumed integral or nonempty: the item does not demand it.
- `0 < r i` excludes degree zero, and `Nat.Coprime (r i) ell` includes degree one and excludes
  ranks divisible by the prime. No characteristic restriction beyond invertibility of `ell`
  has been added.
- The dense open for `p` is an independent existential `V`, not required to equal the given
  `U`. The full restriction `p ∣_ V` prevents a weaker isomorphism on only part of its source.
- The universe `u` is explicit and arbitrary. Finite index sets can always be enumerated by
  `Fin n` independently of `u`; no size or characteristic case is lost.

Searches for an existing statement (performed in this turn):

- `msearch.py ... leanfinder "Prime to ell uniformization proper modification completely
  decomposed etale cover finite locally free regular strict normal crossings"`: OK, eight
  hits, including `AlgebraicGeometry.IsEtale.of_comp`, `Scheme.Hom.normalizationOpenCover`,
  `Scheme.Etale`, `IsEtale`, `Scheme.Hom.toNormalization`, and the ring-theoretic
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`. These concern
  étale morphisms, normalization or polynomial factorization; none states this uniformization.
- `msearch.py ... loogle "IsProper, IsFiniteLocallyFreeOfDegree, IsRegularScheme"`: zero hits;
  service note `loogle: unknown identifier 'IsProper'`. Not counted as a successful match.
- `msearch.py ... grep "uniformi[sz]ation|alteration|[Cc]ompletely[Dd]ecomposed|
  [Nn]ormal[Cc]rossing" AlgebraicGeometry`: OK, zero Mathlib hits.
- `rg -n` in the upstream `WeilConjectures` source and shared `lean/Sheaf`, for the item id,
  prime-to-ell uniformization and completely-decomposed names: no declaration of this
  statement. The item id occurs in the proof docstring of the downstream
  `GabberOpenImmersionSheafFiniteness`; unrelated valuation local-uniformization modules
  concern strictly semistable curves, not the present theorem.
- `rg` in `dag/lean_names_upstream.json` for `uniformization_standard_form` and
  `primeToEll_uniformization`: no matching declaration.

No statement fault or dispute was found. No new nodes or dependency repairs were needed.

Validation: `scompile.py Q16 lem-per-prime-to-ell-uniformization-standard-form <module>`
compiled both the sandbox and intended library module cleanly (2.0 s each, no messages).

## Second reading by Q16

This is a separate self-review pass by the dispatched worker, not a claim of an independent
second agent; the brief prohibits starting agents and reserves independent review for the
maintainer. I reopened the node and the full theorem and matched all four hypotheses and
all conclusion clauses as listed above. I checked especially the distinction between a
finite *family* of étale maps and finite étale morphisms: the actual Lean uses only `Etale`
with separatedness and finite type, as required. I clarified that wording in the docstring.
I checked that no integrality or Noetherianity of `E i` or `W i` was added from the stronger
proof prerequisite, that the dense-open restriction uses the full preimage, and that the
coproduct maps have their commutativity equations. The boundary complement uses the exact
recorded predicate. No signature correction was needed.
