## Worker report

The module `Sheaf.AlgebraicGeometry.AffineOpenStrictLocalCohomology` states
`AlgebraicGeometry.Etale.isZero_cohomology_affineOpen_of_strictlyHenselian`.
Its sole proof is `sorry`; it defines no new notion. The node is unchanged except
for `lean`. No statement correction, new node, or dependency repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme is `X : Scheme.{u}`. A strictly local scheme is affine with a strictly
  henselian global ring: `[IsAffine X]` and
  `[IsStrictlyHenselianLocalRing Γ(X, ⊤)]`. The latter extends the existing
  `HenselianLocalRing` and asserts separable closedness of its residue field.
  This keeps `X` itself in the statement, with its canonical `X.isoSpec` available;
  it does not replace the given scheme by a chosen strict henselization or add a
  property beyond strict locality.
- Noetherianity is `[IsNoetherianRing Γ(X, ⊤)]`, equivalent to Noetherianity of
  this affine scheme. Excellence is `hX : IsExcellent Γ(X, ⊤)`, the recorded
  excellent-ring predicate, on the same affine global ring.
- The coefficient prime and exponent are `ℓ n : ℕ`, `hℓ : ℓ.Prime`, and
  `hn : 1 ≤ n`. The coefficient ring is exactly `ULift.{u + 1} (ZMod (ℓ ^ n))`.
  `ULift` changes only the universe; its standard ring structure transports that
  of Z/ℓ^n. It does not restrict module ranks, stalk sizes within the stated
  universe, or constructibility.
- `d : ℕ` and `hd : ringKrullDim Γ(X, ⊤) = (d : WithBot ℕ∞)` assert finite,
  nonnegative Krull dimension equal to `d`. The affine spectrum identification
  identifies this with the dimension of `X`; it is not a dimension bound on `V`.
- `hunit : IsUnit (ℓ : Γ(X, ⊤))` says precisely that ℓ is invertible on `X`.
- `{V : Scheme.{u}} [IsAffine V] (j : V ⟶ X) [IsOpenImmersion j]` gives the
  arbitrary affine open subscheme with its inclusion. No nonemptiness or
  principal-open hypothesis is imposed.
- `M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1}
  (ULift.{u + 1} (ZMod (ℓ ^ n))))` is an arbitrary module-valued sheaf on the
  ordinary small etale site. This is the module-valued constant-coefficient
  encoding explicitly authorized by `def-weil-pbc-etale-sheaves`; no
  constructibility, finite generation, or local constancy hypothesis appears.
- `q : ℕ` and `hq : d < q` express exactly the degree range.
- `sheafCompose ... (forget₂ ... AddCommGrpCat.{u + 1})` forgets coefficients
  before taking cohomology. `DerivedCategory.singleFunctor _ 0` places that
  abelian sheaf in degree zero. `Etale.cohomology AddCommGrpCat.{u + 1} V (q : ℤ)`
  is the recorded right-derived global-sections cohomology, and `IsZero` of its
  value asserts `H^q(V,M)=0` as an abelian group. It is not merely vanishing of
  sections or a statement about an arbitrarily chosen cohomology functor.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec` (the affine interpretation); the affine interface is
  `AlgebraicGeometry.IsAffine` and `Scheme.isoSpec` in
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, using `IsQuasiExcellent` and
  `IsUniversallyCatenary`, read in full.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`, with its full signature and residue-field field.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the node's mixed record uses
  Mathlib `CategoryTheory.Sheaf` for the abelian and module sheaf categories.
  Read its current source with `scompile.py --source`, since that upstream module
  is absent from the older source checkout. No new sheaf category was defined.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`, whose
  docstrings and definitions identify the desired derived functor.

Proof-only imports preserve the stated plan: affine qcqs instances from
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` and `AffineScheme`;
`Scheme.exists_filtered_colimit_constructible` from
`Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit`;
`Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject` from
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`;
and `Scheme.nonempty_etaleModuleCohomology_forgetIso` from
`Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`.
The constructible affine-open child has no recorded declaration yet, so its
future module cannot be imported; its node and role are named in the proof
docstring. It is a proof prerequisite, not a missing notion needed to type this
statement.

Source check: read ILO Expose XV, printed pp. 219–220 (PDF pp. 225–226), including
1.1.1, Theorem 1.1.2 and Corollaries 1.2.2 and 1.2.4. Corollary 1.2.2 is the
constructible assertion; for the affine open immersion the closure-dimension
function is bounded by `d`. Corollary 1.2.4 alone is only the constant-sheaf
case. The docstring follows all four node proof steps, using constructible
approximation (Stacks 03SA), filtered cohomology colimits (03Q5) and the
module/abelian comparison (03FD) for arbitrary `M`.

Edge cases checked: `d=0` gives vanishing for all positive degrees; `q=0` never
satisfies `d<q`, as required; `n=1` is included, while `n=0` is explicitly
excluded by the source statement. The empty affine open is allowed, and all of
its cohomology vanishes. The identity open is allowed. A generic-point open of
an excellent strictly henselian DVR is allowed with `d=1`, without claiming
vanishing of its potentially nonzero degree-one cohomology. Arbitrary
nonconstructible sheaves remain included. A zero ring cannot satisfy strict
henselian locality, consistently with a local scheme having a closed point.
All universes are explicitly bound; the coefficient and abelian categories are
in the established `u+1` size convention for `Scheme.{u}`.

Searches for an existing statement (actual `msearch.py` results also retained
in sandbox `searches.jsonl`):

- LeanFinder: “Affine open of an excellent strictly henselian local scheme of
  dimension d has etale cohomology zero above d for arbitrary finite torsion
  module sheaves”. Eight results concern algebraic etale loci, formal etaleness
  and standard smoothness. Their returned signatures do not state the bound.
- Loogle: `"cohomology", "IsOpenImmersion"`. Zero hits.
- LeanSearch: “etale cohomology of affine open excellent strictly henselian local
  scheme vanishes above its Krull dimension”. Eight results concern locally
  Noetherian components, structure-sheaf localization, Artinian dimension and
  algebraic etaleness. None states the requested vanishing.
- Mathlib grep: `StrictlyHenselian|Lefschetz|etale.*cohomology` in
  `AlgebraicGeometry`. Zero hits.
- Source-project and side-project `rg`: item id, affine-open/cohomology and
  strict-local/cohomology patterns. No existing statement of this item found.
  Read `Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds`: it cites this
  item in its proof and states different punctured/support/generic-point bounds;
  importing it would create the wrong dependency direction. Ordinary affine
  localization and strict-local germ comparisons also do not state this bound.
- Exact new full declaration name was searched in Mathlib, the source project
  and `lean/Sheaf`; no collision. `dag/lean_names_upstream.json` and the required
  upstream item-id grep give no attachment.

Validation: `scompile.py Q20 lem-per-affine-open-strict-local-cd` compiled both
the isolated sandbox and the library module separately, each in approximately
five seconds, with no errors or warnings. No theorem was proved. No statement
is disputed.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
