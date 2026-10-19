## Worker report

This repair updates `Sheaf.SixFunctors.FrobeniusPointTransportNatural`.  The main
statement remains the node statement, with its finite and integral models made
explicit.  Three helper theorem declarations record the canonical object equalities
needed to write the rational and common-stage qbar squares:
`frobeniusPointRationalPullbackEq`, `frobeniusPointQbarPullbackEq`, and
`frobeniusPointQbarFibreObjEq`.  They are obtained from the object clauses of
`rationalDerivedPullback_existsUnique`, `commonStageDerivedPullback_existsUnique`,
and `pointQbarFibre_existsUnique`; their proofs are postponed at stage 2.

The theorem binds `D`, `l`, the prime instance, `hl`, `E`, its field, algebra,
and finite-dimensional instances, and then states the following clauses.

* The finite sigma component is linear on every complex degree and every
  coefficient element.  The next conjunct gives chain-map naturality for every
  finite complex morphism.  A further conjunct applies `DerivedCategory.Q.map`
  to the same equation, making the derived-level sigma naturality explicit.
* The completed-integral sigma component is linear and natural on chain maps;
  the following `DerivedCategory.Q.map` conjunct is its derived-level form.
* Finite constructible naturality is the square with
  `frobeniusPointFinitePullback`; integral constructible naturality is the
  analogous square with `frobeniusPointIntegralPullback`.
* Rational naturality uses the canonical functor
  `rationalDerivedPullback l E (frobeniusPointIso D).hom`.  Its map is
  transported to the point-transport pullback objects on both sides by
  `eqToHom (frobeniusPointRationalPullbackEq ...)`; there is no existentially
  chosen map.
* Qbar naturality quantifies `u : A ⟶ B` in
  `generalAlgebraicallyClosedConstructibleCategory`, and uses
  `pointQbarFibre.map u` and
  `commonStageDerivedPullback ... .map u`.  The two fibre-functor object
  equalities and the common-stage/pullback object equalities are inserted by
  canonical `eqToHom` maps, so all four sides of the square have the displayed
  source and target.
* The derived sigma definitions are used in additional naturality conjuncts for every derived morphism.
* The final clause quantifies a finite coefficient extension
  `ι : E' →ₐ[ℚ_[l]] L` and states the scalar-extended transport equation after
  conjugation by `pointRationalFibreScalarIso`, the normalized
  `rationalPullbackScalarComparison`, and the rational pullback object equalities.
  The fibre comparison is the canonical normalization built from
  `pointRationalSectionsScalarExtensionIso`.

The imported dependency declarations are from
`Sheaf.SixFunctors.FrobeniusPointTransport` (the finite/integral sigma maps,
transport maps, pullback objects, and qbar objects),
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
`Sheaf.Paper.SfIntegralConstructible`, `Sheaf.Paper.SfRationalizationKaroubi`,
and `Sheaf.Paper.DerivedPullbackTensorHom` (the rational and common-stage
pullback functors).  The point-fibre declarations are
`pointFiniteFibre`, `pointIntegralFibre`, `pointRationalFibre`,
`pointQbarFibre`, and `pointQbarFibreObj` from
`Sheaf.Paper.FiniteCoefficientPoint`.

Edge cases checked were `n = 0` (the finite coefficient level is `n + 1`), zero
complexes and zero maps, identity maps, empty constructible objects, repeated
or identity coefficient inclusions, and a further scalar extension.  The
hypothesis `hl : l ≠ D.p` is retained and supplies the residue-field
`Invertible` instance used by both pullback constructions.

Searches made:

* `msearch.py ... leanfinder` for pro-etale Frobenius point-transport
  naturality: no matching declaration.
* `msearch.py ... loogle` for natural transformations, localization, and
  `sheafFiberComapIso`: only generic natural-transformation/site declarations.
* `msearch.py ... grep` and `rg` over `WeilConjectures/` and `lean/Sheaf/` for
  the item id and Frobenius transport: only the recorded transport module and
  its component definitions were found.
* `rg` for `rationalDerivedPullback`, `commonStageDerivedPullback`, and
  qbar scalar-extension declarations located the canonical interfaces in
  `Sheaf.Paper.DerivedPullbackTensorHom` and `FiniteCoefficientPoint`.

No `STATEMENT-DISPUTED` marker or node fault applies.  The theorem proof and the three helper equalities remain `sorry`, as required
for stage 2; the two derived sigma definitions have real data, by reusing the
recorded transport constructions.

## Second reading by NI

I reread the node, its source proof, every recorded dependency, and the repaired
module.  The returned issues are addressed as follows: the rational conjunct
now uses `rationalDerivedPullback` with canonical `eqToHom` object transports;
the qbar conjunct quantifies morphisms of the general algebraically closed
constructible category and uses `pointQbarFibre.map` together with
`commonStageDerivedPullback.map`; the finite and integral sigma equations are
also stated after `DerivedCategory.Q.map`; and the theorem docstring contains
nine numbered proof steps.  The previous second-reading sentence claiming
that these squares were already stated was removed and replaced by this
explicit account of the repaired equations.  The finite/integral conjuncts,
hypotheses, universes, and the `n = 0` case remain unchanged.  The file passes
`scompile.py` with no compiler errors or warnings.


## Repair details

The former heterogeneous scalar-extension equality was replaced by the typed conjugated square: source and target are transported by `pointRationalFibreScalarIso`, the pullback side by `rationalPullbackScalarComparison`, and the rational pullback object equalities. The derived finite and integral sigma components are explicit definitions (`frobeniusPointFiniteSigmaDerived` and `frobeniusPointIntegralSigmaDerived`) and the theorem states naturality for every derived morphism. The theorem proof docstring is a proper module docstring with the source, blueprint identifier, and nine postponed proof steps. The three helper equalities are theorem declarations with `sorry`, rather than proved proposition definitions.

## Maintainer review fix (cc second reader, 2026-10-18)

The two delivered "derived sigma" definitions were literal aliases of the recorded
transports `frobeniusPointTransportFinite` / `frobeniusPointTransportIntegral`. Their
target was `Γ(s, Lg_s^* N)`, i.e. `ι_N = Γ(κ_N) σ_N`, not `σ_N`. So the conjuncts using
them stated naturality of `ι` on the whole derived category. That is not the node's
clause (1) natural transformation `Γ(s,-) → Γ(s, g_s⁻¹(-))` of functors
`D(s_proet, Λ) → D(Λ)`, and it duplicated a recorded notion under a misleading name.

The fix replaces both definitions with the genuine derived `σ`. They keep the same
names, have no `hl` argument, and carry source/blueprint `/--` docstrings. Each one
conjugates the chain-level `frobeniusPointFiniteSigma` / `frobeniusPointIntegralSigma`
of `DerivedCategory.Q.objPreimage N` by the recorded `mapDerivedCategoryFactors`
isomorphisms and `Q.objObjPreimageIso N`. The target is the recorded exact module
inverse image `inverseImageFiniteDerived` / `inverseImageIntegralDerived` of
def-weil-inverse-image-pullback-comparison. The fix states the two derived conjuncts
with `(inverseImageFiniteDerived …).map f` / `(inverseImageIntegralDerived …).map f`,
for every derived morphism `f`. It also moves the nine numbered proof steps from a
detached `/-!` block into the theorem's `/--` docstring. Every other conjunct is
unchanged. The file compiles per file through nt_compile.py with no diagnostics.
