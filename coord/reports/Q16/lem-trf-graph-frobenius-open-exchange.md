## Worker report

Stage 2, Q16, lem-trf-graph-frobenius-open-exchange. The main module is
`Sheaf.SixFunctors.GraphFrobeniusOpenExchange`; its theorem is
`WeilConjectures.TraceFormulaCoefficientConventions.graphFrobenius_open_exchange`.
All theorem proofs in this delivery are `sorry`. Definitions contain actual constructions;
there are no private copies of coefficient categories, Frobenius maps or open extensions.
The item's natural-language statement and all its DAG edges are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `T : TraceFormulaCoefficientConventions.{u}` supplies the recorded finite-field datum,
  including prime p, positive a, q=p^a, finite k₀ with q elements and its fixed closure k.
  Its `coefficients` supplies prime ℓ ≠ p and the fixed algebraic closure of Q_ℓ;
  `extension` supplies the finite intermediate extension E, and `level`, `level_pos`
  supply n ≥ 1. `T.coefficientRing` is exactly the recorded O_E/(ϖ_E^n), using its
  existing small coefficient-field model and uniformizer. No new coefficient ring is used.
- The source scheme X₀ is `T.X₀`, over Spec k₀; finite type and separation are its
  `finite_type`, `quasi_compact` and `separated` instance fields. The arbitrary target
  `Y₀ : Over (Spec (.of T.datum.k₀))` carries the explicit `LocallyOfFiniteType`,
  `QuasiCompact` and `IsSeparated` hypotheses: together these are separated finite type.
- `j₀ : T.X₀ ⟶ Y₀` is a morphism over k₀, and `[IsOpenImmersion j₀.left]` is exactly
  the open-immersion hypothesis. `graphFrobeniusBaseChangedOpen` is its actual image
  under `Over.pullback` for Spec(k) → Spec(k₀), giving j : X → Y, with the canonical
  base-change open-immersion instance, registered by a direct application of Mathlib's
  `MorphismProperty.overPullbackMap`. It introduces no additional map or condition.
- `(m : ℕ) (hm : 1 ≤ m)` quantifies over every positive iterate. Scheme Frobenius is
  `T.datum.schemeFrobeniusIterate`; Galois Frobenius is the mth power in the endomorphism
  monoid of `T.datum.geometricGaloisFrobenius`. Thus geometric inverse Frobenius is used;
  no hypothesis asserts that it or absolute Frobenius is a k-morphism.
- `selectedSchemeGaloisComparison T Z₀ m hm` selects the iterate from the recorded
  `schemeGaloisComparison` theorem. That theorem's last clause fixes it by the
  factorization, canonical pullback composition, projection-normalized relative Frobenius
  and section-unit-normalized absolute-Frobenius trivialization. A coefficient-annihilator
  helper supplies its required torsion condition from the fixed finite-level datum.
  It is not an arbitrary isomorphism of the two endofunctors.
- `sfIntrinsicDerivedOpen T.coefficientRing j` is the exact termwise derived functor of
  the recorded `sfIntrinsicExtensionByZero`. All pullbacks in the comparison are
  `proEtaleConstantRingDerivedPullback`, the canonical tensor/constant-section version of
  the recorded small-pro-etale derived pullback.
- `graphFrobeniusSchemeExchange` and `graphFrobeniusGaloisExchange` specialize
  `constantOpenSquareExchange` to the first and second Cartesian-square clauses of
  `frobenius_open_square`. Their source is open extension followed by the target
  Frobenius pullback; their target is the source Frobenius pullback followed by open
  extension. This is precisely the direction of b_Phi and b_g in the node.
- The theorem's left transformation is `whiskerLeft j_! κ_Y.hom ≫ b_g.hom`; at M
  this is κ_{Y,j_!M} followed by b_{g,M}. Its right transformation is
  `b_Phi.hom ≫ whiskerRight κ_X.hom j_!`; at M this is b_{Phi,M} followed by
  j_!(κ_{X,M}). Lean's `≫` reads left to right, so these are exactly the displayed
  equation with the node's right-to-left composition convention.
- Both transformations are precomposed with `T.boundedConstructibleFiniteTor.ι`.
  This is the inclusion of precisely the recorded D^b_ctf(X,A), with its actual full
  subcategory and every morphism. Equality in that functor category states the desired
  component equation for every M and includes its naturality in M. It does not assert
  the stronger equation on arbitrary ambient derived objects.

Recorded dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.CoefficientDatum`,
  `.geometricFiber`.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `.coefficientRing`,
  `.boundedConstructibleFiniteTor`. The latter uses `WeilConjectures.finiteTorConstructible`
  from `Sheaf.Paper.FiniteTorAmplitude` with both bounded constructibility and finite Tor.
- `Sheaf.SixFunctors.SchemeFrobenius`: `FiniteFieldDatum.schemeFrobeniusIterate`,
  `.geometricGaloisFrobenius`, the recorded scheme/Galois morphisms and ordinary pullbacks.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`, with its recorded realization.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the finite-level derived-operation interface;
  its ordinary constant-ring specialization is used, not the completed integral or
  rational operations. Its primary recorded common-stage Hom signature was also read.
- `Sheaf.SixFunctors.SchemeGaloisComparison`: `FiniteFieldDatum.schemeGaloisComparison`,
  including its complete normalization clauses and multiplicative iterate family.
- `Sheaf.AlgebraicGeometry.FrobeniusFactorization`:
  `FiniteFieldDatum.absoluteFrobenius_factorization`, used by the specified comparison.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`, the direct reexport of
  `Scheme.proEtaleCanonicalPullbackComposition` and its unique K-flat characterization;
  the constant-coefficient specialization is `proEtaleConstantRingPullbackComposition`.
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`:
  `Scheme.absoluteFrobenius_proEtale_trivialization`, `.proEtaleFrobeniusDerivedIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`:
  `Scheme.SfOpenSquareExchangeData`, `.proEtale_openSquareExchange`,
  `.sfIntrinsicDerivedOpen`; the specified mate and restriction/pasting equations are
  preserved by the unique unit-normalized coordinate transport supplied in this delivery.
- `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`:
  `FiniteFieldDatum.frobenius_open_square`, first and second Cartesian-square clauses.

The module additionally imports the already stated proof dependencies: constant-ring-map,
constant-exactness, tensor-composition-unit and Frobenius-trivialization-pullback. Mathlib's
localization lift/extensionality interfaces come through the imported derived-operation
modules. The proof-only `lem-sf-open-tensor-normalization` has neither a Lean record nor a
Mathlib match; its import is deferred, as its theorem is unnecessary to type the statement.
The seven proof steps, including exactly where that theorem is used later, are in the
main theorem's docstring. The missing proof theorem is not an extra hypothesis.

Edge cases checked before writing: an empty X₀ or empty Y₀ is permitted; no nonemptiness
or reducedness assumption occurs. The geometric fibre and Frobenius declarations retain
nilpotents. Level n=1 and m=1 are included; n=0 and m=0 are excluded only where the node
excludes them. The exchange helpers themselves allow m=0, as the square theorem does.
A zero complex is an ordinary object of the full subcategory. No smoothness, properness,
Weil structure, stalk-conservativity or k-linearity of Galois Frobenius is assumed.
Universe u is explicit throughout, with the existing site object/morphism and coefficient
universe conventions unchanged. No auto-bound variables, local notation or local instances
are used.

Searches (2026-10-18):

- `msearch.py ... leanfinder "Extension by zero commutes with canonical comparison between
  scheme Frobenius and geometric Galois Frobenius pullback"`: eight hits, led by generic
  `Scheme.Pullback.Triplet.Spec_ofPointTensor_SpecTensorTo` and scheme restriction/tensor
  identities; none is this open-exchange comparison.
- `msearch.py ... leansearch "Extension by zero commutes with Frobenius pullback comparison"`:
  eight hits, including `frobenius_zero`, function extension-by-zero maps and finite-field
  Frobenius; none concerns the pro-etale comparison in the node.
- `msearch.py ... loogle 'CategoryTheory.NatTrans, "comp"'`: twelve generic natural-
  transformation/composition hits (`NatTrans.vcomp`, etc.); no specialized theorem.
- `msearch.py ... grep 'Frobenius|extensionByZero' AlgebraicGeometry`: zero Mathlib hits.
- `rg` in upstream WeilConjectures for Frobenius and exchange finds the trace-formula
  Frobenius/localization framework but no theorem comparing open extension with the
  specified scheme/Galois comparison; `grep -rn` for the item id returns no occurrence.
- `rg` in shared `lean/Sheaf` finds the two separate published comparison/exchange
  interfaces, but no compatibility theorem. Searches for the proposed helper names and
  main declaration in upstream declarations and `dag/lean_names_upstream.json` find no
  collisions. The relevant source and full signatures/docstrings were read, including
  both comparison blueprints' proof files. Raw tool results are in sandbox searches.jsonl.

Validation: `scompile.py` checked each delivered file separately in dependency order.
The first assembled-file diagnostic was the missing open-immersion instance; that was
repaired using Mathlib's existing theorem. Server confirmation then compiled all three
modules, including `GraphFrobeniusOpenExchange` (11.0 seconds), with no diagnostics in
any delivered module. An interim overlay snapshot failed in the unrelated published
`IntegralCompactSupportCoefficientData`; after the source publication advanced, the
wrapper's normal server confirmation succeeded. No library files or compiler tools were
edited, and no dependency binding was changed merely to avoid that temporary failure.
The final delivery dry run also checks the complete packet and current source snapshot.

No statement correction and no STATEMENT-DISPUTED flag are needed.

## Dependency modules

`prop-trf-scheme-galois-comparison`: the existing theorem was mathematically adequate but
its nested existentials did not expose a named canonical κ_m; its general finite-ring
annihilator condition also needed its actual finite-coefficient specialization. The new
module `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` publicly reexports the original
full theorem, records finiteness of the same positive-level ring, states the derived
annihilator property, and selects the original normalized κ_m family. Its primary declaration
`FiniteFieldDatum.canonicalSchemeGaloisComparison` retains arbitrary finite A and the
original annihilator hypothesis; `selectedSchemeGaloisComparison` is only its finite-level
wrapper used by this item. All witness choices
retain the original defining conditions, which determine the map: the site relative map
is fixed by projections, its module mate by the unit equation, and κ by composition.
Its definition contains real data selected from that determined construction. The original
comparison, factorization, iterate law and all other clauses remain publicly available.

`lem-trf-open-square-exchange`: the original canonical exchange uses transported fixed-
scalar inverse image (`sfIntrinsicDerivedPullback`), whereas the Frobenius comparison uses
tensor inverse image (`proEtaleConstantRingDerivedPullback`), on identical intrinsic
categories. `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` states the unique
ordinary coordinate identification by the sectionwise adjunction-unit equation, selects
it, descends it termwise and conjugates the already specified canonical exchange. The
exchange data is chosen only together with its `canonical` field, fixing its inverse as
the prescribed mate; that field determines the comparison uniquely. The full old data,
including restriction identity and both pasting/identity laws, is publicly reexported.
There is no new abstract comparison assumption or replacement open-extension functor.

## Second reading by Q16

Author's second pass, not an independent-agent review: the dispatcher brief reserves the
independent review for the maintainer and forbids starting another agent. I reopened the
node, the exact source proofs, and all three written modules. The finite coefficient data,
separation/finite-type assumptions, base-changed open immersion, geometric inverse
Frobenius and positive iterate correspond as listed above. At an object of the full
subcategory, the natural-transformation equality expands to precisely the stated two
composites; there is no ambient-category strengthening. I checked that κ is selected
from the normalization-bearing theorem rather than from a bare Nonempty isomorphism,
and that the exchange is the original mate-defined one under a unique unit-preserving
transport. The initial explicit implicit-argument placeholders for derived open extension
were corrected after compiler diagnostics. The assembled-file check also required
registering the open-immersion property of the explicit `Over.pullback.map` with
Mathlib `overPullbackMap`; this uses the existing base-change theorem directly,
without a new hypothesis or a postponed proof. No mathematical statement change was needed.
