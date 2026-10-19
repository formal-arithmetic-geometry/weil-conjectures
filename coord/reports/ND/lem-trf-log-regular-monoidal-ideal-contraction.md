## Worker report

States `AlgebraicGeometry.FineSaturatedLogScheme.monoidalIdeal_contraction` in
`Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction`. Its only theorem has
proof `sorry`. The two structural-map helpers have actual canonical data, with no
postponed proofs. Only the item's `lean` field changes; its mathematical statement
and dependencies are unchanged. No new node or dependency-record change is delivered.

Source read: ILO, Travaux de Gabber, Exposé VIII 3.4.1--3.4.3, printed p. 110
(PDF page 116), including the convention identifying the log structure with its
structural image, and the extension/contraction proof. No source correction is needed.

Hypothesis and conclusion correspondence:

- `(X : FineSaturatedLogScheme.{u})` bundles the scheme, log structure,
  locally Noetherian hypothesis (`X.locallyNoetherian`), and fs charts
  (`X.fineSaturated`). `(hregular : X.IsLogRegular)` is precisely the recorded
  logarithmic regularity condition, with its regular quotient and dimension
  formula at every geometric point. Underlying-scheme regularity is not assumed.
- `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(x : Spec (.of Ω) ⟶ X.scheme)` give the geometric point.
- `Scheme.strictHenselizationRing x` is exactly the recorded A. The helper
  `strictLocalRingIsoStrictHenselization` canonically compares the ring-valued
  point fibre with this specific small affine pointed-neighbourhood colimit.
  Its functor F is the composite from the chosen small representatives to
  affine pointed neighbourhoods and then all pointed neighbourhoods.
  `(Scheme.strictHenselization_properties x).1` supplies F's initiality, hence
  F.op is final. `Functor.Final.colimitIso` gives the inverse comparison from
  the geometric stalk to the small diagram. The existing
  `Scheme.strictHenselizationRepresentativeIso` with the identity equivalence
  and componentwise identity ring isomorphisms identifies that small diagram's
  colimit with the recorded ring. Thus the comparison respects canonical ring
  germs; no arbitrary map, isomorphism, or ring is assumed or chosen.
- `{P : Type u} [AddCommMonoid P]` writes the chart monoid additively.
  `Multiplicative P` changes only notation for use with the monoid-sheaf API.
  `W` is the étale neighbourhood on which the chart is given, `w` is its lift
  of x, and `c` is the chart map. `hc : X.logStructure.IsChart W c` imposes
  the dependency's exact chart condition. No affine restriction is imposed.
- `hsharp` says that the map induced by this chart's germ to
  `X.logStructure.characteristic x` is bijective. This is precisely the
  identification with the sharp characteristic: the map already preserves
  the monoid operations, so bijectivity is exactly a monoid isomorphism.
- `EtaleLogStructure.chartStrictHenselizationMap` composes c with the prescribed
  monoid germ, `stalkAlpha`, and the preceding canonical comparison. Its value
  at `Multiplicative.ofAdd p` is the structural monomial a(p). It uses the
  given chart; no replacement chart or independent structural map is introduced.
- `(J : Set P)` and `hJ : ∀ j ∈ J, ∀ p : P, j + p ∈ J` express exactly
  J+P contained in J. J is arbitrary: there is no finiteness, nonemptiness,
  or submonoid requirement (in particular J need not contain zero).
- `Ideal.span (a '' J)` is JA; the conclusion
  `a ⁻¹' (Ideal.span (a '' J)) = J` is exactly the contraction equality.
  Elementwise it is precisely `a(p) ∈ JA ↔ p ∈ J`, the node's equivalent
  formulation, so no second independent conclusion is required.

Dependency declarations used and read in full with their docstrings:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `FineSaturatedLogScheme.IsLogRegular`,
  `EtaleLogStructure.IsChart`, `EtaleLogStructure.characteristic`,
  `EtalePrelogStructure.germ`, and `EtalePrelogStructure.stalkAlpha`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselization_properties`,
  `Scheme.strictHenselizationNeighbourhoods`,
  `Scheme.strictHenselizationAffineInclusion`, and
  `Scheme.strictHenselizationRepresentativeIso`. The last is used with the
  identity representative equivalence and the actual coordinate-ring diagram.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, used inside
  the recorded fs log scheme structure rather than repeated as a binder.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points
  are inline as the dependency prescribes. The signature and docstring of
  `Scheme.SpecToEquivOfField` were also read.
- Proof-only `Algebra.FiniteType.isNoetherianRing` is imported non-publicly
  from `Mathlib.RingTheory.FiniteType`. The other proof-only nodes
  `lem-trf-log-regular-sharp-chart` and `lem-trf-kato-tor-independence-chart`
  have no recorded Lean declaration in the base, hence no module to import.
  Their node ids and all four proof steps are included in the proof docstring.

Edge cases checked before writing: J empty gives JA = (0), so the statement
includes nonvanishing of every chart monomial, as in source convention 3.4.1.
J = P gives JA = A and whole preimage. For P = {0} these are the only ideals;
the monomial is 1 in the nonzero strict local ring. P = N and P = N² give the
usual monomial-ideal contraction. A proper ideal need not contain 0, so an
`AddSubmonoid` would be incorrect. The empty scheme has no geometric point and
is correctly vacuous. No characteristic or rank restriction is imposed. All
universes and binders are explicit. The comparison helper has a local proof of
initiality obtained from the existing dependency theorem; no extra hypothesis
or instance is imposed on consumers. The theorem signature has no `let`, local
notation, private declaration, or hidden binder.

Searches for existing statements and canonical maps:

- `msearch.py` LeanFinder: "In a sharp chart of a log regular scheme a monomial
  belongs to the ideal generated by a monoid ideal exactly when its exponent
  belongs to that ideal". Results were multivariate-polynomial monomial
  membership, Rees algebra membership, and power-series results; no match.
- `msearch.py` LeanSearch: "Contraction of a monoid ideal extended to a ring in a
  sharp logarithmically regular chart equals the monoid ideal". Results were
  `Ideal.under`, `Ideal.under_def`, localization extension/contraction, and
  going-up results; no match.
- `msearch.py` Loogle: `AddMonoidAlgebra, Ideal.span`. Result:
  `AddMonoidAlgebra.mem_ideal_span_of'_image`, a support criterion within the
  monoid algebra, rather than in a log regular chart's strict henselization.
- `msearch.py` Mathlib grep: `LogRegular|logRegular|monoidalIdeal|MonoidIdeal`:
  zero hits.
- `rg` in upstream `WeilConjectures/` and project `lean/Sheaf/`:
  `log.regular|monoidalIdeal|monoid.*[Ii]deal|LogRegular.*[Cc]ontraction|logRegular.*[Cc]ontraction`.
  Only other logarithmic regularity statements and unrelated ordinary ideal
  results, no contraction statement. The item id in upstream and the proposed
  declaration names in `dag/lean_names_upstream.json` also gave no hits.
- `rg` for `strictHenselization.*presheafFiber|presheafFiber.*strictHenselization|strictLocalRingIso`
  in both Lean trees gave no existing geometric-stalk/ring comparison. The
  supplied helper composes existing universal colimit comparisons; it does
  not define a second strict henselization or logarithmic notion.

Current module sources were also read using `scompile.py --source` for
`Sheaf.AlgebraicGeometry.StrictHenselization`, `Sheaf.AlgebraicGeometry.LogRegularPair`,
and `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`. Because the
refreshed source abbreviates `strictHenselizationRing` while the published
compiled declaration retains its small diagram, its compiled signature and
that of `strictHenselizationRepresentativeIso` were inspected through a
sandbox `#print`/`#check` compilation. The final comparison uses the existing
representative interface and works with either presentation; it does not
rebind or replace the dependency. Validation uses only the prescribed
`scompile.py` and `deliver2.py` wrappers.

Process finding for the maintainer: preflight of an attempted lean-only binding
repair exposed inherited dependency-graph errors in
`def-weil-pbc-strict-henselization-limit`: its proof steps use
`lem-weil-pbc-affine-etale-essentially-small-cover`,
`lem-weil-pbc-colimit-initial-full-subcategory`,
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and
`lem-weil-pbc-spec-small-colimit-limit` without listing them in `proof_deps`.
That dependency node is not changed in the final delivery; its existing
representative comparison supplies the required interface already.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
