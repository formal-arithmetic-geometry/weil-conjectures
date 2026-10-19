## Worker report

The module `Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance` states
`AlgebraicGeometry.Scheme.indEtale_strictLocal_invariance`. It introduces no definitions and
leaves exactly the theorem proof as `sorry`. The theorem says that a morphism `u : T ⟶ S` with
the stated affine local `proAffineEtale` charts induces the canonical strict-local comparison at
every same-field geometric point, that this comparison remains an isomorphism after every scheme
base change, and that the strict localization of `S` at the closed geometric point supplied by
its own evaluation map is canonically isomorphic to the original strict localization.

Hypothesis and clause correspondence:

* `{S T : Scheme.{u}}` and `u : T ⟶ S` are the schemes and morphism in the node statement.
* `hlocal : ∀ t, ∃ V U, ...` renders the local ind-etale hypothesis. The conjuncts
  `t ∈ V`, `IsAffine V.toScheme`, `IsAffine U.toScheme`, and
  `e ≫ U.ι = V.ι ≫ u ∧ proAffineEtale e` render respectively the point containment, affine
  source and target charts, commutative chart square, and filtered-etale affine condition.
* `∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `barT : Spec (.of Ω) ⟶ T`, `barS : Spec (.of Ω) ⟶ S`,
  `hbar : barS = barT ≫ u` render a same-field geometric point pair and its image equation.
* `∃ e : strictHenselizationScheme barT ≅ strictHenselizationScheme barS` is the canonical
  strict-local isomorphism. Its first equation is the equality over `S`, and its second equation
  is the characterization by the two canonical point-evaluation maps.
* The quantified `S'`, `g`, `Ω'`, and `barT'` clause renders arbitrary scheme base change. Its
  `e'` and the following two equations repeat the over-base and point-evaluation clauses for
  `barT'` and `barT' ≫ pullback.snd u g`.
* The final conjunct
  `IsIso (strictHenselizationMap (strictHenselizationStructuralMap barS)
    (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barS))))`
  renders the node's localization-again clause: the structural map of the strict localization,
  localized at its canonical closed geometric point, has an isomorphism as its canonical map.

The strict-localization objects and inverse-limit construction are imported from
`Sheaf.AlgebraicGeometry.StrictHenselization`; the structural map is
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap` from
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`. The dependency
`lem-weil-pbc-strict-henselization-functoriality` is used through its recorded declaration
`AlgebraicGeometry.Scheme.strictHenselizationClosedLift_over` in
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`. That module publicly imports the
canonical-map, functoriality, and point-evaluation interfaces needed by the statement. The
point-evaluation definition is therefore used through this recorded dependency module; no
dependency node was changed in this repair.

Other imported declarations used in the signature are `CategoryTheory.Limits.pullback` and
`pullback.snd` from Mathlib's `AlgebraicGeometry.Pullbacks`,
`AlgebraicGeometry.Scheme.proAffineEtale` from
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`, and
`AlgebraicGeometry.Scheme.strictHenselizationMap` from the canonical-map module transitively
imported by `StrictHenselizationClosedLift`.

Edge cases checked: affine charts are allowed to vary with each source point; no finite
presentation, separatedness, or finiteness assumption is added; the geometric field and all
base-change schemes are arbitrary in the declared universe; the identity and empty-chart cases
are covered by the quantified local condition; and the final localization clause uses the
canonical evaluation lift rather than an arbitrary point or a mere `Nonempty` choice. All
variables and universes are explicit, and the only postponed proof is the theorem's `sorry`.

Searches made before and during repair: `msearch.py leanfinder` for “ind-etale morphism induces
an isomorphism of strict henselizations”; `msearch.py loogle` for `IndEtale strictHenselization`;
`msearch.py grep` for `strictHenseli|strictLocalization|IndEtale.*stalk` in Mathlib; `rg` over
`WeilConjectures/` and project `lean/Sheaf/` for strict-henselization and ind-etale invariance;
and direct inspection of `StrictHenselizationClosedLift.lean`,
`StrictHenselizationCanonicalMap.lean`, and `StrictHenselizationFunctoriality.lean`. No existing
declaration states this target. The searches found no Mathlib match for the complete assertion.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
