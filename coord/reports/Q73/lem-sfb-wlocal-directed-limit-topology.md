## Worker report

The module `Sheaf.RingTheory.WLocalDirectedLimitTopology` states
`PrimeSpectrum.wLocal_directedLimit_topology`, with its entire proof postponed by `sorry`.
No definitions, helper theorems, new nodes, dependency repairs or statement changes are needed.
The original node is copied with only its `lean` field added.

The source was read directly using `pdftotext -f 6 -l 8` on
`literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`.
Lemma 2.1.9, especially its cofiltered-limit paragraph, supplies preservation of w-locality,
closed points and the closed-point limit comparison. Lemma 2.1.4 and Remark 2.1.5 identify
components with closed points and give naturality. The algebraic expansion follows the
node's ten proof steps, all reproduced in the theorem docstring with their dependencies.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Nonempty small directed poset D | `(D : Type u) [PartialOrder D] [Nonempty D]` and `hdir : Directed (· ≤ ·) (id : D → D)` |
| Direct system of commutative rings and transition maps | `F : D ⥤ CommRingCat.{u}` and `(F.map (homOfLE hde)).hom`; the functor laws are exactly the direct-system laws |
| Every stage is w-local | `hw : ∀ d : D, IsWLocalRing (F.obj d)` |
| Contraction of every maximal ideal under every transition is maximal | `hmax`, quantified over `d`, `e`, `hde : d ≤ e`, and `n : Ideal (F.obj e)`, with premise `n.IsMaximal` and conclusion `(n.comap (F.map (homOfLE hde)).hom).IsMaximal` |
| Colimit ring R with coprojections | `c : Cocone F`, `hc : IsColimit c`, underlying ring `c.pt`, and coprojections `(c.ι.app d).hom` |
| X and X_d are affine spectra | `PrimeSpectrum c.pt` and `PrimeSpectrum (F.obj d)` are definitionally the underlying Zariski spaces of `AlgebraicGeometry.Spec c.pt` and `AlgebraicGeometry.Spec (F.obj d)` |
| Every prime p is contained in a unique maximal m | First conjunct: `∀ p : PrimeSpectrum c.pt, ∃ m : Ideal c.pt, m.IsMaximal ∧ p.asIdeal ≤ m ∧ (∀ n, n.IsMaximal → p.asIdeal ≤ n → n = m) ∧ ...` |
| Each contraction of m is the unique maximal above the corresponding contraction of p | Last part of that conjunct: for every `d`, maximality of `m.comap (c.ι.app d).hom`, containment of `p.asIdeal.comap ...`, and equality of every maximal `n` above this contraction with `m.comap ...` |
| A prime is maximal iff every contraction is maximal | Second conjunct `∀ p, p.asIdeal.IsMaximal ↔ ∀ d, (p.asIdeal.comap (c.ι.app d).hom).IsMaximal` |
| Closed-point locus is the intersection of coordinate preimages | Third conjunct `closedPoints (PrimeSpectrum c.pt) = ⋂ d, (PrimeSpectrum.comap (c.ι.app d).hom) ⁻¹' closedPoints (PrimeSpectrum (F.obj d))` |
| R is w-local | Fourth conjunct `IsWLocalRing c.pt` |
| Canonical homeomorphism of closed points with their inverse limit | Fifth conjunct: existence of a `≃ₜ` to compatible families of elements of `closedPoints (PrimeSpectrum (F.obj d))`; its coordinate formula is `((e m).val d).val = PrimeSpectrum.comap (c.ι.app d).hom m.val` |
| Canonical homeomorphism of components with their inverse limit | Sixth conjunct: existence of a `≃ₜ` to compatible families of `ConnectedComponents (PrimeSpectrum (F.obj d))`; compatibility uses `Continuous.connectedComponentsMap` on transition contractions |
| Component comparison sends [x] to ([p_d(x)]) | Sixth conjunct's formula `(e (ConnectedComponents.mk x)).val d = ConnectedComponents.mk (PrimeSpectrum.comap (c.ι.app d).hom x)` for every `x,d`; every quotient class has a representative |
| Closed points carry the subspace topology | Mathlib `closedPoints` used as a subtype; no replacement topology |
| Components carry the quotient topology | Mathlib `ConnectedComponents` with its existing quotient topology |
| Both inverse limits are compatible-family subspaces of products | Dependent functions have Mathlib's product topology; the displayed compatibility predicates define subtypes with the induced topology |
| Empty spectra and noninjective maps allowed | No `Nontrivial`, nonempty spectrum, injectivity or surjectivity assumption occurs |

The colimit uses an arbitrary colimiting cocone rather than a chosen `colimit F`.
This quantifies over precisely the same colimit data and fixes its coprojections,
without adding a `HasColimit` assumption or selecting a new construction.
The index and ring carrier use the same universe, as required by the project's index-universe
convention; larger small diagrams can be read in a common universe.

Dependency declarations read and used:

- `sk-def-pe-wlocal`: `WLocalSpace` from
  `WeilConjectures.Topology.SpectralSpace.WLocal.Basic`, `IsWLocalRing` and
  `IsWStrictlyLocalRing` from `WeilConjectures.RingTheory.ProEtale.WLocal`, and
  `IsWContractibleRing` from the recorded umbrella module
  `WeilConjectures.RingTheory.ProEtale.WContractible`. The statement uses exactly
  `IsWLocalRing`; the recorded module is publicly imported. Its class expresses spectrality,
  uniqueness of closed specialization and closedness of the closed-point locus.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit`, with the recorded
  `Mathlib.CategoryTheory.Limits.HasLimits` publicly imported. The object and
  coprojections are the fields of this specified colimit cocone.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`
  from `Mathlib.AlgebraicGeometry.Scheme`, publicly imported. Their underlying spaces and
  maps are the `PrimeSpectrum` and `PrimeSpectrum.comap` used in the signature.
- Proof-only imports: `AlgebraicGeometry.filteredSpectrumTopologicalLimit` from
  `Sheaf.Topology.FilteredSpectrumTopologicalLimit`;
  `WLocalSpace.spectralSpace_closedPoints_components` from
  `Sheaf.Topology.WLocalComponents`;
  `AlgebraicGeometry.Scheme.compactSpace_of_isAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`;
  `AlgebraicGeometry.quasiSeparatedSpace_of_isAffine` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`;
  `SpectralSpace` from `Mathlib.Topology.Spectral.Basic`;
  `Ideal.exists_le_maximal` from `Mathlib.RingTheory.Ideal.Maximal`.
  Their full signatures and docstrings were read. These implement exactly the node's
  spectrum-limit, affine-qcqs, spectrality, maximal-existence and component proof dependencies.

Edge cases checked before writing:

- A one-element poset yields the original w-local spectrum and its identity comparisons.
- A zero ring stage forces a zero colimit along the directed system. A compatible prime,
  closed-point or component family would require a coordinate in its empty spectrum,
  so the compatible-family spaces are empty. The theorem never chooses a point there.
- The noninjective projection `k × k → k` preserves maximal ideals by contraction;
  the theorem permits it and gives the single surviving closed point and component.
- A nonzero system need not have injective transitions; the first conjunct speaks only
  of contraction, not extension or representatives of elements.
- Without the transition hypothesis, `ℤ → ℚ` contracts the maximal ideal `(0)` to the
  nonmaximal ideal `(0)`; thus `hmax` is a substantive ring-map condition.
- Stage w-locality is also substantive: `Spec ℤ` has multiple closed specializations of `(0)`.
- The empty index poset is excluded explicitly by `Nonempty D`, exactly as in the node.

Searches for an existing exact statement (all on 2026-10-22):

- `msearch.py ... leanfinder "directed colimit w-local commutative rings closed points connected components inverse limit homeomorphism"`:
  eight results concerning stalks, products, localization and individual spectrum homeomorphisms;
  none states this directed-limit result.
- `msearch.py ... leansearch "w-local rings directed colimit inverse limit closed points connected components"`:
  eight results, including `Ring.DirectLimit`, local-ring closed-point facts and locally ringed
  space coproducts; no w-local limit theorem.
- `msearch.py ... loogle "IsWLocalRing, ConnectedComponents, PrimeSpectrum.comap"`:
  no hits, with unknown identifier `IsWLocalRing` (the notion is upstream, not in Mathlib).
- `msearch.py ... grep "WLocal|w.local|ConnectedComponents.*[Ll]imit"`:
  25 unrelated localization and topology hits; no exact statement.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, with
  `lem-sfb-wlocal-directed-limit-topology|[Ww][Ll]ocal.*([Ll]imit|[Cc]olimit)|([Ll]imit|[Cc]olimit).*[Ww][Ll]ocal`,
  plus searches for `wlocal|WLocal|wLocal`, found the existing definitions, component facts,
  w-localization constructions, and `indfiniteContractibleBase_wStrict`. The latter imposes
  finite finitely presented algebras over a w-contractible base and concludes w-strict locality;
  it is not this statement. The generic spectrum-limit theorem lacks the w-local conclusions.
  No matching declaration was found in `dag/lean_names_upstream.json` either.

Validation: `scompile.py Q73 lem-sfb-wlocal-directed-limit-topology <module>` passed both
sandbox and library-module compilation (10.1 s and 3.2 s), with no errors or warnings.
All variables and the universe are explicitly bound (`autoImplicit false`).
There are no statement disputes or node faults.

## Second reading by Q73

A separate rereading of the node, source and completed signature checked every row above.
This is a worker self-check; the maintainer's independent delivery review remains separate,
and no other agent was started, in accordance with the dispatcher's instruction.
The first conjunct quantifies over every maximal ideal above p, not only a selected subclass;
its coordinate uniqueness likewise quantifies over every maximal ideal above p_d. The two
homeomorphism existentials carry formulas fixing their canonical values, and their codomains
use compatibility equalities in the correct contravariant direction. The component formula
holds on every representative, hence specifies the full quotient map. The fixed colimit
coprojections occur in every contraction. Empty spectra and noninjective transitions remain
allowed. No mismatch was found and no correction was made during this rereading.
