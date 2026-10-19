## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoOpenStrictLocalFibre` states
`AlgebraicGeometry.Scheme.isIso_pseudoOpen_strictLocalFibre` with its sole proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The node copy changes only `lean`.

Source checked: Illusie--Laszlo--Orgogozo, Travaux de Gabber,
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, printed
page 287, XVII Definition 5.2.1 and Proposition 5.2.2 with its proof. The definition
requires a homeomorphism onto the image and an isomorphism of the induced inverse-image
structure sheaf map, exactly the two hypotheses used here. The DAG expands the ordinary
strict-local geometric argument underlying the proposition; all four proof steps are
included in the theorem docstring.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}}` and `(f : Y ⟶ X)`.
- Both schemes are Noetherian: `[IsNoetherian X] [IsNoetherian Y]`. Mathlib's
  `IsNoetherian` means locally Noetherian and quasi-compact; its locally Noetherian
  condition uses `IsNoetherianRing` on every affine open's section ring.
- Homeomorphism onto the image with its subspace topology: `(htop : Topology.IsEmbedding f)`.
  No openness or finite-presentation hypothesis is imposed.
- The natural map of sheaves of commutative rings is an isomorphism: `hsheaf` is
  `IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
  f.base).homEquiv X.sheaf Y.sheaf).symm ⟨f.c⟩)`.
  Here `⟨f.c⟩` is the actual structure-sheaf map `O_X → f_* O_Y`, bundled as a
  sheaf morphism; `homEquiv.symm` gives its adjoint `f⁻¹ O_X → O_Y`.
  Thus this is the specified induced map, not the existence of some sheaf isomorphism.
- Any geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (ybar : Spec (.of Ω) ⟶ Y)`. The geometric point downstairs is exactly `ybar ≫ f`;
  both strict localizations use the identical field Ω.
- The first canonical map is an isomorphism: the first conjunct is
  `IsIso (strictHenselizationMap f ybar)`.
- The natural map to the fibre product is an isomorphism: the second conjunct is
  `IsIso (pullback.lift (f := f)
  (g := strictHenselizationStructuralMap (ybar ≫ f))
  (strictHenselizationStructuralMap ybar) (strictHenselizationMap f ybar)
  (strictHenselizationMap_over f ybar).symm)`.
  These are exactly its two canonical projections. The proof argument supplies only
  the already established commutativity of the canonical square, not an extra hypothesis.
- The equivalent Cartesian-square assertion is rendered by this isomorphism from the
  specified vertex to the chosen categorical pullback; the latter is precisely the
  universal-property formulation of that square being Cartesian.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Scheme.sheaf`, and `f.c`; `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `LocallyRingedSpace.Hom`, inherited by `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used by
  `Mathlib.AlgebraicGeometry.Noetherian`'s `IsNoetherian`/`IsLocallyNoetherian`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points use
  the dependency's recorded inline `Spec (.of Ω) ⟶ Y` encoding.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`,
  `Scheme.strictHenselization_properties`. These are the recorded construction,
  now abbreviating the published upstream pointed-neighbourhood colimit.
- `Sheaf.Paper.StrictHenselizationFunctoriality`:
  `AlgebraicGeometry.strictHenselizationResidue` and
  `AlgebraicGeometry.strictHenselizationFunctoriality`, read in full. The existing
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` publicly imports that module
  and provides `Scheme.strictHenselizationMap_existsUnique`,
  `Scheme.strictHenselizationMap`, and `Scheme.strictHenselizationMap_over`.
  It packages the same uniquely characterized arrow with no caller-supplied residue choices.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, `Scheme.strictHenselizationStructuralMap_eq`.
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pushforward`, and `TopCat.Sheaf.pullbackPushforwardAdjunction`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.

The additional proof-only imports realize the node's existing proof-dependency plan:
`WeilConjectures.Topology.InverseImageStalk` (`exists_inverseImage_stalk_iso_commRing`,
whose current source was retrieved with `scompile.py --source`);
`Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
(`Scheme.affine_strict_local_ring_comparison`);
`Sheaf.RingTheory.StrictHenselizationPresentationIn`
(`Algebra.StrictHenselizationPresentationIn`, publicly importing the original presentation);
`Mathlib.CategoryTheory.Limits.HasLimits` (`Cocone`, `IsColimit`, `colimit`, `colimit.desc`);
`Mathlib.AlgebraicGeometry.AffineScheme`
(`IsAffineOpen.fromSpec_app_self`, `fromSpec_primeIdealOf`, `isLocalization_stalk`,
and the imported open-immersion stalk isomorphism and `Scheme.Hom.germ_stalkMap`);
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
(`AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`).
No proof dependency requires a new module and no import is omitted for a cycle.

Edge cases checked mathematically before writing:

- Empty Y has no geometric point, so the universally quantified statement is vacuous;
  no nonemptiness assumption was added. Empty X forces empty Y.
- Identity morphisms and genuine open immersions satisfy the hypotheses and the two
  canonical arrows become isomorphisms as expected.
- `Spec A_p → Spec A`, including the generic-point localization, is allowed even
  when its image is not open. This checks that `IsEmbedding`, rather than
  `IsOpenEmbedding` or `IsOpenImmersion`, is the correct topological hypothesis.
- A proper closed immersion with a nonzero local defining ideal fails the sheaf
  isomorphism hypothesis; no reduction or nilpotence of the ideal was silently assumed.
- An etale double cover fails injectivity; thus the topological hypothesis cannot be
  replaced by a merely etale or stalk-isomorphism hypothesis.
- No characteristic restriction or bound on dimension is present. The single arbitrary
  universe u is the existing geometric-point and strict-localization convention;
  no independently smaller test universe or equality of unrelated universes is imposed.

Searches made (all against the prescribed directories/services):

- `msearch.py ... leanfinder "Strict localizations of a topological embedding of schemes
  whose inverse image structure sheaf map is an isomorphism are canonically isomorphic
  and the square is Cartesian"`: eight hits, concerning `SpecMapRestrictBasicOpenIso`,
  section-map isomorphisms for open immersions, and `IsOpenImmersion.isoOfRangeEq` and its
  projection formulas. None states the strict-localization assertion for a pseudo-open
  immersion; the returned signatures were inspected.
- `msearch.py ... loogle '"strictHenselization"'`: zero hits.
- `msearch.py ... grep 'strictHenselization|strictLocalization|pseudo.?[Oo]pen'`:
  zero Mathlib hits.
- `rg` for `strictHenselizationRing|strictLocalization|PseudoOpen|pseudoOpen` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no matching assertion.
- `grep -rn 'lem-per-pseudo-open-strict-local-fibre'` in that upstream tree: no hits.
- `rg` in project `lean/Sheaf` for pseudo-open and strict-local canonical maps found
  the existing `StrictHenselizationCanonicalMap` interface (reused) and the closed-immersion
  Cartesian lemma (different hypothesis, and it does not assert the first isomorphism).
- `rg` in `dag/nodes` confirmed the item and its sole citer
  `lem-per-perversity-localization-calculus`; the functoriality node already owns the
  canonical map interface. No duplicate pseudo-open strict-local theorem was found.

Validation: `scompile.py NG lem-per-pseudo-open-strict-local-fibre
<...>/lean/Sheaf/AlgebraicGeometry/PseudoOpenStrictLocalFibre.lean` succeeded for both
sandbox and library module names, with no warnings or errors (2.1 s and 2.0 s).
Every variable and the sole universe are explicitly bound. Lines are at most 100 columns.
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by NG

This is the dispatched worker's self-check; the maintainer supplies the independent review,
as prescribed by the dispatch brief. No other agent was started.

Reopened the node and the final module. Checked the direction `f : Y ⟶ X`, both Noetherian
instances, `Topology.IsEmbedding f`, and the actual sheaf adjoint applied to `⟨f.c⟩`.
The adjunction hom-equivalence maps pullback-to-source maps to base-to-pushforward maps,
so its inverse has exactly the required direction. The source and target sheaves are
`X.sheaf` and `Y.sheaf`, respectively. The point downstairs is definitionally `ybar ≫ f`.
Both conclusions use the existing canonical strict-local map; the comparison's first
projection is the structural map to Y and its second is the map to X_(xbar). The
structural-square equation is supplied with `.symm`, matching `pullback.lift`'s convention.
Consequently its isomorphism is exactly the node's equivalent Cartesian assertion.
There is no arbitrary map or extra residue-field hypothesis. No mismatch or correction
was found, and no additional declaration was introduced. The node record was generated
from the theorem signature verbatim and changes no field other than `lean`.
