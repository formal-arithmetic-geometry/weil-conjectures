## Worker report

The module `Sheaf.AlgebraicGeometry.LocalSpectrumBaseChangeStalks` states the unchanged
node in two theorems, with a real helper defining only the image submonoid of chart
denominators. Both proofs are `sorry`. There are no new nodes, dependency repairs,
statement corrections, or disputed statements. All names and universe variables
are explicit (`set_option autoImplicit false`). Nothing is proved in this delivery.

Hypothesis and clause correspondence:

- Arbitrary schemes and morphism: `{X T Y : Scheme.{u}}`, `f : T ⟶ X`.
  All scheme sizes embed in a common universe; there is no algebraic or geometric
  restriction on f. The base point is `p : X`.
- The local ring A is `X.presheaf.stalk p`, its canonical spectrum map is
  `X.fromSpecStalk p`, and its maximal prime is `closedPoint (X.presheaf.stalk p)`.
  These are the dependency's existing Mathlib constructions.
- The fibre product and its two projections are `Y`, `π`, and `h`, with
  `hpb : IsPullback π h (X.fromSpecStalk p) f`. This is a universal cartesian
  square, not an assumed arbitrary comparison map. Quantifying over its realization
  includes the chosen `pullback (X.fromSpecStalk p) f` and is invariant under the
  unique projection-preserving isomorphism of realizations.
- A point q of T with f(q)=p is `q : T`, `hq : f q = p`.
  `∃! z : Y, h z = q` states exactly uniqueness among ALL points over q.
- For every such z, `π z = closedPoint ...` identifies its base projection with
  the maximal ideal. `IsIso (h.stalkMap z)` is invertibility of the actual induced
  local-ring morphism, with source at `h z`; the equality `h z = q` identifies
  that source with the node's local ring at q.
- Closedness is the implication `IsClosed ({q} : Set T) → IsClosed ({z} : Set Y)`.
  It imposes no closedness assumption on p.
- Every affine U containing p is expressed by `U`, `hU : IsAffineOpen U`, `hp`.
  Its ring R is `Γ(X,U)` and its prime is `(hU.primeIdealOf ⟨p,hp⟩).asIdeal`.
  The chart W is `W`, `hW : IsAffineOpen W`, with `hWU : W ≤ f ⁻¹ᵁ U`.
  Its ring D is `Γ(T,W)`, and the actual R→D map is `(f.appLE U W hWU).hom`.
- `localSpectrumBaseChangeDenominators` is exactly the IMAGE of R minus the
  base prime under that section map. Its definition uses `Submonoid.map`, so
  injectivity is neither assumed nor needed.
- `hV : IsAffineOpen (h ⁻¹ᵁ W)` identifies the inverse-image open as affine.
  The existential algebra `a`, its `IsLocalization` witness, and
  `algebraMap ... = (h.app W).hom` say that its actual section ring B is the
  localization of D at those image denominators. This is not an arbitrary
  localization structure: its coefficient map is fixed by the projection.
- The explicit scheme isomorphism `e : (h ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of
  (Localization ...))` renders the node's canonical localization chart.
  Its displayed composite through Spec of the localization map and `hW.fromSpec`
  equals `(h ⁻¹ᵁ W).ι ≫ h`, fixing its compatibility with the projection to T.
  Uniqueness of a localization map over D makes this the canonical isomorphism.
- For every z in this chart with f(h(z))=p, the equality of ideals states that
  `(hV.primeIdealOf ⟨z,hz⟩).asIdeal = Ideal.map (algebraMap D B) Q`, where
  `Q = (hW.primeIdealOf ⟨h z,hz⟩).asIdeal`. Thus the lifted prime is S⁻¹Q.
  The point theorem supplies this z for every q in W over p.
- `eD` and `eB` identify D_Q and B_P with the two actual stalks. Each is
  normalized by the displayed equality with its germ map on D or B.
  `eB.toRingHom.comp φ.toRingHom = (h.stalkMap z).hom.comp eD.toRingHom`
  ensures φ is precisely the induced stalk map in these coordinates, not an
  abstract isomorphism of the rings.
- The forward formula quantifies over d and `e : Q.primeCompl` and states
  φ(d/e)=(d/1)/(e/1), using `IsLocalization.mk'`, `algebraMap` and `Ring.inverse`.
- The inverse formula quantifies over d,e in D and s,t in the IMAGE denominator
  submonoid, with e outside Q. It states φ⁻¹((d/s)/(e/t))=dt/(se).
  `Ring.inverse` is the inverse of a unit; these denominators are units since
  the prime is the extended Q. No extra input proof that e/t avoids P is required.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, and `Spec.map`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and its carrier `stalkObj`, built on
  Mathlib's `TopCat.Presheaf.stalk`. The structure-ring specialization here is
  `X.presheaf.stalk`; there is no copied stalk or germ construction.
- `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`:
  `Scheme.fromSpecStalk_affine_description`, `fromSpecStalk_local_properties`,
  `fromSpecStalk_module_stalk`, and `fromSpecStalk_quotient_factorization`.
  The current node uses its canonical `Scheme.fromSpecStalk` and affine
  localization description; the module and all four signatures/docstrings were read.
- `Mathlib.AlgebraicGeometry.Pullbacks`: `pullback`, projections, universal
  property (`CategoryTheory.Limits`), `Scheme.pullback_map_isOpenImmersion`,
  `pullbackSpecIso` and its projection identities. `PullbackCarrier` supplies
  `Scheme.Pullback.range_map` for the open-fibre-product proof dependency.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule` and
  `LocalizedModule.mk`. For the ring localization in this node we use Mathlib's
  `Localization`, which is the corresponding ring of fractions; no module
  localization is redefined or used to replace a ring structure.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  the existing localization at a prime, and `IsLocalization.mk'` for fractions.
- Proof dependencies also available through the imports:
  `IsLocalization.tensor` (`Localization.BaseChange`),
  `PrimeSpectrum.localization_comap_isEmbedding` / `localization_comap_range`
  (`Spectrum.Prime.Topology`), `IsLocalization.lift` / `ringHom_ext`
  (`Localization.Defs`), `IsAffineOpen.fromSpec_app_self`, `isLocalization_stalk`,
  and `fromSpec_primeIdealOf` (`AffineScheme`), `Scheme.Hom.germ_stalkMap`
  (`Scheme`), and `LocallyRingedSpace.Hom` (`Geometry.RingedSpace.LocallyRingedSpace`).
  The node's postponed proof is reproduced step by step in the theorem docstrings.

Edge cases checked before and after writing:

- Empty T or empty fibre: the point statement has an input point over p and is
  vacuous otherwise; the affine chart statement allows an empty W and zero B.
- Generic p: the construction uses arbitrary prime localization, not a closed
  embedding or an open immersion. No assumption that p is closed appears.
- Nonclosed q: the lift and actual stalk isomorphism hold; only the closed-lift
  implication has a closedness premise.
- Noninjective R→D and rings with nilpotents or zero divisors: denominators are
  mapped by `Submonoid.map`. Neither cancellation nor regularity is assumed.
  For example R=k[x], D=k[x]/(x²), p=(x) is included.
- For the identity morphism, the lift is the maximal point of Spec O_X,p and
  the stalk comparison is the canonical one. If the base is a field, the
  pullback is T with unchanged local rings.
- Denominators in the inverse formula are in the image submonoid; s and e are
  outside Q, so se is outside Q. The two germ normalizations force the maps to
  be the actual morphism's stalk comparison in arbitrary affine coordinates.
- The square realization and all rings/schemes use one explicitly bound u;
  arbitrary scheme pairs can be placed in a common larger universe.

Sources opened: local Stacks `schemes.tex` at lemma-morphism-from-spec-local-ring
and equation-canonical-morphism (01J6/02NA), and `algebra.tex` at
lemma-tensor-localization (00DK) and lemma-spec-localization (00E3).
These supply exactly the local-spectrum, tensor-localization and prime
correspondence arguments; the closed-point consequence is the inverse image of
a closed singleton under the continuous projection. No source correction needed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “Base change to Spec of a local ring has unique
  lifts over the fibre and isomorphic local rings”: eight results including
  `SpecToEquivOfLocalRing`, stalkwise criteria, `Spec_closedPoint`, and
  `IsPreimmersion.of_isLocalization`; none includes the complete statement.
- `msearch.py ... loogle`: `"fromSpecStalk", "pullback"`: no hits.
- `msearch.py ... grep`: `fromSpecStalk|stalkMapIsoOfIsPullback` in
  AlgebraicGeometry: 25 results, primarily uses of the canonical map and the
  open-immersion pullback-stalk interface, not this arbitrary base change.
- `msearch.py ... leansearch`: “Base changing a scheme morphism to the spectrum
  of a local ring preserves local rings at points above its closed point”:
  eight results, including `closedPoint`, `Spec_closedPoint`, and local-ring
  spectrum-morphism results; no complete match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for fromSpecStalk, localization
  stalks and the item id: the closest upstream result is
  `WeilConjectures.AlgebraicGeometry.Morphisms.AffineLocalizationPullbackStalk`,
  `Scheme.exists_lift_stalkEquiv_of_isLocalization`. Its full signature and
  proof were read: it gives existence and a normalized inverse equivalence
  over an affine base, without uniqueness, the closed-base projection, closed
  lift, the general scheme base, or both explicit affine fraction formulas.
- Exact proposed declaration names were searched in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.

Validation: single-file `scompile.py` in sandbox and library module modes passes;
only postponed theorem proofs remain. A first compile correctly required the
image-denominator helper to be marked noncomputable because `primeIdealOf` is
noncomputable; this was repaired. Final dry run and delivery use `deliver2.py`.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
