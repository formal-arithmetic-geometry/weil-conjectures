## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothMarkedLogChart` states the two cases of
`lem-trf-smooth-marked-log-chart` as `AlgebraicGeometry.smooth_associatedLogChart`
and `AlgebraicGeometry.marked_associatedLogChart`. Both proofs are `sorry`; there
are no new definitions, axioms, helper theorems, or dependency modules.

Source read: ILO Exposé VI 1.1, 1.4, 1.8 and Proposition 1.9, printed pp. 69--71
(PDF pages 75--77). This supplies the smooth-locus argument and its marked
coordinate chart. I also read the latest blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and proof.
As the node's accepted split report records, this log-geometric lemma belongs to
the historical nearby-duality route; the current ancestor uses contracting
correspondences. No change to either the node statement or the blueprint unit is
needed to state this supporting lemma.

Hypotheses, objects, and their encodings (in both declarations except where noted):

- The locally Noetherian scheme Y and its fs divisorial log structure are bundled
  as `Y : FineSaturatedLogScheme.{u}`. The existing field
  `Y.locallyNoetherian` supplies its local-Noetherian hypothesis. The other scheme
  is `W : Scheme.{u}` with `[IsLocallyNoetherian W]`.
- The closed subset T is represented by its complement `UY : Y.scheme.Opens`;
  thus `T = (UY : Set Y.scheme)ᶜ`. `hdY : DenseRange UY.ι` is its stipulated dense
  complement, and `hpair` is exactly the recorded
  `IsDivisorialFineSaturatedLogRegularPair` for that complement. Bundling Y as fs
  adds no mathematical assumption: fs is already part of a log regular pair.
- `eY` and `heY` identify `Y.logStructure` with the prescribed divisorial
  presheaf over UY by its structural map. These record that MY is the divisorial
  structure, rather than an unrelated log structure on the same scheme.
- The fs chart monoid is `P : Type u`, `[CommMonoid P]`, `hP`. Its global chart
  is `a`, with `ha : Y.logStructure.IsChart (Scheme.Etale.mk (𝟙 Y.scheme)) a`.
  The node's alpha is exactly `Y.logStructure.alpha.app (...) ∘ a`; there is no
  independent structural map or extra compatibility assumption to choose.
- Case (i) takes `g : W ⟶ Y.scheme` with `[Smooth g]` and no marking.
  Case (ii) takes `c : W ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.scheme` with
  `[Etale c]`. The named `g` is fixed by `hg` to be its composite to Y; the named
  `z` is fixed by `hz` to be `c.appTop` of `AffineSpace.coord (ULift.up 0)`.
  These are names for the stipulated objects, not stronger hypotheses.
- `L : EtaleLogStructure W` is given with its global chart `b` and `hb`.
  In (i) its chart monoid is P. In (ii) it is `P × Multiplicative ℕ`, the
  multiplicative encoding of P direct sum N. In (i) `hab` specifies the structural
  value as `g.appTop (alpha(p))`; in (ii) it specifies precisely
  `g.appTop (alpha(p.1)) * z ^ p.2.toAdd`.
  The recorded `IsChart` definition says that the induced map from the actual
  associated stalk pushout is an isomorphism. Consequently `hb` plus `hab` is
  exactly the assertion that L is the log structure associated to the node's
  prelog map, presented without selecting a sheaf from a nonunique existence
  statement. This is the node's definition of chart, not an additional smoothness
  or regularity assumption on L.
- `U : W.Opens` and `hU` name exactly the node's complement: `g ⁻¹ᵁ UY` in (i),
  and `g ⁻¹ᵁ UY ⊓ W.basicOpen z` in (ii). In the latter, the complement of
  `W.basicOpen z` is the support of V(z); in the former E is empty. Thus Uᶜ is
  exactly B = g⁻¹(T) union |E|, with no boundary component omitted.

Conclusions, clause by clause:

- `∃ hfs : L.IsFineSaturated` says L is fs. Using that proof solely to bundle
  `(W,L)`, the next conjunct is its recorded `IsLogRegular` predicate.
- The existential `f : EtaleLogHom ... Y` supplies the log morphism. Its `hf`
  says `g ≫ 𝟙 Y.scheme = 𝟙 W ≫ f.base`, hence its underlying map is exactly g.
  The equation for `f.sectionMap` sends `a p` to `b p` in (i), and to `b (p,1)`
  in (ii). Because `1` in `Multiplicative ℕ` is additive zero, this is precisely
  the inclusion of the base chart. The existing log-hom compatibility fixes the
  map on units; no arbitrary map replaces the chart-induced morphism.
- `Function.Injective (Algebra.GrothendieckGroup.lift (...))` is injectivity of
  the actual groupification of `MonoidHom.id P` or
  `MonoidHom.inl P (Multiplicative ℕ)`. In (i), `Subsingleton` of its quotient
  by the range says the cokernel is zero. In (ii), the quotient's multiplicative
  equivalence to `Multiplicative ℤ` says its cokernel is Z.
- The pullback in each comparison conjunct is exactly
  `Y ×[Spec Z[P]] Spec Z[Q]`: its first map is the already defined
  `EtaleLogStructure.chartToSpec`, and its second map is `Spec.map` of
  `MonoidAlgebra.mapDomainRingHom ℤ` for the specified chart inclusion.
  In (i), the isomorphism e to Y has `e.hom = pullback.fst`; in (ii), e to A1_Y
  is over Y and is normalized by the equation identifying its coordinate with
  the pullback of `[1,1]` (multiplicatively `(1,ofAdd 1)`). Thus these are the
  canonical identifications, not arbitrary scheme isomorphisms. The equations
  `k ≫ pullback.snd = L.chartToSpec ... b` and `k ≫ e.hom = g` or `= c`
  identify the comparison with g or c and its second projection with the chart
  map. The first projection of k is g: in (i) this follows from e being fst;
  in (ii) it follows by composing `k ≫ e.hom = c` with the displayed over-Y
  equation and using hg. Hence k is exactly the canonical pullback comparison,
  characterized by both projections.
- `∃ hd : DenseRange U.ι` proves density of the specified open U;
  `L.trivialityLocus = (U : Set W)` gives the exact triviality locus.
- The presheaf isomorphism e with `e.hom ≫ divisorialStructuralMap U.ι = L.alpha`
  is the canonical structural identification with O_W intersect j_* O_U^units.
  The equality over the structure map fixes this identification uniquely, since
  the divisorial structural map is an inclusion.
- `interior (closure ((U : Set W)ᶜ)) = ∅` is nowhere density of B, explicitly.
  The last `IsDivisorialFineSaturatedLogRegularPair ... hd` is precisely (W,B)
  log regular. Its definition also supplies the divisorial presheaf sheaf condition.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.LogRegularPair`: `divisorialLogPresheaf`,
  `divisorialStructuralMap`, `IsFineSaturatedMonoid`,
  `IsDivisorialFineSaturatedLogRegularPair`; read their complete definitions,
  including strict-local rings, chart congruences and geometric stalk conditions.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `EtaleLogStructure.IsChart`, `EtaleLogStructure.IsFineSaturated`,
  `FineSaturatedLogScheme`, `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogHom`,
  and `EtaleLogStructure.trivialityLocus`; read their signatures and docstrings.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its canonical over-Y
  projection, and `AffineSpace.coord`; the node's `mathlib_match` explicitly
  authorizes `ULift (Fin n)`, with n = 1 here.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`:
  `EtaleLogStructure.chartToSpec`. The existing node
  `def-per-fs-log-smooth-etale` is added to stmt_deps to cite that already landed
  canonical construction. I read its node and full source; no copy is introduced.
- `Sheaf.AlgebraicGeometry.LogSmoothLogRegular`: `logSmooth_logRegular`,
  including `InjectiveFSLogChart`; imported privately as the recorded proof
  dependency. This is the proof's preservation and divisorial-recovery theorem.
- Mathlib's actual `Algebra.GrothendieckGroup`, `lift`, `MonoidHom.range`, and
  group quotient provide the two group cokernels; no substitute quotient is defined.

Edge cases checked before finalizing:

- W empty and Y empty: no nonempty hypothesis is imposed; density and the
  geometric-point conditions allow the empty scheme. Empty affine-line charts
  and empty complements are not silently excluded.
- T empty: UY = top is allowed. The smooth case recovers a trivial log structure
  on regular W; the marked case retains exactly the coordinate-zero boundary.
- P trivial and P with units: no sharpness or cancellation class is added to the
  binders; the exact fs predicate and groupification are used. In particular
  characteristic group rank is not confused with the chart's group cokernel.
- z invertible (the marking absent on W): basicOpen z = top is allowed. The
  associated chart absorbs that coordinate into units; its *chart* cokernel is
  still Z as stipulated. z zero identically on nonempty W is incompatible with
  the given étale map to A1_Y; no extra nonzero-divisor assumption is introduced.
- No characteristic restriction, nonempty fibre, separatedness, affineness,
  relative-dimension restriction on the smooth case, or chosen geometric point
  is added. P, schemes and sheaf sections share the published interface universe u;
  the finite coordinate type is lifted into u, whereas N and Z remain their
  genuine small monoids/groups.

Searches made on 2026-10-24:

- msearch LeanFinder: "A smooth morphism or an etale marked affine line chart
  over a log regular pair has associated fine saturated log regular divisorial
  log structure". Eight hits: ordinary smooth/étale morphisms and polynomial
  smooth presentations, no log regularity or associated divisorial comparison.
- msearch LeanSearch: "The log structure associated to a smooth or marked
  affine line chart is log regular". Eight hits, ordinary smooth morphisms,
  smooth loci and unrelated manifold infrastructure; no exact statement.
- msearch Loogle: `"LogRegular"`; zero hits.
- msearch grep: `LogStructure|FineSaturated|Divisorial|markedLog` in Mathlib's
  AlgebraicGeometry directory; zero hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `smooth_marked|smoothMarked|markedLog|logRegular.*smooth|smooth.*logRegular`.
  Only the unrelated `smooth_marked_controlled_blowup` statements matched.
- grep of the item id in `lean/WeilConjectures`: no hit.
- rg searches for `chartToSpec` and associated-log charts found the existing
  `FSLogSmoothEtale` construction and `AssociatedLogUniversalStalks`. The former
  is reused. The latter was read to confirm that `IsChart` is the associated-log
  characterization; no duplicate associated-log sheaf is constructed.
- rg of both proposed names in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no name collision.
- `tools/blueprint_refs.py search 'log smooth'`: no blueprint unit match; no new
  node is needed because the canonical comparison construction is already recorded.

No STATEMENT-DISPUTED flag or statement correction: the Lean statements retain
both cases and every clause of the accepted statement. The only DAG delta outside
lean is addition of the already landed canonical-chart construction to stmt_deps.

Validation: scompile.py compiled both the sandbox and the actual module against
the live published server library with no error or warning (8.3 s and 6.2 s).
All binders and the universe are explicit, all new theorem proofs are sorry, and
there are no diagnostic commands, file-local notation, instances or private definitions.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
