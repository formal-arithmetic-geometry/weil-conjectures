## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceAdicFlatnessNearClosedFibre`
states `AlgebraicGeometry.AlgebraicSpace.isOpen_moduleFlatLocusOverSpectrum_and_closedFibre_subset`.
Its only theorem has proof `sorry`. Its five helper definitions have real data; no
new axiom, arbitrary map, atlas choice, or existentially chosen fibre product is used.

Source read: `literature/stacks-project/spaces-more-morphisms.tex:6088–6114`,
Tag 08VP, `lemma-flatness-over-Noetherian-ring`, statement and proof. The source's
accidental “pullback to X” means X_n, and “flat over X” means over S, as its proof
explicitly confirms. The accepted node already gives this correct reading, so no
statement correction is needed. Also read `spaces-cohomology.tex:1876–1906`,
`lemma-coherent-Noetherian`: its clauses (1) and (3) identify coherent and finitely
presented modules on the locally Noetherian space in question.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The ambient scheme and universe convention are `{S : Scheme.{u}}` and the explicit
  universe `u`. The ring is `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
  This is the universe of schemes and rings fixed by the recorded algebraic-space
  framework; points and the etale site naturally occupy `u+1` and are not forced into `u`.
- The arbitrary ideal is `(I : Ideal A)`, and the specified structural map is
  `(a : Spec (CommRingCat.of A) ⟶ S)`.
- The source is `(Y : AlgebraicSpace S)`, and the given morphism is
  `(p : Y ⟶ schemeSpace (Over.mk a))`. `schemeSpace` is the existing actual
  representable fppf sheaf of Spec A, with its existing algebraic-space witness.
- Local finite presentation is `(hp : MapIsLocallyOfFinitePresentation p)`, exactly
  the recorded all-compatible-etale-chart predicate, without quasi-compactness.
- `(F : Y.Modules)` is a sheaf on the existing ringed small etale site;
  `(hF : F.IsFinitePresentation)` is Mathlib's local cokernel of a map between finite
  free sheaves, not finite generation alone. `(hFqc : F.IsQuasicoherent)` explicitly
  retains the node's quasi-coherence hypothesis. The former implies the latter, but
  both properties are the ones stated in the node.
- `adicQuotientSpectrumMap a I n` is Yoneda applied to the actual scheme map induced
  by `Ideal.Quotient.mk (I ^ n)`, with composite structural map to S.
  `adicFibre a p I n` has underlying sheaf `Limits.pullback p.hom ...`.
  Its proof field is the first projection of the recorded fibre-product theorem,
  which uniquely fixes this object; no data is selected from a mere existence theorem.
  `adicFibreInclusion` and `adicFibreProjection` are the actual first and second
  projections of that sheaf pullback.
- `((moduleTensorPullback (adicFibreInclusion a p I n)).obj F)` is precisely F_n.
  Pullback is the existing normalized tensor pullback, not an unrelated restriction
  functor or an arbitrary module isomorphic to it.
- `moduleFlatLocusOverSpectrum a p F` is the node's U. For every chart `T` and ordinary
  point `t` above a space point `z`, it asks for `Module.Flat` of the ordinary stalk
  of `(Y.schemeRestriction T).obj F`, over the local ring at the image in Spec A.
  The composite chart morphism is recovered by fully faithful Yoneda as
  `(yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left`. The scalar action is explicitly
  `ModuleCat.restrictScalars` along its actual `stalkMap t`, not a freely chosen algebra
  structure. All charts are tested; no chart-independence theorem is silently assumed
  as a hypothesis.
- The first conjunct, `IsOpen (moduleFlatLocusOverSpectrum a p F)`, asserts openness
  unconditionally, before the reduction-flatness assumption.
- The implication's antecedent `∀ n : ℕ, 1 ≤ n → ModuleIsFlatOver ...` states exactly
  flatness of every F_n over Spec(A/I^n) for positive n, using the already recorded
  chartwise relative-flatness predicate. It does not assume flatness for n = 0.
- The implication's conclusion tests `p⁻¹(V(I)) ⊆ U` on every etale scheme chart:
  `I ≤ ((yoneda.preimage ...).left t).asIdeal` says that the image prime contains I,
  and `schemePointMap T.obj.hom t ∈ moduleFlatLocusOverSpectrum a p F` puts its space
  point in U. Every space point has a chart lift by the algebraic-space atlas;
  therefore this all-chart formulation is exactly containment of the closed inverse
  image, including points represented by arbitrary residue-field extensions.
- There is no completeness, separatedness, proper support, quasi-compactness, or
  Jacobson-radical assumption. Flatness is only concluded over the specified closed
  inverse image, not over all Y.

Dependency declarations used (all source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the existing slice
  instances and `QCoh`, built from Mathlib's `SheafOfModules.IsQuasicoherent`.
  Finite presentation is Mathlib's `SheafOfModules.IsFinitePresentation` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:267`, whose docstring and
  finite local presentation data at lines 202–244 were checked.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, defined using `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  the left adjoint of the normalized `moduleDirectImage`; its defining signatures,
  adjunction and model uniqueness were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` fixes the actual sheaf pullback used in `adicFibre`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: the existing `Point` and
  `schemePointMap`, owned by `def-a1-algebraic-space-point-classes`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: final `pointTopologicalSpace`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, used by the existing `ModuleIsFlatOver` interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`: `ModuleIsFlatOver`.
  Only relative flatness is used; `HasProperAnnihilatorSupport` is not a hypothesis.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, with its existing
  representable sheaf data, owned by `def-trf-scheme-algebraic-space`. The enlarged-site
  theorem itself is not a statement dependency.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor` at the ordinary chart point.

The already landed nodes for scheme restriction, relative module flatness, scheme
spaces, module stalks, and point classes were added to `stmt_deps` to cite the exact
interfaces needed by the statement. No dependency node was changed, and no new node
was created. All existing recorded statement dependencies are imported publicly;
stated proof dependencies (including Mathlib matches) are imported privately unless
already used publicly. The two proof dependencies
`lem-sfb-space-qcoh-affine-chart-calculus` and
`lem-sfb-space-module-flat-point-chart-independence` currently have no Lean record and
are therefore described in the proof docstring without inventing private theorem
copies. The docstring carries all four accepted proof steps, with their named inputs
and the quotient-module identifications.

Edge cases checked mathematically before drafting:

- Empty Y and the zero ring A: there are no source points, the flat locus is open,
  and every containment clause is vacuous, without a nonempty assumption.
- The zero module: all ordinary stalks are flat, so U is the entire point space.
- I = 0: every positive quotient is A; the hypothesis detects flatness everywhere,
  consistently with V(0) = Spec A.
- I = top: every positive quotient is the zero ring, but V(top) is empty; the
  conclusion adds no global-flatness assertion.
- n = 0: helpers are defined canonically, but the theorem tests only n ≥ 1.
- A non-complete Noetherian A and non-quasi-compact Y are admitted unchanged.
- No restriction on characteristic, reducedness, or irreducibility is made.

Searches actually run using the prescribed `msearch.py NS <item>`:

- LeanFinder query: “Adic flatness criterion for a finitely presented quasi-coherent
  module on an algebraic space over a Noetherian ring: open flat locus containing the
  closed fibre when all ideal-power reductions are flat”. Eight hits, including
  `AdicCompletion.flat_of_isNoetherian`, smooth algebra flatness, and scheme morphism
  stalk-flatness; none states this algebraic-space module criterion.
- Loogle query: `"Module.Flat", "IsNoetherianRing"`. Zero hits.
- Mathlib grep query: `flat.*(adic|powers|locus)|openness.*flat`. Thirteen hits,
  principally adic completion flatness and unrelated tensor equalizers; no match.
- LeanSearch query: “Adic criterion for flatness and openness of the flat locus of
  finitely presented quasi-coherent sheaves”. Eight hits, ordinary module localization
  criteria and `SheafOfModules.QuasicoherentData.IsFinitePresentation`; no theorem match.
- Project grep: `grep -rn 'lem-sfb-space-adic-flatness-near-closed-fibre'
  lean/WeilConjectures` returned no hit. `rg` for `adic.*flat|flat.*adic|flat.*[Ll]ocus`
  in `lean/WeilConjectures/AlgebraicGeometry` found scheme-specific flat loci and
  normalization arguments, not the statement. `rg` for flatness and finite-presentation
  names in `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*` found `ModuleIsFlatOver`,
  the existing coherent-module interfaces, and no flat-locus/adic-criterion duplicate.
  These results determined the reused definitions rather than private replacements.

Validation: prescribed `scompile.py` compiles the module cleanly in sandbox and library
module modes. An initial mistyped import of a nonexistent Modules.Stalk module was
replaced by the recorded ModuleStalkFunctor module; a missing parenthesis in the
Yoneda map construction was fixed. No warning or error remains. No statement is
disputed and no source-based node correction was necessary.

## Second reading by NS

This is the author's second reading under the dispatcher instruction not to start
other agents; the maintainer supplies the independent review. I reopened the accepted
node, Tag 08VP, and the final module. In particular I checked that openness is the
first conjunct, rather than conditional on reduction flatness; that positive n is
explicit; that the quotient map is A → A/I^n with the correct contravariant Spec map;
that the first pullback projection pulls F back while the second is the relative base;
that the image-prime condition uses I itself and has no support restriction; and that
the stalk module uses the chart module and the actual composite stalk map. The
all-chart conclusion is exactly the pullback test of p⁻¹(V(I)) ⊆ U because the charts
cover every point. The finite-presentation predicate uses finite generators AND
relations on the small etale site, and the source coherent/finitely-presented
identification is valid because A is Noetherian and p is locally finitely presented.
No hypothesis or conclusion mismatch was found. The compilation repairs above changed
only the malformed import and parentheses. Canonical helpers introduce no extra theorem
obligation or arbitrary object. No node statement, proof step, or proof dependency changed.

## Repair of return bf8a1b167b02

H2: replaced `lem-trf-space-enlarged-etale-ringed-site-model` in the saved packet's
`stmt_deps` by `def-trf-scheme-algebraic-space`. Read the latter's existing:true
record and the full definition of `schemeSpace`: it packages the actual Yoneda fppf
sheaf with its algebraic-space property. The file uses this definition, not any
enlarged-site comparison theorem. Replaced the public `AtlasEtaleRestriction` import
by the direct public `EnlargedEtaleRingedSite` import, and updated `lean.note`.

Advisory addressed: added `def-a1-algebraic-space-point-classes` to `stmt_deps` and
publicly imported `AlgebraicSpacePointClasses`. Read the recorded declarations:
`Point` is the quotient of field-valued representatives, and `schemePointMap` sends
an ordinary scheme point to its residue-field representative. These are the exact
objects used in the flat-locus definition and final containment clause.

The initial saved-packet dry run passed at 9d221876f37. Compared the saved node with
current main: only `lean` and the authorized added `stmt_deps` differ. The returned
head's reported dependency and import are present in that saved packet and are
repaired above. The delivery wrapper rebases this packet on current main. The theorem
signature, five helper bodies, source docstrings, accepted statement and proof are
unchanged. Rechecked the hypothesis/clause correspondence and edge cases in the
worker report against the final file; this repair changes only dependency ownership
and public imports. No new nodes or dependency modules are needed.

Repair validation: `scompile.py` compiled the repaired module cleanly in sandbox
and library modes (9.6 s and 8.7 s). The signature matches `lean.statement` verbatim;
only `lean` and authorized added `stmt_deps` differ from current main. Both ownership
nodes have matching direct public imports. One theorem uses `sorry`; helper data
remain explicit and all Lean lines satisfy the 100-character limit.
