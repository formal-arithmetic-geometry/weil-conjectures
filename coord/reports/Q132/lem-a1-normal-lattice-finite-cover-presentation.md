## Worker report

The module `Sheaf.Paper.NormalLatticeFiniteCoverPresentation` states
`AlgebraicGeometry.ProEtale.normal_lattice_finite_cover_presentation`, with proof
`sorry`. The node's mathematical statement and accepted nine-step proof are unchanged.
All six helpers are definitions or abbreviations with actual data; none postpones a
construction or chooses an unspecified ring or map. No other theorem is introduced.

Hypotheses and clauses, read against the node and Lean file:

- `X : Scheme.{u}` is the specified scheme. `ConnectedSpace X` includes nonemptiness
  (`ConnectedSpace.toNonempty`), so no redundant nonempty binder is needed.
  `[IsLocallyNoetherian X] [CompactSpace X]` is precisely the node's definition of
  Noetherian. `[X.IsSeparated]` is separatedness over the terminal scheme.
- `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)` states exactly that every local ring is an
  integrally closed domain, using the recorded normal-domain inline convention.
- `l : ℕ`, `[Fact l.Prime]`, and `hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`
  render a prime invertible on X. `[Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]` render the finite coefficient extension.
  `Padic.coefficientExtensionIntegers` and `coefficientExtensionUniformizer`
  supply the chosen valuation ring and uniformizer without extra hypotheses.
- `TopologicalSpace.NoetherianSpace X ∧ QuasiSeparatedSpace X` is the full first
  assertion. The topology conclusion is not replaced by just the input local
  Noetherianity.
- `Scheme.finiteCoefficientLimit l X E` is the actual ring-sheaf limit of
  `finiteCoefficientTower`. At `op n` the tower is the sheafification of the
  constant ring `A / varpi^(n+1)`, including its quotient transition maps. Thus
  the index starts at positive exponent one, exactly as in the node.
- `i` identifies `latticeCoefficientSheaf X (latticeCoefficientIntegers l E)`
  with that completed ring. `normalLatticeCompletionNormalized` gives a finite
  constant-sheaf/continuous-function isomorphism `q` at every positive level,
  its value on every constant, and the equality between each limit projection
  and pointwise quotient reduction. Consequently `i` fixes constants as well
  as reductions. It is determined by its projections, rather than an arbitrary
  abstract coefficient isomorphism.
- `normalLatticeUniformizerSection` transports the actual continuous constant
  uniformizer through `i`. `normalLatticeRationalRing` uses the existing
  `ringedLocalizationRingOfUniverses` on this section; its data is sectionwise
  `Localization.Away`, followed by ring sheafification. This is `R_X = B_X[1/varpi]`.
  `normalLatticeCoefficientMap` is the existing localization unit.
- `e` identifies the continuous rational coefficient sheaf with `R_X`.
  The equation `integralLatticeCoefficientMap X l E ≫ e.hom = i.hom ≫
  normalLatticeCoefficientMap l E X i` fixes the integral inclusion.
  `eell` identifies `B_X[1/l]` with `R_X`; its unit equation fixes every integral
  numerator, hence by localization every fraction. Composing `e` with
  `eell.symm` gives exactly the intervening `E_X ≅ B_X[1/l]` identification.
- `∀ L, L.IsFiniteLocallyFree → ...` ranges over every lisse `R_X`-module.
  `ringedSiteModules` is the recorded abbreviation for `SheafOfModules`.
  `normalLatticeContinuousModule` restricts its action along `e.hom` and is the
  very same L regarded as a continuous E-module. It is not an independently
  chosen rational module.
- `F : Sheaf ... (Type (u+2))`, its class map `c`, and
  `IsLatticeClassPresentation ... F c` use the dependency's exact interface.
  This says the class maps are surjective, their fibres are precisely integral
  isomorphisms intertwining the specified rationalizations, and restrictions
  are characterized by equality of the embedded lattice images. Thus the
  pair includes alpha, and the sheaf has exactly the claimed quotient sections.
- The first covering-family clause gives an isomorphism of `F.over (U j)`
  with a constant sheaf on every member: local constancy. The second gives an
  inhabited section set on every member: local nonemptiness. Both use
  `CoversTop`, and the families need not be the same.
- The `∀ U r t` clause supplies an isomorphism `k` with the constant sheaf on
  `integralMatrixCosets ... r` under every chosen rank-r trivialization `t`.
  For every constant matrix `g` and actual pair `P`, `k([g]) = c U P` if and only
  if `∀ T, Set.image (t.hom.val.app T) (P.image T) = matrixLatticeImage ... g T`.
  Here `[g]` is sent into the constant sheaf by `toSheafify` at the terminal
  slice object `Over.mk (𝟙 U)`. Thus this is the specified map `g ↦ g A^r`
  relative to `t`, including the rationalization in `P`, exactly as the dependency
  `integralLatticeSheaf_locallyConstant`; it is stronger than a bare same-cardinality
  isomorphism. This is the right-coset set `g GL_r(A)`; rank zero is allowed.
- `∃ Y : X.ProEt, IsFinite Y.hom ∧ Etale Y.hom ∧ Surjective Y.hom` is the
  finite etale surjection p, retaining its actual scheme and map.
  `Nonempty (IntegralLatticePair ... Y)` gives an actual module M with its
  finite-local-free proof and rationalization alpha. By surjectivity of c
  this is an actual representative of an element of F(Y), not just a
  formal section of a sheafification with no representative.
- `iY` is the same normalized integral coefficient identification on Y.
  `cR` is a rational inverse-image ring isomorphism. Its equation over
  `Scheme.proEtaleProfiniteComparison Y.hom (finiteCoefficientRingTower l E)`
  fixes the completed coefficient pullback and its localization. The latter
  comparison is the canonical one specified by every finite quotient projection.
- The final M is a finite locally free module over `finiteCoefficientLimit ... Y.left`.
  Its scalar extension along `normalLatticeCoefficientMap` is isomorphic to the
  canonical inverse image of L, followed by scalar extension along `cR.hom`.
  This spells out exactly `M[1/varpi] ≅ p^{-1}L` as a module over `R_Y`.
  Neither finite-cover conclusion contains a descent datum.

The coefficient presentation uses `WithAbs` solely as the dependency's topology-bearing
synonym of E. `latticeCoefficientIntegers` is the comap of the recorded valuation subring
under `WithAbs.equiv`. The actual conversion through this equivalence occurs explicitly
in the reduction normalization and constant uniformizer, rather than pretending the
underlying types are definitionally equal. Ring values and module sections live in
universe u+1; the dependency's unshrunk isomorphism-class sheaf lives in u+2. The pro-etale
site keeps object universe u+1 and morphism universe u. No equation between those universes,
no smallness hypothesis, and no finiteness bound on the class set is imposed. E and X are
put in a common universe u, as in the recorded lattice-class and completion interfaces;
universe lifts place any finite extension in that universe.

Dependency declarations used (their signatures and docstrings were read):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  Topology.Connected.Basic: `ConnectedSpace`; AlgebraicGeometry.Noetherian:
  `IsLocallyNoetherian`, `IsLocallyNoetherian.quasiSeparatedSpace`,
  `IsNoetherian.noetherianSpace`.
- Mathlib.AlgebraicGeometry.Morphisms.Separated: `Scheme.IsSeparated`;
  Morphisms.UnderlyingMap: `Surjective`; Morphisms.Finite: `IsFinite`;
  `Etale` and the infimum-property `MorphismProperty.Over` give the recorded
  finite-etale category, here written as properties of the actual cover map.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: `IsIntegrallyClosed`,
  with `IsDomain` for the recorded normal-domain conjunction.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  `Padic.finite_coefficientExtensionRing`, publicly retaining the actual
  integers, uniformizer, ideal powers and quotient rings of CoefficientExtension.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`;
  CategoryTheory.Sites.ConstantSheaf: `constantSheaf`, `toSheafify`.
- Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized: the recorded
  `lisseContinuousCommRingSheafUniverses` and retained continuous-function interfaces;
  Sheaf.Paper.LatticeSheafLocallyConstant supplies the precise coefficient variant
  used by the lattice pairs: `latticeCoefficientSheaf`, `latticeCoefficientIntegers`,
  `integralLatticeCoefficientMap`, `IntegralLatticePair`,
  `IsLatticeClassPresentation`, `integralMatrixCosets`, `latticeFreeSheaf`,
  and `integralLatticeSheaf_locallyConstant`.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`;
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: the recorded
  independent-universe tensor interface, retaining `SheafOfModules.changeOfRings`.
  The lattice pair's rationalization is that existing sheaf tensor extension.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: `proEtaleSheafInverseImage`,
  `proEtaleModuleInverseImage`. These are the recorded base-change/site-adjunction
  constructions, with no arbitrary pullback functor substituted.
- Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic:
  `finiteCoefficientRing`, `finiteCoefficientRingMap`, `finiteCoefficientTower`,
  `finiteCoefficientLimit`, `finiteContinuousCoefficientSheaf`, and
  `finiteContinuousCoefficientValue`, owned by `def-a1-finite-coefficient-sheaves`.
- Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion:
  `finiteCoefficientRingTower`, owned by `def-a1-finite-coefficient-ring-tower`.
  The theorem `continuousCoefficientCompletion` is a proof dependency only.
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage:
  `proEtaleConstantComparison`, `proEtaleCoefficientTower`, and
  `proEtaleProfiniteComparison`, owned by `def-a1-proetale-profinite-comparison`.
  The theorem supplying invertibility and projection identities is a proof dependency.
- Sheaf.Paper.LatticeSheafBasic: `IntegralLatticePair`, its `Equivalent` and `image`,
  `IsLatticeClassPresentation`, `integralMatrixSubgroup`, `integralMatrixCosets`,
  explicitly cited through `def-sfb-integral-lattice-pairs`.
- Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses:
  `ringedLocalizationRingOfUniverses`, `ringedLocalizationRingUnitOfUniverses`.
  This already-landed definition node is added to stmt_deps, together with the
  three new definition ownership nodes described below for the completed finite
  coefficient sheaves, ring-valued tower and canonical profinite comparison.
  Their `existing: true` records reuse the unchanged published definitions.
  The two theorem nodes remain in `proof_deps`, where their conclusions are used.
- Proof-only imports: Sheaf.AlgebraicGeometry.ContinuousCoefficientLocalization
  (`continuousCoefficientLocalization`), Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
  (`extension_integers_dvr`), and Sheaf.SecPurity.NormalLocallyConstantFiniteSection
  (`exists_finiteEtale_section_of_normal_locallyConstant`). The other recorded
  proof dependencies are directly imported, with the two coefficient theorem modules
  publicly imported because their real-data definitions also occur in the signature.

Edge cases checked before drafting: the empty X is excluded exactly by connectedness;
rank zero is allowed in the free object and matrix cosets; local ranks can vary; the
finite etale cover may be disconnected; the first quotient is exponent one (not zero);
ramification permits `l = unit * varpi^e` for e greater than one, and is why the
unit-normalized ell-localization is explicit; covers may contain empty objects and all
constant sheaves are sheafifications, including over such objects. No fixed global rank,
chosen basis, or descent data is added. The completed-ring and continuous coefficient
comparisons are normalized on all sections, not only on nonempty test objects.

Sources read locally: Bhatt--Scholze PDF pp. 59--61 (completion/localization and the
coset argument), pp. 68--72 (geometric coverings and Lemma 7.4.10); accepted DAG node and
all its statement dependencies and their Lean/mathlib records. The proof docstring
includes all nine accepted DAG steps, including the coefficient pullback check of step 8.
No statement fault or STATEMENT-DISPUTED finding.

Searches actually run:

- msearch.py leanfinder: "A lisse rational ell adic sheaf on a connected normal
  Noetherian scheme has an integral lattice after a finite etale surjection".
  Eight results on integral scheme morphisms/normalization and integral closures;
  no matching lattice assertion.
- msearch.py leansearch: "lisse sheaf integral lattice finite etale cover normal scheme".
  Eight results on finite morphisms, the small etale topology and normalization;
  no matching assertion.
- msearch.py loogle: "AlgebraicGeometry.Scheme, AlgebraicGeometry.Etale,
  AlgebraicGeometry.IsFinite". One result, `exists_etale_isCompl_of_quasiFiniteAt`,
  unrelated to lattice coefficients or local systems.
- msearch.py grep: `lattice.*(finite|etale)|finite.*lattice` in Mathlib/AlgebraicGeometry.
  Zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for normal/lattice/finite-cover terms,
  and for the node id. No exact complete assertion; found the recorded lattice
  sheaf, coefficient-comparison, finite-section, and normal integral-model modules.
  The latter model assertion does not include the coset-class and finite-cover
  presentation requested here and is not an existing match.
- rg of dag/lean_names_upstream.json for finite-lattice combinations: no match.
  rg of Mathlib, WeilConjectures and Sheaf for all seven proposed declaration names:
  no name collision.

Validation of the original packet: scompile.py compiled the sandbox and final module paths. The first pass
identified explicit WithAbs conversions and localization universe parameters that needed
spelling out; those were repaired. The next pass type-checked and reported two long-line
warnings, both repaired before the final dry run. Every theorem body is exactly `by sorry`.

## Second reading by Q132

No second reading by another worker: this dispatched worker delivers directly. The
maintainer's independent review is the required independent mathematical reading.


## Repair of returned head 2e004cf8162b

The initial required `deliver2.py --no-push` on the saved packet passed preflight and
both compiles as commit 08d782dc746. That mechanical pass does not resolve the independent
review's H2 and H3, which were still present in the actual saved Lean and node record.
The live item has no Lean record; this repair preserves the saved mathematical prose,
source, nine-step proof and proof_deps, and changes the Lean clause and statement ownership.
No direct Git command or edit in the read-only project was used.

H2: removed the completion and profinite inverse-image theorem nodes from the additions
to `stmt_deps`; both remain in `proof_deps`. Added the three definition nodes below, all
`existing: true`, owning precisely the unchanged definitions needed to state this item.
The finite quotient sheaves were previously owned only by a theorem node; the ring-valued
tower had no separate record; the constant and limit comparisons were owned only by the
profinite inverse-image theorem. The Id/Comp node owns different maps and is not used as
an ownership substitute. An exact declaration-name ownership census of all DAG nodes
confirmed these facts. No theorem conclusion is needed to form these definitions.
Also followed the advisory to cite `def-sfb-integral-lattice-pairs` explicitly.

H3: replaced `Nonempty (constantSheaf cosets ≅ F.over U)` and unused `_t` by `∃ k`
and the full constant-matrix/embedded-image equivalence from
`integralLatticeSheaf_locallyConstant`. The chosen trivialization is now used as
`t.hom.val.app T` on every slice object. The coset map is evaluated on a sheafified
constant `[g]` and equated with the actual pair class `c U P`; the right side is exactly
the equality of its image with `g A^r`. No new hypothesis or prose statement correction
is required: this restores the already requested identification.

Self-check: compared the new clause term for term with the dependency theorem, replacing
its `L,e,n` by the restricted module, `t,r`. Opened the definition of
`matrixLatticeImage`: it is the range of integral linear combinations of the columns of
`g` in the standard rational free sheaf. Re-read Bhatt--Scholze, Proposition 6.8.4(6),
printed p. 60: the construction is explicitly the map `g ↦ g A^n`. Checked the unit coset,
rank zero (empty sums give the zero lattice), empty charts (vacuous image equality is
compatible with the unique restricted section), and right multiplication by an integral
invertible matrix. The clause does not choose a basis on the integral module and retains
all `U`, `r`, `t`, `g`, `P` and `T` quantifiers. All other hypotheses and clauses retain
the previously reviewed signatures and the clause-by-clause correspondence above.

The revised sole Lean module passed `scompile.py` in both its sandbox and final module
paths (16.9 s and 14.8 s), with no warnings or errors. Only the one original named theorem
has `sorry`; no definition or theorem was added to the library. The dry run and push below
are performed on this repaired packet.

## New nodes

`def-a1-finite-coefficient-sheaves` owns the existing real-data declarations
`finiteCoefficientRing`, `finiteCoefficientRingMap`, `finiteCoefficientTower`,
`finiteCoefficientLimit`, `finiteContinuousCoefficientSheaf`, and
`finiteContinuousCoefficientValue` in `Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic`.
Its self-contained statement defines the lifted quotients at exponent `n+1`, their quotient
maps, constant sheaf tower, sheaf limit, discrete continuous quotient sheaf, and evaluation.
It asserts no completion or discrete-continuous isomorphism. Source: Bhatt--Scholze,
Definition 6.8.1, Lemma 6.8.2(1), and Lemma 4.2.12. This is a definition ownership record,
not a new construction or a duplicate of the theorem that the continuous presheaf is a sheaf.

`def-a1-finite-coefficient-ring-tower` owns `finiteCoefficientRingTower` in
`Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion`, built from the previous node's
rings and quotient maps. It is the ring-valued diagram before applying the constant-sheaf
functor and has no scheme argument. Source: Bhatt--Scholze, Definition 6.8.1 and
Lemma 6.8.2(1), pp. 58–59. No theorem conclusion is part of its interface.

`def-a1-proetale-profinite-comparison` owns `proEtaleConstantComparison`,
`proEtaleCoefficientTower`, and `proEtaleProfiniteComparison` in
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`. It defines the natural
transformation of canonical constant-section adjuncts and the canonical limit comparison
followed by the induced limit map. It applies to arbitrary countable ring diagrams, with
no finiteness, surjectivity, limit preservation or invertibility assumption. Source:
Bhatt--Scholze, Lemma 6.8.2(1) and Remark 6.8.15, and the published construction's Stacks
Tags 098T(2), 04D3, 097N and 01YW. The existing Id/Comp definition node owns only coherence
isomorphisms; it does not own any of these three definitions.

All three nodes reuse unchanged published definitions with `existing: true`; they deliver
no Lean file. Searches are recorded separately in each node with the actual tool queries
and results: msearch LeanSearch (8 hits about profinite groups and evaluation preservation,
no exact match), LeanFinder (8 hits on condensed/LightProfinite limits and affine-transition
limits, no exact match), Loogle (`limit.post`, `limMap`: one generic `limit.map_post` hit),
and Mathlib grep (zero hits for these names). Project `rg` found precisely the reused
modules; the exact DAG ownership census found only the theorem owners described above.
`blueprint_refs.py search coefficient tower` and `search profinite comparison` found broad
adic/derived coefficient notions, not definition owners for these concrete constructions.
`blueprint_refs.py ancestor` gives `lem-a1-affine-hc0`; each new node records this ancestor
and the item's full via chain. No additional blueprint match was found.
