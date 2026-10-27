## Worker report

The module `Sheaf.Paper.ChartLeftScalarNormalization` states the chart coefficient square,
its compactification independence, its agreement with the recorded restricted-closure
chart comparison, and its actual sum-then-affine counit. All four theorem proofs are
`sorry`. The two helper definitions have real data: a composite of the existing
isomorphisms, and transport of the existing ordered affine adjunction. No statement
correction, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

- The base field and positive characteristic are `(k : Type u) [Field k] [CharP k p]`,
  `(hp : 0 < p)`. The prime distinct from the characteristic is `[Fact ell.Prime]`
  and `hEll : p ≠ ell`. These are explicitly included in the main theorem.
- Schemes over k use `Scheme.Over (Spec (.of k))`; separated finite type uses
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on their structural maps.
  All standing hypotheses, including characteristic and separatedness, are explicitly
  retained with `include`; Lean cannot silently discard unused section instances.
  Both `e` and the affine projection carry `IsOver`; their composite is therefore
  the stated k-morphism g. The middle affine tower is also in the standing setting.
- Finite unital commutative coefficients use `[CommRing A] [CommRing B] [Finite A]`
  `[Finite B]` and `φ : A →+* B`. The common annihilator is `ell ^ n`, with
  `hA : ((ell ^ n : ℕ) : A) = 0` and `hB : ((ell ^ n : ℕ) : B) = 0`. Primality implies this
  integer is at least one, including n=0. No flatness instance is requested.
  Coefficients have universe u+1, exactly the fixed-module convention of the
  recorded ordinary-site interfaces; the site objects and morphisms remain u+1/u.
- The ordinary derived categories are `Etale.DerivedCategoryModule`. The input
  predicates `_hL` and `_hK` use the existing `AdjunctionTransfer.etaleProperty`:
  bounded constructible cohomology intersected with finite Tor amplitude, whose
  degree-zero module tests share one finite interval. No replacement ctf predicate
  is defined. The pro-etale wording in the node fixes conventions; its asserted
  coefficient equation and chart adjunction are on the ordinary etale site.
- `Etale.scalarExtension φ T` is the existing derived coefficient extension T_T;
  `etaleCoefficientMap φ cp/cg` are the existing proper-counit/open-tensor maps.
  `sumCoefficientIso φ e` is exactly the published summandwise tensor identification.
- The affine space and projection use `affineTraceTower Y d` and
  `affineTraceProjection Y d`, the same ordered-coordinate model used by the
  recorded affine-space top-trace lemma. Its zero-dimensional stage is Y itself.
  `e` has the specified separated, etale and finite-type hypotheses.
- `ce`, `cp`, and `cg` are arbitrary independently supplied `Compactification`
  values. Their middle schemes are proper over standing schemes, hence again
  separated finite type over k with their induced structural morphisms; no extra
  middle-scheme choice or restriction is made.
- `MA` and `MB` are the existing graph-normalized
  `EtaleCompactSupportNormalization` records. Their existence is recorded in
  `nonempty_etaleCompactSupportNormalization`; quantifying over these records
  retains their graph, representative, refinement and counit equations, rather
  than supplying arbitrary endpoint isomorphisms.
- `chartScalarLeftComparison` is literally `F_d(c_e⁻¹)` followed by the canonical
  `etaleCompositor`. Its return type is a natural isomorphism, giving the asserted
  isomorphism for both coefficient rings. `chartLeftScalarNormalization_comparison`
  identifies it with `Etale.etaleAmbientLeftComparison`, the recorded construction
  using the restricted closure. The Noetherian structures in this interface are
  consequences of the section's finite-type field assumptions; they add no
  mathematical hypothesis to the main theorem.
- `chartLeftScalarNormalization` reads in diagrammatic Lean order as
  `T_Y(lambda_A) ≫ beta_g = beta_d(E_A L) ≫ F_d,B(sigma_e) ≫ lambda_B(T_U L)`.
  Thus all three arrows on the right and both arrows on the left are the specified
  ones; neither beta is replaced by its inverse or by an arbitrary map.
- `chartScalarAffineAdjunction` transports the actual `affineTraceAdjunction`
  through the canonical `reductionEtaleAffineLeftIso`. The supplied twist transport
  `t` and normalized P1 datum `D` are precisely the data of the recorded affine
  adjunction, using roots-of-unity Tate lines, and `hY` is invertibility of N on Y
  (automatic here from ell different from the characteristic). They introduce no
  independent trace. The target right functor is the ordered model of
  `p_d^*(-)(d)[2d]`.
- `chartLeftScalarNormalization_counit` composes the derived sum/evaluation
  adjunction with that actual affine adjunction, transports the composite by the
  specified lambda, and states `lambda(H K) ≫ epsilon_g(K) =
  F_d(v(G_d K)) ≫ epsilon_d(K)`. This is the retained sum-then-affine counit,
  on the stated ctf inputs, rather than an existence assertion for a new counit.
- `chartLeftScalarNormalization_refinement` changes all three independently chosen
  compactifications. It uses `rightDerivedLowerShriekOfCompactificationIso` on the
  source and target, the canonical comparison through common refinement. The e
  comparison cancels. Combined with the dependency's actual coefficient refinement
  square, this is the asserted validity for every specified compactification.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, for the standing
  setting and its separated finite-type conventions (reexported by coefficient compatibility).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategory.torsionCohomology` and `Etale.DerivedCategoryModule`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, for the pro-etale convention.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`:
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses`, the actual interval test.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `AdjunctionTransfer.etaleProperty`, `etaleProEtaleAdjunctionTransfer`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`;
  the ordinary site uses `Etale.scalarExtension` from the coefficient module.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `Scheme.finiteEtaleTateTwist`, with roots-of-unity scalar extension and tensor powers.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `Etale.etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`;
  its projection module supplies `derivedEtaleLowerShriekUpperStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `Etale.etaleAmbientLeftComparison`.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:
  `Etale.EtaleCompactSupportNormalization`, `nonempty_etaleCompactSupportNormalization`.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `etaleCoefficientMap`, `sumCoefficientIso`, `normalizedSumComparison`, `etaleCompositor`,
  and the composition, sum and refinement statements of
  `etaleProEtaleCoefficientCompatibility`.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `Etale.exists_affineSpaceTopTrace`;
  its construction module supplies `affineTraceAdjunction` and the ordered tower.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`: the canonical coherent
  compactification comparisons.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `Adjunction.id`,
  `Adjunction.ofNatIsoLeft`, with their actual counits.
- Existing helper `reductionEtaleAffineLeftIso` in
  `Sheaf.SecSmoothPurity.ReductionExceptional` supplies the canonical unbounded affine
  tower comparison. Reusing this definition avoids duplicating a canonical construction.
  Its theorem `reductionExceptionalComparison_isIso` is not used. Maintenance import
  note: adding a proof import of this delivery back into that same module would close
  an import cycle and must be omitted under stages/2-statements.md section 3 rule 7;
  future proof integration can put the consumer proof in a later module. No DAG edge
  to the downstream theorem has been added.

The unstated proof dependency `lem-sp-etale-ctf-chart-domain` has no Lean record, so no
module for it can currently be imported. Its notion is already supplied by etaleProperty;
this delivery needs no additional definition from that node. All stated proof dependencies
are imported; the full proof plan is retained in the theorem docstrings.

Edge cases checked before writing: d=0 uses the literal identity affine adjunction;
e=id uses identity normalization; empty U gives zero sum extension and no false nonempty
hypothesis; A=B and identity φ recover the normalized identity coefficient square;
nonflat Z/ell² → Z/ell is allowed; n=0 forces zero coefficient rings and remains allowed;
zero complexes are admitted by etaleProperty. Refinement changes all three compactifications,
not just cg. Morphisms are linear over the target coefficient ring throughout.

Searches actually run using msearch.py for this group/item:

- leanfinder: `graph normalized etale compact support chart comparison commutes with
  derived change of finite coefficient rings`: eight hits on StandardEtalePair and
  StandardEtalePresentation algebra, no sheaf-derived chart comparison.
- loogle: `CategoryTheory.Adjunction.ofNatIsoLeft, CategoryTheory.Adjunction.counit`:
  one hit, `CategoryTheory.Adjunction.ofNatIsoLeft_counit`, used as the categorical
  normalization formula, not a match for the geometric coefficient square.
- grep: `chart.*[Ss]calar|[Ss]calar.*chart|etaleAmbientLeftComparison`: two unrelated
  manifold scalar-action hits, no match in Mathlib.
- leansearch: `The normalized compact support comparison for an etale affine space chart
  commutes with derived extension of finite coefficient rings`: eight ring-etale,
  StandardEtalePair and unrelated analysis hits, no match.
- Direct rg of the same concepts and the item id under lean/WeilConjectures and
  lean/Sheaf found the existing chart/affine helper definitions in ReductionExceptional,
  etaleAmbientLeftComparison and its consumers, but no theorem stating this square.
  Exact new declaration names were also searched in Mathlib, both project roots,
  and dag/lean_names_upstream.json, without a collision.

No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by Q13

A second pass by the same dispatcher worker (the brief forbids launching other agents)
compared the node with all six declaration signatures. The maintainer supplies the
independent delivery review. This pass checked the two directions of lambda, beta,
and sigma; confirmed that the affine counit uses the ordered P1 data and not an arbitrary
adjunction; checked the identity and empty cases; and checked all three compactification
changes. It added a separate equality with the recorded restricted-closure comparison,
and restricted the counit assertion to ctf inputs. It also moved the explicit section
inclusion before the main theorem's docstring. No mathematical statement was changed.
