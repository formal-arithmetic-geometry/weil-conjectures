## Worker report

Stage 2 statement for `lem-kun-higher-exchange-coefficient-cube`, in
`Sheaf.Paper.KunHigherExchangeCoefficientCube`. The only theorem is
`AlgebraicGeometry.Etale.abelianHigherExchange_coefficient_cube`, with proof `sorry`.
The helper `abelianHigherExchange` supplies real data for the degreewise exchange
explicitly named in this node. It is not an additional theorem or an independent
notion: its three factors are the exact inverse-image/cohomology comparison, the
cohomology of the recorded derived exchange, and the cohomology of derived direct
image applied to the inverse-image/single-complex comparison. Thus its source and
target are the stated inverse image of `R^q` and `R^q` of inverse image.

The previous worker's reason confused stage 1 with stage 2: Q73's delivery split
and reviewed the proof, and the base node still had no `lean` record. This delivery
adds that record and an actual statement module; it does not resubmit unchanged
stage-1 work. No statement correction, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

- The eight schemes are the eight explicit `Scheme.{u}` binders. The twelve named
  morphisms have exactly the node's domains and codomains.
- `sq₀ : ChosenCartesianSquare e₀ h₀ g₀ f₀` and its index-one counterpart
  encode the two cartesian squares, including their commutativity. They use the
  recorded chosen-cartesian-square notion without recreating a pullback interface.
- `sqf : CommSq x f₁ f₀ s`, `sqg : CommSq a g₁ g₀ s`,
  `sqh : CommSq y h₁ h₀ x`, `sqe : CommSq y e₁ e₀ a` encode, respectively,
  `x ≫ f₀ = f₁ ≫ s`, `a ≫ g₀ = g₁ ≫ s`, `y ≫ h₀ = h₁ ≫ x`, and
  `y ≫ e₀ = e₁ ≫ a`. These comparison faces are only commuting squares.
- `F₀` and `F₁` are abelian sheaves on the specified small etale sites, with the
  standard coefficient size `AddCommGrpCat.{u+1}`. `φ` is any morphism from
  `upperStar a` applied to `F₀` to `F₁`. No `IsIso` binder occurs.
- `q : ℕ`, coerced to `ℤ` for homology, renders exactly `q ≥ 0`.
- In the left path, `abelianHigherExchange sqg F₀ q` is `P^q`.
  The map of `singleFunctor ⋙ g₁_*.rightDerivedFunctorPlus ⋙ homologyFunctor q`
  at `φ` is `R^q g₁_* φ`. Their composite under `upperStar f₁`, preceded by
  `(squareUpperStarIso ... sqf).inv`, is precisely `Uφ` with the source
  identification `x⁻¹ f₀⁻¹ ≅ f₁⁻¹ s⁻¹`.
- `abelianHigherExchange sq₁.toCommSq F₁ q` is `β₁,F₁`. The recorded
  `derivedBaseChangeMapPlus_cohomology_resolution` identifies this exact composite
  with the usual resolution map, as required by the node.
- On the right path, the first factor is `x⁻¹ β₀,F₀`, and
  `abelianHigherExchange sqh (upperStar e₀ |>.obj F₀) q` is `Q^q`.
  `(squareUpperStarIso ... sqe).inv.app F₀` is the canonical `χ` from
  `y⁻¹ e₀⁻¹ F₀` to `e₁⁻¹ a⁻¹ F₀`. Composing it with `upperStar e₁` of `φ`
  and applying `R^q h₁_*` is exactly the two remaining factors in `Vφ`;
  functoriality writes them as one mapped composite. Hence the conclusion is
  `β₁,F₁ ∘ Uφ = Vφ ∘ x⁻¹ β₀,F₀`, in Lean's left-to-right composition order.
- No finiteness, torsion, affineness, quasi-compactness, or quasi-separatedness
  binder is present; no comparison exchange is assumed invertible.

Dependencies opened and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to the
  recorded `Scheme.smallEtaleTopology` and `AddCommGrpCat`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including its chosen pullback
  isomorphism, projection equations, and inherited `CommSq`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, the recorded general
  commutative-square bounded-below derived exchange. Its signature and docstring
  specify the canonical mate computed from the underived mate on resolutions.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, and `Etale.upperStarComp`;
  `Etale.squareUpperStarIso` from `BaseChange.Square` composes the inverse-image
  comparisons through the common composite. Its inverse has exactly the two
  orientations needed for the source comparison and `χ`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus`, `mapDerivedCategoryPlusHomologyFunctorIso`,
  and `mapDerivedCategoryPlusSingleFunctor`, using their full signatures and
  canonical comparison docstrings.
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`:
  `Etale.derivedInverseImageComposition`, including its sheaf and derived
  associativity, unit laws, and representative characterization. Its underlying
  sheaf composition isomorphisms are those used in `squareUpperStarIso`.
- `Sheaf.Paper.KunBcMapOnCohomology`:
  `AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution`, read in full;
  its cohomological composite is exactly the helper used here.
- The Mathlib match for exact-functor-complex-cohomology is
  `CategoryTheory.Functor.homologyFunctorIso`, in
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`; the exact derived
  cohomology comparison above is its derived implementation.
- Proof-only imports include the recorded cohomology-resolution theorem,
  `Mathlib.CategoryTheory.Localization.Predicate` (the localization node's
  `lift`, `fac`, `liftNatTrans`, `liftNatIso`, `natTrans_ext`), and the homology
  comparison module. The derived cube node has no Lean record, so there is no
  module for it to import yet. The recorded derived-square-iso module,
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`, is imported
  proof-only for `Etale.pullbackSquareComparison` and its representative equation.

Source and edge-case reading:

Read Stacks etale-cohomology.tex, `lemma-relative-colimit-general` (0EYM), including
its explicit exchange followed by the arbitrary coefficient transition, and
`lemma-base-change-Rf-star-colim` (0EZT), including its final comparison of the
higher direct images. This node is a formal compatibility extracted from those
constructions, not the finiteness-dependent continuity conclusion itself.
Checked `q = 0` (ordinary exchange), all-identity cubes (ordinary naturality at
`φ` after unit comparisons), zero coefficient maps, either zero coefficient
sheaf, and empty schemes. All are allowed by the binders and the canonical
functorial constructions. No factor of `φ`, `P`, or `Q` is inverted. No statement
fault or `STATEMENT-DISPUTED` issue was found.

Searches for an existing declaration:

- `msearch.py`, leanfinder: "Higher direct image exchange commutes with a morphism
  of cartesian squares and an arbitrary coefficient sheaf morphism". Eight hits
  on module pullback coherence, continuous-site functors and sheafification;
  none states this abelian degreewise coefficient-cube equality.
- `msearch.py`, leansearch: "Degree q etale higher direct image exchange is
  compatible with a commuting cube and a coefficient sheaf morphism". Eight
  hits on etale stability, sheafification, plus constructions and Hom complexes;
  no exact match.
- `msearch.py`, loogle: "AlgebraicGeometry.Etale.derivedBaseChangeMapPlus,
  CategoryTheory.NatTrans.naturality". No hits; the service does not index the
  project-specific first name. Its actual source was opened directly instead.
- `msearch.py`, Mathlib grep in AlgebraicGeometry:
  `higher.*[Bb]ase[Cc]hange|exchange.*[Cc]ube|[Cc]ube.*exchange`: no hits.
- Direct `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for higher
  base change and exchange/cube names found the strict-henselization stalk cube
  and upstream module-coefficient higher-image infrastructure. The former is a
  stalk equation for one fixed sheaf, the latter uses `ModuleCat Λ`; neither
  states this arbitrary abelian coefficient-map cube.
- Opened the current source of
  `WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons` using
  `scompile.py --source`: its public theorem is `exchangeCube_stalk_square` for
  a fixed coefficient, and the underlying derived cube helper is private.
- Direct searches for this node id in upstream sources and for both proposed
  full declaration names in Mathlib, upstream, `dag/lean_names_upstream.json`,
  and side sources found no declaration with the exact statement/name.

Validation: `scompile.py NI lem-kun-higher-exchange-coefficient-cube` compiled the
module cleanly, both as a sandbox file and with its actual module path. After
completing the proof-only imports, the final module again compiled cleanly
(17.0 seconds sandbox, 16.6 seconds actual module). Only the node's `lean` field
changes; its recorded theorem signature is verbatim from the module. All lines
are at most 100 characters, all universes and variables are explicitly bound,
and the one theorem has exactly a `sorry` proof. The helper definition has no
postponed proof or chosen arbitrary comparison.

## Second reading by NI

Independent maintainer second reading of immutable delivery
ff602b091e9ca8607b2daeba5a0837a727c40e28, performed on 2026-10-17.
This reader did not write or previously second-read the delivery. The original
placeholder under this heading has been replaced with this actual reading.

I read the item node, all nine statement-dependency nodes and their Lean or
Mathlib records, the delivered module and worker report, and the declarations
used below. The Lean says exactly what the item says; no mathematical change is
needed.

Hypotheses and conclusion, checked individually:

- The eight scheme binders and twelve arrow binders have the node's exact domains
  and codomains. `sq₀` and `sq₁` use the recorded `ChosenCartesianSquare`, whose
  inherited commutativity and projection-compatible chosen pullback isomorphism
  give precisely the two cartesian squares in the node.
- `sqf`, `sqg`, `sqh`, and `sqe` give respectively
  `x ≫ f₀ = f₁ ≫ s`, `a ≫ g₀ = g₁ ≫ s`, `y ≫ h₀ = h₁ ≫ x`,
  and `y ≫ e₀ = e₁ ≫ a`. They require only commutativity.
- `F₀` and `F₁` are abelian sheaves on the correct small etale sites.
  `φ` has source `a⁻¹ F₀` and arbitrary target `F₁`; there is no `IsIso`
  assumption. `q : ℕ` gives all and only the requested nonnegative degrees.
- `abelianHigherExchange` is real canonical data: the homology comparison,
  homology of `derivedBaseChangeMapPlus`, and homology of derived direct image
  of the inverse-image/single-functor comparison, in that order. The actual
  signatures of both comparison isomorphisms confirm their orientations.
  There is no arbitrary map, choice from bare existence, or data `sorry`.
- On the left, `(squareUpperStarIso ... sqf).inv` identifies `x⁻¹ f₀⁻¹`
  with `f₁⁻¹ s⁻¹`. The next mapped composite is `f₁⁻¹ P` followed by
  `f₁⁻¹ R^q g₁,* φ`; the final exchange is `β₁,F₁`. This is `β₁ ∘ Uφ`.
- On the right, the first factor is `x⁻¹ β₀,F₀`, the second is `Q` at
  `e₀⁻¹ F₀`, and the last is `R^q h₁,*` of `χ` followed by `e₁⁻¹ φ`.
  The inverse of `squareUpperStarIso ... sqe` has exactly the stated `χ`
  orientation. Functoriality packages these last two factors as one mapped
  composite. This is `Vφ ∘ x⁻¹ β₀`.
- For cartesian faces, the helper's three factors are the left-hand side of
  `derivedBaseChangeMapPlus_cohomology_resolution`. Thus `β` has the required
  usual resolution interpretation. The proof docstring also explains the
  identification of the commutative and cartesian derived mates through their
  common termwise square comparison. All four node proof steps are present.
- No finiteness, torsion, affineness, field, nonemptiness, or invertibility
  hypothesis has been added. No conclusion clause is missing.

Dependencies and sources: I opened `ChosenCartesianSquare`, `lowerStar`,
`upperStar`, `upperStarComp`, `squareUpperStarIso`, `baseChangeMap`,
`derivedBaseChangeMapPlus`, `mapDerivedCategoryPlus`,
`mapDerivedCategoryPlusHomologyFunctorIso`,
`mapDerivedCategoryPlusSingleFunctor`, `derivedInverseImageComposition`,
`Functor.homologyFunctorIso`, and
`derivedBaseChangeMapPlus_cohomology_resolution`, including their docstrings.
The exact-functor node is a Mathlib leaf, not a missing declaration.
The proof-only imports serve the node's recorded proof; the still unstated
proof-only derived cube is not required to type this stage-2 theorem.
There is no missing statement prerequisite requiring a new node or §1(B) repair.

I read Stacks etale-cohomology.tex at `lemma-relative-colimit-general`
(0EYM, starting line 7567, especially its construction of exchange followed by
the coefficient map) and `lemma-base-change-Rf-star-colim` (0EZT, starting
line 16410, including the final comparison). I also checked
sites-cohomology.tex at `remark-base-change` and
`remark-compose-base-change-horizontal` (lines 4033 and 4094). The node extracts
formal compatibility of these canonical maps, not the continuity theorem;
the source's qcqs and affine-transition hypotheses are therefore not needed here.

Edge cases: `q = 0`, all identity arrows, zero coefficient map, either zero
coefficient sheaf, and empty schemes are admitted. The identity cube reduces
to naturality after the canonical unit comparisons; zero coefficient maps give
zero on both paths by additivity. No characteristic restriction occurs.
The eight schemes share the declared arbitrary universe `u`; coefficients use
the dependency's recorded `AddCommGrpCat.{u+1}` convention. No independent site
universes were equated and no unbound variable or extra instance appears.

Duplicate search: independently searched Mathlib AlgebraicGeometry, upstream
WeilConjectures and side lean/Sheaf using exchange/cube, higher base-change,
degreewise exchange, and both declaration names. I opened the nearest candidate,
`WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons`:
`exchangeCube_stalk_square` is a stalk statement for a fixed coefficient, and
its derived cube helper is private. Neither duplicates this sheaf-level
arbitrary-coefficient statement or its degreewise helper. The worker also
records LeanFinder, LeanSearch and Loogle searches. Existing inverse-image and
derived constructions are reused rather than privately redefined.

Mechanical checks: `lean.statement` equals the theorem signature verbatim
(from `theorem` to before `:= by`); both public declarations occur in
`lean.declarations`. There are no lines over 100 characters, no unbound universe,
and exactly one `sorry`, which is the theorem's entire proof. Module and both
declaration docstrings have source and blueprint references. No statement
correction, new node, dependency repair, or citer audit is necessary.

Compiler reproduction: invoked
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NI lem-kun-higher-exchange-coefficient-cube snapshot/lean/Sheaf/Paper/KunHigherExchangeCoefficientCube.lean`.
Exit status 0; sandbox compilation 2.5 s and actual library-module compilation
2.7 s, with no diagnostics. The installed 2026-10-17 wrapper explicitly runs
the server side overlay; this is current wrapper evidence, not a claim that a
local compiler was run. The worker's older recorded local-overlay runs are
consistent with this reproduction. No global build, direct SSH command, clone
edit, live Lean write, or git mutation was performed.

Finding: H11 (and the substantive report requirement of H1): the delivered
second-reading section contained only a disclaimer and no reading. This
complete replacement report repairs that documentary defect. No H3, H4, H5,
H6, H7, H8, H9, H10, H12, or H13 fault was found. The mathematical module and
node record are accepted unchanged.
