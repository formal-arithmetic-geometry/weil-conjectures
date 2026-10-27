## Worker report

Item: `lem-pur-etale-normalization-comparison-coherence`.
Module: `Sheaf.AlgebraicGeometry.EtaleNormalizationComparisonCoherence`.
The module states all three numbered parts in twelve named theorems, with whole-body
`sorry` proofs. Eleven helper definitions construct the specified arrows. No definition
contains postponed data. The original node is unchanged outside `lean`; there are no new
nodes, dependency-record repairs, or statement corrections.

### Hypotheses and objects

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the recorded size convention of the ordinary etale module category, and permits
  the zero ring. All schemes are `Scheme.{u}`.
- Noetherian is `[IsNoetherian U] [IsNoetherian X]`, and the corresponding instances for
  the open restrictions. Mathlib `IsNoetherian` means locally Noetherian and compact;
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the node's finite affine
  Noetherian cover. The additional open schemes have these properties because they are
  open subschemes of Noetherian schemes; these binders do not restrict the open case.
- The separated etale finite-type map is `(e : U ⟶ X) [Etale e] [IsSeparated e]
  [QuasiCompact e]`. Etaleness supplies `LocallyOfFiniteType e`, so the final binder is
  exactly the remaining finite-type condition, not an extra geometric restriction.
- `DerivedCategoryModule A T` is the recorded ordinary unbounded derived category
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. Exact pullback is
  `(upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory`. Tensor objects and tensor
  arrows are `derivedTensor` and `derivedTensorHom`, rather than another tensor model.
  There is no boundedness, constructibility, perfection, or Tor-amplitude hypothesis.
- Each `c : Compactification e` is arbitrary. `F_e^c` is the recorded
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c`.
  The chosen right adjoint is a functor `G` with `(adj : F_e^c ⊣ G)`; its counit is
  `adj.counit`. Quantification over this pair allows every choice of right adjoint.
- `S_e` is the actual `etaleLowerShriek ... e inferInstance |>.mapDerivedCategory`.
  Its evaluation adjunction is `derivedEtaleLowerShriekUpperStarAdjunction`.
  The canonical `d_e^c` is `canonicalEtaleCompactSupportComparison A e c`, the inverse
  of the specified graph map. No arbitrary isomorphism with these endpoints is used.
- `etaleNormalizationRho` conjugates `(canonicalEtaleCompactSupportComparison A e c).symm`
  under `adj` and the sum adjunction. `etaleNormalizationEta` is its component at
  `constantComplex A X` followed by `etaleSumPullbackUnitIso A e`. Thus `W_e^c` is
  exactly `G.obj (constantComplex A X)`; no new definition of the coefficient object is
  needed. The unit map and pullback compositor come from the recorded exact-pullback
  comparison dependency.
- `etaleNormalizationProjection` uses `projectionMapOfCompactification`, followed by
  `F_e^c` of the tensor of the canonical `L(e^*) ≅ D(e^*)` comparison. This is the
  projection specified by support-map compatibility (2), with its exact-pullback target.

### Every conclusion

Part (1) is `etaleNormalizationComparison_refinement` and
`etaleNormalizationComparison_refinement_laws`.

- The actual `t` is `rightDerivedLowerShriekOfCompactificationIso A c d`, and its inverse
  conjugate `r` is `etaleNormalizationRefinement A c d G H adj adj'`.
- The first conjunct is `t.hom ≫ d_d.hom = d_c.hom` as a natural-transformation equality.
- The second conjunct is `r ≪≫ rho_d = rho_c`. Equality of natural isomorphisms records
  the displayed equality of their specified underlying transformations.
- The third conjunct is `r.app (constantComplex A X) ≪≫ eta_d = eta_c`.
- The last conjunct, universally quantified over `M,K`, is precisely
  `P_c ≫ t.app (M tensor e^*K) = (t.app M tensor 1_K) ≫ P_d`. Lean composition reads
  left to right; this is the node's displayed equation with its right-to-left notation.
- The laws theorem states identity and three-compactification cocycle equations for both
  `t` and `r`. They make every route through a common refinement equal to the pairwise
  comparison. The imported unbounded comparison's refinement-normalization theorem
  identifies these pairwise maps with every actual proper-refinement map, including
  noncartesian refinements; thus this is not limited to one chosen cartesian refinement.

Part (2) is stated with arbitrary `(sq : IsPullback h e' e g)`, not merely the one
chosen fibre product. `[IsOpenImmersion g] [IsOpenImmersion h]` are the specified opens;
`e'` has the inherited etale, separated, finite-type properties. This includes the actual
pullback projections, using `(IsPullback.of_hasPullback g e).flip`.

- `etaleNormalizationBeta` is exactly the pullback-composition map
  `T_e ⋙ T_h ≅ T_g ⋙ T_e'`. It uses `unboundedEtaleUpperStarCompIso`, the equality
  `sq.w`, and the same exact-functor composition comparison.
- `etaleNormalizationOpenLeft` constructs the canonical `S_g F_e'^d ≅ F_e^c S_h`:
  transport the supplied compactifications to the global compact-support functors,
  identify only the two open factors by their `d` comparisons, apply the actual
  proper/open compositors on the two sides of `sq.w`, and transport back. The comparison
  is not defined using rho or by assuming its normalization equation.
- `etaleNormalizationChi` is its conjugate under exactly the two composite adjunctions
  in the node. It is constructed as a natural isomorphism, so its underlying natural
  transformation is an isomorphism as asserted. In `etaleNormalizationComparison_open`
  the first conjunct is, at every `K`, `chi_K = h^*(rho_K) ≫ beta_K ≫ rho'_(g^*K).inv`.
- `etaleNormalizationXi` is `chi.app A_X ≪≫ H.mapIso (etaleSumPullbackUnitIso A g)`.
  The second conjunct of `_open` states `xi.hom ≫ eta'.hom = h^*(eta.hom) ≫ u_h.hom`,
  with all coefficient-object identifications explicitly inserted.
- `etaleNormalizationSumExchange` descends the existing module-sheaf etale base-change
  isomorphism on the arbitrary square. `_sum_exchange_normalization` states that on the
  canonical fibre product it is exactly `exactEtaleSumExchange A e g`, the specified
  inverse degreewise base-change map of the dependency. This retains the identity and
  arbitrary chosen-pullback cases, rather than assuming an arbitrary exchange.
- `_open_counit` states the restriction equation at every `K`, using the actual evaluation
  counits and `beta_K` inside the target sum functor. It is stronger than checking only
  the coefficient object's component in the sense of covering all inputs requested by
  the node; all node hypotheses are retained.
- `etaleNormalizationSumProjection` takes the `p` witness directly from
  `etaleSupportMapCompatibility`. That theorem fixes `p.inv` to be
  `etaleSupportSumProjectionReverse`, so the inverse law determines `p` uniquely.
  This is the specified lift-generator projection; it is not a bare `Nonempty` choice.
  `_open_sum_projection` states its full restriction square. The two displayed tensor
  comparisons are `etaleSupportExactUpperTensorIso` and `derivedTensorHom (1) beta_K`.
- `etaleNormalizationExchange` is `unboundedEtaleCompactSupportExchange` for `c`, followed
  by the canonical comparison from the pulled-back compactification to the arbitrary
  `d : Compactification e'`. `_open_support` asserts its invertibility and the equality
  `E ≫ h^*(d') = g^*(d) ≫ sumExchange`. This states restriction of the specified `d`.
- `_open_projection` states restriction of the actual `P`, under that same `E` and the
  canonical exact-pullback tensor comparison. Its source is
  `g^*(F_e^c M) tensor g^*K`; one route first identifies this with the pullback tensor,
  pulls back `P`, applies `E`, and converts `h^*(M tensor e^*K)` to
  `h^*M tensor e'^*g^*K`. The other applies `E_M tensor 1` followed by `P'`.
  Hence this is equality of actual maps and includes arbitrary `d`.
- `_open_refinement` gives the mixed squares for `chi`, `xi`, and the actual support
  exchange `E`, with independently chosen compactifications and right adjoints on both
  sides. Together with the `d` and `P` normalization squares this says their restrictions
  agree with part (1). `_open_composition` states two-successive-open equations for
  `chi`, `xi`, `E`, and sum exchange. It inserts the specified pullback compositors and
  uses `sq₂.paste_horiz sq₁`, requiring no new Cartesianity hypothesis for the composite.
  The counit and projection restriction squares therefore paste for further opens too:
  they are equalities for each of the two squares and the pasted square, with these
  very same exchange comparisons.

Part (3) is `_tensor_refinement` and `_tensor_open`.

- `v` and `v'` are natural transformations from exact pullback followed by
  `derivedTensorRight ... W` to the supplied right adjoint. Thus naturality is data,
  and the source is exactly `e^*K tensor W_e^c`.
- `hv` and `hv'` assert at EVERY input that `v_K ≫ rho_K` equals
  `derivedTensorHom (1) eta.hom ≫ derivedTensorRightUnitor ...`. These are exactly the
  normalization assumptions; there is no assumption about projection transposes.
- `_tensor_refinement` concludes `v_K ≫ r_K = (1 tensor r_A) ≫ v'_K`.
- `_tensor_open` concludes `delta_h ≫ h^*(v_K) ≫ chi_K =
  (beta_K tensor xi) ≫ v'_(g^*K)`. Here `delta_h` is the canonical exact-pullback tensor
  comparison, with source the tensor of the two pullbacks. This is the node's displayed
  equality after its explicitly allowed tensor-pullback identification. Mixed and
  iterated transports agree by the preceding comparison laws and these equations.

### Recorded dependency declarations used

The direct public imports preserve the recorded statement interfaces. In addition to the
Mathlib scheme, etale, open-immersion, pullback, Noetherian, and adjunction definitions:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `DerivedCategoryModule` via its
  public coefficient module; `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact` fixes the constant-module exact-pullback interpretation.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`,
  `derivedTensorRight`, `derivedTensorHom`; its `TensorStructure` module supplies
  `derivedTensorRightUnitor`. No monoidal instance is chosen or redefined locally.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`;
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`;
  `LowerShriekLeftAdjoint`: `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  A chosen adjunction is an explicit parameter as the node specifies.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `etaleLowerShriek`;
  `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `derivedEtaleLowerShriekUpperStarAdjunction`, publicly re-exported from the exact
  derived-adjunction implementation. Its locality theorem is retained as a dependency.
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`: `quasifiniteCompactSupportExact`;
  `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence` publicly exports the actual
  `canonicalEtaleCompactSupportComparison` (defined in `EtaleCompactSupportGraphDerivedIso`)
  and supplies `etaleSumPullbackUnitIso` and `etaleSumSupportIso`.
- `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`: `etaleSupportMapCompatibility`,
  `etaleSupportExactUpperTensorIso`, `etaleSupportSumProjectionReverse`; the actual `P`
  is `projectionMapOfCompactification` in its public proper/open projection imports.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleLowerShriekCongr`,
  `unboundedEtaleCompactSupportExchange`, `unboundedEtaleUpperStarCompIso`, and the
  comparison coherence/refinement normalization results. Its public upstream
  `LowerShriekIndependenceUnbounded` exports `rightDerivedLowerShriekIso` and
  `rightDerivedLowerShriekOfCompactificationIso`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`:
  `isIso_etaleLowerShriekBaseChangeMap`; the public existing arbitrary-square interface
  `WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange` supplies
  `etaleLowerShriekBaseChangeIso`. Their specified-map identification is stated here.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  is retained as the general tensor-pullback dependency. Its concrete ordinary-etale
  realization here is the existing `etaleSupportExactUpperTensorIso`, transporting the
  canonical left-derived tensor comparison to exact inverse image.
- The two Mathlib leaves with no `lean` record are used directly:
  `CategoryTheory.conjugateIsoEquiv`/`conjugateEquiv` (`Adjunction.Mates`) and
  `CategoryTheory.Adjunction.comp` (`Adjunction.Basic`). The convention-only
  scheme-morphism-properties node introduces no declaration to duplicate.

Recorded proof-only modules are plain imports: `EtaleSupportNestedSummands`,
`ExactDerivedTransformationPasting`, `DerivedPullbackCompositionMonoidal`,
`EtaleSheafProjectionMap`, `EtaleSumTensorTotalization`, `EtaleSumFlatKFlat`, and
`SiteDerivedTensorDescentIndependentCoefficients`. The mate-pasting dependency is a
Mathlib leaf. `lem-pur-etale-sum-exchange-counit` has no recorded module in the read tree,
so there is no module to import for that proof-only edge. Its needed counit equation
is explicitly among this item's own conclusions, not an assumed missing object.

### Sources and searches

Read the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md`, Step 1; Stacks
`etale-cohomology.tex`, `lemma-shriek-base-change` (03S6); and `more-etale.tex`,
`lemma-f-shriek-projection` (0GKF). The node's ten proof steps are distributed across
all theorem docstrings: comparison cancellation; specified projection cancellation;
sum-compositor unit calculation; conjugacy/mate pasting; coefficient-unit naturality;
restriction on generators and K-flat totalization; cancellation for arbitrary `d`;
refinement transport of `v`; open transport of `v`; and successive/mixed coherence.

Searches performed before writing and checked again for declaration-name collisions:

- `msearch.py ... leanfinder "Refinement and open restriction coherence of canonical
  normalized etale compact support right adjoints and tensor families"`: eight hits,
  unrelated open restriction/normalization constructions; none state this theorem.
- `msearch.py ... loogle "conjugateIsoEquiv, conjugateEquiv, Adjunction.comp"`: zero hits,
  the service reports unknown short identifier `conjugateIsoEquiv`.
- `msearch.py ... grep "conjugateIsoEquiv|conjugateEquiv" CategoryTheory/Adjunction`:
  nineteen hits, including the exact generic conjugacy API in `Adjunction/Mates.lean`.
- `msearch.py ... leansearch "coherence of adjunction conjugates of etale compactification
  comparisons and normalized tensor transformations"`: eight generic adjunction hits,
  including `conjugateEquiv`, `conjugateIsoEquiv`, and their composition identities;
  no specialized result with the support, projection, open, and normalized-family clauses.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `normalization.*coherence|normalizationComparison|NormalizationComparison` found
  no declaration of this node. It found the neighboring right-adjoint coherence module,
  which was read and reused for the fixed unit and actual compact-support comparison.
- `rg` in both source directories for every newly introduced full-name stem found
  no pre-existing declaration. Mathlib conjugacy, compactification comparison, derived
  tensor, and sum-base-change interfaces are reused, rather than copied.

### Edge cases and verification

The empty source, empty open restriction, identity maps, identity refinements, equal
compactifications, and repeated identity opens remain permitted. The equations are
ordinary categorical equations even on zero objects. The finite zero coefficient ring
is permitted (no `Nontrivial` assumption); arbitrary finite nonreduced rings such as
Z/4 are permitted. Inputs `M,K` are arbitrary objects of the whole unbounded derived
categories. The right adjoints and their adjunctions are arbitrary choices; even the
mixed-refinement theorem allows different choices on each compactification. No universe
is equated artificially, and no `let`, local notation, private definition, or local
instance occurs in a statement. No node fault or STATEMENT-DISPUTED issue was found.

Every module-mode probe and final compile uses the prescribed `scompile.py` wrapper;
no direct compiler or global build was used. Successful single-file compiles have no
errors or unexpected warnings. All new theorem bodies remain `by sorry`; helper
construction bodies use only real existing functors, maps, isomorphisms, and adjunctions.

## Second reading by N9

This is a second source-and-signature pass by the same dispatcher worker; no other agents
were started, as explicitly required by the brief. The maintainer performs the independent
review of the delivery. I reopened the node and final module and checked the clause mapping
above. In particular:

1. Checked that rho conjugates the INVERSE of d, and r the INVERSE of t; all displayed
   compositions therefore have the node's directions. The arbitrary right-adjoint binders
   were retained rather than specializing to the global exceptional adjoint.
2. Checked chi's two composite adjunctions against its specified left comparison, and
   checked that OpenLeft uses the actual compact-support compositor before rho is defined.
3. Added the explicit identification with `exactEtaleSumExchange` on the chosen pullback,
   so the generalized-square helper is tied to the specified dependency transformation.
4. Checked both projection squares start from the tensor of pulled-back objects and
   finish at the sum/support functor of `h^*M tensor e'^*g^*K`, using beta in that direction.
5. Checked both `v` assumptions quantify over every input, that naturality is intrinsic in
   their natural-transformation types, and that the open equation includes the actual
   tensor-pullback map before `h^*v`. There is no purity or projection-transpose hypothesis.
6. Checked the final mixed and successive restriction equations, especially the inverse
   compositor on the starting iterated pullback and the forward compositor on the target.
   The composite Cartesian square is constructed from the two given squares.
7. Replaced bare monoidal tensor notation in the first draft with the recorded
   `derivedTensor` objects, avoiding the upstream module's documented instance-elaboration
   mismatch. Retained the explicit Noetherian and finite-coefficient assumptions on the
   counit clause. The final module compiles within the required limit.

No statement change or dependency repair was required after this pass.
