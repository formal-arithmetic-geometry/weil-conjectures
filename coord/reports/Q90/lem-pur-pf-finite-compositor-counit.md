## Worker report

Item: `lem-pur-pf-finite-compositor-counit` (stage 2, Q90).
Module: `Sheaf.Paper.FiniteCompositorCounit`.
Namespace: `WeilConjectures.PurityFiniteSetting`.

The main theorem `finiteCompositorCounit` states the conjugacy of the specified
finite direct-image compositor, its ordinary counit equation, and the
compositor-normalized projection equation. `finiteCompositorCounit_identity`
states the two direct-image identity normalizations;
`finiteCompositorCounit_identityProjection` states that identity projection is
identity after the canonical endpoint identifications. All three theorem proofs
are `sorry`. The one additional instance, `finiteCompositor_preservesFlat`, is
constructed from the published finite-quotient finiteness theorem and the
published flat-pullback instance; its data contain no `sorry`.

No mathematical statement or dependency list was changed. No new node and no
dependency repair was needed. No statement dispute or outstanding node fault.

### Hypothesis and clause matching

* Finite datum `A=A_{E,n}`: `(P : PurityFiniteSetting.{u})`, with the exact ring
  `P.Coefficient`, the existing size lift of `P.Ring = O_E/(varpi_E^P.level)`.
  Its structure includes the fixed finite-field datum, ell distinct from p,
  finite coefficient extension, and `P.level_pos : 1 ≤ P.level`. No arbitrary
  ring or coefficient-comparison parameter replaces that datum.
* Separated finite-type k-schemes: `U V W : Over (Spec (CommRingCat.of P.field.k))`,
  with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances on
  each structure morphism. Locally finite type plus quasi-compact is finite type.
* The proper k-morphisms are `(h : U ⟶ V) (g : V ⟶ W)` and
  `[IsProper h.left] [IsProper g.left]`. Being morphisms in `Over` includes
  compatibility with the structure maps. The composite is `h.left ≫ g.left`.
* Ordinary unbounded derived constant-A module categories are
  `DerivedCategory (Sheaf (ProEt.topology U.left) (ModuleCat.{u+1} P.Coefficient))`
  and the analogous categories on V and W. This is the published fixed-scalar
  presentation of the constant-ring module category. The intrinsic realization
  used by the recorded operations is canonical; these are the same ordinary
  operations in those coordinates, as already used by the sibling
  `Sheaf.SmoothPurity.OrdinaryDerivedCompositeTranspose`. In particular no
  completion, constructible restriction, or choice of left/right adjoints is made.
* `P_t` is the published `L((t)^*[ModuleCat P.Coefficient])`, and `R_t` is
  `R((t)_*[ModuleCat P.Coefficient])`. Their specified adjunction and counit
  are `derivedUpperStarLowerStarAdjunction` and its `.counit.app`.
* The actual `a` is `leftDerivedUpperStarComp ... h.left g.left`. Its definition
  derives `upperStarComp` and uses the exact/K-flat comparison of composition;
  it has direction `P_gh ≅ P_g ⋙ P_h` in Lean's diagrammatic convention.
  The recorded general comparison and its finite specialization are imported
  from `IntegralFinitePullbackComposition`; no substitute compositor is defined.
* The actual `c` is exactly `finiteDirectImageComposition P.Coefficient h.left g.left`.
  Its definition is the inverse of `rightDerivedFunctorCompIso'` applied to the
  underived `lowerStarComp`; the latter is fibre-product pasting. Neither an
  arbitrary isomorphism nor the mate of an unspecified comparison is a parameter.
* Conjugacy is the first conjunct: `c.inv = conjugateEquiv (adj_g.comp adj_h)
  adj_gh a.hom`. The reversal is essential: a maps composite pullback to iterated
  pullback, so its conjugate maps iterated direct image to composite direct image.
* The counit equality is the second conjunct, quantified over every M on U:
  `epsilon_gh = P_gh.map c_M ≫ a_(R_g R_h M) ≫ P_h.map epsilon_g ≫ epsilon_h`.
  Lean composition reads left to right. Both sides have the literal source
  `P_gh.obj (R_gh.obj M)` and target M, with no HEq or weaker isomorphism assertion.
* `pi_t` is the existing `rightDerivedLowerStarProjectionMap ... t`, evaluated
  by `.app M |>.app N`. Its definition is precisely the right-adjoint projection
  mate of the canonical `leftDerivedUpperStarTensorComparison`; its transpose
  is comparison followed by counit tensor identity (Stacks 0B56).
* The tensor is the existing curried `derivedTensor ... U.left`, not a new
  tensor structure. The map `d=1_M tensor a_N` is its `.obj M |>.map a_N`.
* The third conjunct quantifies over every M on U and N on W. Its left side is
  `pi_gh ≫ c_(M tensor P_gh N) ≫ R_g.map (R_h.map d)`; its right side is
  `(tensor.map c_M).app N ≫ pi_g(R_h M,N) ≫ R_g.map pi_h(M,P_g N)`.
  These are exactly the two endpoint identifications and ordering in the node.
* Naturality is retained by using actual natural transformations, including
  the projection transformation between curried bifunctors. All component
  equalities are universal in the derived objects; naturality is not a
  hypothesis on supplied component maps.
* Identity cases: the main theorem includes identities since neither proper
  morphism is required nonidentity. `finiteCompositorCounit_identity` further
  identifies `c_(id,f)` followed by `R_f(r_id)` and `c_(f,id)` followed by `r_id`
  with the canonical derived `lowerStarCongr` maps of `id_comp` and `comp_id`.
  Here `r_id = rightDerivedLowerStarId`. Consequently these compositors become
  identity under the stated identifications.
* Identity projection: the final theorem says
  `pi_id ≫ r_id_(M tensor P_id N) ≫ (1_M tensor l_id,N)
   = r_id,M tensor 1_N`, where `l_id = leftDerivedUpperStarId`.
  Thus transporting source and target to `M tensor N` gives precisely identity.
* No boundedness, etale origin, constructibility, finite Tor amplitude or
  projection invertibility assumption occurs. No inverse of a projection is used.

### Dependencies and declarations read and used

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, and the recorded field/coefficient instances.
* `def-weil-scheme-morphism-properties` is explicitly a convention node with
  no declaration. Its properness, separatedness and finite-type meanings use
  Mathlib `AlgebraicGeometry.IsProper`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `CategoryTheory.Over`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded
  `Scheme.proEtaleConstantRingDerivedPullback` and reexported intrinsic ordinary
  operations, including their canonical coefficient identification and adjunction.
  Their fixed-scalar realization uses upstream `ProEtale.upperStar/lowerStar`
  and `derivedUpperStarLowerStarAdjunction` from the FiniteCoefficient API.
* `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition` and
  `integralFiniteCanonicalPullbackComposition`, reexporting the canonical
  termwise module comparison. The fixed-scalar comparison is the upstream
  `ProEtale.leftDerivedUpperStarComp`, whose full definition was read.
* `Sheaf.Paper.FiniteDirectImageComposition`:
  `AlgebraicGeometry.ProEtale.finiteDirectImageComposition`, including its
  defining use of `lowerStarComp` and the right-derived universal compositor.
* Mathlib `CategoryTheory.Adjunction.Mates`: `conjugateEquiv` (the recorded
  match for `def-weil-pbc-adjunction-conjugate`). Mathlib `Adjunction.comp`
  is the recorded composite adjunction. The counit identity is the recorded
  `Adjunction.eq_unit_comp_map_iff` and its Hom-equivalence characterization.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: recorded
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and
  `compactificationProjectionFromData`; these expose the counit projection
  construction without obsolete imports. The exact finite ordinary projection
  used here is `ProEtale.rightDerivedLowerStarProjectionMap` from upstream
  `FiniteCoefficient.Derived.LowerStarProjection`, whose defining term and
  `homEquiv_symm_rightDerivedLowerStarProjectionMap` were read.
* `Sheaf.Paper.DerivedPullbackTensorIso`:
  `WeilConjectures.derivedPullbackTensorIso`, its finite comparison,
  unit/composition clauses, and the underlying `canonicalFinitePullbackTensor`.
  In the fixed-scalar presentation this is the published
  `ProEtale.leftDerivedUpperStarTensorComparison` used by the projection map.
* Upstream `FiniteCoefficient.Derived.LowerStarComp`:
  `rightDerivedLowerStarId`. The two equality transports use `lowerStarCongr`
  and `Functor.rightDerivedFunctorNatIso`; pullback identity is
  `leftDerivedUpperStarId`.
* The instance specialization uses
  `Padic.finite_coefficientExtensionRing` from
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, Mathlib
  `isNoetherian_of_finite`, and upstream
  `ProEtale.upperStarPreservesFlat_moduleCat` from
  `FiniteCoefficient.UpperLowerStar.FlatModuleCat`.
* All stated proof-dependency modules are imported privately when they are not
  already public statement imports: ringed-site K-injective resolutions with
  independent universes, right-adjoint preservation of K-injectives, ringed
  direct-image composition, independent-coefficient K-flat resolutions,
  homotopy adjunction, general pre-derived adjunction, K-injective localization,
  and `Sheaf.Paper.RingedProjectionTensorComposition`. The main docstring carries
  all six proof steps and the named DAG inputs, including the representative
  normalization and endpoint identifications.

### Edge cases and source checks

Read the item and all eight statement-dependency records and their source
interfaces. Read Stacks `categories.tex`, lemma-compose-counits and its displayed
formula, and `sites-cohomology.tex`, equation-projection-formula-map: the latter
explicitly permits arbitrary unbounded derived inputs. Read the current
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/sk-prop-an.proof.md`;
this is an ordinary compatibility input and changes no purity/integration route.
No released repair note exists for this item in the provided checkout.

Checked zero M, zero N, the tensor unit N, an empty scheme, h or g identity,
and both maps identities. None is excluded by a binder. The two identity laws
use the canonical derived identities, including the congruence from `id_comp`
or `comp_id`; they do not pretend those functors are definitionally identities.
All site object/morphism and coefficient sizes follow the published scheme-u /
module-u+1 conventions, with explicitly bound universe u. No equality of distinct
site universes or extra smallness assumption was imposed.

### Searches

All remote searches used `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q90
lem-pur-pf-finite-compositor-counit`.

* LeanFinder: `derived finite proetale direct image compositor conjugate pullback
  counit projection formula composition`; eight hits including the ordinary
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv`,
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`, and slice-category counit
  formulas. They do not state the finite derived compositor plus projection law.
* Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp`;
  twelve hits, including unitors, associators and generic
  `Adjunction.conjugateEquiv_leftAdjointCompIso_inv`. These provide generic
  conjugation operations, not the geometric derived normalization and projection
  identity of this item.
* Mathlib grep via msearch: `conjugateEquiv.*Comp|projection.*composition|compose.*counit`
  in `CategoryTheory`; 25 hits, principally generic adjunction/slice formulas.
* LeanSearch: `derived pushforward compositor conjugate pullback composition
  counit projection formula`; eight hits, principally ordinary sheaf-module
  composition and slice-category counit identities; no exact match.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `finiteDirectImageComposition`, `compositor.*counit`, `finiteCompositor`,
  projection/finite/composition names, and the item id. Found
  `OrdinaryDerivedCompositeTranspose` (successive transposes, no projection law)
  and the private `finiteDirectImageComposition_conjugate` in
  `FiniteCoefficientDirectImage` (the first clause only, not a public exact
  match). The existing projection transformation was reused directly.
* `grep -rn 'lem-pur-pf-finite-compositor-counit' lean/WeilConjectures`: no hits.
  `rg` of all four proposed declaration names in Mathlib, upstream, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no existing declarations with those names.

### Validation

Every compiler invocation used `scompile.py`; no direct local Lean or global build.
The initial compile diagnosed the missing flat-preserving instance; it was
resolved by specializing the existing theorem with the actual finite quotient.
The main statement and then the complete file including identity formulas passed
both the isolated sandbox and actual module-name server compiles, with no errors
or warnings. Final reported times were 7.6 s and 7.3 s. All lines are at most
100 characters; `autoImplicit` is false. The node copy differs only in `lean`;
its primary signature is copied verbatim from the module.

## Second reading by Q90

Author's second pass (the independent mathematical reading is the maintainer's
review under this dispatch protocol). Reopened the node and the complete Lean
module. Matched the coefficient datum and all three separated finite-type
structure morphisms; checked both proper maps and their `Over` compatibility.
Checked the first equality's conjugacy direction is c inverse rather than c.
Checked that the second equality starts at P_gh R_gh M and the middle a is
at R_g R_h M. Checked all four factors of the projection identity, including
the source c_M tensor 1_N, target c_(M tensor P_gh N), and the map d in the
second tensor variable under R_g R_h. Verified both derived arguments range
over the entire unbounded categories and that all maps are actual natural
transformations. Added the two explicit identity-compositor equations and the
transported identity-projection equation so the last paragraph of the node is
represented, including when both maps are identities. The compilation repair
supplies the source-implied flat-preserving instance as a real term; it adds
no theorem hypothesis or arbitrary map. No remaining mismatch was found.
