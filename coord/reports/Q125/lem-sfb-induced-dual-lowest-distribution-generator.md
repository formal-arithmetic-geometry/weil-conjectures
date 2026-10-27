## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.InducedDualLowestDistributionGenerator`
states `AlgebraicGeometry.InducedDualLowest.induced_dual_lowest_distribution_generator`.
This is stage 2: the theorem has `sorry`; the four helpers have explicit data.
No original statement, proof step, or proof dependency is changed. The only added
statement dependency is the landed `def-sfb-rational-highest-weight-data`, whose
canonical coordinate Hopf algebra and contragredient predicate are used directly.

Source read: Mathieu, *Tilting Modules and their Applications* (2000), online PDF
https://www.imsc.res.in/~knr/vdk/mathieu.pdf, printed pp.150--155, in particular
Section 2's coaction/action description, the definitions of V(lambda) and
Delta(lambda), Lemma 2.1 and the opening of the proof of Lemma 2.3. The latter
uses the full hyperalgebra for cyclicity before imposing the restricted-weight
hypothesis for the restricted enveloping algebra. The node's eight-step evaluation
and rank-one proof is included in the theorem docstring. Also read the current
latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof (3).
The lemma is a supporting node, not that blueprint unit's statement.

Hypotheses matched against the node:

- `F : Type u`, `[Field F]`, `[IsAlgClosed F]`, `p`, `[Fact p.Prime]`, `[CharP F p]`
  give exactly the algebraically closed field of positive prime characteristic.
- `S T B U : Grp (Over (Spec (.of F)))` are actual group schemes. `hS` is the
  recorded `IsSemisimpleGroupScheme S.X`: smooth, connected, affine, finite type
  and no nontrivial smooth connected solvable normal closed subgroup scheme.
  Affine instances for S, T, U expose properties implied by this geometric setting.
- `hsc` spells out the node's simply connected condition on every semisimple S',
  every group homomorphism, surjectivity, finite scheme-theoretic kernel and its
  centrality over every commutative F-algebra. Its conclusion is `IsIso f`.
  It is the same interface as the existing simply-connected character-lattice lemma.
- `iT`, `iB`, `jT`, `hTB`, `hT`, `hsplit`, `hB` give the inclusions T in B in S,
  a split maximal torus, and the Borel. `hU` is exactly the closed, normal, smooth,
  connected, unipotent and maximal radical condition used in the Borel-pair record.
- `pT`, `hpT`, `hker`, `hBT` give the Borel projection, its identity on T, its
  scheme-theoretic kernel U, and the multiplication isomorphism U times T to B.
  These are the radical complement supplied by the recorded dependency.
- The two `IsCommMonObj` instances expose character groups, and the two `ModObj`
  instances expose tangent-weight actions. `hconjS` and `hconjB` pin them to actual
  conjugation. `Φ`, `P`, `[P.IsReduced]`, `b`, `hroot`, `hpair`, `hweights`, `hpos`
  are exactly the finite reduced root datum on actual character/cocharacter Hom
  groups from the Borel-pair theorem. `hpair` fixes the integer pairing by powers
  of the multiplicative group, and `hweights`/`hpos` fix roots and positivity by
  the actual character weights on the tangent spaces of S and B.
- `x : b.support → (Ga ⟶ U)` is a parametrization into U. `hx` says its composite
  into S is a closed immersion, T-stable and has precisely the corresponding root
  tangent space. Its image is thus the smooth connected closed normalized subgroup
  of the root-parametrization theorem (the image is isomorphic to Ga); uniqueness
  there identifies it with U_alpha. Conversely every prescribed root isomorphism
  in the node gives such an x. This neither replaces x by a differential nor chooses
  an unrelated map. The added T-stability clause was caught on the second reading.
- `n`, `e`, `he`, `hlongest` describe a representative of w0 and its torus
  automorphism: e(t)=n inverse t n, and pullback by e reverses positive roots.
  This is the characterization in `rho_regular_weyl_orbit`, also used in the
  landed simple-module-dual-highest-weight theorem. `eta` is the actual additive
  character and `hdominant` asserts all integer simple-coroot pairings nonnegative.
- `Q`, `π`, `hQ`, `hQft`, `hQqc`, `hπf`, `hπs`, `hπi`, `hπt` present the proper
  finite-type quotient and its faithfully flat right B-torsor, precisely as in the
  Borel-pair and homogeneous-line dependency signatures.
- `line : AssociatedCharacterLineBundle.Presentation ... (pT ≫ e.hom ≫ eta.toMul)`
  is L_(w0 eta)=M_(-w0 eta). Its right quotient action is the inverse of that
  character, namely (-w0 eta)(pT(b)) on z. `eV` and `heV` are the recorded canonical
  identification of its actual global sections with inverse-character right
  semi-invariants. They specify the given quotient line bundle rather than an
  arbitrary vector space. Their existence is the homogeneous-line-sections theorem.

Conclusions and definitions matched clause by clause:

- The first two conjuncts are `Nontrivial (sections Q line.L)` and
  `FiniteDimensional F (sections Q line.L)`: nonzero and finite-dimensional V_eta.
- The existential `c` has the two existing `HopfAction` coaction laws. The following
  explicit equation on every A,s,g,v says that contracting c at s and evaluating
  the section function at g gives f_v(s inverse g). Thus this is exactly left
  translation, including arbitrary scalar extensions.
- The existential `d` has the same rational coaction laws and the existing
  `RationalHighestWeight.IsContragredient c d` condition. Its contraction identity
  with the coordinate antipode is equivalent to (g ell)(v)=ell(g inverse v) after
  every scalar extension, and determines the dual action uniquely.
- `distributions U` is the set of full convolution-dual elements annihilating some
  power `(ker epsilon)^(r+1)`. A functional factors through F[U]/m^(r+1) exactly
  when it annihilates that ideal, so this is exactly the union in the node, embedded
  in the existing `WithConv (Module.Dual ...)` convolution algebra. Product and
  unit are Mathlib's `LinearMap.convMul` and counit; no additional algebra is chosen.
- `distributionAction` is `(TensorProduct.rid ...).toLinearMap` composed with
  `a.ofConv.lTensor` and c. This is precisely (1 tensor a)c.
- `coordinateEvaluation` uses the affine isoSpec morphism and the inverse of
  Mathlib's `Spec.mapMulEquiv` to get the canonical algebra hom on the coordinate
  Hopf algebra. This handles its scalar presentation without an equality assumption
  or an arbitrary comparison. `rootDistribution` composes it at the universal
  additive point X with `Polynomial.lcoeff F n`, giving exactly [t^n]x_i^* f.
- `∃ w`, `w ≠ 0` give a nonzero dual vector. Its displayed restricted coaction
  equation is `w tensor characterElement (-eta).toMul`, the full character weight
  -eta on all algebras, rather than the differential weight.
- `Submodule.span F {z | ∃ a ∈ distributions U, z = distributionAction ... a w}=⊤`
  says exactly W_eta=Hw with the linear span convention stated in the node.
- The final universal quantifiers cover every simple-root index i and every natural
  k with integer inequality `<eta,alpha_i coroot> < k`. The coefficient distribution
  kills w. There is no condition `<eta,alpha_i coroot> < p` anywhere.

Dependency declarations read and reused:

- Mathlib `Field` (Algebra/Field/Defs.lean:180), `IsAlgClosed` (FieldTheory/
  IsAlgClosed/Basic.lean:62), and `GrpObj` (CategoryTheory/Monoidal/Grp.lean:43);
  the algebraic-closure node is used through its explicit algebraically-closed clause.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`,
  `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`
  and `additiveParameterPoint`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit`,
  `AlgebraicGeometry.rho_regular_weyl_orbit`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`,
  `AlgebraicGeometry.exists_homogeneousLineBundle_sections`, with the public
  `AssociatedCharacterLineBundle.Presentation`, `sections`, `pullbackCoordinate`
  and `RhoSection.sectionModule`, `evaluate` from its defining imports.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`,
  `coordinateAlgebra`, `coordinateHopf`, `coordinateMap`, `characterElement`,
  `IsContragredient`, and the existing `HopfAction.Coassociative` / `Counital`.

All recorded and stated proof-dependency modules are imported. The boundary-section,
opposite-root-SL2 and root-intersection-product nodes have no Lean module in the
read node records, so there is no recorded module to import for those proof-only
inputs. They are named in the proof docstring; they are not needed to type this
statement. No statement dependency is missing or privately duplicated.

Searches actually made:

- msearch LeanFinder: "Dual of a dominant induced algebraic group module generated
  by distributions of the positive unipotent radical from its lowest weight vector".
  Eight LieModule weight/chain hits; none is the algebraic-group distribution result.
- msearch Loogle: "Representation, Coalgebra, Module.Dual". Zero hits.
- msearch grep: "DistributionAlgebra|distributionAlgebra|hyperalgebra|lowestWeight".
  Zero Mathlib hits.
- msearch LeanSearch: "distribution algebra affine group scheme finite order linear
  functional augmentation ideal". Eight hits on monoid algebras and finite-group
  Tannaka duality; none defines the required finite-order distribution object.
- msearch grep: "pointEvaluation|eval.*AlgHom|ΓSpecIso|coordinate", subdirectory
  AlgebraicGeometry/Group: Group/Affine.lean hit. Reading that file found the existing
  `Spec.mapMulEquiv` used for the canonical evaluation helper.
- rg of lean/WeilConjectures and lean/Sheaf for the item id, distributionAlgebra,
  DistributionAlgebra and lowest/distribution combinations found no exact statement.
  Broader distribution/coaction searches found the existing Borel Kostant comparison
  and rational highest-weight data. The former uses the same finite-order condition
  inline and proves a comparison, not this cyclicity or a duplicate distribution type.
- tools/lean_names_upstream.py show and rg of dag/lean_names_upstream.json found no
  item declaration. blueprint_refs.py search "distribution algebra" returned zero
  blueprint nodes; ancestor returned None for the inherited created-node chain.
- Read the withdrawn CompactObject example and its current upstream node binding;
  use the current public-import, module-docstring, declaration-docstring conventions.

Edge cases: For S=1, b.support is empty; no rank positivity or nonempty-root hypothesis
occurs. The associated quotient is Spec F, the line trivial, V=W=F. The augmentation
ideal of F is zero and all linear functionals have order zero, so H=F; take w=1.
For eta=0, hdominant permits all pairings zero, and the final relations start at k=1.
For SL2 and eta=m omega, including m=p and larger, the cyclicity uses all coefficient
functionals and the root relation only kills orders above m; it does not incorrectly
replace distributions by first derivatives. k=0 is admitted as a distribution but
cannot satisfy the strict inequality when eta is dominant. Test-algebra quantifiers
use the scheme/field universe u, admitting the coordinate algebra and universal
polynomial test point, including nonreduced algebras. No characteristic is excluded.

Validation: scompile.py compiled both the sandbox form and the final module name
cleanly (7.3 s and 7.5 s in the final run before delivery checks). All binders and
universes are explicit (`autoImplicit false`); all lines are at most 100 characters.
No statement dispute, correction, new independent notion, or dependency repair was needed.

## Second reading by Q125

A fresh pass over the node and final file was performed by this same dispatcher
worker; no separate agent was started, as the human brief explicitly prohibits it.
The maintainer's independent mathematical review remains the independent reading.
This section records the actual second pass, not a claim of a different reviewer.

The pass checked the signs in the quotient action and in eV: the character of line
is w0 eta, so the regular functions have right character -w0 eta; the dual vector
has character -eta. It checked that V is actual global sections, d is the unique
canonical contragredient and the translation equation tests all algebras. It found
that the first draft's root embeddings specified tangent space and closedness but
omitted T-stability. Added `TorusCharacterTangent.IsStable T S ...` to hx, making
root-subgroup uniqueness applicable exactly as the dependency states it.

It also checked the scalar discrepancy between RhoSection.Coordinate and the Hopf
coordinate algebra. Replaced the attempted direct reuse of RhoSection.evaluate on
the Hopf tensor factor with `coordinateEvaluation` through the existing affine
Spec.mapMulEquiv; this supplies the canonical map without a scalar-identification
hypothesis. Removed the unnecessary `IsLeftTranslation` wrapper and wrote that
condition directly in the theorem. No helper is a hollow definition and the only
postponed theorem is the matching item theorem. Finally rechecked the empty-root,
zero-weight and unrestricted SL2 weight cases, every hypothesis listed above,
span rather than set equality for Hw, and the strict integer/natural truncation
inequality. The item node's statement and accepted proof remain verbatim.
