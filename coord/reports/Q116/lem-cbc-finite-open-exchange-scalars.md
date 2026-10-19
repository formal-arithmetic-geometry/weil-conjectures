## Worker report

Item: `lem-cbc-finite-open-exchange-scalars`. Group: Q116. Stage 2 only: every theorem
introduced in this packet has proof `sorry`; every definition has actual data. The module
is `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`, in namespace
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars`. The primary declaration is
`exchange_restrictScalars`; the node's `lean.declarations` lists the entire statement bundle,
including the other clauses and the canonical comparisons needed to type them.

The interrupted packet had a source file, an unchanged node copy and search logs, but no
report and no Lean record. The required first `deliver2.py --no-push` failed for the missing
`## Worker report`. Its first compile then exposed a duplicate public declaration in the
legacy `LowerShriek.OpenImmersion.BaseChange` import. Inspection of the dependency record
showed that the published replacement is already `FiniteOpenBaseChangeNormalized`.
The packet now uses that recorded interface. The inherited expressions also used a ring
homomorphism in the exchange's scheme-map position and applied a pullback to a sheaf on
the wrong scheme. Those expressions were repaired; no original mathematical statement
was changed.

### Hypotheses and clauses

* The four schemes and the arrows of the open square are the explicit binders
  `{U' U X' X : Scheme.{u}}`, `gU`, `j'`, `j`, `g`. Both open-immersion assumptions are
  `[IsOpenImmersion j]` and `[IsOpenImmersion j']`. Commutativity is
  `h : gU ≫ j = j' ≫ g`, and cartesianness is `hsq : IsPullback gU j' j g`, exactly the
  signature of the recorded normalized base-change dependency. These are the properties
  of `OpenImmersionSquare`; its chosen pullback identification does not enter a canonical
  adjunction mate. No arbitrary isomorphism of schemes or extra condition on `g` is used.
* Finite commutative coefficients and every ring homomorphism are
  `{B C : Type (u + 1)} [CommRing B] [CommRing C] [Finite B] [Finite C] (a : B →+* C)`.
  There is no injectivity, surjectivity, flatness or nonzero-ring assumption.
* `coefficients` and `Modules`, imported from `StrictConstantTowerOperations` through the
  recorded base-change dependency, are the actual constant commutative ring sheaf on
  `Scheme.ProEt.topology X` and its `SheafOfModules` category. `coefficientMap` is the
  constant-sheaf functor applied to `CommRingCat.ofHom a`. `res` is the existing
  `Scheme.proEtaleRingRestrictScalars`, hence Mathlib's `SheafOfModules.restrictScalars`.
  It changes the action and retains the underlying abelian sheaf. These are neither
  completed coefficients nor arbitrary substitutes for the constant sheaves.
* Inverse image is the recorded `modulePullback`, along the canonical constant-preserving
  `constantRingIso`. `coefficientSquare` explicitly states its naturality in `a`.
  `pullRes` specializes the published `proEtaleRingRestrictionPullbackInv`, whose data are
  the mate of identity on direct-image sections. `pushRes` specializes the corresponding
  identity-on-sections direct-image comparison. No choice of an unnormalized natural
  isomorphism is made.
* Extension by zero is the recorded `moduleJ` with its `moduleJAdj`. `openResMap` is the
  inverse mate of `pullRes.inv` under the two open adjunctions. `openResMap_isIso` states
  invertibility using the direct-sum/sheafification construction of Stacks 03DI.
  `openRes` packages exactly this map as an isomorphism. The exactness and sheafified
  construction of extension are already supplied by the imported dependency framework.
* `beta` is the inverse of the *recorded* `singleBetaInv`, using the recorded
  `singleBetaInv_isIso`. It has direction `moduleJ j ⋙ modulePullback g` to
  `modulePullback gU ⋙ moduleJ j'`, i.e. the node's beta direction.
  `betaC` is `NatIso.mapHomologicalComplex ... (.up ℤ)`, so the quantifier over `F` in
  `exchange_restrictScalars` ranges over all unbounded cochain complexes on U.
* `sourceRes` composes the canonical open scalar comparison with the canonical pullback
  scalar comparison. `targetRes` composes them in the other order. Their complex versions
  are termwise. The equation in `exchange_restrictScalars` says
  `sourceResC.hom ≫ Res(beta_C) = beta_B ≫ targetResC.hom`. Thus the equality uses the
  canonical identifications, with all endpoints made explicit, rather than equating
  differently typed morphisms or merely asserting existence of some identification.
* `open_unit_counit` states BOTH the unit equation and the counit equation for
  `moduleJAdj`, with `pullRes` and `openRes` inserted at their actual endpoints.
  `pull_unit_counit` states BOTH corresponding equations for the specified normalized
  module inverse-image/direct-image adjunction. These are sheaf equations in every
  object, hence apply termwise to every complex; the comparison maps are natural.
* `inverse_unit_transpose` states at every integer degree `i` that `betaC.inv` is
  `(moduleJAdj A j').homEquiv.symm` of the pulled-back unit followed by
  `moduleSquareG.inv`. The latter is the recorded inverse-image composition comparison,
  formed from `moduleGComp`, hence from the unit-preserving conjugate of sectionwise
  fibre-product pasting. This is exactly the displayed inverse mate of the node.
* Naturality in chain maps is part of every `NatIso` used above, on complexes, and is
  recorded more generally by `exchange_transition`: it quantifies over an arbitrary
  strict B-linear chain map `t : F ⟶ (resC a U).obj G` and gives commuting squares for
  BOTH the forward exchange and its inverse. This includes ordinary chain maps by
  identity scalar restriction, as well as every coefficient transition.
* Identity and composite coefficient maps are retained explicitly. `resId` and
  `resComp` are fixed by unique identity-on-sections characterizations.
  `scalar_identity` gives the open-extension and open-pullback identities;
  `pull_identity` gives the identity for an arbitrary scheme map.
  `scalar_composition` gives open-extension composition, and `pull_composition` gives
  pullback composition for every scheme map. All these are natural equalities, so their
  termwise images give the identities on complexes. Direct-image comparisons are
  already uniquely identity on sections. Thus identity or composite `a` is not excluded.
* For towers, `A : ℕ → Type (u + 1)`, the pointwise ring and finiteness instances,
  `a : ∀ n, A (n + 1) →+* A n`, `F` and strict `t` are exactly the node's data.
  `sourceStep` and `targetStep` insert the canonical scalar comparisons and then forget
  scalars using Mathlib's `toSheaf`; `resForget` is literally `Iso.refl`.
  `exchange_strict_towers` produces an isomorphism between the two actual
  `Functor.ofOpSequence` diagrams in abelian sheaf complexes. Its two component
  equalities fix the hom to the underlying beta and the inverse to the underlying
  inverse beta at every level. These are strict diagrams of complexes, not diagrams
  in derived categories, and every composite tower arrow is included by functoriality.
* For the last clause, `R` is an arbitrary ring sheaf on X', with maps
  `r n : R ⟶ ringCoefficients (A n) X'` and exactly the compatibility equation
  `r (n + 1) ≫ ringCoefficientMap (a n) X' = r n`. `ambientRes` is the unique identity on
  sections between the two restricted actions. `ambientSourceStep` and
  `ambientTargetStep` are R-linear chain maps. `exchange_ambient_towers` supplies the
  corresponding actual strict-tower isomorphism in R-module complexes, fixing BOTH
  components to the restricted finite exchanges. This includes an ambient action
  obtained by pullback from a ring sheaf on another scheme.
* No quasi-compactness, constructibility, boundedness or etale-origin binder occurs.
  The site has scheme object universe `u+1`, morphism universe `u`, and module values
  in `u+1`; no site-universe equality was imposed. `set_option autoImplicit false`
  prevents auto-bound variables. The sole universe is declared explicitly.

### Dependencies read and used

The nine original dependency nodes and their complete statements and recorded Lean
interfaces were read. In particular:

* `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `AlgebraicGeometry.OpenImmersionSquare`,
  extending `ChosenCartesianSquare`, supplies the interpretation of the square properties.
* `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`:
  `StrictTower.singleBetaInvApp`, `singleBetaInv`, `singleBetaInv_isIso`, `singleBeta`,
  and `moduleSquareG`. This is the current record of
  `lem-cbc-proetale-extension-zero-base-change`; it reexports
  `StrictTowerOpenExtension.moduleJ/moduleJAdj` and
  `StrictConstantTowerOperations.coefficients/Modules/modulePullback/moduleGComp`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `Scheme.sfIntrinsicConstantModuleAdjunction`, the record of
  `def-weil-proetale-inverse-image`, and its reexported original
  `ProEtaleInverseImage.proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, and
  `proEtaleConstantInverseImageMap` were read. This packet uses those original ring-site
  operations through the normalized constant-ring interface of the base-change dependency.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the Mathlib match of `def-pc-sheaf-restrict-scalars`.
* `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; current source was read with
  `scompile.py --source`. The direct-sum formula and empty/unique-lift cases were checked.
  The existing normalized extension already implements this notion via its adjunction;
  no second presheaf construction is introduced here.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction` were read at the
  identity ring map. Module sheafification remains the existing construction.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`:
  `proEtale_extension_by_zero` and `openExtensionScalarMap` were read, including all
  exactness, adjunction, complex, stalk and scalar clauses. Its fixed-module presentation
  is not redefined; this packet uses the recorded base-change module's constant-ring
  coordinates and its open adjunction to avoid mixing incompatible legacy imports.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientModulePullback_exact` and `finiteCoefficientModulePullback_tensor`
  were read. The module pullback used here is the existing commutative constant-ring
  tensor pullback through the canonical coefficient isomorphism, already exact in the
  imported `StrictConstantTowerOperations` interface.
* `WeilConjectures.CategoryTheory.SiteMorphismComposition`:
  `CategoryTheory.siteMorphism_composition`, including its unit-preserving uniqueness
  clause, was read from current source with `scompile.py --source`. The canonical
  composition used here is the existing specialized `moduleGComp/moduleSquareG`.
* One already-landed dependency was added to `stmt_deps` as authorized by brief-stage2
  section 5: `lem-weil-pbc-ring-sheaf-change-adjunction`, module
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. Its full statement and
  source were read. This packet directly uses `Scheme.proEtaleRingRestrictScalars`,
  `proEtaleRingRestrictionDirectImage`, `proEtaleRingRestrictionPullbackInv` and its
  invertibility theorem. Adding the existing dependency prevents a private copy of
  these canonical scalar comparisons. No dependency record is repaired or overwritten.

Only the normalized base-change module, the existing ring-sheaf comparison module and
Mathlib's complex/sequence constructors are imported directly. Other dependency
notions are supplied through those modules' public import closures. In particular the
legacy open base-change module is intentionally absent because the concrete first
compiler diagnostic showed it imports an overlapping `upperStarIsoLowerStarInv`.

### Edge cases

Checked against the construction and endpoints: identity coefficient maps; two
composable coefficient maps; zero coefficient ring (no nontriviality assumption);
empty U and U'; identity open immersion; identity g; zero and unbounded complexes;
a constant tower; a single adjacent transition; composites of transitions; nonsurjective
coefficient maps; quotient systems such as Z/l^(n+1) to Z/l^n; and arbitrary compatible
ambient actions. Extension on the empty open and zero coefficients gives zero maps
and the zero-object isomorphism; the inverse-unit formula has the same normalization.
At an identity open, it is the canonical inverse-image comparison. In a constant tower
the diagrams reduce to ordinary naturality. No node fault or disputed statement was
found. No mathematical statement correction or new definition node was necessary.

### Searches

The saved search log was retained, and the following actual searches were inspected:

* msearch grep `extensionByZero|lowerShriek|singleBeta`: 0 Mathlib hits.
* msearch loogle `"extensionByZero"`: 0 hits.
* msearch leanfinder `Canonical extension by zero base change commutes with restriction
  of scalars along finite coefficient ring homomorphisms`: 8 unrelated IsBaseChange
  algebra hits, no matching sheaf exchange statement.
* msearch grep `finiteOpenExchange|openImmersionLowerShriekBaseChangeIso` in the upstream
  tree: 25 hits, predominantly etale derived base-change modules. These do not state
  coefficient restriction, the inverse-unit normalization and strict varying towers.
* msearch leanfinder `Open extension by zero exchange inverse adjoint mate commutes with
  coefficient restriction and strict inverse system transitions`: 8 order-theoretic
  `InverseSystem` hits, no sheaf exchange result.
* msearch loogle `SheafOfModules.restrictScalars`: four hits, including the exact
  existing definition and additive instance, reused here.
* Direct rg searches in both the upstream and `lean/Sheaf` trees for the item id,
  `FiniteOpenExchangeScalars`, `finiteOpenExchange`, base-change/scalar names and
  strict-tower comparisons found the recorded normalized base-change module and the
  generic ring-sheaf scalar comparison. Those interfaces were read and reused.
  Searches for identity/composite sheaf restrictions and `Functor.ofOpSequence`
  found Mathlib's scalar restriction definition and sequence constructor; both are
  used instead of introducing new notions. No declaration states the complete item.

### Validation

All compiles use the prescribed `scompile.py`; there was no global build or direct
Lean invocation. The scalar exchange core and unit/counit/identity/composition clauses
passed separate earlier full-file compiles while constructing this same module.
Final complete-file compilation and delivery dry run are recorded below after completion.

## Second reading by Q116

This is the dispatched worker's separate self-check pass; the independent maintainer
reading is performed after delivery, as the dispatch brief specifies. No other agent
was started and no independent reader is being claimed here.

I reopened the unchanged node and checked each clause against the declarations listed
above. The initial saved draft failed both typing and completeness: it used sheaves
instead of complexes and did not state the inverse normalization or actual tower
assertions. The repaired file uses the recorded `singleBetaInv` and its open-unit
transpose, gives both scalar adjunction equations, and explicitly fixes both maps of
actual strict towers, including ambient actions. The successor map types use
`A (n+1)`-linearity into restriction from `A n`, in the same direction as the node.
Source and target comparison orders and beta's direction were checked independently
at each endpoint. Identity/composite scalar coherence includes arbitrary scheme maps,
not only open maps. Every data choice from a postponed result has a unique section
normalization, or is inversion of an already specified invertible map.

### Resumed self-check, 2026-10-17

The required initial dry run of the saved packet exposed invalid local reducibility
changes, including changes to imported declarations and a repeated irreducible
attribute. Removing them entirely made elaboration exceed the unchanged 60-second
limit. The repair scopes the irreducibility attributes to each tower theorem and
only marks this module's own helper definitions; imported declarations keep their
published attributes. Both scopes close normally, so the ambient transition
constructions elaborate with the original helper transparency. No mathematical
signature or construction changed. The declaration list now also records the two
ring-sheaf abbreviations that were already present in the saved module.

I reread the current normalized base-change module, its inverse-unit transpose,
the constant-ring module operations and their normalized composition, the open
adjunction, and the scalar-change adjunction comparison. The source blueprint
paragraph and every node clause agree with the packet. The current upstream
extension-presheaf and site-composition sources were fetched through
`scompile.py --source`; no extra copy of those notions was introduced.

The final elaboration repair also gives explicit result types to `resC`, `betaC`,
`sourceResC`, and `targetResC`, and uses the same type-transparency option as the
normalized dependency modules. These annotations spell out the existing termwise
functors and isomorphism endpoints; no hypothesis, map or conclusion changes.

Validation: the complete module passed `scompile.py` on 2026-10-17 with no errors
or warnings, both as `Sheaf.Stage2.Sandbox0` and under its delivered library name.
The library artifact check took 42.5 seconds under the unchanged 60-second limit.
The recorded primary signature matches the file verbatim, and every Lean line
is at most 100 characters. The complete file has 16 named postponed theorems,
each with the item's blueprint tag and a source/proof docstring; all definition
data are explicit constructions or uniquely normalized adjunction/section data.

Required `deliver2.py Q116 lem-cbc-finite-open-exchange-scalars --no-push`
passed the server preflight and both per-file compile checks: `OK (dry run)`,
commit `1c895bde92` (nothing pushed). The final delivery retains the checked Lean
file and node record.
