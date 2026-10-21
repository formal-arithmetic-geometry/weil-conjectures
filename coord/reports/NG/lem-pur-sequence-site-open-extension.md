## Worker report

Item: `lem-pur-sequence-site-open-extension`, group NG, stage 2, 2026-10-21.
Module: `Sheaf.Paper.SequenceSiteOpenExtension`.
Main declaration: `WeilConjectures.SemilinearSections.sequenceSiteOpenExtension`.
Only the main theorem has `sorry`; all helper definitions have actual data or define
explicit predicates/structures. The node is unchanged outside `lean`.

The theorem existentially packages the geometric localization, the exact module
adjunction and its prescribed level comparisons. It also asserts their actual
ordinary and derived transition equations, scalar preservation and the normalized
ordinary unbounded derived adjunction. No coefficient flatness, surjectivity,
Noetherian hypothesis, boundedness or cartesianness is assumed.

Hypothesis and clause correspondence:

* Schemes and open immersion: `(W : Scheme.{u}) (V : W.ProEt)
  [IsOpenImmersion V.hom]`. An arbitrary open immersion j into W is the weakly
  etale object `ProEt.mk j`; its domain is `V.left`. Thus this is the original
  open immersion, not a separate open subset or an auxiliary morphism.
* Small pro-etale sites and sizes: `Scheme.ProEt.topology W`, with site objects
  in u+1 and morphisms in u. Coefficients are in `max (u+1) r`; r is independent.
  Generic helper signatures retain independent c, v, r and the actual slice
  category has object universe `max c v`. The existing `EssentiallySmall`
  size instance is used. The scalar ring has its own arbitrary universe s.
* Strict tower: `B` and the adjacent actual maps `τ`. The recorded `rings` and
  `coefficientMap` compose these maps, so there is no replacement of the actual
  tower by objects with unspecified transition arrows. Index n in Lean means
  paper index n+1; every positive level, equality index and triple is included.
* Restricted ring C_n: `openTower` is `(B n).over V`; `openTowerMap` is
  `(J.overPullback CommRingCat V).map (τ n)`. These are actual sectionwise
  restrictions of objects and ring maps. The site `J.over V` is the canonical
  localized presentation of the domain's pro-etale site, by the recorded
  `Scheme.ProEt.sliceEquiv W V` and its covering identification.
* Sequence sites and semilinear modules: `coefficientSequenceTopology`,
  `systemRing` and `Systems` from the recorded dependency. The canonical
  `completionSystemEquivalence` is the identity equivalence of this model;
  no second system category or different derived category is introduced.
* Geometric morphism: `SequenceOpenOrdinary.geometric` uses
  `RingedToposMorphismOfUniverses`. It includes inverse and direct image,
  their adjunction, left exact inverse image, structural ring map and the
  normalized induced module direct image.
* Levelwise inverse image: `inverseUnderlying` identifies its underlying
  presheaf functor with restriction along `(𝟭 ℕ).prod (Over.forget V)`.
  This is a natural isomorphism, so morphisms as well as objects are retained.
* Localization at the constant represented subterminal: `H`,
  `constantRepresentable : H.obj ≅ Prod.snd.op ⋙ uliftYoneda.obj V`,
  and `subterminal`. `slice` identifies the source sheaf topos with `Over H`;
  `localization` identifies inverse image with `Over.star H`, the product
  localization functor. It does not assert representability of H by an object
  of the sequence site.
* Ring inverse image identifies B with C: `ring_identity` is the equality
  of the structural map with the identity on each actual ring section under
  `inverseUnderlying`. The source ring is exactly `systemRing` of `openTower`.
* Module restriction L: `L_obj`, `L_map`, `L_restrict` specify section modules,
  morphism maps and presheaf restrictions, including horizontal arrows.
  `moduleUnderlying` links L to the geometric inverse image and
  `moduleInverse : L ⊣ geometric.modules` links it to the induced direct image.
* Extension by zero: `Jfun ⊣ L` is `adjunction`, so Jfun is geometric module
  extension by zero. `additive`, `limits`, `colimits` assert exactness.
  These are fields in the existence conclusion, never extra hypotheses.
* Level value and naturality: `level n` is the natural isomorphism
  `Jfun ⋙ evaluation n ≅ evaluation_open n ⋙ localizedSystemExtension (B n) V`.
  The last functor is the recorded extension presheaf followed by actual module
  sheafification. Naturality of the iso specifies the value on all system maps.
* Every m≥n transition: the predicate `Transitions` is the equation of actual
  module maps after the two level identifications: apply the level-m open
  extension to the recorded open transition, apply `coefficientRestriction`,
  then the prescribed coefficient comparison. The auxiliary
  `coefficientRestriction_section` fixes the identity between the iterated
  restricted tower coefficient map and restriction of the iterated original
  map. This avoids trying to identify proof-generated composites by reduction.
* Coefficient comparison: `SequenceOpenCoefficientData.comparison φ` has type
  `Res_(φ|V) ⋙ j_!,R ≅ j_!,S ⋙ Res_φ`, the same direction as the node.
  `summand` fixes this iso on each original extension-presheaf summand using
  `openExtensionSection`, which is the already normalized adjunction unit.
  Both additive sheaves are the same sheafification of the same direct-sum
  presheaf; equality on all these generators is precisely the identity on
  that common underlying additive sheaf. It excludes arbitrary automorphisms.
* Composition and identities of coefficients: `composition_section` and
  `overComposition_section` normalize the restriction-composition isos by
  identity on underlying groups. `comp` is the comparison cocycle equation,
  and `identity` is identity on all sections for the identity coefficient map.
* Units and counits: `restriction` and `restriction_section` give the actual
  coefficient/restriction comparison. `unit` and `counit` assert both coefficient
  adjunction squares. `restrictionLevel`, `unit_level`, `counit_level` identify
  the system adjunction with the levelwise adjunctions.
* Ordinary unbounded derived descent: `derivedLevel` and `derivedComparison`
  are actual definitions using `mapDerivedCategoryCompIso` and
  `mapDerivedCategoryNatIso` applied to the specified ordinary isomorphisms.
  Their domain is the derived category of systems itself, not a diagram of
  derived categories. The functors are the termwise exact descents, via the
  recorded `mapDerivedCategoryFactors` comparison to `DerivedCategory.Q`.
  Naturality is built into these natural isomorphisms on every derived morphism.
* Actual derived transitions: `DerivedTransitions` is the corresponding equation
  with the recorded `derivedTransition`, `resD`, `e` and localized coefficient
  restriction. These are the localization of the actual ordinary maps.
* Derived units/counits: `SequenceOpenDerivedAdjunction` gives the derived
  adjunction; its `unit` and `counit` equations identify its maps on Q(K) with
  Q of the actual degreewise ordinary adjunction maps, using
  `Adjunction.mapHomologicalComplex` and `mapDerivedCategoryFactors`.
  The localization universal property makes these equalities natural on all
  derived morphisms, and transports the ordinary identity, coefficient
  composition and adjunction compatibility equations unchanged.
* Actual R-scalars: `Scalars` quantifies an arbitrary commutative ring R and
  compatible sectionwise ring homomorphisms `a n X`. `ha` is restriction
  naturality and `hτ` is compatibility with every actual coefficient map;
  this is the sectionwise expression of compatible maps R→Γ(W,B_n).
  Its conclusion gives the actual scalar endomorphisms f and g, fixes their
  action on every section and asserts `Jfun.map f = g`. Additivity plus this
  equation is the recorded `Functor.linear_iff` criterion. It passes termwise
  to complexes and through Q via the actual derived factorization; no arbitrary
  linear structure or scalar action is assumed in place of the specified action.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.OpenImmersion: `AlgebraicGeometry.IsOpenImmersion`.
* Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
* Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization:
  `Scheme.ProEt.sliceEquiv`, `sliceFrom_cover`, `weaklyEtale_localization`.
* Sheaf.Paper.SemilinearSystemModels: `Mod`, `Systems`, `DS`, `ring`, `rings`,
  `systemRing`, `evaluation`, `coefficientMap`, `res`, `transition`,
  `derivedTransition`, `e`, `resD`, and standard size/derived instances.
* Sheaf.Paper.SequenceSiteCompletionProjection: `completionSystemEquivalence`,
  `completionUnderlying`, `RingedToposMorphismOfUniverses`.
* Mathlib.CategoryTheory.Sites.Over: `Sheaf.over`, `GrothendieckTopology.over`,
  `overPullback`, and the actual `Over.forget`.
* Sheaf.CategoryTheory.LocalizedModuleExactForSystems:
  `localizedSystemExtension`, `localizedSystemRestriction`,
  `localizedSystemAdjunction`, and their exactness instances.
* Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  `SheafOfModules.restrictScalars` (through recorded `res`).
* Mathlib.Algebra.Homology.DerivedCategory.Basic and ExactFunctor:
  `DerivedCategory`, `Q`, `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`.
* WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  `Functor.mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`.
* WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction:
  `Adjunction.mapHomologicalComplex` (in the dependency import closure).
* Mathlib.CategoryTheory.Linear.LinearFunctor: `Functor.Linear`, `linear_iff`.
* Proof imports retain the recorded RingedSheafSliceAdjunction,
  DiagramSiteRealization, RingedPresentationTransport, adjunction mates and
  Localization.Predicate APIs. These supply the proof route in the docstring;
  their smaller-universe slice interface need not be generalized or replaced
  to state this node, whose geometric interface already has independent sizes.
* The size-convention node is metatheoretic, with no Lean declaration to import.

Sources opened: Stacks sites-modules.tex, extension-by-zero lemma and its proof
(03DI), exactness lemma and proof (03DJ), module sheafification (03CY); the
blueprint main-20261015 compact-support representative-independence proof, first
sentence. The node's eight proof steps are rendered in the main theorem docstring.

Edge cases checked before finalizing:

* Empty open V: the constant represented sheaf remains subterminal, the localized
  presentation is valid, and no nonempty assumption is imposed. Empty summand
  sets give the zero module, as in the actual extension presheaf.
* Identity open: coefficient comparison and extension identities remain included.
* Zero rings and zero modules: no nontriviality assumption, scalar maps may be zero.
* Arbitrary nonflat and nonsurjective coefficient transitions: restriction and the
  additive sheafification comparison use no flatness or surjectivity.
* Equality m=n and all composites: `≤` includes equality, `identity` fixes the
  comparison at the identity map, and `comp` includes identity factors.
* Unbounded complexes and arbitrary derived morphisms: no boundedness predicate;
  natural isomorphisms are defined on `DS`, with its standard Q localization.
* Site object and morphism universes remain distinct. Raising coefficient r and
  scalar s is allowed. An open immersion is neither assumed qc nor proper.

Existing-declaration searches (prescribed msearch wrapper plus local rg):

* LeanFinder: "Open localization of a ringed sequence site has extension by zero
  computed levelwise, commuting with restriction of scalars". Eight hits, including
  ModuleCat.Tilde.openToLocalization and SheafOfModules.mapFree; none states this node.
* Loogle: "SheafOfModules, CategoryTheory.Adjunction". Eight generic adjunction
  hits, including sheafificationAdjunction and overMapPushforwardAdj; none compares
  open extension of variable-coefficient semilinear systems.
* msearch grep: "sequence.*[Oo]pen|[Oo]pen.*sequence|extensionByZero", CategoryTheory.
  Two unrelated sequence hits; no statement of this comparison.
* LeanSearch: "Extension by zero of module sheaves on an inverse sequence site is
  computed levelwise and commutes with restriction of coefficients". Eight hits,
  including SheafOfModules.over and unrelated colimit/zero lemmas; no match.
* rg on both lean/WeilConjectures and lean/Sheaf for this node id: no existing module.
* Broader rg for open extension/scalar/sequence names found existing constant-ring
  finite-coefficient material (OpenScalarSiteCoherence, EtaleOpenScalarCoherence,
  OpenFactorCoherence), not this arbitrary ring-sheaf tower assertion.
  The existing extension presheaf, restriction, scalar restriction and semilinear
  systems are used directly, rather than duplicated.

No statement correction, new DAG node, dependency repair or STATEMENT-DISPUTED issue.
Helper structures are the data of this very theorem, not independent new notions.

Validation: prescribed scompile.py compiles the entire delivered file cleanly both
in sandbox and at its real module name, under the unchanged 60-second limit.
The final version includes the derived adjunction unit/counit normalization; the
last compile reported 38.4 s and 36.4 s, with no warnings or errors.

## Second reading by NG

A second complete source-to-node reading was performed by this worker, since the
brief explicitly prohibits starting another agent. Independent mathematical review
is left to the maintainer as specified in the task, not claimed here.

I reread the final node statement and all final declarations. Open immersion and
all strict coefficient maps are bound. The localized domain is the recorded canonical
slice presentation, not an unrelated site. Its ring and structural map retain actual
sections. The constant represented open sheaf is explicitly subterminal; no sequence
site representing object is assumed. The extension is exact and adjoint to the
specified restriction; each level and actual transition is compared naturally.
The coefficient iso is normalized on generators, includes composition and identity,
and has both unit and counit squares. The ordinary and unbounded derived system
categories use the recorded models. Derived transitions and units/counits are the
localization of actual maps, not objectwise assertions on a diagram of D-categories.
Finally scalar preservation states equality of the actual endomorphisms.

The second pass repaired a presentation problem: forming restricted tower maps by
composition and restricting composed tower maps are not definitionally identical
in Lean. I added a uniquely section-normalized coefficientRestriction isomorphism,
and used it in both ordinary and derived transition equations. This changes no
mathematical statement. I also added moduleInverse/moduleUnderlying and the derived
adjunction normalization so that no geometric or unit/counit clause is merely
mentioned in prose. Universe annotations now use the genuine slice object universe
and canonical standard localization instances. No theorem proof was filled in.
