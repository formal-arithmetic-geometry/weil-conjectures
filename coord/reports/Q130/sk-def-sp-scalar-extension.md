## Worker report

The delivery states sk-def-sp-scalar-extension in
`Sheaf.Paper.SmoothPurityScalarExtension`. The main declaration is
`AlgebraicGeometry.ProEtale.scalarExtensionCtfFunctor`. Definitions have real data;
all six theorem declarations have `sorry` proofs. Their natural-language proofs
are in their docstrings and implement this node's three existing justification
steps. There is no statement correction, disputed statement, or dependency repair.
The current blueprint unit was read at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/_section.md`,
along with the adjacent detailed scalar-extension blueprint file.

Hypotheses and clauses, in order:

* The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. Finite commutative rings use `[CommRing A]`
  and `[Finite A]`, independently for A, B and C. The exponent assumptions are
  `hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0`, and similarly `hB`, `hC`.
  Distinct exponents are allowed. The ring maps are the actual unital
  `f : A →+* B`, `g : B →+* C`; direct extension uses `g.comp f`.
* The scheme is arbitrary `(T : Scheme.{u})`. The ambient category is exactly
  `Scheme.proEtaleDerivedCategory T A`: modules over the sheafification of the
  constant presheaf `ULift A` on `T.ProEt` with `ProEt.topology T`, followed by
  ordinary unbounded derived localization. Site objects have universe u+1,
  morphisms u, and coefficient sections/modules u+1. No site universes were
  equated; finite rings are in the scheme universe, as in the recorded ambient
  scalar functor (the section ring is canonically lifted).
* The full subcategory is the existing `spFiniteConstructibleTorCategory T A`
  from `Sheaf.Paper.SmoothPurityNormalizedTowers`, owned by
  `sk-def-sp-normalized-towers`. Its predicate `spFiniteConstructibleTor T A`
  requires an ordered finite cohomological interval, intrinsic
  `Scheme.IsConstructibleProEtaleModuleSheaf` in every degree, and
  `Scheme.HasFiniteProEtaleTorAmplitude`. An ordered finite interval is
  equivalent to finite support in integer degrees, including empty support.
  The local duplicate predicate and category have been removed.
* The displayed object K_B and morphism u_B are exactly the object and map of
  `scalarExtensionCtfFunctor`. It is `ObjectProperty.lift` of the inclusion
  followed by the recorded `scalarExtensionFunctor f T`. Thus inclusion yields
  the ambient tensor functor definitionally on objects and morphisms. Its
  coefficient action is the action through the scalar tensor factor of that
  existing derived change-of-rings construction, not a forgotten action.
  `scalarExtensionCtf_preserved` supplies only the proof of membership, using
  clause 2 of the detailed dependency. It does not assume flatness of f or
  finite projective dimension of B over A.
* The associativity comparison is `scalarExtensionCtfComposition`. Its named
  existence/uniqueness theorem specifies, component by component after the
  full-subcategory inclusion, exactly
  `scalarExtensionFunctor_composition f g T`. This is the already normalized
  K-flat tensor associator, not an unspecified isomorphism. The result is a
  natural isomorphism of functors, so it includes compatibility with every
  derived morphism u. Its choice is from an existence-and-uniqueness theorem,
  with equality of ambient components, which fixes the object completely.
* For the coefficient convention, `scalarExtensionDiscreteRing A` is the
  commutative condensed ring of continuous functions into A. We work for any
  topology with `[DiscreteTopology A]`; this is exactly the discrete topology
  of the statement, since such a topology is uniquely discrete, and adds no
  restriction on finite commutative rings. `scalarExtensionDiscreteMap f` is
  the published postcomposition morphism of these continuous-map ring sheaves,
  bundled as a commutative-ring-object morphism. No alternative condensation
  or ring structure is defined.
* The canonical identification p_T^* underline A ≅ A_T is the existing
  `FiniteDiscreteOrdinary.Encoding.ringIso`, in the inverse direction. Its
  normalization identifies each constant section with the image of
  `canonicalAbelianMap`, defined by the strong monoidal `upperStarFromPoint`
  and `constantSchemeIso`. The source is the constant commutative ring sheaf;
  the target is the reconstructed section ring of `condensedRingObj`.
  `Encoding.ordinary_functor` fixes the forward module functor to the actual
  `sectionModuleEquivalence` followed by restriction along this ring
  identification. `Encoding.ordinaryDerived` is its termwise exact derived
  equivalence. Existence for every finite discrete ring and every scheme is
  the existing `encoding_exists`; we quantify over these already normalized
  encodings, never choose arbitrary data from a bare Nonempty theorem.
* `scalarExtensionDiscreteRestriction_existsUnique` fixes the coefficient
  restriction comparison to identity on every section (HEq accommodates the
  equality field `Encoding.ordinary_functor`; it does not forget a ring action).
  `scalarExtensionDiscreteRestrictionDerived` localizes that comparison
  termwise using `mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`.
  The scalar adjunction helpers expose the existing published derived
  adjunction, with its actual canonical monoidal and ring-object structures
  passed explicitly to avoid instance-resolution ambiguity.
* `scalarExtensionDiscreteComparison_existsUnique` fixes the comparison between
  the condensed and ordinary derived coefficient tensors by its displayed
  adjunction-unit equation. This is the canonical mate of the identity-on-
  sections restriction comparison. Thus it identifies coefficient actions,
  not merely underlying objects or some unrelated natural isomorphism.
* Finally, `scalarExtensionDiscreteComparison_tower` is the explicit commuting
  equation between the transported `CondensedRing.scalarSixTower` (clause 3 of
  det-prop-scalar-six-pullback) and the recorded
  `scalarExtensionFunctor_composition`. The intermediate functors and maps
  are written in full. `scalarExtensionDiscreteMap_comp` identifies the
  composite condensed ring map with postcomposition by `g.comp f`.
  `scalarExtensionDiscreteTower` uses that equality only to align the endpoint
  of the existing associator. Restricting the ordinary side is precisely the
  already fixed `scalarExtensionCtfComposition` above.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
  The actual ordinary derived presentation is publicly retained in
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`: the retained
  `Scheme.IsConstructibleProEtaleModuleSheaf`, with its full definition in
  `Sheaf.Paper.ProEtaleConstructibleSheaf`, and the recorded fixed-module
  specialization. The underlying `Scheme.Stratification` extends the existing
  finite constructible locally closed topological stratification.
* `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`: retained
  `Scheme.HasProEtaleTorAmplitude`, `HasFiniteProEtaleTorAmplitude`, and the
  fixed-module specialization. The interval predicate quantifies over every
  degree-zero module sheaf and K-flat resolutions, and includes a ≤ b.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: retained generic
  `SheafOfModules.DerivedChangeOfRingsCochainModel` construction, used through
  the published ambient scalar extension; no ordinary-module replacement for
  a ringed-site functor is made here.
* `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spFiniteConstructibleTor`
  and `spFiniteConstructibleTorCategory`, owned by
  `sk-def-sp-normalized-towers`. Read their full signatures and docstrings;
  they require exactly T, a commutative ring A, and finiteness of A.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`,
  `_preserves_constructible_tor`, `_composition`, its unique K-flat balancing
  specification and naturality. This is the ambient functor, not a copy.
* `Sheaf.Topology.ProfiniteCondensedRing` and its public source constructors:
  the condensed-ring type and `Profinite.continuousCoefficientRingObj` (the
  existing universe-polymorphic C(S,A) construction).
* `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `sfbPullbackFromPoint`, the alias of `upperStarFromPoint`, with its full
  test-object, adjunction and monoidal specification.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `sectionModuleEquivalence`, as used by the normalized
  Encoding. `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` supplies
  the normalized internal/sectionwise scalar comparison used in the proof
  plan; `Sheaf.CategoryTheory.SheafTensor` supplies the stated sheaf tensor.
* `Sheaf.SixFunctors.ScalarSixPullback`: `CondensedRing.ScalarSixRing`,
  `scalarSixChange` and `scalarSixTower`. The ambient associator is valid for
  arbitrary schemes; none of the finite-type assumptions used in that node's
  unrelated immersion clauses is imposed here.
* Uses the existing recorded definition dependency
  `def-pe-finite-discrete-presentation-encoding`, module
  `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`: `Encoding`,
  `canonicalAbelianMap`, `sectionEncoding` and `Encoding.ordinaryDerived`.
* Added existing recorded definition dependency
  `def-sfb-continuous-map-condensed-ring-map`, module
  `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `continuousMapRingObjMapOfUniverse` and
  `continuousMapRingSheafMapOfUniverse`.
* The recorded K-flat predicate module
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` is imported for the
  node's second justification step. Actual K-flat computations and uniqueness
  are inherited from the scalar-extension dependency, not duplicated here.

Edge cases checked against the definitions and signatures: empty schemes
(intrinsic constructibility permits a positive partition with empty stratum),
zero rings and zero complexes (no Nontrivial assumption), non-flat maps such as
Z/ell² → Z/ell, identity maps, different annihilating exponents, and arbitrary
possibly negative Tor bounds. Rings need not be fields; ell need not be
invertible on T. No Noetherian, qcqs, separated, finite-type, or etale-origin
assumption occurs. The coefficient convention imposes no topology beyond the
specified discrete one. The natural comparison is on all ambient derived
objects and hence on all objects of the full subcategory, not just degree-zero
or chosen representatives.

Searches (all run on the named read-only directories or with msearch.py):

* msearch leanfinder: `Derived scalar extension on bounded constructible proetale
  complexes with finite Tor amplitude`: 8 hits about ordinary etale algebras
  and differentials; no derived sheaf scalar restriction.
* msearch loogle: `CategoryTheory.FullSubcategory,
  CategoryTheory.ObjectProperty.lift`: no hits (unknown former identifier).
  Direct source reading finds Mathlib's existing `ObjectProperty.lift`, used
  here; it does not define this particular coefficient functor.
* msearch grep: `scalarExtension|changeOfRings` in
  `Algebra/Category/ModuleCat/Sheaf`: the existing ChangeOfRings import; no
  constructible finite-Tor restriction.
* msearch leansearch: `restriction of derived scalar extension to bounded
  constructible sheaves of finite Tor amplitude`: 8 hits, ordinary restriction
  of scalars definitions and maps; no match for this statement.
* rg in lean/WeilConjectures and lean/Sheaf for Dctf, scalarExtension,
  constructible finite Tor, finite discrete constant comparisons and
  continuous-map functoriality: found the detailed ambient functor,
  FiniteDiscreteOrdinary.Encoding and the postcomposition map, all reused.
  The generic upstream Dctf predicate uses the distinct fixed-module/etale-
  origin constructibility convention and cannot silently replace the node's
  intrinsic global-stratification convention. No full-subcategory restriction
  with this exact intrinsic predicate and ambient functor was found in the
  original search. The return identifies the existing intrinsic finite-level
  category in `SmoothPurityNormalizedTowers`; the repair reuses it.
* rg for this node's id in lean/WeilConjectures: no hits. Searches of
  dag/lean_names_upstream.json and both source trees for the new declaration
  names found no overlap. No Mathlib or project tensor, constructibility,
  Tor amplitude, scalar-extension functor, or module equivalence is copied.

Compilation uses only the prescribed scompile.py, with the default per-file
limit. The module passed both sandbox and module-path compiles before packet
validation. The final dry run and delivery repeat the prescribed checks.

## Second reading by Q130

No second reading by a worker: the dispatcher brief requires direct delivery
and forbids starting agents. The maintainer's independent review reads this
packet. The report above is the author's clause-by-clause audit, not a claimed
independent review.

## Returned-delivery repair

Read the immutable-head review for 3b3e483406c7 and compared the saved node
against the current shared base using a JSON field comparison, without Git.
The initial saved packet passed deliver2.py --no-push (229674758fe), but the
following substantive repairs are applied before delivery:

* H2: replace `lem-sf-finite-discrete-normalized-encoding` in `stmt_deps` by
  the existing definition node `def-pe-finite-discrete-presentation-encoding`.
  Only the supplied `Encoding`, `Internal`, canonical maps and termwise
  `Encoding.ordinaryDerived` occur in signatures and data. `encoding_exists`
  is mentioned as a proof route, but never invoked to choose an encoding.
  No change to the coefficient-comparison declarations is needed.
* H4: delete `scalarExtensionCtf` and `ScalarExtensionCtfCategory`, import
  `Sheaf.Paper.SmoothPurityNormalizedTowers`, and use its existing
  `spFiniteConstructibleTor` and `spFiniteConstructibleTorCategory` in the
  preservation statement, functor and associator. Add the owning node
  `sk-def-sp-normalized-towers` to `stmt_deps`. The finite-level definitions
  bind only T and A; their surrounding tower parameters ell and E do not
  occur in their signatures. Thus no coefficient-field or scheme assumption
  is introduced. Bounds versus finite support are equivalent over integers,
  including the zero complex and the empty scheme.

No mathematical statement correction, new node or dependency module is needed.
The main `lean.statement` is updated verbatim and the deleted names are removed
from `lean.declarations`. All remaining data and normalization equations are
retained. Compilation and final dry run are run on the repaired module.

Self-check of the repair: only `lean` and `stmt_deps` differ from the current
base node. The `sk-def-sp-normalized-towers` transitive statement/proof closure
contains neither this item nor `det-sp-scalar-extension-functor`, so the added
edge is acyclic. The module has no line exceeding 100 characters, explicitly
sets `autoImplicit false`, and retains exactly six named sorry theorems.
The primary `lean.statement` equals the revised file signature verbatim.
