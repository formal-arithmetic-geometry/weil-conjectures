## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` states
`AlgebraicGeometry.Scheme.etaleOriginProperOpenInterchange`. It constructs the specified
five-arrow isomorphism and its conjugate by a retained origin pair; the only postponed
proof is the named theorem, with the complete nine-step DAG argument in its docstring.
All other declarations have actual data assembled from canonical published functors,
comparison isomorphisms, and their universal localization compatibilities.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`. Fixed-scalar
  sheaves use `ULift.{u+1,u} A` in `ModuleCat.{u+1}`, precisely the existing size
  convention; the canonical realization returns to intrinsic constant-A modules.
- Schemes V,T,W are arbitrary `Scheme.{u}`, p and i their named morphisms;
  `[IsProper p]` and `[IsOpenImmersion i]` are the exact geometric hypotheses.
  U, k and r are `pullback p i`, `pullback.fst p i`, `pullback.snd p i`.
  The proper/open instances on r,k follow by base change and are not extra binders.
- All four Noetherian hypotheses are explicit `IsNoetherian` instances, including
  the pullback. Mathlib defines this as locally Noetherian and compact, equivalently
  quasi-compact. No finite-dimensional, regular, separated-scheme or finite-CD
  assumptions are inserted.
- Ordinary uncompleted pro-etale categories are `proEtaleDerivedCategory T A`;
  Rp and Rr are `proEtaleConstantDerivedDirectImage`; open extension is
  `sfIntrinsicDerivedOpen`; open inverse image is `sfIntrinsicDerivedPullback`.
- The exact comparison a is `etaleOriginOpenComparison`: the published fixed-scalar
  `comparisonUpperStar.mapDerivedCategory` followed by the canonical
  `sfIntrinsicDerivedEquivalence.functor`, with no newly chosen ring map.
- `etaleOriginOpenDirectImageComparison` is exactly the counit-normalized
  `fixedComparisonDirectImageMatePlus`, included into D by the published
  `rightDerivedFunctorPlusCompatibility` and `mapDerivedCategoryPlusCompatibility`,
  and transported by the K-injective-normalized
  `sfIntrinsicDerivedDirectImageComparison`. It is not an arbitrary endpoint iso.
- e is `etaleOriginOpenExtensionComparison`: exact termwise descent of the recorded
  `openImmersionLowerShriekComparisonUpperStarIso`, with the realization unit/counit
  inserted by `etaleOriginOpenCoordinates`. Those coordinates cancel the realization
  equivalence at the intermediate scheme; they do not change extension by zero.
- Gamma-e is `etaleOriginOpenEtaleInterchange`, selected from the SAME
  `Etale.unboundedProperOpenInterchange` existential with its full representative,
  open-transpose and coherence conditions. This is permitted determined data:
  its maps on every K-injective representative are fixed by that theorem.
- M0 is the binder K in `DerivedCategory.Plus` of ordinary etale module sheaves.
  `etaleOriginProperOpenIso` is, in order: i_! b_r inverse; e_i inverse;
  a_T Gamma-e; b_p; Rp_* e_k. Its two additional Plus compatibility factors only
  identify k_! of K.obj with the inclusion of k_! K; they are the specified universal
  functor compatibility maps, not an extra mathematical arrow.
- Invertibility is asserted by the first conjunct for all K, and again on each
  witnessed conjugate. The helpers return actual isomorphisms, since every named
  comparison factor is already an isomorphism in the dependency interface.
- The retained witness is universally bound as the pair `(K, alpha)`, with
  `alpha : a_U K.obj ≅ M`. This unpacks the recorded origin-witness notion instead
  of choosing a witness. It uses the intrinsic constant-ring realization of the same
  pair; the dependency's older structure is in continuous-function coefficients.
  No separate origin predicate, existential choice, arbitrary map or new category
  is defined. Exactness of a implies that such M is bounded below.
- `witnessedEtaleOriginProperOpenIso` is the displayed conjugation: first i_!Rr_*
  of alpha inverse, then C at a_U K, then Rp_*k_! of alpha.
- The second conjunct of the witnessed assertion quantifies over EVERY second pair
  `(L,beta)` for the same M and equates the conjugated maps. Thus independence
  includes both the choice of antecedent and the isomorphism, not merely a fixed K.
- The next conjunct quantifies over N, every retained pair for N, and every map
  `f : M ⟶ N`. Its equation is the full naturality square, including maps which
  were not supplied with an etale lift.
- `etaleOriginOpenLambda` is the inverse of the RECORDED
  `proEtaleOpenRestrictionLambdaInverse`, with its invertibility supplied by
  `proEtaleDerivedOpenRestriction`. It is no alternative normalization.
  The first adjunction equation is the open unit at Rr_*M, followed by i^* C,
  followed by lambda, equal to identity. This explicitly includes the identification
  of i^*i_!Rr_*M by the invertible open unit stated in the node.
- The final equation is i_! of the recorded lambda inverse followed by the counit
  of `exceptionalOpenAdjunction i A`, exactly the specified mate formula.
- There is no ambient exceptional adjoint binder, constructibility restriction or
  all-sheaf finite-CD datum. The open is arbitrary; no separate quasi-compact-open
  hypothesis appears. All variables and universes are explicitly declared.

Dependency declarations read and used (including their docstrings):

- Mathlib: `Scheme`, `IsOpenImmersion`, `IsProper`, `IsLocallyNoetherian`,
  `IsNoetherian`, `Scheme.ProEt`, `constantSheaf`, `pullback`, its projections and
  `IsPullback.of_hasPullback`; scheme-conventions is a convention-only node.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently
  `SheafOfModules` with its existing category and abelian structure.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its public intrinsic
  operations: `proEtaleConstantDerivedDirectImage`, `sfIntrinsicDerivedPullback`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and etale derived modules:
  `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, exact termwise open extension.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, its exactness and derived descent.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, i.e. the Plus restriction of the termwise
  `comparisonUpperStar.mapDerivedCategory` used in the construction.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, `isIso_fixedComparisonDirectImageMatePlus`,
  and its counit normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and its coherence theorem.
- `Sheaf.Paper.UnboundedProperOpenInterchange`:
  `Etale.unboundedProperOpenInterchange`, with all specified normalizations retained.
- `Sheaf.Paper.RingedEtaleOriginWitness`: the retained origin pair and its canonical
  constant-ring realization; unpacked here as K and alpha in intrinsic coordinates.
- `Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction`:
  `proEtaleOpenRestrictionLambdaInverse`, `proEtaleDerivedOpenRestriction`.
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`:
  `exceptionalOpenAdjunction`, including its actual unit and counit.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`, `sfIntrinsicModuleEquivalence`;
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit`: `sfIntrinsicOpenUnit_isIso`.
- Canonical presentation coordinates from
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDerivedEquivalence`, `sfIntrinsicDerivedDirectImageComparison`.
  They are already in the public dependency closure.

Proof imports retain the stated unit-normalization, comparison-pullback,
transport-identifies-exchange, ambient-exchange and fully-faithful-unit interfaces.
The node's natural-language proof is reproduced with all its steps in the theorem
comment; no dependency is replaced by an arbitrary comparison iso.

Edge cases checked before writing: A may be the zero ring; no Nontrivial binder occurs.
Empty schemes and the empty open are admitted. Identity p and identity i are admitted,
as are arbitrary non-identity open immersions. K may be zero, a sheaf in degree zero,
or have cohomology in arbitrarily high degrees; Plus imposes only a lower bound.
Both distinct origin objects and distinct isomorphisms from a single antecedent are
covered by the independence quantifiers. Naturality allows every map between the
resulting ordinary intrinsic objects. No independent smaller testing universe is used.

Searches for an exact existing declaration:

- msearch leanfinder: “Etale proetale comparison transports proper open interchange and
  satisfies open adjunction normalization”; eight hits on etale schemes/topologies,
  no statement of this comparison.
- msearch loogle: “Functor.mapDerivedCategoryNatTrans, Adjunction.homEquiv”; no hits
  (the first queried name is absent). Existing localization NatIso and adjunction
  APIs were then read directly in the source.
- msearch leansearch: “Canonical etale proetale comparison proper open interchange
  adjunction witness independent”; eight generic open-adjunction/restriction hits,
  none gives the five-arrow identity or witness independence.
- msearch grep: `properOpen.*[Tt]ransport|[Ee]taleOriginProperOpen`; no Mathlib match.
- rg of upstream WeilConjectures and side lean/Sheaf for the item id,
  etaleOriginProperOpen and properOpen transport names: no exact match.
  `ProperOpenSiteTransport.properOpen_site_transport` was read: it assumes FINITE
  proper edges, does not handle arbitrary proper p, and does not contain the full
  intrinsic witness-independence and current lambda normalization clauses.
  `ProperExceptionalOpenBaseChange` supplies the underlying canonical map but does
  not state its five-arrow identification in the generality of this item.

No new DAG node, dependency-record replacement or statement correction is needed.
The archived main blueprint proof file still contains its earlier four-step argument;
the item's retained repaired nine-step proof and source-place qualifier specify the
extracted obligation followed here. This discrepancy is recorded rather than silently
attributing a pro-etale theorem to the etale Stacks source.

Validation: scompile.py passed both sandbox and library file checks with no errors or
unexpected warnings. The prescribed delivery dry run follows.


## Second reading by Q113

Author's final self-check (the dispatcher brief assigns independent review to the
maintainer and forbids spawning other agents): reopened the node, complete module,
and canonical dependency interfaces. Verified that k,r are the actual chosen pullback
projections, not a merely commutative square; all four schemes have exactly the stated
Noetherian assumptions. Checked the order and directions of all five factors and the
inserted Plus-to-D compatibility maps. Checked that the witness equations quantify over
both arbitrary antecedents and arbitrary alpha, and that naturality quantifies over all
maps between the intrinsic objects. Checked the first normalization starts with the
actual open unit and ends with the inverse of the recorded lambda inverse, while the
second is exactly its open-adjunction transpose. No clause was weakened or added.
The two parser line-break errors from the first compile were repaired; the completed
file then compiled cleanly in both modes. No statement or dependency correction was
required. This is not represented as an independent review.

Dry-run metadata repair: the signature field now ends immediately before the `:=`
delimiter, as required by preflight; no Lean source or mathematical statement changed.
