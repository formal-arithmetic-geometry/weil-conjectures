## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport` states
`AlgebraicGeometry.ProEtale.etale_proEtale_exceptional_transport`, with one `sorry`.
The three helper definitions contain real data: intersections of the already recorded
finiteness predicates, and composition of the specified functors. They introduce no
alternative tensor, site, constructibility notion, compact support, or adjoint.

The source read was the whole final restriction paragraph of the current blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/`
`sk-prop-sf-rf-shriek-preservation.proof.md`, together with all six detailed proof steps
of this DAG node. The detailed transport is an agent-written refinement recorded by
the node; the blueprint paragraph itself does not number a Step 8. No node statement
correction is needed. No repair note exists for this item.

Hypothesis-by-hypothesis correspondence:

- The field is `(k : Type u) [Field k]`; characteristic is `[CharP k p]`. The node's
  positive field characteristic is rendered by `p.Prime`; a field has prime
  characteristic when its characteristic is positive. `_hl` says that `l` is prime,
  and `_hlp : l ≠ p` is the distinct-prime condition.
- `(A : Type (u+1)) [CommRing A] [Finite A]` is the finite commutative coefficient
  ring. `_hA : ∃ n : ℕ, (l ^ n : A) = 0` says exactly that a power of l annihilates A.
  No nonzero-ring condition is added. Coefficients are discrete in the fixed-ring
  sheaf encoding, with no topology chosen as an extra parameter.
- `X Y : Scheme.{u}`, `f : X ⟶ Y`, and `s : Y ⟶ Spec (.of k)` provide the schemes
  and their compatible k-structures; the structure map of X is `f ≫ s`.
- Each of f, s, and `f ≫ s` has the indicated `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact` binders. Locally finite type plus quasi-compact is finite type.
  Thus both the morphism and the two schemes have exactly the stated properties.
- `c : Compactification f` supplies the SAME open immersion c.i, proper map c.g,
  and factorization equation. Its intermediate k-scheme has structure `c.g ≫ s`;
  the final three geometric instances say it is separated and finite type over k.
- Both compact-support functors are the recorded
  `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`, in their respective
  Etale and ProEtale namespaces. Both use unbounded ordinary derived categories;
  no ambient pro-etale right adjoint is postulated.
- R is any chosen ordinary etale right adjoint, with its adjunction explicitly
  given by `adj`. This renders “let f^times be the ordinary etale right adjoint,”
  rather than adding an existence hypothesis beyond that datum.
- `_hR` is precisely preservation of bounded constructible finite-Tor objects.
  `exceptionalTransportEtaleObjects` uses the recorded finite-value predicate
  `Etale.DerivedCategory.isBoundedConstructible` and an ordered finite Tor interval
  in `Etale.DerivedCategory.hasTorAmplitudeIn`.

Clause-by-clause correspondence:

- The pro-etale input category is the FULL subcategory cut out by
  `exceptionalTransportProEtaleObjects A Y`. This means standard boundedness,
  intrinsic global-partition constructibility of every cohomology sheaf, and an
  ordered finite Tor interval tested against EVERY pro-etale module sheaf.
  In particular, no etale-origin hypothesis is hidden in this input predicate.
- The existential functor E gives `K_et` simultaneously for every K and every
  morphism. The natural isomorphism alpha identifies `nu_Y^* E` with the inclusion
  of that full subcategory. The first conjunction says that every E(K) is bounded
  constructible finite-Tor. This is the stated etale-origin conclusion.
- `exceptionalTransportImage A R E` is DEFINITIONALLY E then R then the termwise
  exact comparison on X. Thus its object is precisely H_K = nu_X^* f^times K_et.
  The second conjunction states the intrinsic bounded constructible finite-Tor
  property of these objects. The functor supplies their naturality in K.
- beta is a natural isomorphism between the specified composites, restricted at
  their source by `DerivedCategory.Plus.ι`. It says exactly
  `nu_Y^* F_et ≅ F_proet nu_X^*` on ALL D-plus inputs. Neither input constructibility
  nor input finite Tor is imposed in this clause.
- t is a natural transformation from H followed by F_proet to the input inclusion.
  Its displayed component equation is, in Lean's left-to-right composition order,
  `beta.inv` followed by `nu_Y^*(adj.counit)` followed by alpha. The existential hRE
  merely packages the derived boundedness of R(E(K)) for evaluating beta on D-plus;
  it is a conclusion, not a stronger preservation assumption on arbitrary objects.
- For every input K and EVERY `M : DerivedCategory.Plus (...)`, the displayed
  `Function.Bijective` is exactly bijectivity of `h ↦ F_proet.map h ≫ t.app K`.
  Its domain is Hom(nu_X^* M,H_K) and target is Hom(F_proet nu_X^* M,K).
  This specifies the forward Hom bijection as required. Naturality in M follows
  from functoriality of F_proet and precomposition; naturality in K is the naturality
  equation of t together with the functor E. Thus no arbitrary Hom equivalence or
  arbitrary counit map replaces the claimed formula.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, whose left adjoint is the existing
  `ProEtale.comparisonUpperStar (ModuleCat A) T` (left Kan extension/sheafification).
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule` and `Etale.DerivedCategory.hasTorAmplitudeIn`;
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` retains this interval predicate.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (available through the
  recorded compatibility import): ordinary derived categories and cohomology.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, using
  `Scheme.IsConstructibleEtaleModuleSheaf` from its recorded Sheaf module.
  Its existing node `def-weil-pbc-constructible-complexes` is added to stmt_deps.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, as repaired below.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`:
  `ProEtale.DerivedCategory.torAmplitudeIn`, as repaired below. Its source specializes
  `DerivedCategory.torAmplitudeIn`, tensoring with arbitrary sheaves in degree zero.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and the pro-etale
  `FiniteCoefficient.Derived.LowerShriek`: their fixed-compactification composites.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` supplies the
  ordinary adjoint existence assertion; the theorem accepts any chosen adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the canonical realization
  identifies fixed-ring sheaves with the continuous-function coefficient encoding
  of `def-weil-pbc-proetale-modules`; it is imported through the fixed-module
  constructibility dependency. The statement uses its ordinary fixed-ring encoding.

The proof-dependency imports include ComparisonTorInterval, ProEtaleExtensionZeroComparison,
ComparisonPullbackExact, ProEtaleDirectImageComparison, and CompactSupportComparisonUnit.
The finite-type-over-Noetherian and constructible-comparison nodes have no recorded module
in the current DAG, so there is no module to import for those two. The proof docstring
preserves all six steps, including the all-module Tor test and independence of witnesses.

Edge cases checked: zero coefficient ring (n=0 allowed); empty schemes and empty
strata (the positive-stratum convention permits one empty stratum); zero complexes;
any shifts and ordered Tor intervals including a=b; identity morphisms; and arbitrary
bounded-below nonconstructible M. No common stratification across all degrees or all
K is imposed. The site object and morphism universes remain distinct; A lies in the
usual coefficient universe u+1, and no universe equality or finite-rank assumption is
added. Neither this theorem nor its dependencies used here require a nonempty scheme.

Searches actually run through msearch.py, all on 2026-10-18:

- leanfinder: “etale proetale comparison exceptional adjunction compact support
  transport finite coefficients”: 8 hits, concerning condensed/profinite adjunctions;
  none states this transport package.
- loogle: `CategoryTheory.Adjunction, CategoryTheory.Equivalence`: 6 hits, including
  Equivalence.toAdjunction and transportSheafificationAdjunction; none is the theorem.
- leansearch: “transport exceptional adjunction from etale to proetale using
  comparison and compact support”: 8 hits, general sheaf adjunctions and condensed
  local constancy; none is the theorem.
- grep Mathlib/AlgebraicGeometry/Sites: `exceptional|rightDerivedUpperShriek|proetale`:
  10 site and ell-adic-cohomology hits; no exceptional transport statement.
- rg in slopmaster2 WeilConjectures, the framework, and lean/Sheaf for the item id
  and exceptional/transport combinations: no exact theorem. Read upstream
  ProEtale/Derived/UpperShriek.lean: its generic Hom equivalence is related but uses
  a chosen compactification, HasBoundedBelowUpperShriek and an etale-origin domain;
  it does not assert the present intrinsic constructible origins and preservation
  package for an arbitrary fixed compactification. It therefore is not an exact match.
- Searches for every new declaration name in Mathlib, upstream-name index, source,
  and lean/Sheaf found no collision. The existing fixed-module constructibility and
  all-module Tor declarations were found and reused, rather than redefined.

Validation: scompile.py compiled the complete module in sandbox and library placement
cleanly (3.8 s and 4.3 s reported in the final pre-delivery compile). Earlier errors
were repaired: finite type uses LocallyOfFiniteType plus QuasiCompact; derived imports
use the migrated FiniteCoefficient family to avoid duplicate comparison declarations.
There are no mathematical statement disputes or source corrections.

## Dependency modules

`def-weil-proetale-constructible-sheaf`: lean-only existing-declaration repair.
The recorded coefficient-module predicate cannot consume the fixed-ring sheaves of
ordinary compact support. The published `IsConstructibleProEtaleFixedModuleSheaf`
states exactly the same global finite partition, local constancy and finite-stalk
condition in that presentation, without any etale-origin assumption. Its full definition
and docstring were read locally and through scompile.py --source.

`def-weil-proetale-tor-amplitude`: lean-only existing-declaration repair.
The recorded AsSmall/ConstantCompletion predicate cannot consume ordinary fixed-ring
complexes. The published `ProEtale.DerivedCategory.torAmplitudeIn` tests EVERY sheaf
with the canonical derived tensor in exactly this category. The consumer explicitly
requires ordered intervals, and finite amplitude existentially chooses such an interval.
The full upstream declaration, generic tensor predicate and docstrings were read.

`def-sfb-finite-derived-lower-shriek-compactification`: lean-only binding repair.
Its attachment omitted the module and primary declaration. The record now names the
already published FiniteCoefficient.Derived.LowerShriek declaration, whose real body is
exact degreewise open extension followed by total right derived pushforward. Its old
and migrated sources agree on this body. No new dependency module is written.

## Second reading by Q04

This is the dispatched worker's explicit self-check; no independent reader is claimed.
The dispatcher forbids starting other agents and the maintainer performs the independent
review. I reopened the node and final file and checked every binder and conclusion:
finite coefficients and prime conditions, compatible field structure maps, the same
compactification on both sites, actual etale adjunction, and exactly constructible
finite-Tor preservation. The input full subcategory is intrinsically defined, not
assumed to have etale origin. E and alpha supply that missing origin as a conclusion.
The image definition is literally E-R-nu_X, and its output condition is intrinsic.
The beta source is all D-plus, and M has no finiteness assumptions. In the t equation,
beta inverse has source G P R E, the mapped ordinary counit ends in Q E, and alpha
ends in K; each arrow therefore has the required source and target. The bijection has
exactly the required forward formula. I also reopened all three repaired dependency
records and their published declarations: these are representation/binding repairs,
with their mathematical statements unchanged. The only change after this reading was
aligning old derived-module imports with the published FiniteCoefficient modules;
there was no statement change. All universes and variables are explicitly bound.
