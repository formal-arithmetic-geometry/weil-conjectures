## Worker report

The module `Sheaf.AlgebraicGeometry.SupportQuotientPairPullback` states
`AlgebraicGeometry.Scheme.supportQuotient_pair_pullback`, with its entire proof `sorry`.
The node's statement and dependencies are unchanged. No statement dispute or dependency
repair was needed. All writes are in the prescribed sandbox; only the prescribed wrappers
compile or prepare delivery bookkeeping.

The theorem asserts existence of two families of ordinary sheaf morphisms, each pointwise
unique by its quotient equation. It uses the exact cokernels and quotient maps already
defined by `lem-pur-support-quotient-flat`, rather than another construction of support.
Its finite fixed-scalar sheaves are the recorded dependency's presentation of modules over
the constant ring sheaf. `etaleSumFlatModuleRealization` and
`ProEtale.finiteCoefficientIntrinsicRealization`, used in that dependency's statement,
are the canonical realizations into `SheafOfModules`; the pro-etale equivalence is also
`sfIntrinsicModuleEquivalence`. No arbitrary comparison or alternate coefficient action
is assumed. The one-level `ULift A` is the dependency's coefficient size convention.

Hypothesis and clause correspondence:

1. A finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`.
   Both sites and all coefficient universes are inherited from the recorded ordinary
   quotients, with schemes in universe `u` and modules in `u+1`. There is no independent
   smaller site universe, no identification of object and morphism universes, and no
   nonzero-ring hypothesis.
2. A closed immersion with quasi-compact open complement is bundled by
   `SupportQuotientPair`: `T`, `C`, `a : C ⟶ T`, `closed : IsClosedImmersion a`,
   and `qc : QuasiCompact a.openComplement.ι`. These structures add no new mathematical
   notion: they just collect the theorem's inputs, allowing identities and composites
   to quantify over one common family. The two module objects and quotient maps are
   `etaleSupportQuotient A a`, `proEtaleSupportQuotient A a`, and their recorded `Map`s.
3. A morphism `f : T' ⟶ T` carrying `C'` into `C` is `SupportQuotientPairMap P Q`:
   `f : P.T ⟶ Q.T`, the factorization `s : P.C ⟶ Q.C`, and
   `w : s ≫ Q.a = P.a ≫ f`. Any factorization in the node gives such data. Conversely
   these data give exactly that factorization. Since the target closed immersion is a
   mono, its factorization is unique, so the presentation adds no choice or restriction.
4. Existence in each topology is `∃ (cEt : EtaleSupportQuotientPairMaps A)
   (cPro : ProEtaleSupportQuotientPairMaps A)`. The first two conjuncts assert, for every
   pair morphism, its quotient equation and uniqueness among ALL ordinary module-sheaf
   morphisms of that type. The etale coefficient identification is the hom of the actual
   `Etale.constantSheafCompUpperStarIso`; the pro-etale coefficient map is the recorded
   `proEtaleConstantInverseImageMap` specialized to the regular coefficient module.
   Both preserve constant sections by their adjunction constructions. These equations
   explicitly insert the coefficient maps which are suppressed in the node's formulas.
5. The third conjunct quantifies over all separably closed geometric fields and points
   `t : Spec Ω ⟶ P.T`. On `Set.range P.a` it provides source and target isomorphisms
   `eS`, `eT` with the regular module. Each is normalized by the quotient's actual
   constant-germ map to be the identity. For the source this uses the inverse of the
   canonical constant pullback isomorphism before the pulled-back quotient map.
   The equation `sheafFiber.map (cEt f) ≫ eT.hom = eS.hom` is therefore the identity
   `A → A` under the prescribed identifications, rather than an unconstrained pair of
   isomorphisms. The constant germ helper is exactly the final-object unit-and-germ
   composite already written in `supportQuotient_flat_kflat_stalk_comparison`.
   Off `C'`, `IsZero` asserts the target stalk is zero and the mapped morphism equals
   zero. The source is allowed to be nonzero there.
6. The fourth conjunct uses `IsPullback f.s P.a Q.a f.f` for the ACTUAL scheme-theoretic
   pullback square, and concludes `IsIso (cEt f) ∧ IsIso (cPro f)`. Mere containment of
   underlying support sets is not substituted for this hypothesis.
7. The fifth conjunct says that the identity pair maps give the hom components of the
   canonical identity comparisons `supportSiteEtaleComparisonId` and
   `supportSiteProEtaleComparisonId`. After these inverse-image identifications, these
   are precisely identity maps of the quotients.
8. The sixth conjunct quantifies over every composable pair of input morphisms. For
   `g.comp f`, it equates its map to the hom of the canonical inverse-image composition
   comparison, followed by pullback of the map for `f`, followed by the map for `g`.
   This is the node's displayed equation in Lean's left-to-right composition convention.
   All three complements are quasi-compact by their three input pairs.
9. The seventh conjunct quantifies over the normalized comparison isomorphisms `α` and
   `α'` of `lem-pur-support-quotient-flat`, imposing precisely that dependency's quotient
   equations using `supportQuotientConstantComparison`. It states
   `f_pro^*(α.hom) ≫ cPro f = ρ.inv.app Q_et ≫ ν'^*(cEt f) ≫ α'.hom`, where `ρ` is
   the exact `supportSiteComparisonCoefficientPullbackIso` from the comparison dependency.
   Thus it is the node's comparison square with its canonical domain identification
   inserted. The dependency gives existence and uniqueness of these normalized `α`s,
   so this universal formulation neither adds a hypothesis nor strengthens the result.
   All equations are in the ordinary sheaf categories, with no derived/stalkwise
   replacement for their equality.
10. No flatness instance on `f`, no reducedness of `C` or `C'`, and no conservativity
    hypothesis on pro-etale geometric stalks occur anywhere.

The data helpers `SupportQuotientPair`, `SupportQuotientPairMap`, their identity and
composition, and the family-type abbreviations package this node's inputs and output.
Identity and composition are actual terms on schemes and factorization witnesses;
their equality fields use category laws. No helper uses `sorry`, choice from an
underdetermined existence theorem, private notation, private definitions, or local instances.
All helper declarations are listed in `lean.declarations` with source/blueprint docstrings.
The only postponed theorem is the main statement, matching the item DAG node, with its
complete eight-step natural-language proof in the docstring.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  `constantSheafAdj`, and `toSheafify` from the sheafification module.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent `SheafOfModules` presentation used by the intrinsic realizations.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`: `QuasiCompact`.
  Only quasi-compactness, not local finite type, is imposed here.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: chosen pullbacks,
  represented invariantly by the ordinary `IsPullback` predicate.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek` and its adjunction, giving the existing quotient arrow.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero`, expressing the
  same recorded pro-etale extension by zero in the intrinsic presentation.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `upperStarLowerStarAdjunction`;
  its `.ConstantSheaf` module: `Etale.constantSheafCompUpperStarIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  `proEtaleSheafAdjunction`, `proEtaleConstantDirectImageMap`,
  `proEtaleConstantInverseImageMap`; the latter's fixed-scalar specialization uses the
  same underlying Kan extension and coefficient-section map as the module pullback.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparison`,
  `proEtaleSiteComparisonModules`; its ordinary module functor is
  `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.SupportQuotientFlat`: all six quotient/arrow/map definitions,
  `supportQuotientConstantComparison`, `supportQuotient_flat_kflat_stalk_comparison`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `ProEtale.supportSiteEtaleComparisonId`, `supportSiteEtaleComparisonComp`, their
  pro-etale counterparts, `supportSiteComparisonCoefficientPullbackIso`, and
  `supportSiteComparison_pullback_coherent`.

All recorded proof-dependency modules are also imported (non-public when only needed for
stage 3): `ProEtaleConstantRingComposition`, `ComparisonPullbackExact`, the upstream
`EtaleInverseImageAlgebraicStructures`, `InverseImageStalkGerm`,
`EtaleInverseImageModulesExact`, extension-by-zero `.FiniteComparison`, and upstream
`.Sites.EtalePoint`. The Mathlib-only exact-stalk dependency uses `Point.Basic`,
`Point.Skyscraper`, and `ShortComplex.ShortExact`. The source was checked directly:
Stacks `etale-cohomology.tex`, `lemma-stalk-pullback` (Tag 03Q1), and the current blueprint's
`sec-smooth-purity/sk-prop-an/lem-pur-kunneth-supported.proof.md`, final paragraph.
The node correctly attributes the pair-map refinement to the agent rather than to 03Q1 alone.

Edge cases checked before and after writing:

- `C = ∅`: the defining open is the whole scheme and its support quotient is zero;
  pair maps exist only with the appropriate empty-source factorization.
- `C = T`: the open is empty, the quotient is the constant coefficient sheaf; the
  normalized map is ordinary constant-coefficient pullback.
- `C' = ∅` and strict `C' ⊂ f⁻¹(C)`: target stalk zero, even where source stalk is A;
  the theorem asserts no isomorphism without the Cartesian square.
- Empty ambient schemes, the zero ring and zero modules remain allowed. All stalk
  assertions have their ordinary vacuous/zero interpretation and require no Nontrivial.
- Identity maps and arbitrary two-step composites are included, with explicit canonical
  inverse-image transports. Nonflat morphisms and nonreduced closed subschemes remain
  included; topological containment alone is never used as a scheme factorization.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "support quotient cokernel open extension by zero functorial
  pullback closed pairs etale proetale"`: eight results, including `opensDiagramι`,
  `liftCoborder_app`, and unrelated etale-locus and limit results; no pair quotient theorem.
- `msearch.py ... loogle "CategoryTheory.Limits.cokernel.desc"`: twelve cokernel API
  results, including `cokernel.desc` and `cokernel.π_desc`; these supply the universal
  property but not the geometric normalized pair-map statement.
- `msearch.py ... grep "supportQuotient|SupportQuotient"`: zero Mathlib hits.
- `rg` over the prescribed `lean/WeilConjectures` and `lean/Sheaf` source trees for
  `supportQuotient`, `SupportQuotient`, the item id, and pair/pullback combinations:
  found the existing `SupportQuotientFlat` and `SupportQuotientProduct` definitions and
  unrelated pairings; no existing exact theorem. These existing quotient declarations
  are reused, and no alternative support quotient or tensor construction is supplied.
- Additional direct source searches found the existing canonical etale constant-sheaf
  pullback isomorphism, pro-etale constant-section inverse-image map, and comparison
  identity/composition isomorphisms, all reused directly.

Validation: `scompile.py Q64 lem-pur-support-quotient-pair-pullback <module>` passed both
its sandbox compile (36.4 s) and delivery module compile (24.0 s), with no errors or warnings.
All lines are at most 100 characters and `set_option autoImplicit false` is explicit.

## Second reading by Q64

A second pass by the same worker reopened the unchanged node statement and the complete
Lean module; no other agent was started, as required by the dispatch brief. Independent
mathematical review is left to the maintainer's delivery reader.

The seven main conjuncts were checked against the node in order: etale existence and
uniqueness; pro-etale existence and uniqueness; the two stalk cases; the actual Cartesian
square; identity maps in both topologies; arbitrary compositions in both topologies; and
the normalized ordinary comparison square. The two bundled schemes and closed immersions
supply precisely the original hypotheses. The pair map's `s` and `w` are the originally
assumed factorization, and uniqueness of a lift through a closed immersion means the
family does not acquire an unwanted dependence on factorization data. The constant-germ
normalizations of both `eS` and `eT` prevent the stalk identity from being made vacuous
by arbitrary changes of basis. The composition arguments have order `g` then `f` in Lean,
matching `T'' → T' → T` in the node. The comparison equation starts at `f_pro^*ν^*Q`, so
uses `ρ.inv`, as required. The boundary cases listed above remain included. No mismatch
requiring a statement change or additional node was found.
