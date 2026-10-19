## Worker report

The module `Sheaf.AlgebraicGeometry.SfFullcdUsedClass` states the single theorem
`AlgebraicGeometry.ProEtale.sfFullcdUsedClass`, with proof `sorry`. It supplies no new
definitions and proves nothing. Its docstring gives all eleven steps of the repaired DAG
proof, including reflection of vanishing, arbitrary proper base change, and the counit
arguments for extensions and colimits.

Source read: blueprint
`sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/thm-sf-fullcd-used-class.md`, order 1796.
The DAG's repaired eleven-step proof is used in place of the blueprint's abbreviated
extension argument: exactness alone would not establish extension closure of an image.

The already landed `def-sf-fullcd-class` is added to `stmt_deps`, as permitted by the
standing brief's STMT_DEPS MAY GAIN LANDED NODES rule. Its recorded predicate is used
unchanged, rather than restating its two vanishing clauses. There is no DAG path from
that node back to this item, so this added dependency does not introduce a cycle.
No other node is delivered or changed. The item's statement and proof remain unchanged.

Hypotheses and clauses are rendered as follows.

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum, algebraic closure k | `(D : WeilConjectures.FiniteFieldDatum.{u})`; all base schemes use `Spec (CommRingCat.of D.k)` |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Positive level n | `(n : ℕ)` and level `n + 1` throughout; the substitution is a bijection from natural numbers to positive levels |
| A = O_E / uniformizer^n | `Padic.coefficientExtensionRing l E (n + 1)`, using exactly the dependency's chosen uniformizer and quotient |
| Finite-type k-schemes Xbar and Y | `(X Y : Scheme.{u})`, their `Over` instances, and `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism |
| Proper finite-type k-morphism p | `(p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of D.k))] [IsProper p]`; properness already entails finite type, so no redundant finite-type premise is added |
| Dimension at most d | `(d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))` |
| Class membership | `(comparisonUpperStar (ModuleCat (ULift A)) T).essImage F`, using the recorded `CategoryTheory.Functor.essImage`, i.e. existence of an etale sheaf and an isomorphism, not a chosen witness |
| Absolute and relative vanishing, bound 2d | `sfClassFullCohomologicalDimension p (Padic.coefficientExtensionRing l E (n + 1)) (2 * d)` |
| Uniformly over every V of Y_proet | The second conjunct of that existing predicate quantifies over `(V : Y.ProEt)` without a finite-type condition; it uses `pullback.snd p V.hom` and pulls the original-source F back along `pullback.fst p V.hom` |
| Cohomology H^r(Rp_*F[0]) = 0, r > 2d | The predicate uses `DerivedCategory.homologyFunctor`, `rightDerivedFunctor`, `DerivedCategory.singleFunctor _ 0`, `IsZero`, and integer comparison with the same bound |
| Closed under inverse image | The next conjunct quantifies over finite-type `T T' : Over (Spec (.of D.k))`, `h : T' ⟶ T`, and every F in the essential image, and asserts membership of `(upperStar ... h.left).obj F` |
| Closed under extensions | For every finite-type T, the same predicate has `IsClosedUnderExtensions`, whose Mathlib definition quantifies over short exact sequences and requires membership of the middle object from membership of both end objects |
| Closed under colimits | For arbitrary explicitly bound universes w and v, `(J : Type w) [Category.{v} J]`, every diagram H, and any colimit cocone c, membership of all H.obj j implies membership of c.pt |
| Contains the constant coefficient sheaf | Membership of `(constantSheaf (ProEt.topology T.left) (ModuleCat (ULift A))).obj (ModuleCat.of (ULift A) (ULift A))`, the constant regular rank-one module sheaf |
| Contains every etale-origin sheaf | The final clause explicitly takes an etale sheaf G and `Nonempty (comparisonUpperStar.obj G ≅ F)` as an existence hypothesis and returns essential-image membership of F. This definitional clause is retained because the node expressly requests it |

Coefficient presentations: the imported `sfIntrinsicModuleEquivalence` is the canonical
associated-module-sheaf equivalence between fixed-scalar module-valued sheaves and the
recorded intrinsic constant-ring modules. `sfIntrinsicDerivedEquivalence` and
`sfIntrinsicDerivedDirectImageComparison` identify their ordinary derived direct images.
The inverse image is the recorded exact fixed-scalar `ProEtale.upperStar`, whose
canonical intrinsic transport is `sfIntrinsicPullback` in the recorded inverse-image
module. The exact realization preserves homology and zero objects. Thus the first
conjunct states precisely the two clauses of `sfFullCohomologicalDimension` restricted
to the recorded class; it does not assert FullCD for all pro-etale sheaves. No arbitrary
map, scalar identification or equivalence is supplied as an extra hypothesis.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension`:
  `AlgebraicGeometry.ProEtale.sfClassFullCohomologicalDimension`; its definition has
  exactly the two vanishing clauses on original-source etale-origin sheaves.
- `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`:
  `AlgebraicGeometry.Scheme.sfFullCohomologicalDimension`; read to check both quantifiers.
- `Mathlib.CategoryTheory.EssentialImage`: `CategoryTheory.Functor.essImage`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, used by the class-bound predicate.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; the right-derived-plus declaration is actually
  defined in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, not the
  older recorded Defs module. This is a proof dependency only; the conclusion is pro-etale.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; read the exact common site universes.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting `Padic.coefficientExtensionRing`
  and the integer ring, maximal ideal, uniformizer and coefficient quotient construction.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction`, `sfIntrinsicDerivedEquivalence`, and
  `sfIntrinsicDerivedDirectImageComparison`, reexporting the existing `sfIntrinsicPullback`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- The scheme-properties convention introduces no declaration: its recorded property
  declarations are used, in particular `IsProper`, `LocallyOfFiniteType`, `QuasiCompact`
  and the `Over`/`IsOver` structure-map conventions.
- The Mathlib extension predicate is `ObjectProperty.IsClosedUnderExtensions`, read in
  `Mathlib.CategoryTheory.ObjectProperty.Extensions` and used without redefining it.

Proof imports: every stated proof dependency with a compatible module is imported.
`thm-sf-fullcd-etale-origin` has no Lean record yet, so has no proof import.
Two proof imports must be omitted: `Sheaf.AlgebraicGeometry.ComparisonDirectImage` and
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`. They import the legacy
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`, which duplicates the operations
in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` imported by
the already recorded class-restricted predicate. The first compile specifically reported
`environment already contains 'AlgebraicGeometry.ProEtale.«term(_)_*[_]»'` from those two
upstream Defs modules. In accordance with the launcher's duplicate-import repair rule,
the compatible finite-coefficient side is retained. Their mathematical proof steps remain
fully documented; no dependency node or live module is changed. This is an import-closure
limitation for stage 3, not a change to the statement.

Edge cases checked before writing:

- Level one is `n = 0` in the Lean parameter; every positive level occurs, and the
  excluded level-zero quotient is not accidentally imposed.
- `d = 0` gives vanishing in every positive degree; the empty scheme has dimension
  bottom and satisfies the dimension inequality. No nonempty or connected hypothesis occurs.
- The zero sheaf and infinite, nonconstructible etale module sheaves are included.
  No finite stalk or constructibility premise has been added.
- A pro-etale site object V need not be finite type over k. The FullCD class predicate
  restricts original-source F, not arbitrary sheaves on the base-changed source.
- Identity pullback and all morphisms over k are covered. Bundled Over morphisms impose
  exactly compatibility with the k-structures.
- Colimits use any colimit cocone, not a chosen diagram lift. Empty diagrams and the zero
  colimit are included. The index and morphism universes are independent and explicit.
  No additional colimit existence hypothesis is imposed on sheaves; `IsColimit c` merely
  specifies what the quantified cocone represents, also allowing any existing large colimit.
- Site objects remain in u+1 and site morphisms in u. Module values are in u+1 and the
  coefficient ring is lifted canonically from u; no site-universe equality is imposed.

Searches made (2026-10-16), using the prescribed msearch wrapper:

- LeanFinder: `Proper direct image of etale origin proetale module sheaves vanishes above
  twice dimension, and etale origin is closed under extensions and colimits`. Eight hits
  concerned etale morphisms, etale loci and the small etale site; no full-statement match.
- Loogle: `CategoryTheory.Functor.essImage, CategoryTheory.Limits.IsColimit`. Six hits were
  condensed/light condensed discreteness characterizations, not this assertion.
- Grep: `cohomologicalDimension|CohomologicalDimension|etaleOrigin`. Zero Mathlib hits.
- LeanSearch: `The essential image of etale to proetale inverse image is closed under
  extensions and all small colimits`. Eight hits included generic object-property
  extension/colimit predicates and fully faithful essential-image colimit closure;
  none combines geometric vanishing with the requested closure assertions.
- `rg` over upstream `WeilConjectures` for fullcd/FullCD/full cohomological dimension found
  `ExceptionalAdjoint.lean`. Its `isZero_homology_rightDerivedLowerStar_comparisonUpperStar`
  is a vanishing theorem only, with a different coefficient interface, not the full
  vanishing-and-closure assertion. The exact node-id search found no declaration.
- `rg` over project `lean/Sheaf` for sf/FullCD/essential-image/comparison-pullback found the
  already landed `sfClassFullCohomologicalDimension`, reused here, and the canonical
  realization/comparison declarations. No existing theorem states this item.
- Declaration-name search for `sfFullCdUsedClass|sfFullcdUsedClass` in the project and
  upstream source found no collision.

No statement correction, disputed mathematical statement, new node, or dependency module.
Validation: `scompile.py Q28 thm-sf-fullcd-used-class` compiled this module both as sandbox
and as its final library module without errors or warnings after the import repair.

## Second reading by Q28

I read the sandbox node and theorem independently against the blueprint source
`sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/thm-sf-fullcd-used-class.md`
(order 1796) and its `_section.md`. The node has no `statement_change` and its
statement agrees with that source. The unit assumes a separably closed base and
finite coefficients; this node explicitly specializes to the global algebraic
closure of a finite field. The following is my object/hypothesis/conclusion list,
with its Lean rendering and verdict.

| Item in the node | Rendering checked in the file | Verdict |
| --- | --- | --- |
| Global datum and algebraically closed field k of characteristic p | `D : WeilConjectures.FiniteFieldDatum.{u}` and `Spec (CommRingCat.of D.k)`; I opened the structure, including `prime`, `card_base`, and `isAlgClosure` | Exact global datum, with the field properties supplied by its instances |
| Prime ell unequal to p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` | Exact; includes every allowed prime |
| Finite extension E of Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` | Exact; a finite-dimensional extension, not an arbitrary field |
| Positive coefficient level and A = A_E,n | `(n : ℕ)` and `Padic.coefficientExtensionRing l E (n + 1)` at every occurrence | Exact reindexing of all positive levels |
| Ring of integers and chosen uniformizer in this quotient | The imported `coefficientExtensionRing` is the quotient by `coefficientExtensionIdeal`, the n-th power of the ideal generated by the recorded uniformizer | The dependency's ring is used; no new coefficient construction |
| Finite-type k-schemes Xbar and Y | `(X Y : Scheme.{u})`, their `Over` instances, and `LocallyOfFiniteType` plus `QuasiCompact` of each structure morphism | Exactly finite type; no separatedness assumption on the schemes |
| Proper finite-type k-morphism p | `(p : X ⟶ Y) [p.IsOver (Spec ...)] [IsProper p]` | Exact; Mathlib properness includes finite type |
| Dimension at most d | `(d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))` | Exact finite bound in the recorded Krull dimension |
| Coefficient class, existence rather than chosen descent data | `(comparisonUpperStar (ModuleCat (ULift A)) T).essImage F` | I opened `Functor.essImage`: precisely `∃ G, Nonempty (ν*.obj G ≅ F)` |
| Absolute vanishing in degrees r > 2d | First clause of `sfClassFullCohomologicalDimension p A (2 * d)` | I opened the predicate: all original-source class members, integer r, `IsZero` of homology of the right-derived direct image of `singleFunctor _ 0` |
| Relative vanishing with the same bound for every V in Y_proet | Second clause of that predicate, `∀ (V : Y.ProEt) (F : ...) (_hF : ...essImage F) (r : ℤ), ...` | Exact; uses `pullback.snd p V.hom` and pullback along `pullback.fst p V.hom`; no finite-type premise on V, and no quantifier over unrelated sheaves on the base-changed source |
| Inverse-image closure along morphisms of finite-type k-schemes | First explicit closure conjunct, `∀ (T T' : Over (Spec ...)) ... (h : T' ⟶ T) (F : ...), ... → ... ((upperStar ... h.left).obj F)` | Exact same coefficient ring and essential-image predicate on both schemes |
| Extension closure | For each finite-type T, `(...comparisonUpperStar ...).essImage.IsClosedUnderExtensions` | I opened Mathlib's class: membership of both ends of any short exact sequence implies membership of its middle |
| Colimit closure | `∀ (J : Type w) [Category.{v} J] (H : J ⥤ ...) (c : Cocone H), IsColimit c → (∀ j, ... H.obj j) → ... c.pt` | Every existing colimit, with independent explicitly bound object and morphism universes; no chosen lift of H or extra colimit-existence assumption |
| Constant coefficient sheaf belongs to the class | Essential-image membership of `constantSheaf ... (ModuleCat (ULift A))` applied to `ModuleCat.of (ULift A) (ULift A)` | Exactly the constant regular A-module, not an arbitrary constant object |
| Every sheaf of etale origin belongs to the class | Final `∀ F, (∃ G : Sheaf T.left.smallEtaleTopology ..., Nonempty (...obj G ≅ F)) → ...essImage F` | Exact definitional containment explicitly requested by the node; not an assumption of constructibility |

I opened every statement dependency's node and its recorded signatures. In particular,
`SfClassFullCohomologicalDimension.lean` and `SfFullCohomologicalDimension.lean` distinguish
the class restriction from the all-sheaf assertion. `SfIntrinsicRealizationTransport.lean`
provides the section-normalized equivalence and derived direct-image comparison, and
`ProEtaleIntrinsicFiniteOperations.lean` defines inverse image by that actual equivalence.
Consequently the fixed-scalar coordinates in this statement have the specified intrinsic
constant-ring meaning. I also read `ProEtaleDerivedCategory.lean`, the quotient and
finiteness declarations, `constantSheaf`, `DerivedCategory.homologyFunctor`,
`topologicalKrullDim`, the comparison inverse-image construction, and both ordinary
finite-coefficient pro-etale functors. The Etale direct-image dependency is for the
proof's Etale comparison, not a substitution of Etale for pro-etale in the conclusion.
The 51-module framework and its finite-coefficient import distinction are recorded in
`coord/pefw-upstream-framework.md`, which I read. There are no new nodes or dependency
modules in this delivery to audit under H12/H13.

For the source hypotheses behind the proof, I read the Stacks TeX at Tags 095T
(`etale-cohomology.tex`, `theorem-proper-base-change`) and 099T, 099V, 09A6, 09B1
(`proetale.tex`, `lemma-fully-faithful`, `lemma-relative-comparison`,
`lemma-morphism-comparison`, `lemma-compare-derived`). Proper base change allows any
base morphism and requires a torsion abelian sheaf. The finite coefficient quotient
ensures torsion without finite stalks. The comparison of direct images requires qcqs,
which properness supplies after every base change. The fully faithful and extension
comparison results assume only a scheme and the given ring. No missing Noetherian,
constructibility, characteristic, or finite-type condition on V should be added.

Edge cases: `n = 0` in the Lean parameter gives actual level one, while all higher
positive levels remain represented. Actual level zero is outside the node. `d = 0`
gives vanishing in every positive degree. The empty scheme has dimension bottom and
is allowed, as are zero sheaves, disconnected schemes and infinite nonconstructible
Etale sheaves. Identity and arbitrary k-morphisms appear in the pullback quantifier.
Empty diagrams and their zero colimit are included. The site object universe is u+1
and its morphism universe u; coefficients and module values use the canonical ULift
to u+1. There is no imposed equality between those site universes. A common universe
for the finite field, finite extension, and schemes can always be enlarged; there is
no independent lower universe that would make a test-object hypothesis vacuous.
The index universes v and w are independently declared and no variable is unbound.

Independent searches, 2026-10-16, with different phrasing from the worker:

- LeanFinder via msearch: `The essential image of etale comparison pullback is closed
  under extensions and colimits and has cohomological dimension at most twice the
  dimension for proper maps`. Eight hits on Etale schemes/site structures; no theorem.
- Loogle via msearch: `CategoryTheory.Functor.essImage,
  CategoryTheory.ObjectProperty.IsClosedUnderExtensions`. No hits.
- LeanSearch via msearch: `Etale to proetale comparison essential image is closed under
  extensions, colimits, and inverse images`. Eight hits, including generic closure
  under colimits for a fully faithful functor and generic extension predicates; none
  states this geometric theorem with all clauses.
- Grep via msearch: `etaleOrigin.*(extension|colimit)|CohomologicalDimensionLEOnEtaleOrigin`:
  no Mathlib hits. Direct rg in Mathlib, upstream `WeilConjectures`, the side framework,
  and `lean/Sheaf` found the existing predicates and individual ingredients. I opened
  the side `WeilConjectures/SixFunctors/ProEtale/FullCohomologicalDimension.lean`,
  especially `etaleOrigin_upperStar_obj`, `etaleOrigin_isClosedUnderColimitsOfShape`,
  `etaleOrigin_unit`, `etaleOrigin_of_shortExact`, and
  `hasCohomologicalDimensionLEOnEtaleOrigin`. These are separate pieces; the colimit
  instance additionally requires Etale colimits of that shape. None is the complete
  statement of this node, so dropping this module as an existing declaration would
  lose clauses. The older upstream `ExceptionalAdjoint.lean` has a vanishing result
  only. The project `FullCDClassRestriction.lean` states restriction closure only.
- Exact-name search in `dag/lean_names_upstream.json`, the upstream source and project
  finds no `sfFullcdUsedClass`/`sfFullCdUsedClass` collision.

Mismatch and repair: the signature has no H3 mismatch and is preserved verbatim. Proof
step 10 of the docstring originally took an Etale colimit without discussing the large
index universes permitted by the signature. I retained the existing small-colimit
argument and added the general counit argument: origin objects are precisely objects
left orthogonal to every comparison counit; that condition passes through any existing
colimit by its universal property. A section of the object's counit, followed by
injectivity against that counit for its origin source, proves the counit invertible.
This justifies the entire quantified colimit clause without assuming a large Etale
colimit. All eleven DAG proof steps remain present. No mathematical statement, node
proof, dependency record, or import was changed. The module has exactly one theorem
with `sorry`, no data definitions, no local notation or instances, and no extra proof.

The initial prescribed wrapper compile was clean for both sandbox and library paths.
The final edited file is compiled again before the dry run and delivery; the node's
`lean.statement` is checked byte-for-byte against the unchanged signature.

Final validation: scompile.py compiled the edited module cleanly at both sandbox and
library paths (6.7 s and 7.4 s). An explicit byte-for-byte comparison confirms that
`lean.statement` equals the file signature; all Lean lines are at most 100 characters.
