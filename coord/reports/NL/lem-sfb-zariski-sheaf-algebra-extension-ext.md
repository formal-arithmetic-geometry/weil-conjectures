## Worker report

The delivery states `TopCat.SquareZeroSheaf.exists_classification` in
`Sheaf.Topology.ZariskiSheafAlgebraExtensionExt`. Its sole theorem has proof
`sorry`. All helper definitions and structures contain actual data; none chooses
an object from this existence theorem. A separate definition module
`Sheaf.Topology.SquareZeroSheafAlgebra` supplies the previously missing extension
notion for arbitrary ring sheaves on arbitrary topological spaces.

This repairs returned delivery f6e5aea4ffac. The saved packet was inspected and
its required initial dry run passed at 2301c675983 without pushing. That dry run
checks compilation and preflight; the H3 normalization fault in the return was
still present and has now been repaired. Compared with current main, the item
still changes only `lean` and adds the new definition to `stmt_deps`. Its
accepted statement, proof, and review metadata remain unchanged.

Read sources: `defos.tex`, lemma-extensions-of-relative-ringed-spaces (0GPZ),
remark-extensions-of-relative-ringed-spaces (0GQ0),
lemma-extensions-of-relative-ringed-spaces-functorial (0GQ1),
remark-extensions-of-relative-ringed-spaces-functorial (0GQ2), and
lemma-huge-diagram-ringed-spaces (08U8). The source's naive cotangent Ext is
related to the node's full cotangent Ext by its accepted truncation argument,
using 08US and 08UR. No statement correction is made.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary topological space T | Every field quantifies `T : TopCat.{u}`. |
| Map R to A of commutative unital ring sheaves | `R A : T.Sheaf CommRingCat.{u}` and `f : R ⟶ A`. The bundled category's morphisms preserve the unit. |
| A-module sheaf G | `G : Modules A`, transparently the recorded `ringedSiteModules (SheafDifferentials.ring A)`. |
| Standard polynomial sheaf cotangent complex | `cotangent C S f` is precisely `SheafCotangent.sheafComplex (S.sheaves T (Arrow.mk f)).sections`, the dependency's standard resolution with its prescribed polynomial coordinates. `C` and `S` specify its existing construction, not arbitrary complexes. |
| Derived category and G in degree zero | `Ext L G n` is Hom from `DerivedCategory.Q.obj L` to `((DerivedCategory.singleFunctor (Modules A) 0).obj G)⟦n⟧`, using Mathlib's standard localization. |
| Exact additive extension | `Extension.i`, `i_natural`, `injective`, `kernel`, and `surjective`. Middle exactness is sectionwise, but the last map is locally surjective. |
| E is a commutative unital R-algebra, p is an algebra map | `ring`, `base`, `p`, `base_p`. A ring-sheaf map from R defines exactly its R-algebra structure. |
| Square-zero kernel with prescribed quotient action | `Extension.square_zero` and `action`, for every open and all its sections. |
| Isomorphisms fix G and A | `Iso.ringIso`, `base`, `quotient`, `kernel`, with the coefficient map the identity. |
| Canonical extension class, Stacks 0GQ0 | `cl_normalization` supplies `ConormalClass` for the given extension. `class_eq` is the equality `cl E = Q(projection) ≫ comparison⁻¹ ≫ singleClass 1 map`; the factors are fixed on all local polynomial coordinates. `formula` requires `i(map([j])) = eval(base,id)(j)`, so the conormal map is the one of the canonical lift R[E] → E. |
| Bijection on isomorphism classes | `Classification.cl`, `onto`, and `classes`: the class function is surjective and has equal values iff an extension isomorphism exists. This is precisely a bijection on classes, without choosing representatives or adding a second quotient definition. |
| Split extension A direct-sum G maps to zero | `split_exists` and `split`, with `IsSplit E` an R-algebra section of p. The coordinates `(a,g) ↦ s(a)+i(g)` give exactly the stated direct-sum multiplication, as follows by expanding and using `action` and `square_zero`. Thus this specifies the split extension up to its named-end isomorphism, not an arbitrary zero-class extension. |
| Every coefficient map G to H | `v : G ⟶ H`, without any mono, epi, finiteness or flatness condition. |
| Coefficient pushout and postcomposition on Ext | `pushout_exists`, `Hom E F v`, and `coefficient`; `coefficientMap` explicitly composes with the shifted derived single-complex map of v. An extension morphism inducing v and identity on A identifies the target with the coefficient pushout: on the kernel it is v, and locally every target section is the image of a source lift plus an H-section. |
| Fibre product and pushout along addition for Baer sum | `Baer.b` is an actual natural ring map on pairs with equal quotient. Its `add`, `mul`, `one`, `base`, `quotient`, `kernel` say exactly that it is an R-algebra map over A with kernel map `(g,h) ↦ g+h`. The target extension is the kernel-addition pushout by the same local-lift argument. `baer_exists` gives such a diagram; `baer` identifies its class with the sum. |
| Every open restriction, including empty | `openModules` is Mathlib's restriction through Over U and its equivalence to opens of the subspace. `OpenRestriction` fixes the actual restricted ring and kernel maps. `restriction_exists` provides the extension and `restriction` gives the class equality. `OpenCotangent.iso` is a complex isomorphism normalized on all standard coordinates; `restrictionMap` is the induced derived functor with its actual localization/single/shift comparisons. `open_exact` supplies the exactness, rather than assuming it. |
| Derivations additive, Leibniz, and zero on R | Existing `G.val.Derivation' f.hom`, whose `d`, `d_mul`, `d_map`, `d_app` were read in Mathlib. It is a genuine natural additive map, not a sectionwise unrelated family. |
| Aut(E) identified with derivations | `automorphism E : G.val.Derivation' f.hom ≃ Iso E E`. |
| Formula e maps to e+i(d(p(e))) | `automorphism_formula`, on every open and every section. |
| Composition corresponds to addition | `automorphism_add`, where k is the pointwise sum of d and e, identifies its algebra map with the composite. This states additivity without imposing a new ad hoc group structure on the existing derivation type. |
| Derivations identified canonically and additively with Hom(L,G[0]) | `derivation_ext` is an equivalence, `derivation_add` states additivity, and `derivation_normalization` requires `DerivationClass.formula` and `class_eq`. On a degree-zero standard differential tensor b ⊗ dx the map is b • d(ev(x)); in particular d[X a] ⊗ 1 maps to d(a). Its Ext morphism is exactly `singleClass 0 map`. Composing its inverse with `automorphism` gives the two identifications in the node. |
| Both identifications commute with coefficient pushout | `derivation_coefficient` uses existing `Derivation.postcomp`; `automorphism_coefficient` is the actual equation `T_d ≫ q = q ≫ T_(vd)`. |
| Both identifications commute with open restriction | `derivation_restriction_exists` supplies the derivation with identical restricted section maps; `derivation_restriction` identifies its Ext class under the actual derived restriction, and `automorphism_restriction` conjugates the actual restricted algebra automorphism by the fixed restricted-ring isomorphism. |
| No quasi-coherence, flatness, finiteness or Noetherian condition | None of these appears in any binder or field. The ring-module derived-category localization parameters are those already used by the recorded standard cotangent interface. |

All canonical maps are now constrained by equations in Lean, including the two
maps identified in the return. `ConormalCoordinates` specifies the two-term
presentation by its conormal universal property, the existing differential sheaf,
the differential `[j] ↦ dj ⊗ 1`, and zero objects in every other degree. The
universal property is on compatible local polynomial relations, with additivity,
`[qj] = ev(q)[j]`, and restriction, so it identifies the sheafified J/J² even
when evaluation is only locally surjective. It does not demand surjectivity on
sections. No unrelated conormal comparison is assumed.

`ConormalProjection.zero` and `.neg_one` fix the standard projection by tensor
and face-difference coordinates. `ConormalClass.conormal` and `.differential`
fix the comparison induced by relabeling e ↦ p(e); `quasiIso` requires it to be a quasi-isomorphism.
`conormalRepresentative` uses the localization inverse of precisely Q.map of
that chain comparison; no freely chosen derived isomorphism remains. `ConormalClass.formula` fixes the conormal
map through the injective named kernel map of the extension, and `class_eq`
fixes cl. `singleClass` is defined with Mathlib's own single/shift comparison,
so an unspecified target shift isomorphism cannot introduce another sign.
`DerivationClass.formula` fixes the other cochain map on every degree-zero
standard generator, and `class_eq` fixes its Ext class. Other target components
are zero. These coordinate descriptions belong to the item's canonical-map
normalization interface; they contain no further postponed helper theorem and
are all listed in `lean.declarations`.

Dependency declarations used, with full signatures/docstrings read:

* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
  Its exact Mathlib target `SheafOfModules`, `SheafOfModules.Hom`, evaluation,
  and forgetful functors were also read.
* `Sheaf.Topology.SheafCotangentComparison`:
  `TopCat.SheafCotangent.SectionModel`, `SheafModel`, `StandardSheafModel`,
  `Comparison`, `sheafComplex`, `sectionElement`, `sectionArrow`, and
  `exists_comparison`. In particular `S.sheaves` retains the free-sheaf-algebra
  and standard simplicial differential identifications, not a bare complex.
* The recorded standard-resolution coordinates additionally use
  `Algebra.CotangentResolution.Coherence.standard_spec`, `standardTerm`, and
  `complexGenerator`, as read in `Sheaf.RingTheory.CotangentResolutionCoherence`.
  The conormal degree-zero term and its generating tensors use the existing
  `TopCat.SheafCotangent.differentialSheaf` and `differentialSection`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory`, `DerivedCategory.Q`, and
  `DerivedCategory.singleFunctor`, and `DerivedCategory.singleFunctors`.
  `SingleFunctors.shiftIso` fixes the single/shift normalization, and
  `HomologicalComplex.singleObjXSelf` fixes the surviving degree of a single
  complex. These signatures were read from Mathlib, together with the
  localization instance inverting `QuasiIso` maps.
* `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `mapDerivedCategorySingleFunctor`, and its `CommShift` instance.
* `Mathlib.Topology.Sheaves.Module`, `Over`, and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `Opens.sheafOfModulesEquivOver`, and
  `Opens.sheafRestrict`. Their composition is the actual open restriction.
* `Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`:
  `PresheafOfModules.Derivation'` and `Derivation.postcomp`.

All recorded, stated proof dependencies are imported (the sheaf cotangent
comparison, sheafification tensor comparison, sheafified differential cokernel,
local sheafification sections, and exact inverse image); Mathlib supplies the
standard t-structure, orthogonality and triangle-Hom API. The currently unstated
proof nodes (sheaf polynomial comparison, chain projection, boundary cokernel,
two-term Hom boundary, and Ext representative) have no modules to import. They
remain proof dependencies and their steps are retained in the theorem docstring.
No proof dependency is added as a hypothesis.

Edge cases checked before and after drafting:

* T empty and U empty: local surjectivity is vacuous where appropriate; sheaves
  on the empty space have terminal section data. No nonempty hypothesis occurs.
* G zero: the extension is isomorphic to A and the automorphism and Ext groups
  are trivial; the coefficient and Baer formulas specialize to zero.
* Arbitrary v, including the zero map: the statement does not assume sectionwise
  lifting, injectivity or surjectivity of v. Its coefficient diagrams remain valid.
* Rings of all characteristics, including zero rings: no characteristic or
  nontriviality assumptions appear. The square-zero local formulas use only
  commutative-ring and module axioms.
* Non-affine opens where an epimorphism of sheaves is not surjective on sections:
  explicitly accommodated by `Presheaf.IsLocallySurjective`, not a sectionwise
  `Function.Surjective` requirement.
* Derived degrees 0 and 1: the target is G[0] shifted by n, not G placed in
  cochain degree +1. The derived restriction factors preserve this convention.
* Value and space universes: both range over arbitrary u, as does the recorded
  topological sheaf cotangent interface. No extra identification of distinct site
  object and morphism universes is imposed. There are no auto-bound variables.

Searches actually executed with `msearch.py` for this item:

* LeanSearch, `square zero extensions sheaves commutative algebras`: 8 hits,
  including `TrivSqZeroExt`, its lifts, and `liftOfDerivationToSquareZero`.
  These are individual rings, not the sheaf classification.
* LeanFinder, `Square zero extension of a sheaf of commutative algebras by a
  module sheaf`: 8 hits, headed by `TrivSqZeroExt`, presheaf differentials,
  tilde modules and `PresheafOfModules.Derivation'`; use the last one directly.
* Loogle, `"Sheaf", "extension"`: 12 Kan-extension hits, none classifies
  algebra extensions.
* msearch grep `SquareZero|squareZero|AlgebraExtension`, subdirectory
  `Algebra/Category`: 0 hits. Also grep `square.zero|SquareZero|squareZero`
  across Mathlib: split ring extensions and derivation lifts, no sheaf interface.
* Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and DAG definition nodes:
  geometric thickenings and several unrelated extension modules; no extension
  notion for arbitrary ring sheaves on arbitrary topological spaces.
* `blueprint_refs.py search 'square-zero extensions'`: 0 blueprint nodes.
  `blueprint_refs.py ancestor` returns `None`, consistent with the item's
  imported ancestry metadata.

No STATEMENT-DISPUTED issue or source correction was found. The only initial
compiler defects were the open-restriction transport and missing explicit
additivity evidence for mapping complexes. Both were repaired, with no change
in the mathematical statement. Final compilation and delivery validation are
performed with the prescribed wrappers only.

## New nodes

`def-sfb-square-zero-sheaf-algebra` defines the extension, coefficient morphism,
fixed-end isomorphism, split-section predicate, Baer diagram and open restriction
interface used above. Source: Stacks 0GPZ, 0GQ0, 0GQ2 and 08U8. The three search
kinds and actual results are recorded in its `mathlib_searches`. Mathlib's
`TrivSqZeroExt` defines only a split extension of individual rings. The live
`def-sfb-space-square-zero-extension-data` is specifically for algebraic spaces
on their small etale sites; it does not apply to arbitrary topological spaces.
It is therefore not a replacement for this general definition. The module uses
the existing module sheaves and restriction equivalence rather than constructing
another module category or another differential notion. Its only statement
dependency is the existing general module-sheaf definition. No existence theorem
is hidden in this definition node.

## Repair of returned delivery

H3: The original structure permitted both cl and -cl and both derivation_ext
and -derivation_ext. The new `cl_normalization` and `derivation_normalization`
fields require the concrete representatives above. In particular, negating the
Ext class while keeping the extension fixed changes the sign of its conormal
map. `ConormalClass.formula` then fails whenever the conormal image is nonzero,
since i is injective. Negating a derivation class changes the value at d[X a]
from d(a) to -d(a), violating `DerivationClass.formula` when these differ. A
change of coordinates in a presentation cannot undo this: the projection,
comparison, and conormal map must all change compatibly, leaving their composite
unchanged. Thus the original independent sign freedoms are eliminated.

H11: The second reading below explicitly checks determination of both maps,
including every intermediate comparison and the canonical single/shift factor.
It replaces the insufficient discussion in the returned report. This is a
same-worker reading, as required by the dispatch's prohibition on other agents;
the maintainer performs the independent review.

Additional repair searches: msearch LeanFinder, "Sheaf polynomial presentation
conormal module universal property square zero extension canonical class", gave
8 hits on sheaf-module presentation maps and presheaf differentials, with no
canonical extension-class normalization. msearch Loogle, `"Cotangent", "map"`,
gave 12 ordinary ideal/cotangent-module map hits, not this sheaf classification.
msearch grep `ConormalFamily|ConormalCoordinates|ConormalClass|DerivationClass`
gave 0 hits. Direct rg of Mathlib, Sheaf and WeilConjectures confirmed the new
fully qualified helper names do not exist; the existing standard-resolution and
sheaf differential constructors are reused. No new independent notion or
postponed theorem is introduced in the repair.

## Second reading by NL

I reread the unchanged node and Stacks defos.tex, 0GQ0
(remark-extensions-of-relative-ringed-spaces), with both delivered modules open.
This is a same-worker reading; I do not claim a second worker reviewed it.

The hypothesis check remains arbitrary T, arbitrary unital R → A, and any module
sheaf G, with exactly the previously recorded cotangent universes. Extension
surjectivity stays local. Its named kernel identification stays injective,
compatible with restrictions and the prescribed A-action, and square zero.
Nothing in the repair imposes finiteness, flatness, quasi-coherence, or
Noetherianity. The unchanged onto/classes, split, coefficient, Baer, restriction,
and automorphism fields still render the clauses individually matched in the
table above.

I specifically tested the gap from the return rather than inferring canonicality
from naturality. On the canonical polynomial lift R[E] → E, coefficients map
by E.base and X e maps to e. Its evaluation of any relation j is exactly
E.i of the degree-minus-one representative (`ConormalClass.formula`). Kernel
injectivity determines that representative on every relation. The conormal
universal property determines its whole sheaf-module map; the target single
complex is zero in all other degrees. The presentation comparison is fixed
on every conormal relation and every differential tensor, and both complexes
vanish outside -1,0. Its derived inverse is fixed by localization in `conormalRepresentative`, and
`ConormalProjection` is fixed on all standard generators in its only two
nonzero target degrees. The equality `class_eq` therefore determines cl from
the actual conormal construction. This checks all factors, rather than leaving
an unnormalized comparison able to absorb a sign.

For derivations I checked the local generator x = X a with tensor coefficient
b = 1: `standardPolynomial` reads the existing resolution's actual coordinates;
`polynomialEval f (𝟙 A)` evaluates x to a; `DerivationClass.formula` gives
exactly d(a). All degree-zero tensor generators are covered by the quantified
formula, and other degrees of the target are zero. `singleClass 0` uses the
canonical shift-zero comparison, and `class_eq` is an equality to its image
under Q. This determines derivation_ext independently of its additive and
naturality clauses and agrees with universal differentials / H⁰(L) = Ω.

I rechecked the empty space and empty open (the sheaf universal properties still
apply), G = 0, the zero coefficient map, zero rings, characteristic two (where
negation may coincide), and an ordinary nonzero conormal class outside
characteristic two. The formulas hold in all of these cases; the last case is
the one that exposes the former sign freedom. Concretely, on the one-point
space take k = ℚ, A = k[t]/(t²), E = k[t]/(t⁴), and identify G = A with the
kernel by i(g) = t²g. The polynomial relation X(t)² evaluates to t² in E,
so the required conormal map sends it to 1, whereas its negative sends it to
-1. The class is nonzero in A/(2t), so negation changes the class. Separately,
for A = ℚ[t] and G = A the derivation d(t) = 1 requires the degree-zero
generator d[X(t)] to map to 1, excluding the negative map.

A non-affine open still need not
lift sections of A to E: the conormal universal property is imposed on local
relations and makes no global lifting choice. No definition chooses data from
`exists_classification`, and the only proof remains that theorem's `sorry`.
