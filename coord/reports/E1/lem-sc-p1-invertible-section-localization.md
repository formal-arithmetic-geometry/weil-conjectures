## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleSectionLocalization` states
`AlgebraicGeometry.Scheme.Modules.exists_sectionFraction_nonvanishing_equiv`, with `sorry`
as its sole proof. Its domain is the explicit fraction presentation supplied in the new
module `Sheaf.AlgebraicGeometry.SectionFractionPresentation`. No theorem is proved.

Read the item's entire statement and two proof steps, and the statements/records of all four
statement dependencies. Read the recorded declarations and docstrings: Mathlib's `Scheme`
(Scheme.lean:35–47), `CompactSpace` (Topology/Defs/Filter.lean:279–283),
`Scheme.Modules.IsInvertible` (WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean:55–61),
and the full landed `Sheaf.AlgebraicGeometry.Coherent` module. That module explicitly records
that its quasi-coherent clause is Mathlib's `SheafOfModules.IsQuasicoherent`, whose docstring
and signature were read at Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249–252.
The recorded main declaration `RingedSpace.IsCoherent` is not used: the item only assumes
quasi-coherence, and the dependency explicitly identifies the Mathlib declaration for that
clause. No dependency replacement is necessary.

The local literature checkout contains only indices, not `properties.tex`; read the source at
https://stacks.math.columbia.edu/tag/01PW (lemma-invert-s-sections), part (2), and its linked
https://stacks.math.columbia.edu/tag/0B5L (equation-module-invert-s). The statement has precisely
the qcqs hypotheses and the twisted-section fractions in the node. No statement correction.

Hypothesis and clause correspondence:

- Scheme `X`: `(X : Scheme.{uL})`; no finite-dimensional, Noetherian, affine, separated,
  field, nonempty, or characteristic restriction.
- Quasi-compact: `[CompactSpace X]`, the recorded Mathlib match; this definition imposes no
  Hausdorff condition.
- Quasi-separated: `[QuasiSeparatedSpace X]`. Read
  `quasiSeparatedSpace_iff_forall_affineOpens` in Morphisms/QuasiSeparated.lean:56–58: it is
  precisely compactness of the intersection of every pair of affine opens. This API is
  available through the ClearDenominators import.
- Invertible module: `(L : X.Modules) [L.IsInvertible]`, the exact recorded upstream class.
- Global section: `(s : 𝟙_ X.Modules ⟶ L)`. This is the standard equivalent encoding of a
  global section; evaluation at `1` gives `s.app ⊤ (unitSectionsEquiv ⊤ 1)`. Conversely a
  section defines the module morphism by `r ↦ r • res(s)` on every open. Naturality and
  linearity follow from the module restrictions, so no section or case is excluded.
- Quasi-coherent module: `(F : X.Modules) [F.IsQuasicoherent]`, the quasi-coherent clause
  of `pqf-def-coherent`, not its stronger coherent or finite-type clauses.
- Nonvanishing open `X_s`: existential `U : X.Opens` with `(U : Set X) =
  nonvanishingLocus L (s.app ⊤ (unitSectionsEquiv ⊤ 1))`. This uses the mandated shared
  definition in `Sheaf.AlgebraicGeometry.Ample`, not `generatingLocus` or the zero scheme.
  Its definition is the germ outside maximal-ideal times the stalk; for rank one this is
  nonzero in the residue-field fibre. Existence of this open is a conclusion, not an
  added openness assumption.
- Integer-graded `N`, its tensor powers and multiplication by `s`: the domain uses its
  explicit degree-zero fraction presentation. Every denominator is `s^n`, `n : ℕ`, so its
  homogeneous numerator lies in degree `n`, namely `Γ(F ⊗ L.tensorPow n, ⊤)`; no negative
  degree contributes a degree-zero fraction. Negative twists in `N` are therefore not
  discarded cases: they cannot be numerator degrees in this part of the localization.
  Multiplication by powers of `s` is upstream `mulTensorPowSection s F n b`, using canonical
  tensor-power addition isomorphisms. Multiplication by the section ring is the tensor
  multiplication of sections; for this localization only multiplication by `s` is needed.
- `N_(s)`: `SectionFractionPresentation L F s`, the quotient of the direct sum of these
  nonnegative numerator degrees by the submodule spanned by
  `ι_n(t) - ι_(n+b)(s^b t)`. This is a concrete presentation of the same localized module,
  not an arbitrary comparison object. At a common degree, equality means equality after
  further multiplication by a power of `s`, exactly the localization relation. Every finite
  sum reduces to one fraction by a common denominator. The scalar module is over
  `A = Γ(X, O_X)`, with addition and scalar action inherited from the quotient.
- Canonical map and isomorphism: `∃ e : SectionFractionPresentation L F s ≃+ Γ(F, U)`,
  together with the scalar-compatibility conjunct for every `r : Γ(X, ⊤)` and fraction `z`.
  Thus this is an isomorphism of `A`-modules, with target scalars restricted by
  `X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op`.
- Required formula on `t/s^n`: the final conjunct says
  `tmulSection (e (sectionFraction L F s n t)) (tensorPowSectionOne s n U) = res(t)`.
  On exactly this open, `s` is a free generator and tensoring with `s^n` is invertible, so
  this characterizes `res(t) ⊗ (s|_U)^(-n)` without choosing duality data. Together with
  additivity and the fraction generators this specifies the canonical map uniquely.
  It also forces compatibility with the localized section-ring action (tensor the same
  numerator formula for its homogeneous fractions); no unprescribed isomorphism is asserted.

Dependency APIs used: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`;
`Mathlib.Topology.Defs.Filter`, `CompactSpace`; upstream
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Scheme.Modules.IsInvertible`;
Mathlib `SheafOfModules.IsQuasicoherent` as explicitly identified by
`Sheaf.AlgebraicGeometry.Coherent` for `pqf-def-coherent`. Further existing APIs reused:
`nonvanishingLocus` in `Sheaf.AlgebraicGeometry.Ample`; `tensorPowSectionOne` and
`mulTensorPowSection` in upstream `Modules.ClearDenominators`; `tmulSection` and
`unitSectionsEquiv` in upstream `Modules.TensorSection`; Mathlib `DirectSum.of`,
`Submodule.span`, and `Submodule.Quotient.mk`. These imports all contribute used declarations.

Edge cases checked before writing: empty scheme, zero `F`, zero section `s`, a nowhere-zero
section, exponent zero, nilpotent coefficients and arbitrary characteristic. If `s=0`, the
nonvanishing open is empty and the relation with `b=1` kills every numerator, so the quotient
is zero as required. A nilpotent section similarly produces zero localization without any
non-zero-divisor hypothesis. When `s` is everywhere a generator, multiplication identifies all
numerator degrees with degree zero. For `n=0`, `s^0=1` and the tensor unit identifies the formula
with ordinary restriction. `uL` is arbitrary and no independent smaller test universe occurs.

Searches (all actually run with `/home/ubuntu/weil-launcher/msearch.py E1
lem-sc-p1-invertible-section-localization`, recorded in `searches.jsonl`):

- LeanFinder, `global sections invertible sheaf twists localization at section nonvanishing
  open`: eight hits on affine structure-sheaf localizations and `ModuleCat.Tilde`, no general
  invertible-section module statement.
- Loogle, `IsLocalization, Module`: twelve ordinary ring/module localization APIs, no
  twisted-section module or canonical comparison on qcqs schemes.
- LeanSearch, `localization graded sections invertible sheaf`: HTTP 500, unavailable,
  not interpreted as a no-match search.
- grep, `invert.s.sections|gradedSections|section.*[Ll]ocalization`, AlgebraicGeometry:
  seven hits on rings, projective-spectrum ring fractions and unrelated section headings.
- LeanFinder, `direct limit global sections tensor powers invertible module multiplication
  by section`: eight generic tensor-product/direct-limit hits, no section-fraction notion.
- grep, `SectionFractions|sectionFractions|twist.*[Dd]irect[Ll]imit|section.*[Dd]irect[Ll]imit`:
  one generic ModuleCat direct-limit section heading.
- `rg` of `WeilConjectures` and `lean/Sheaf` for these expressions, localization/twisted
  sections, and the proposed full names: no existing concrete section-fraction presentation
  or item statement. `rg` for the item id in upstream found none. The upstream section-power
  and multiplication maps exist and are reused. The landed `InvertibleSectionRing` is the
  ring with `F=O_X`, not the module fractions required here.
- DAG searches for section fractions, degree-zero localization, tensor fractions and the
  corresponding definitions found `def-sc-degree-zero-module-fractions`. Its actual module
  was read: it names a subset of `LocalizedModule T M` given an already constructed ring and
  module with degree subsets; it does not construct the tensor-power section module or its
  fraction presentation. No duplicate generic localized-module or degree-zero-subset API is
  written here. `tools/blueprint_refs.py search 'localization sections'` and
  `search 'section fractions'` each returned zero blueprint nodes. `ancestor` returned
  `lem-sc-p1-graded-resolution`.

Server validation: both modules compiled together without errors or warnings. Initial issues
were a repeated universe identifier in the combined-file compile and an underdetermined open
in scalar restriction; distinct `uL` and explicit `U ≤ ⊤` repaired both. No mathematical
statement was altered in that repair. All variables and universes are explicitly bound.

## New nodes

`def-sc-section-fraction-presentation` gives the concrete generators-and-relations module of
fractions of tensor-power sections, with the canonical fraction classes and their operations.
Source: Section 01PU and equation module-invert-s (Tag 0B5L), the presentation used in Lemma
01PW's numerator/power-torsion argument. Its definition is entirely explicit; there are no
` sorry` data or postponed law proofs. It is recorded in
`Sheaf.AlgebraicGeometry.SectionFractionPresentation`, with `sectionFractionRelations`,
`SectionFractionPresentation`, and `sectionFraction`. The actual searches listed above,
including unavailable LeanSearch, are also recorded in its `mathlib_searches`. The generic
`LocalizedModule.degreeZeroFractions` needs a preconstructed graded section module over its
section ring and does not give this concrete presentation. The ring-only `InvertibleSectionRing`
does not give it either. The new node cites the existing scheme and invertible-module notions,
and the item gains only this id in `stmt_deps`. Its blueprint ancestor and place are the
item's `lem-sc-p1-graded-resolution` comparison of graded sections on the standard opens.

## Second reading by E1

Read the sandbox node, both delivered modules, each of the four original dependency
nodes and their declarations, and the new definition node independently. Source checked
against properties.tex, lines 2202–2304, fetched read-only from the Stacks source:
https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex.
Also read https://stacks.math.columbia.edu/tag/01PW and the whole contextual section
https://stacks.math.columbia.edu/tag/0B5K, including equation 0B5L. The source introduces
an arbitrary scheme, invertible module, section and quasi-coherent module, and assumes
qcqs for part (2); it imposes no other ambient hypotheses.

Object/hypothesis/conclusion checklist (each verdict is a match):

- Scheme X: `X : Scheme.{uL}`. Read Mathlib's Scheme.lean:35–47 and the node
  def-pc-scheme. This is the locally affine locally ringed space of the source.
- Quasi-compact X: `[CompactSpace X]`. Read Filter.lean:279–285: compactness of
  the whole space, without separation, as def-weil-pbc-quasi-compact-scheme requires.
- Quasi-separated X: `[QuasiSeparatedSpace X]`. Read the equivalence at
  Morphisms/QuasiSeparated.lean:56–58: exactly compact intersections of affine opens.
  No separated-over-affine hypothesis of the upstream clearing-denominators theorem
  is imported as a binder into this statement.
- Invertible L: `(L : X.Modules) [L.IsInvertible]`. Read upstream
  Modules/Invertible.lean:55–61: every point has an open neighbourhood on which L
  is isomorphic to the unit module. This is def-sc-invertible-module's rank-one notion.
- Section s: `(s : 𝟙_ X.Modules ⟶ L)`. Evaluation at `unitSectionsEquiv ⊤ 1`
  gives the source's global section. Conversely a global section defines this morphism
  on each open by scalar multiplication with its restriction. The unit-sections
  equivalence was read at Modules/TensorSection.lean:292–303. Thus no section is lost.
- Quasi-coherent F: `(F : X.Modules) [F.IsQuasicoherent]`. Read
  pqf-def-coherent, its landed Coherent.lean, and Mathlib's class at
  ModuleCat/Sheaf/Quasicoherent.lean:249–252. The dependency explicitly identifies
  this Mathlib class for its quasi-coherent clause; its coherent main declaration
  would be a stronger and incorrect assumption here, and is appropriately not used.
- Nonvanishing open X_s: `∃ U : X.Opens` and equality of its underlying set with
  `nonvanishingLocus L (s.app ⊤ (unitSectionsEquiv ⊤ 1))`. Opened Ample.lean's
  definition: germ outside maximal-ideal times the stalk, exactly nonzero residue-field
  fibre. Openness is a conclusion, not an additional assumption. Equality determines U.
- Integer-graded N and its s-action: numerator degrees in the degree-zero localization
  over denominators s^n are precisely `n : ℕ` and `Γ(F ⊗ L.tensorPow n, ⊤)`.
  Negative twists exist in N but cannot contribute a homogeneous degree-zero numerator
  with a nonnegative denominator exponent. Read upstream tensorPowSection,
  tensorPowSectionOne, mulTensorPowSection and its associativity maps in
  ClearDenominators.lean:49–175. They encode exactly multiplication by s^b.
- Degree-zero localization: `SectionFractionPresentation L F s` is the concrete
  quotient of the direct sum by the span of the displayed transition differences.
  Every finite sum can be moved to one common denominator degree. Its equality
  relation is equality after further multiplication by a power of s, including torsion;
  this is exactly N_(s), not an arbitrary source of an isomorphism.
- Canonical map is an isomorphism: the additive equivalence `e` plus the `∀ r z`
  scalar equality is precisely an isomorphism over Γ(X,O_X), with the target module
  acted on through restriction to U. No arbitrary isomorphism remains: the last
  conjunct prescribes the value on every fraction generator.
- Formula t/s^n maps to res(t) tensor s^(-n): the `∀ n t` equation says
  `tmulSection (e (sectionFraction ... n t)) (tensorPowSectionOne s n U) = res(t)`.
  On U the section s generates L, so tensoring by s^n is bijective, also for arbitrary
  F. This is equivalent to the source's inverse-power formula. The source action
  of localized homogeneous section-ring fractions is likewise respected, as follows
  by applying this formula to tensor products of numerators; no additional action
  compatibility is left unspecified. Quantifiers and both parts of the isomorphism
  conclusion cover every source choice.

New-node reading: def-sc-section-fraction-presentation's statement introduces X, L, F,
s, A, all B_n, K, Q, and the canonical classes; each is rendered literally by the
three declarations of SectionFractionPresentation.lean. Its construction is available
for arbitrary L (it only needs nonnegative tensor powers); specializing it to the
node's invertible L gives exactly the intended presentation, without changing any
object. No data or laws are postponed. Read the source's fraction equivalence in
properties.tex:2265–2267 and its numerator degrees at 2202–2224. This presentation
is a concrete implementation of that construction. Its fields satisfy brief §5:
fresh definition id in the item's chapter, split status, cited scheme and invertible
notions, empty proof/dependencies, null mathlib_match, three search kinds, created
worker/item/date/group, ancestor and via, none audits, same chapter/unit and complete
Lean record. There are no dependency modules in this delivery.

Independent searches actually run (recorded by msearch in searches.jsonl):

- LeanFinder: `quasicoherent module sections over principal open as colimit of tensor
  twists` returned eight hits, notably ModuleCat.Tilde.toOpen, exists_const,
  openToLocalization and tildeInModuleCat. These are affine tilde-section constructions,
  not twisted section fractions or the general qcqs comparison.
- Loogle: `LocalizedModule.mk` returned ordinary localized-module fraction APIs
  (mk, induction_on, mk_neg, mk_eq_mk', smul'_mk), not the section module in question.
- LeanSearch: `sections quasicoherent tensor twists principal open colimit` returned
  HTTP 500; unavailable, not evidence of absence.
- msearch grep: `GammaStar|gammaStar|twist.*localiz|localiz.*twist` returned zero hits.
- Independently used rg on Mathlib/AlgebraicGeometry, all upstream WeilConjectures,
  and lean/Sheaf for section/localization in either order, sectionfraction, GammaStar
  and gammaStar. Hits are structure-sheaf or affine tilde localization, projective
  spectrum fractions, or unrelated localization sections. No matching declaration.
- Searched DAG text for fraction presentation, section fractions, tensor-power sections
  and degree-zero sections. Read def-sc-degree-zero-module-fractions and its actual
  DegreeZeroFractions.lean: it selects a subset of LocalizedModule given an already
  supplied ring/module/grading. It supplies neither these tensor-power sections nor
  their transition maps. InvertibleSectionRing is the ring-only construction, not
  this F-dependent module. Thus the new definition does not duplicate either notion.

Edge cases: empty scheme and zero F are allowed; all section groups then give the
appropriate zero quotient. For s=0 the b=1 transition kills each generator, and U is
empty. Power-torsion (including nilpotent s) is retained by the quotient relation,
without any regularity assumption. A nowhere-zero s makes all transition maps
invertible and recovers Γ(X,F). For n=0, the tensor unit and its right unitor give
ordinary restriction. The index is the fixed nonempty ℕ of denominator exponents;
there is no externally quantified index set to exclude. No field, characteristic,
Noetherian, dimension, nonempty-space or extra universe restriction occurs. uL and
u are explicitly bound and arbitrary, and every variable is bound by eye.

Mismatches and repairs: the new node and all four corresponding source docstrings
incorrectly said Section 01PU (actually the ample-restriction lemma). Corrected them
to Section 0B5K, whose equation 0B5L and following lemma 01PW are the actual source.
Also corrected the theorem docstring's scalar-ring notation from Γ(X,X) to Γ(X,O_X).
The earlier Worker report's 01PU citations should be read with this correction.
No mathematical signature or item statement needed correction; both lean.statement
records remain verbatim the signatures in the files. One theorem has only `sorry`,
no definition is hollow, and all declarations have the required source/blueprint
and the theorem has both proof steps. Imports and namespace conventions are correct.

Validation: compiled both delivery modules together with scompile.py in dependency
order on the server; delivery preflight and dry run recorded below.

Both modules compiled cleanly in 2.6 seconds (exit 0, no warnings). deliver2.py
--no-push returned OK: the full delivery passes preflight and compiles.

## Review by R-pis1207 (FIX)

The statement matches Stacks 01PW(2) hypothesis by hypothesis (qcqs X as `CompactSpace`/`QuasiSeparatedSpace`,
invertible `L`, quasi-coherent `F`, X_s as `nonvanishingLocus`, N_(s) as the direct-limit presentation over
nonnegative numerator degrees, additive equivalence with Γ(X,O_X)-compatibility and the prescribed value on
every generator `t/s^n`). One fix: the global section s ∈ Γ(X,L) was encoded as a morphism `𝟙_ X.Modules ⟶ L`,
and X_s was taken of `s.app ⊤ (unitSectionsEquiv ⊤ 1)`. Following the landed convention (C1 ae9de4f0c
`nonvanishing_section_trivializes`, E1 9c18da458, sibling F1 s-torsion), s is now `(s : Γ(L, ⊤))` in both
modules (the node says s ∈ Γ(X,L)), with `nonvanishingLocus L s` and the morphism
`homOfGlobalSection L s` wherever upstream `mulTensorPowSection`/`tensorPowSectionOne` need one;
`SectionFractionPresentation`, `sectionFractionRelations`, `sectionFraction` take `s : Γ(L, ⊤)`.
Both fixed modules compiled together (SHEAF_GROUP=L, no errors).
