## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSectionLocalization` defines the integer tensor-power
notion `integerTensorPower`, the graded direct sum `H0Star`, and the localization record
`DegreeZeroLocalization`; it states `affine_section_localization` with proof `sorry`.
The theorem binds an affine scheme `Y`, an invertible module `L`, a quasi-coherent module `F`,
a global section `s`, and an open `U` identified pointwise with the nonvanishing locus. Its
conclusion is bijectivity of the canonical degree-zero localization map, represented by
`D.map`; this is the Lean rendering of the fraction map `ξ/s^n ↦ s⁻ⁿξ`.

The integer tensor-power definition uses `L.tensorPow n` for nonnegative integers and
`(Lᵛ).tensorPow (n+1)` for negative integers. `H0Star` is the direct sum over `ℤ` of global
sections of `F ⊗ₘ L^{⊗ n}`. The localization record carries the additive map from this graded
section object to sections over `U`.

Dependencies used: `def-sc-invertible-module` is rendered by
`AlgebraicGeometry.Scheme.Modules.IsInvertible` (source declaration, imported through
`WeilConjectures.AlgebraicGeometry.Modules.Dual`); `pqf-def-coherent` is rendered by
`SheafOfModules.IsQuasicoherent`; `def-pur-sheaf-tensor-product` is rendered by
`Scheme.Modules.tensorObj` and notation `⊗ₘ`; `def-weil-pbc-ample-invertible-module` is
rendered by `Scheme.Modules.nonvanishingLocus` from `Sheaf.AlgebraicGeometry.Ample`; and the
scheme notion is Mathlib `AlgebraicGeometry.Scheme` with `[IsAffine Y]`.

Edge cases checked: `n = 0` gives the unit tensor power; negative indices use the dual; the
section `s = 0` is allowed and yields the empty nonvanishing locus; and no nonemptiness of `Y`
or `U` is assumed. The universe is shared by the scheme, modules, direct sum, and sections.

Searches made: LeanSearch query “degree zero localization of graded sections of a
quasi-coherent sheaf at a section of an invertible sheaf” (no declaration for scheme sheaf
section localization); LeanFinder query “sections on affine scheme after inverting a section
of an invertible module” (only structure-sheaf basic-open localization declarations); grep
`rg -n -i 'invert.*section|section.*localiz|graded.*section'
/home/ubuntu/weil-src-slopmaster2/.lake/packages/mathlib/Mathlib/AlgebraicGeometry` (no theorem
for invertible-module section localization). Existing project declarations were searched with
`rg -n 'SectionRing|tensorPow|localization' lean/Sheaf` and the source tree; only the positive
section ring was found, so the integer graded section and localization statement were written.

## Earlier second reading (a previous round; superseded)

I reread the node and source Properties Lemma 01PW (part (2)) and checked each hypothesis:
`Y` affine is `[IsAffine Y]`; `L` invertible is `[L.IsInvertible]`; `s` is a global section;
`F` is quasi-coherent; `U` is the nonvanishing locus via `hU`. The conclusion is
`Function.Bijective D.map`, corresponding to the canonical localization comparison. The
module compiles cleanly on the server with the one expected `sorry` proof warning suppressed.

## Second reading by G1

Read the item's JSON, both proof dependency nodes, all five statement dependency nodes,
and their actual declarations. Read Stacks Properties `lemma-invert-s-sections` (01PW),
its preceding `equation-module-invert-s` and proof, and Cohomology of Schemes
`lemma-invert-s-cohomology` (09MR), including the affine p = 0 clause. The local literature
checkout has no Stacks .tex files, so official stacks/stacks-project sources were fetched
into this item's scratchpad; the same paragraphs were independently available in the
local c1-stacks-review source cache. No repository/source checkout was edited directly.

Object/hypothesis/conclusion inventory and matching:

1. An arbitrary affine scheme Y: `(Y : Scheme.{u}) [IsAffine Y]`. PASS. The Mathlib scheme
   and affine-scheme definitions impose neither a field nor Noetherian assumptions.
2. An invertible O_Y-module L: `(L : Y.Modules) [L.IsInvertible]`. PASS. Opened the source
   Modules/Invertible.lean:57: local isomorphism with the structure sheaf. This is the
   recorded scheme-module notion, not an unrelated invertibility predicate.
3. An arbitrary quasi-coherent O_Y-module F: `(F : Y.Modules)` and
   `[SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) F]`. PASS. Read the recorded
   Coherent.lean: it explicitly delegates the quasi-coherent clause to this Mathlib
   declaration (local presentations), not its new coherent predicate. No coherence,
   finite type or rank condition was added.
4. A global section s: `(s : Γ(L, ⊤))`. PASS. The source `homOfGlobalSection L s`
   identifies this with O_Y → L; read PullbackFreeGenerator.lean:54 and its formula.
5. Integral graded sections H^0_* using duals in negative degrees, localized in degree
   zero: the original `H0Star` direct sum was not localized. FAIL, repaired. The new
   `SectionFractionLocalization L F s` is a real quotient presentation: its generators
   are `Γ(F ⊗ L.tensorPow n, ⊤)` for n ≥ 0, and its relations identify t/s^n with
   (t ⊗ s)/s^(n+1). Every degree-zero homogeneous fraction has numerator degree n
   equal to the nonnegative exponent of its denominator; negative degrees never supply
   such fractions. Every finite sum can be brought to a common denominator. The quotient
   is therefore the additive carrier of precisely the node's degree-zero localization,
   with no truncation of any degree-zero fractions. Full integer grading is auxiliary
   data unnecessary to this presentation; removed the unused private integer-power and
   graded-sum definitions rather than inventing a second integer tensor-power system.
6. The nonvanishing open Y_s: `(U : Y.Opens)` and
   `hU : ∀ y, y ∈ U ↔ y ∈ nonvanishingLocus L s`. PASS. Read Ample.lean:31: germ not
   in maximal ideal times stalk, precisely nonzero residue-field value. Taking an open
   with this carrier is a presentation of Y_s, not an extra geometric hypothesis.
7. The canonical fraction map ξ/s^n ↦ s⁻ⁿξ: originally `D.map` was an arbitrary
   additive map from the unlocalized direct sum, and neither s nor U constrained it.
   FAIL, repaired. The displayed equality now specifies the image of every fraction:
   restriction of t equals multiplication by s^n of `e (sectionFraction L F s n t)`.
   Since s is a free generator on U, multiplication by s^n is invertible there; thus
   the equality determines that image uniquely and is exactly the canonical formula.
8. That canonical map is an isomorphism: `∃ e : SectionFractionLocalization L F s ≃+
   Γ(F, U), ...` with the formula above. PASS after repair. This states existence of the
   canonical additive equivalence, not existence of an unrelated equivalence. It implies
   the canonical module isomorphism too: multiplication and restriction are linear, the
   formula forces compatibility with multiplication by global functions, and numerator
   generators generate the quotient. Conversely the source's module isomorphism supplies
   this equivalence. No arbitrary map/record binder remains.

The original statement is demonstrably false: over Spec ℤ with L = F = O and s = 1,
the record permits the zero map although sections on U = Y are nonzero. This was a Lean
encoding fault, not a fault in the node's natural-language statement. The latter, its
proof and its proof dependencies were left unchanged; no statement_change is needed.
Added only the missing definition dependency under the stage-2 extra-nodes rule.

Dependencies were checked by signatures and bodies. `tensorPow` is the source's recursive
nonnegative tensor power with zeroth power O_Y. `tensorPowAddIso` supplies exponent addition;
`tmulSection` tensors actual sections. The scheme-module monoidal structure is the source
`SheafOfModules.monoidalCategory`, and `tensorObjIsoSheafification` identifies it with the
sheafification of the sectionwise presheaf tensor product, exactly the tensor clause of
`def-pur-sheaf-tensor-product`. No separate tensor construction was introduced. The source
imports make these existing declarations available; importing the project's generic tensor
module would add unused declarations, not a different tensor operation.

Edge cases: s = 0 gives U empty and all transition maps zero; the relation subgroup kills
every summand, giving the zero localization and the unique empty-open sections. F = 0 and
the empty scheme likewise give zero groups. n = 0 uses the existing monoidal unit and
right unitor, so the fraction formula is restriction, not an excluded case. There is no
empty variable index set (the fixed denominator indices are ℕ); no nonemptiness of Y/U,
characteristic, domain, field, finiteness or separatedness binder is imposed. Universes
u/uSL are explicitly bound and cover every scheme universe, with sections and quotients
in its universe; the fixed ℕ index does not restrict scheme size. The separate universe
names avoid duplicate declarations when the delivery modules are compiled together.

Independent searches (recorded by msearch.py): LeanSearch “direct limit tensor powers line
bundle global sections nonvanishing open” was unavailable (HTTP 500), so no verdict is
claimed for it. LeanFinder “invertible sheaf graded module fractions degree zero localized
sections” returned 8 Proj/structure-sheaf ring localization results; opened/checked the
relevant signatures, which are not this sheaf-module statement. Mathlib grep
`section.*(fraction|localization)|localization.*section|tensorPowSection` found only ring
or structure-sheaf localization. Independent rg on WeilConjectures and lean/Sheaf using
`localiz`, `fraction`, `colimit`, `tensorPowSection` and the proposed declaration names
found tensor-power section operations and the nonnegative section ring, but no scheme
section-module fraction construction or this theorem. Searched DAG definition nodes and
read `def-sc-degree-zero-module-fractions` and `def-sc-localized-homogeneous-piece`, together
with their modules: both take an already constructed graded ring/module and s-action;
neither constructs the tensor-power section module or its fraction presentation. The new
node supplies that missing construction using existing additive direct-sum/quotient APIs.
It does not duplicate their predicates on localized ring modules.

H5/H6/H8/H9: every definition has explicit data, no proof or data sorry. The sole theorem
proof is sorry. Removed the empty localization record, restored the copyright header,
and replaced its inadequate theorem docstring with the node's two proof steps and their
named dependencies. All new declarations have source and blueprint docstrings; line
lengths are ≤ 100. The new node was independently matched against the source's numerator,
denominator and fraction-identification paragraphs. Its fields follow §5, no maintainer
fields are supplied. There are no dependency modules or node statement corrections.

Validation: both delivery modules compiled together on the server cleanly (2.4 seconds),
with no errors or warnings. No global build was run. Node signatures were regenerated
using the project's stage2_delivery declaration reader, so the recorded signatures match
the files exactly under the tool's whitespace normalization.

## New nodes

`def-sc-section-fraction-localization`: degree-zero tensor-power section localization,
constructed as the direct sum of numerator groups modulo the additive relations induced
by multiplication by the given section. `sectionFraction` supplies its numerator classes.
Source: Stacks Properties equation module-invert-s and the fraction-equivalence paragraph
in Lemma 01PW's injectivity proof. The missing object is now real data in its own module,
`Sheaf.AlgebraicGeometry.SectionFractionLocalization`. Searches and the comparison with
existing generic homogeneous-localization predicates are detailed in the second reading
above. The node has empty proof/proof_deps, source, three search kinds (LeanSearch explicitly
unavailable), created provenance, inherited chapter/unit and blueprint ancestry, and its
own complete Lean record; the item cites it. No new fact is assumed by the definition.

Dry-run repair: the ancestry check follows the full current blueprint chain, which extends
the old item copy's abbreviated via list. Updated only the new node's via to that complete
chain, as reported by the preflight. The existing item's ancestry fields were not edited.

## Reviewer fix (R-asl1222)

The delivered new node def-sc-section-fraction-localization and its module
`Sheaf.AlgebraicGeometry.SectionFractionLocalization` duplicated the landed
def-sc-section-fraction-presentation (E1 fd20d27a0): the same quotient of
`⨁ n, Γ(F ⊗ L^n, ⊤)` by the s-multiplication relations, and even the same full names
`AlgebraicGeometry.Scheme.Modules.sectionFractionRelations` / `sectionFraction` (H4/H12).
Dropped the node and the module; the statement now uses the landed
`SectionFractionPresentation`/`sectionFraction` in the form of the landed general lemma
lem-sc-p1-invertible-section-localization (`exists_sectionFraction_nonvanishing_equiv`)
with `[IsAffine Y]`: an open U with carrier `nonvanishingLocus L s`, an additive
equivalence compatible with restricted scalars, and the fraction formula
`e(t/s^n) ⊗ s^n = t|_U`.
