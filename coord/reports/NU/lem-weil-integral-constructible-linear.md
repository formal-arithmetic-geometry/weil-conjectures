## Worker report

The module `Sheaf.Paper.IntegralConstructibleLinear` states
`WeilConjectures.integralConstructible_linear`, with its whole proof postponed by
`sorry`. The helper `integralConstructibleTriangulatedStructure` extracts component
2 of the already recorded triangulated-closure theorem; it constructs no new shift
or triangulation and proves no new lemma. No mathematical statement is corrected.

Hypotheses and clauses, matched individually:

- The source's global finite-field convention is `D : FiniteFieldDatum.{d}`.
  The prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` renders ell != p.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. Its actual valuation ring and chosen
  uniformizer are the recorded `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`, used by the coefficient sheaves.
- The scheme is arbitrary `Y : AlgebraicGeometry.Scheme.{u}`, following the
  recorded bounded-integral interface. No geometric finiteness, nonemptiness,
  separatedness, or characteristic condition on Y is imposed.
- The ambient category is exactly `completedIntegralDerivedCategory l E Y D hl`:
  the derived category of module sheaves over the inverse-limit coefficient
  sheaf, rather than the discrete constant O_E sheaf.
- The existential family `c` consists of unital ring maps from O_E to sections
  on EVERY object of the opposite small pro-etale site. Its first conjunct
  says the maps commute with EVERY restriction map.
- Its second conjunct says that for EVERY object, EVERY finite positive level
  n+1, and EVERY a in O_E, projection of c(a) is `toSheafify.app U` applied to
  the lifted class `Ideal.Quotient.mk ... a`. This uniquely specifies the
  constant sections of the inverse-limit sheaf, and in particular the map
  to global sections at the terminal site object. Naturality identifies c_U
  with restriction of that global section. Completeness of O_E identifies
  the source with lim A_E,n; no identification with a discrete constant
  coefficient sheaf is assumed.
- The first existential `Linear O_E (completedIntegralModuleSheaves ...)`
  supplies the Hom module structures and composition bilinearity. The following
  sectionwise identity `(a • f).val.app U x = c U a • f.val.app U x` fixes this
  structure to the specified coefficient action, rather than an arbitrary one.
- The next existential supplies `Linear O_E (completedIntegralDerivedCategory ...)`.
  Linearity of `DerivedCategory.Q` requires that this is the induced action
  from complexes of those module sheaves. In particular Q sends multiplication
  by c(a) on complexes to a times the identity, and bilinearity specifies the
  action on all derived morphisms, including localized ones.
- `∀ m : ℤ, Functor.Linear O_E (shiftFunctor ... m)` renders linearity of
  EVERY ambient integer shift.
- The full subcategory is the exact recorded
  `boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y`.
  Its Hom module structure is Mathlib's `Linear.fullSubcategory` from the
  selected ambient structure. The inclusion `.ι` is asserted linear, and
  the last clause asserts linearity of EVERY induced integer shift.
  Its triangulation is precisely the inherited one supplied by the named
  dependency theorem, extracted by the helper instance.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the recorded
  coefficient definitions from `Sheaf.NumberTheory.Padics.CoefficientExtension`:
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionIdeal`,
  `coefficientExtensionRing`, `coefficientExtensionTransition` and the chosen
  uniformizer. The main record's `Padic.finite_coefficientExtensionRing` supplies
  the required finite-level interface without changing those constructions.
- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `WeilConjectures.completedIntegralCoefficientSheaf`,
  `completedIntegralCoefficientProjection`, `completedIntegralModuleSheaves`,
  `completedIntegralDerivedCategory`, and `integralCoefficientSheaf`.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`:
  `WeilConjectures.boundedConstructibleDerivedCompleteIntegral` and its
  `boundedConstructibleDerivedCompleteIntegralCategory` full subcategory.
- `Sheaf.Paper.IntegralConstructibleTriangulated`:
  `WeilConjectures.boundedConstructibleDerivedCompleteIntegral_isTriangulated`;
  also its fixed-size sheafification and locally-bijective instances. This
  dependency landed while this worker was checking an older sandbox draft;
  the delivery now imports the landed declaration and contains no replacement.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear` and
  `CategoryTheory.Linear.fullSubcategory`. Its `homModule`, `smul_comp`, and
  `comp_smul` fields are exactly the module and bilinearity conditions.
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`: the existing linear
  structure, linear localization, and linear shift instances, used in the
  proof plan for `lem-weil-linear-abelian-derived-category`.
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`:
  `Padic.finite_module_adic_complete_and_hom` (part 2 of
  `lem-pod-adic-limit-finite-modules`), imported for the rank-one completeness
  identification in proof step 1.
- The limit is Mathlib `CategoryTheory.Limits.limit` and its projections;
  module sheaves are the recorded `CategoryTheory.ringedSiteModules` alias of
  `SheafOfModules`; the derived category and Q are Mathlib's standard
  `DerivedCategory` localization. No private copies of these notions occur.

Edge cases checked: the empty scheme and zero module/derived objects impose
no extra requirements. Constant sections into the zero section ring on an
empty object remain unital ring maps. The integer shift includes zero and
negative integers. The natural index n starts at exponent n+1, so the first
quotient is A_E,1, with no accidental zero-level quotient. E = Q_l and arbitrary
finite ramification are allowed. The scheme and coefficient universe follows
exactly the recorded integral category; the site retains object universe u+1
and morphism universe u, and the repaired general dependency interfaces retain
separate t and u with coefficient size max u (t+1).

Searches (all searched before adding declarations):

- `msearch.py leanfinder`, query “The derived category of sheaves of completed
  integral coefficient modules is linear over the valuation ring and its
  shifts are linear”: general DerivedCategory linear/localization/shift
  instances; no theorem for this coefficient action or constructible category.
- `msearch.py leanfinder`, query “The derived category of completed integral
  coefficient sheaves on the pro-etale site and its constructible subcategory
  are linear over the valuation ring”: eight condensed-module results,
  none states this node.
- `msearch.py loogle`, `SheafOfModules, CategoryTheory.Linear`: zero hits.
- `msearch.py grep`, `Linear|homModule`, subdirectory
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- Source and side-library `rg` for `integralConstructible_linear`, the item id,
  `Linear.*SheafOfModules`, and `SheafOfModules.*Linear`: no identical theorem;
  unrelated module/global-scalar results and sheaf free-section linear maps
  do not concern completed integral coefficients.
- `dag/lean_names_upstream.json` checked for the new names: no collision.
  The existing scalar-linearity Mathlib instances and the recorded source
  definitions were read in full at their actual signatures and docstrings.
- The previous sandbox's triangulation searches (`leanfinder` for integral
  constructible derived-complete triangulated subcategories and Mathlib grep
  for `integralConstructible|boundedConstructibleDerivedComplete`) found only
  generic derived triangulation. That dependency has now landed and is reused.
  No new DAG notion or definition node is required.

Validation: `scompile.py NU lem-weil-integral-constructible-linear` compiles
all six delivery modules separately in dependency order, including the affected
integral-category and triangulation sources. All are clean, with
only the expected postponed theorem proofs. The delivery dry run is the final
mechanical check. An initial record-extraction error at the named argument
`C := ...` was repaired by recording the full signature through the theorem
body delimiter. The author leaves the independent second-reading section to
the next reader, as required by the dry-run wrapper.

## Repair of returned delivery

The return identified two file-only compilation failures. First, the local overlay
tried to compile `DerivedCompleteIntegralDetailed` before the delivered
`DerivedComplete` artifact existed. Both `DerivedCompleteIntegralDetailed` and
`IntegralConstructibleTriangulated` now belong to the same dependency-ordered source
packet, with their existing node records repaired under section 1(B). This lets the
file-only compiler build the entire consumer chain in order. They retain their
recorded definitions, theorem statements, structures and proof plans verbatim;
only module documentation and Lean metadata change.

Second, the server's compiled `IsKFlatResolution` interface rejected the three
explicit universe arguments in `IntegralReductionTower`. Those three applications,
and the matching application in `DerivedComplete`, now omit the explicit universe
list. The explicit topology, commutative coefficient sheaf and complex morphism
still determine the same universes: site objects t+1, site morphisms t, coefficients
max u (t+1). The canonical maps and all mathematical hypotheses are unchanged.
This supersedes the explicit-universe description in the earlier second reading;
that independent reading predates this repair and must be checked again by the
next reader. The item's own theorem and its hypothesis/clause matching are unchanged.

All six node records use the current UTC date (`date -u +%F`: 2026-10-15). No statement correction or new node
is needed. The revised six-file packet compiles through `scompile.py` with no errors or
extra warnings. The first dry run found a truncated triangulation signature record
at its named `C :=` argument; the record now includes its full signature through
the actual theorem-body delimiter. The final dry run checks the repaired metadata.

## Dependency modules

`lem-weil-integral-reduction-tower-well-defined`: the returned immutable-head repair required the actual canonical well-definedness source in the packet. Its published artifact exposed the stale fixed-universe K-flat interface. The paired module publicly imports `Sheaf.Algebra.Homology.KFlat` and gives every `IsKFlatResolution` binder the independent specialization `{t + 1, t, max u (t + 1)}`; all tower comparison, augmentation and transition formulas remain unchanged.

`def-weil-integral-derived-reduction`: this transitive dependency is compiled beside the repaired K-flat and tower interfaces so the canonical additive change-of-rings functor and derived reduction comparison are available to the repaired well-definedness source. Its declarations and statements are unchanged.

`def-pc-kflat-complex`: the published compiled interface fixes coefficient
size to the maximum of site universes, while its recorded source provides
independent u, v, w. The paired module explicitly retains
`isMonoidal_W_separateHomUniverse.{u,v,w}`, `monoidalCategory.{v,u,w}`, and
`IsKFlat.{u,v,w}`. It has the SAME acyclic-total-tensor definition and K-flat
resolution predicate, with the existing named infrastructure theorems and
proof docstrings. Its source is recompiled alongside the consumer chain to
expose the recorded general interface. The only new source text explains the
paired use; the mathematical declarations are unchanged.

`def-weil-integral-reduction-tower`: compiling its recorded source against
the stale K-flat artifact gives a coefficient-universe type mismatch. Its
paired source lets Lean infer the `IsKFlatResolution` universes from the explicit
site, coefficient sheaf and complex morphism. Its actual `Functor.ofOpSequence`, localized transition
maps, unit maps with the inverse resolution isomorphism, naturality statement,
and cone are unchanged. No arbitrary comparison or map is introduced.

`def-weil-derived-complete`: this paired source likewise infers the
K-flat-resolution specialization and recompiles the canonical tower dependency.
Its definition remains existence of a representative, K-flat resolution, and
Roos triangle with the CANONICAL tower legs and first arrow. The product and
last Roos arrow remain existential, as the recorded node requires. The site
and coefficient universes remain independent. These three already landed
nodes are added to the item's statement dependency list to record the exact
paired interfaces used by its integral-category dependency chain.


`def-weil-derived-complete-integral-detailed`: include its existing canonical
`boundedConstructibleDerivedCompleteIntegral` object property and full subcategory
in the packet because its import of the paired `DerivedComplete` could not be
compiled before that sibling's artifact existed. Its exact predicate remains
completeness plus constructibility of every positive reduction in one common
cohomological interval; no definition or binder changes.

`lem-weil-integral-constructible-triangulated`: include its existing sheafification
specializations and the exact isomorphism-closed/triangulated theorem in the packet
because its detailed-category dependency must follow the paired completeness
module. The full source proof docstring and theorem signature remain unchanged.
The source packet now contains the complete chain through the item's two direct
category dependencies rather than asking the overlay to compile them early.

## Earlier second reading (a previous round; superseded)

Independent second reading, 2026-10-16. I read the item node and all four
sandbox modules, then the recorded dependency signatures and their definitions.
Verdict: the Lean says what the node says. No mathematical or Lean repair was
needed; this reading adds this audit and independent search evidence only.
There is no `statement_change` and no new definition node.

Source checked first: blueprint `def-weil-rationalization-karoubi.md`, order
1460, assumes the global finite-field datum, a prime ell distinct from p, a
finite extension E/Q_ell, an arbitrary scheme Y, and the integral category with
its O_E-linear triangulated structure. It imposes no qcqs, Noetherian,
separatedness, or nonemptiness condition on Y. I also read Stacks `dga.tex`,
Definition 09MJ and the following definition of linear functor;
`sites-modules.tex`, Definitions 03CW and Lemma 03DA; and `derived.tex`,
Definition 05RU with its abelian-category context. They add no geometric
hypothesis. Bhatt--Scholze Section 6.5 itself works with qcqs X, but this item
uses the blueprint's arbitrary-scheme, uniformly bounded-reductions variant,
whose triangulation is the already recorded dependency. Its scalar-linearity
calculation does not use qcqs. I read the actual dependency theorem rather
than importing the stronger assumptions of that external discussion.

The node's objects, hypotheses and conclusion, item by item:

1. Global characteristic p and prime ell != p: `D : FiniteFieldDatum.{d}`,
   `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p`. The finite-field datum comes
   from the source's global convention and the completed-coefficient
   dependency. Verdict: exact; no condition on Y being over that field.
2. Finite extension E/Q_ell: `E : Type u`, `[Field E]`,
   `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
   Verdict: exact finite field extension; no extra topology or valuation
   supplied by the caller.
3. Its valuation ring, uniformizer and quotients: the statement uses the
   recorded `Padic.coefficientExtensionIntegers l E`,
   `coefficientExtensionIdeal l E (n + 1)` and
   `coefficientExtensionRing l E (n + 1)`. I read
   `CoefficientExtension.lean`: these use the spectral absolute value,
   the chosen uniformizer, its principal ideal power, and the actual ring
   quotient. `CoefficientExtensionFinite` preserves those definitions.
   Verdict: the node's O_E and A_E,n, with no abstract replacement ring.
4. An arbitrary scheme Y: `(Y : AlgebraicGeometry.Scheme.{u})`, with no
   additional typeclass. `Scheme.ProEt Y` and `ProEt.topology Y` are the small
   weakly-etale site with fpqc covers; I read Mathlib `Sites/Proetale.lean`,
   the group clone's upstream `Proetale/Basic.lean`, and the framework note.
   Verdict: the recorded site, with object universe u+1 and morphism universe u.
5. Ambient D(Y_proet,O_E): `completedIntegralDerivedCategory l E Y D hl`.
   I opened `CompletedIntegralCoefficients`: its coefficient sheaf is
   `limit (integralCoefficientSheafSystem l E Y)`, projections are `limit.π`,
   module sheaves are `ringedSiteModules` = `SheafOfModules`, and its derived
   category is Mathlib `DerivedCategory` with `HasDerivedCategory.standard`.
   Verdict: modules over the inverse-limit ring sheaf as required.
6. Canonical map from O_E = lim A_E,n to global sections: `∃ c : ∀ U, O_E →+*
   (completedIntegralCoefficientSheaf ...).obj.obj U`, with the first
   conjunct requiring naturality for all restriction arrows and the second
   requiring every projected section to equal the sheafification of the
   quotient class of a. Verdict: exact canonical action. Limit projections
   jointly determine c; it is not a freely chosen scalar map. The terminal
   object Y gives the required global section, and naturality gives all its
   restrictions. Positive exponents form the same cofinal completion tower.
7. Action on Hom groups: the first `∃ (_ : Linear O_E
   (completedIntegralModuleSheaves ...))` and the sectionwise identity
   `(a • f).val.app U x = c U a • f.val.app U x` fix the action before
   localization. The next `∃ (_ : Linear O_E
   (completedIntegralDerivedCategory ...))`, together with
   `Functor.Linear O_E (DerivedCategory.Q ...)`, extends that SAME action
   to the derived category. Verdict: the constant-section action on every
   derived Hom group. The localization clause fixes the images of scalar
   endomorphisms; composition then fixes scalar multiplication of all
   localized arrows as well.
8. Composition O_E-bilinear: `CategoryTheory.Linear` has `homModule`,
   `smul_comp` and `comp_smul`, over the fixed preadditive structures. I read
   their fields in `CategoryTheory/Linear/Basic.lean`. Verdict: all module
   and bilinearity clauses, including additivity, are present.
9. Ambient shift functors linear: `∀ m : ℤ, Functor.Linear O_E
   (shiftFunctor (completedIntegralDerivedCategory ...) m)`.
   Verdict: every integer shift, not just the shift by one.
10. The consequent full category D^b_c(Y,O_E):
    `boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y` is the
    recorded full subcategory of derived-complete objects whose positive
    reductions are intrinsically constructible in one common integer
    cohomological interval. I read both its object property and abbreviation.
    Verdict: the node's exact category, with uniform reduction amplitude.
11. Its specified triangulation: `integralConstructibleTriangulatedStructure`
    extracts `.2` of `boundedConstructibleDerivedCompleteIntegral_isTriangulated`.
    That theorem has the same coefficient and scheme binders and asserts
    `IsClosedUnderIsomorphisms ∧ IsTriangulated` for this object property.
    Mathlib's `Triangulated/Subcategory` provides the inherited shifts and
    triangles. Verdict: precisely the dependency's structure, without a
    new closure hypothesis or a new triangulation.
12. Its O_E-linear structure and linear shift: `Linear.fullSubcategory`
    supplies the inherited Hom modules; `Functor.Linear O_E (...).ι`
    states compatibility of inclusion, followed by `∀ m : ℤ,
    Functor.Linear O_E (shiftFunctor (...Category ...) m)`.
    Verdict: all concluding clauses, with the ambient scalar action.

Quantifier order is correct: fix the source data first, choose the canonical
section maps, then a sheaf-level linear structure constrained by those maps,
then an ambient derived linear structure compatible with Q, then assert the
shift and full-subcategory properties. The existential structure binders are
class-valued and register the structures used by subsequent scalar notation.
No free variable or universe is left unbound. The common E/Y universe is the
recorded integral-subcategory convention, not an equality of site object and
morphism universes. Any coefficient field and scheme can be placed in a
common larger ambient universe; no finiteness or smallness premise is added.

Edge cases: Y may be empty; the empty-object section ring is the zero ring,
which admits the indicated unital map, and zero module sheaves and zero
complexes are included. No nontriviality of a Hom group is required. There is
no optional index set that is assumed nonempty: the fixed completion tower
is ℕ, with `n = 0` representing exponent one. Thus no source level is lost
and no spurious quotient by the unit ideal enters. Shifts include zero and
negative integers. The prime two, every allowed residue characteristic,
E = Q_ell and arbitrary finite ramification are covered. Nothing forces
char(Y) = p. The auxiliary field-datum universe d is independent of u.

I read each paired dependency against its own node and source, not merely
its name. `def-pc-kflat-complex` is the acyclic total-tensor predicate of
Stacks 06YN, with a quasi-isomorphism for its resolution; its independent
u,v,w interface and essentially-small condition are unchanged from the
recorded source. `def-weil-integral-reduction-tower` uses actual termwise
reduction, `Functor.ofOpSequence`, transitions Q(tau_n), and augmentation
[q] inverse followed by Q(gamma_n). `def-weil-derived-complete` requires the
Roos triangle with precisely the canonical cone legs, transported from a
representative, with first arrow `Pi.lift` and second arrow 1-s. I checked
Bhatt--Scholze p. 24, Proposition 3.5.1 and Definition 3.5.2, and the
blueprint's explicit triangulated-category formulation. The paired source
differences are explanatory comments plus explicit
`IsKFlatResolution.{t+1,t,max u (t+1)}` applications in the last two modules.
They preserve maps, predicates, objects and hypotheses. No arbitrary map,
Nonempty choice or site-universe identification replaces a construction.
The three nodes change only `lean`, have explanatory `lean.note`, and are
cited in the item's added dependencies. No new node needs a stage-1 audit.

Independent searches, using different wording from the first worker:

- LeanFinder: “A sheaf of modules over a commutative ring sheaf is linear
  over its global sections and the derived localization preserves this
  scalar action.” Eight results, concerning module structures on sections,
  tilde modules, and module sheafification; none gives this statement.
- Loogle: `SheafOfModules, CategoryTheory.Linear`: zero results. A second
  quoted-name query found only a smallness instance in sheaf limits.
- Mathlib grep through msearch, `Linear.*SheafOfModules|SheafOfModules.*Linear|homModule`
  in `Algebra/Category/ModuleCat/Sheaf`: zero results.
- Direct rg in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for `Linear .*SheafOfModules`, `Linear .*ringedSiteModules`,
  `completedIntegral.*[Ll]inear`, and the two proposed declaration names:
  no matching theorem or duplicate name. Scheme scalar-cohomology and
  restricted-scalar-cone results have different objects and conclusions.
- LeanSearch was attempted independently and returned Internal Server Error;
  this is recorded as unavailable. The other searches completed.

The generic Mathlib derived-linearity, Q-linearity, integer-shift and
full-subcategory instances were opened and checked at their actual
signatures. They are reused, and do not already state the canonical completed
coefficient action. The proof docstring follows all five node proof steps,
including finite-module completeness, coordinatewise sections, sheaf Hom
scalars, linear localization, and inheritance to the full subcategory.
All definitions have real data; every theorem body in these delivery modules
is postponed. No statement correction, proof, or duplicate notion was added.

Validation: independent `scompile.py` on all four delivered files succeeded,
with no errors or extra warnings. It also recompiled the affected
`DerivedCompleteIntegralDetailed` and `IntegralConstructibleTriangulated`
imports. Each invocation stayed below 3 seconds, with nice 19, two threads,
and the unchanged 60-second limit. All four `lean.statement` records match
the full signature text verbatim; all Lean lines are at most 100 characters.

## Earlier second reading (a previous round; superseded)

I reread the source place, the node copy, every recorded dependency signature, and
the delivered declarations. The source is the hypothesis in
`def-weil-rationalization-karoubi` (blueprint order 1460): for a global finite-field
datum, a prime `l != p`, a finite extension `E/Q_l`, and a scheme `Y`, the integral
constructible category is assumed to be `O_E`-linear and triangulated with
`O_E`-linear shifts. The source adds no qcqs, Noetherian, separatedness,
connectedness, or nonemptiness hypothesis on `Y`.

The node's objects, hypotheses, and conclusion match the Lean as follows.

1. The characteristic datum and prime are rendered by `D : FiniteFieldDatum.{d}`,
   `l : Nat`, `[Fact l.Prime]`, and `hl : l != D.p`. Verdict: exact global
   characteristic and distinct-prime hypotheses.
2. The finite extension is rendered by `E : Type u`, `[Field E]`,
   `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`. Verdict:
   exact finite extension data, with no extra field or topology assumption.
3. The valuation ring, uniformizer, and finite quotients are the recorded
   `coefficientExtensionIntegers l E`, `coefficientExtensionIdeal l E (n+1)`,
   and `coefficientExtensionRing l E (n+1)`. Verdict: the dependency's actual
   chosen coefficient datum is used; no replacement quotient is introduced.
4. The scheme is the arbitrary `(Y : AlgebraicGeometry.Scheme.{u})`; its site is
   `Scheme.ProEt Y` with `ProEt.topology Y`. Verdict: the small pro-etale site,
   with its separate object and morphism universes, is retained.
5. The ambient completed coefficient sheaf and derived category are rendered by
   `completedIntegralCoefficientSheaf l E Y D hl`,
   `completedIntegralModuleSheaves l E Y D hl`, and
   `completedIntegralDerivedCategory l E Y D hl`. Verdict: these are the
   recorded inverse-limit sheaf, module category, and derived localization.
6. The canonical coefficient action is the existential `c` whose components are
   ring maps from `coefficientExtensionIntegers l E`, natural under every site
   map and whose every projection is the sheafified quotient class at exponent
   `n+1`. Verdict: both the canonical-section and all finite-level projection
   clauses are present, with the same quantifier order.
7. The sheaf-level action is the existential
   `Linear ... completedIntegralModuleSheaves`, constrained by
   `(a • f).val.app U x = c U a • f.val.app U x`. Verdict: it fixes the action on
   every sheaf Hom group through the canonical sections.
8. The derived action is the existential
   `Linear ... completedIntegralDerivedCategory`, followed by linearity of
   `DerivedCategory.Q`. Verdict: localization is explicitly compatible with
   the same action; no unrelated scalar action is chosen.
9. The clause `forall m : Z, Functor.Linear ... (shiftFunctor ... m)` gives all
   integer shifts. Verdict: zero and negative shifts are included.
10. The final category is the full subcategory
    `boundedConstructibleDerivedCompleteIntegral D l hl E Y`, with inclusion
    linear and with all its integer shifts linear. Verdict: this is exactly the
    detailed derived-complete constructible category, not a weaker bounded or
    finite-level variant.
11. The triangulated structure is supplied by the recorded
    `boundedConstructibleDerivedCompleteIntegral_isTriangulated`; the local
    `integralConstructibleTriangulatedStructure` instance is its second
    component. Verdict: the specified dependency structure is used, with no
    additional closure assumption.
12. Composition bilinearity is the `CategoryTheory.Linear` structure used by the
    existential actions. Verdict: the module and both composition bilinearity
    clauses are inherited exactly as required by the source.

Edge cases were checked explicitly. The scheme may be empty and the module or
derived object may be zero; no nonzero Hom or point is assumed. There is no free
index type: the coefficient tower is indexed by `Nat`, with `n = 0` giving the
first quotient at exponent one. All integer shifts, including zero and negative
integers, are quantified. Prime `l = 2`, every allowed residue characteristic,
`E = Q_l`, and ramified finite extensions remain covered. The independent
finite-field universe `d` and scheme/coefficient universe `u` are not identified,
and the pro-etale object/morphism universe separation is preserved.

I read the dependency declarations for the coefficient extension, completed
coefficients, detailed integral category, triangulated closure, linear category,
K-flat complex, reduction tower, and derived-complete object. Their interfaces
match the node records, including the repaired separate-universe K-flat and
reduction/derived-complete interfaces. No hollow definition or private duplicate
was found; all postponed theorem bodies are named `sorry` declarations with
source and blueprint docstrings. The search record was independently checked:
LeanFinder, Loogle, Mathlib grep, project grep, and upstream grep found only the
generic derived-category linearity and shift structures, not this completed
integral constructible action. The unavailable LeanSearch service is recorded
in `searches.jsonl`; the other searches suffice. Citer audit found the two
downstream uses (`def-weil-rationalization-karoubi` and
`def-weil-integral-scalar-extension`), and their uses still hold.

No mismatch was found and no source, statement, dependency, or Lean declaration
was changed in this second reading. The full six-file packet compiles cleanly
through `scompile.py`, with only the expected postponed theorem proofs.

## Earlier second reading by NU (superseded by immutable-head return)

I reread the node `sec-smooth-purity/lem-weil-integral-constructible-linear.json`,
the source place `def-weil-rationalization-karoubi`'s integral-linearity hypothesis,
and the current module `Sheaf.Paper.IntegralConstructibleLinear`. The node fixes a
prime ell distinct from p, a finite E over Q_l, and a scheme Y; it asserts that the
completed-coefficient derived category is O_E-linear via constant sections, with
bilinear composition and linear integer shifts, and that the full bounded
constructible derived-complete subcategory inherits the triangulated and linear
structures.

The Lean signature renders these items as follows. `D`, `l`, `[Fact l.Prime]`, and
`hl` give the global finite-field convention and ell distinct from p; `E` with
`Field`, `Algebra (Padic l) E`, and `FiniteDimensional` gives precisely the finite
extension; `Y` is arbitrary and has no qcqs, Noetherian, separated, connected, or
nonempty hypothesis. `completedIntegralDerivedCategory` is the derived category of
modules over the recorded inverse-limit coefficient sheaf. The family `c` is
natural on every pro-etale object and every projection is the sheafified class
modulo `coefficientExtensionIdeal (n + 1)`, so its terminal component is exactly
the constant-section map in the node. The first `Linear` existential fixes the
sectionwise Hom action, the second fixes the derived action and makes `Q` linear,
and the two `∀ m : ℤ` clauses cover every positive, zero, and negative shift. The
final inclusion and shift clauses use the recorded full subcategory and its
inherited triangulation. `CategoryTheory.Linear` supplies the Hom modules and
both composition bilinearity laws. Quantifier order and all conclusion clauses
agree with the node; no stronger geometric or coefficient assumption is present.

Edge cases checked: the empty scheme and zero objects are allowed; the tower index
`n = 0` is exponent one; all positive levels occur; zero and negative shifts are
included; `E = Q_l`, ramified finite extensions, and `l = 2` (when distinct from
p) remain covered. The field-data universe `d` is independent. The coefficient
and site interfaces preserve the separate site object/morphism universes.

I searched the current project, upstream `WeilConjectures`, and Mathlib with `rg`
for the item and declaration names, `completedIntegral.*[Ll]inear`,
`Linear.*SheafOfModules`, and `SheafOfModules.*Linear`; I also checked the recorded
LeanFinder, Loogle, and Mathlib-grep searches in `searches.jsonl`. Only generic
derived-category, localization, shift, and full-subcategory linearity was found;
there is no existing theorem for this completed coefficient action. I read each
statement dependency and its actual declaration, including the repaired K-flat,
reduction-tower, and derived-complete interfaces. No hollow definition, duplicate
notion, missing helper, or citer break was found.

No mismatch was found, so no Lean, node, or dependency record was changed. The
required `scompile.py` run compiled all six packet modules separately with no
errors and only the expected postponed theorem warnings.


## Repair of immutable-head return a45e11644efd

This section supersedes the earlier repair's claim that omitting universe arguments
was sufficient. The returned file-only failure was reproduced with the full six-file
packet. A scratch `#check`/`#print` probe read the actual KFlat interface and the
canonical `integralTowerAugmentationIso`; the server source was also read with
`scompile.py --source Sheaf.Algebra.Homology.KFlat`. The current source provides
three independent universes. The general declaration must be directly public-imported
by consumers rather than reached only through the well-definedness proof import.

In `IntegralReductionTower`, add `public import Sheaf.Algebra.Homology.KFlat` and
write all three resolution binders as
`CochainComplex.IsKFlatResolution.{t + 1, t, max u (t + 1)}`. This explicitly uses
site objects in t+1, morphisms in t, and coefficients/modules in max u (t+1), with
no equality imposed. The same public import and explicit specialization are applied
to the resolution binder in `DerivedComplete`. No definition data, mathematical
hypothesis, canonical map, theorem conclusion or postponed proof is changed.
`integralReductionTowerMap` now elaborates, so the subsequent unknown-identifier
errors disappear. Its inverse-resolution-isomorphism followed by the canonical unit
is unchanged, as are the naturality theorem and cone.

All six node Lean records now identify this repair as NU and use the current UTC
date. The item's statement dependencies additionally cite the already recorded
K-flat, tower and completeness nodes, matching the three dependency modules actually
supplied. No node's natural-language statement is changed. The earlier independent
readings concern older versions; the second reader must inspect this repair.

Validation: all six delivery modules were separately compiled through `scompile.py`
in dependency order, both under the sandbox module name and their library names.
The entire packet passed with no errors and no extra warnings. The general tower
and completeness modules compile with independent t and u, so the check covers the
coefficient-size case that the returned narrower artifact excluded. The remaining
modules specialize the same repaired interface without altering the existing empty
scheme, zero complex, first positive reduction, identity tower-arrow, or arbitrary
integer-shift cases. The mandatory `deliver2.py --no-push` is run after these record
and report repairs; no push is made by this worker.


The first repair dry run compiled successfully but preflight rejected three sibling
sources because their unchanged bytes already matched the latest base. Keep their
necessary source-packet ownership explicit: `KFlat` now sets `autoImplicit false`
(the declarations already bind every variable), and the detailed-category and
triangulation modules carry a comment explaining their paired compilation against
the repaired public K-flat dependency. Their declarations remain unchanged. The
second-reading section remains intentionally absent until the independent reader.

## Earlier second reading (a previous round; superseded)

Independent reading of the current six-file repair, 2026-10-16 local date
(2026-10-15 UTC). I opened the item node, its source and Lean statement, every
statement-dependency record and declaration, and all five sibling modules. This
reading concerns the explicit-universe/public-import repair described above;
the superseded readings are not evidence for this version.

The source of the item is blueprint `def-weil-rationalization-karoubi`, order
1460, specifically its application of an O_E-linear triangulated category to
D^b_c(Y,O_E). The shared checkout omits the literature files; I read the local
literature copy under `/home/ubuntu/work-bp/sheaf/literature/`, including this
blueprint and order 1459. I also read Stacks `dga.tex`, Definition 09MJ and the
following linear-functor definition; `sites-modules.tex`, Definition 03CW and
Lemma 03DA; `derived.tex`, Definition 05RU; and `sites-cohomology.tex`, Definition
06YN and Lemma 06YS. The linearity source assumes the global finite-field datum,
a prime ell different from p, a finite extension E/Q_ell and an arbitrary scheme
Y. The cited Stacks contexts impose no extra geometric hypothesis. The Bhatt--
Scholze Section 6.5 sentence is used for the blueprint's uniform-reduction
variant, not to add that section's qcqs hypothesis to this node. I read its
Definition 3.5.2 and the sentence after Definition 6.5.1 in the available text
extraction as well.

Hypotheses, objects and conclusion, checked individually:

1. Global characteristic and allowed prime: `D : FiniteFieldDatum.{d}`,
   `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`. Verdict: exact source convention;
   no characteristic condition on Y is added.
2. Finite extension E/Q_ell: `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`. Verdict: exactly finite-dimensional field
   extension, with no extra topology or valuation supplied by the caller.
3. Valuation ring, chosen uniformizer and quotients: the actual dependency's
   `Padic.coefficientExtensionIntegers l E`, `coefficientExtensionIdeal l E n`
   and `coefficientExtensionRing l E n`. I read their spectral-absolute-value,
   integer-subring, chosen-uniformizer, ideal-power and quotient constructions,
   and `finite_coefficientExtensionRing`. Verdict: the recorded O_E and A_E,n,
   with no replacement coefficient ring.
4. Scheme and site: `(Y : AlgebraicGeometry.Scheme.{u})`, `Scheme.ProEt Y`,
   `ProEt.topology Y`. I read Mathlib's weakly-etale over-category definition
   and generated covering topology and the group clone's upstream
   `AlgebraicGeometry/ProEtale/Proetale/Basic.lean`. Verdict: arbitrary Y on
   the recorded small pro-etale site; no nonempty, separated, Noetherian or
   finiteness assumption.
5. Ambient category: `completedIntegralDerivedCategory l E Y D hl`. I read
   `CompletedIntegralCoefficients`: completion is `limit` of the positive
   constant quotient ring-sheaf system, its projections are `limit.π`, module
   sheaves are `ringedSiteModules` = Mathlib `SheafOfModules`, and the derived
   category uses `HasDerivedCategory.standard`. Verdict: modules over the
   completed coefficient sheaf, exactly as the node specifies.
6. Constant global sections and their action: `∃ c : ∀ U, O_E →+* ...` is
   constrained by naturality for every restriction map and by its image under
   every `completedIntegralCoefficientProjection ... n`. The latter is exactly
   `toSheafify.app U` of the lifted quotient class of a at exponent `n+1`.
   Verdict: the canonical map, including at the terminal site object Y.
   Naturality restricts its global component to every object, and the limit
   projections determine it uniquely; the existential is not an arbitrary
   ring action or an identification with the discrete constant O_E sheaf.
7. Hom module structures and composition bilinearity: the first existential
   `Linear O_E (completedIntegralModuleSheaves ...)` has the sectionwise
   constraint `(a • f).val.app U x = c U a • f.val.app U x`. I read the fields
   `Linear.homModule`, `smul_comp`, `comp_smul` and the inherited preadditive
   structures. Verdict: all module identities and both composition laws,
   using the canonical sections on every module morphism.
8. Derived Hom action: the next existential `Linear O_E
   (completedIntegralDerivedCategory ...)`, with `Functor.Linear O_E
   (DerivedCategory.Q ...)`, extends that same sheaf/complex scalar action.
   Verdict: it also determines scalars on localized arrows, since the images
   of scalar identity endomorphisms determine scalar multiplication by
   bilinear composition. No unrelated derived action is chosen.
9. Ambient shifts: `∀ m : ℤ, Functor.Linear O_E (shiftFunctor ... m)`.
   Verdict: all integer shifts, not just one shift or only positive shifts.
10. Full integral constructible subcategory: the recorded
    `boundedConstructibleDerivedCompleteIntegral ...` and its `...Category`
    abbreviation. Its predicate is derived completeness plus constructibility
    of every positive reduction in one common interval `[r,s]`, `r ≤ s`.
    Verdict: exactly the node's full category, without a uniform rank or
    stratification condition.
11. Specified triangulation: `integralConstructibleTriangulatedStructure`
    extracts `.2` of the dependency's
    `boundedConstructibleDerivedCompleteIntegral_isTriangulated`. I read its
    exact signature and Mathlib's `ObjectProperty.IsTriangulated` and inherited
    full-subcategory triangulation. Verdict: the stated dependency's inherited
    structure, with no closure hypothesis added to the item.
12. Inherited linearity and shifts: Mathlib's `Linear.fullSubcategory` fixes
    the subcategory Hom structures; `Functor.Linear O_E (...).ι` and the last
    `∀ m : ℤ, Functor.Linear O_E (shiftFunctor ... m)` give the inclusion and
    all induced shifts. Verdict: the full concluding assertion with the same
    ambient action.

The quantifiers occur in the required order: source data, canonical natural
section maps, sheaf-level linear structure constrained by those maps, derived
linear structure compatible with localization, then shifts and inheritance.
All variables and universes are bound. The common E/Y universe follows the
recorded full-category interface; the site's object and morphism universes
are still distinct, and the finite-field universe d is independent.

Edge cases: Y may be empty, and module sheaves and derived objects may be zero.
No nontrivial Hom group or point is assumed; maps to the zero section ring are
unital. There is no arbitrary index type requiring nonemptiness. The tower is
ℕ with n=0 denoting exponent one, so every positive quotient is included.
Integer shifts include zero and negative integers. E=Q_ell, arbitrary finite
ramification, and ell=2 when distinct from p are included. No condition ties
the scheme's characteristic to p.

Sibling audit, against each sibling's node and source:

- `def-pc-kflat-complex`: `IsKFlat` universally tests acyclic F with the actual
  total tensor `mapBifunctor F K (curriedTensor _)`, and `IsKFlatResolution`
  is `QuasiIso q ∧ IsKFlat ...`. These are Stacks 06YN/06YS. The previously
  recorded independent u,v,w and relative `EssentiallySmall.{w}` interface
  remains intact. The only difference from the shared source is explicit
  `autoImplicit false`; the named sheafification/tensor infrastructure and
  proof docstrings remain unchanged.
- `def-weil-integral-reduction-tower`: `Functor.ofOpSequence` uses the actual
  localized termwise reductions and transitions. `integralReductionTowerMap`
  is the inverse augmentation isomorphism followed by Q of the canonical
  tensor unit; the named naturality theorem supplies its cone. I opened
  `IntegralReductionTowerWellDefined` to check its uniquely characterized
  pure-tensor units/transitions and augmentation isomorphism. The direct
  public KFlat import and explicit `IsKFlatResolution.{t+1,t,max u (t+1)}`
  retain the required site and coefficient universes and canonical maps.
- `def-weil-derived-complete`: `IsDerivedComplete` existentially chooses a
  representative, its K-flat resolution and representative isomorphism, then
  requires `IsDerivedLimitTriangle` for the canonical cone legs transported
  along that isomorphism. I read the current server declaration with
  `scompile.py --source`: the triangle's second arrow is exactly the tower
  transition endomorphism 1-s. Its first arrow is `Pi.lift` of those legs;
  only the final Roos arrow and product witness are existential. Thus no
  arbitrary comparison replaces completeness. The public-import and explicit
  universe repair changes no hypothesis or definition data.
- `def-weil-derived-complete-integral-detailed`: precisely completeness plus
  intrinsically bounded constructible reductions with common support bounds.
  I opened `intrinsicFiniteTorsionConstructible` and
  `proEtaleCohomologicalSupport` too. The paired file differs only by its
  compilation comment; its declarations and predicate are unchanged.
- `lem-weil-integral-constructible-triangulated`: exactly isomorphism closure
  and `IsTriangulated` of that predicate, with the same coefficient/scheme
  binders. Its two sheafification specializations select the recorded
  coefficient size. Its proof docstring follows the recorded eight steps.
  The paired file differs only by its compilation comment.

There are no new nodes and no statement correction; no citer audit is required
by §1(C). Every sibling changes only its Lean record, and the item only gains
the already recorded prerequisite interfaces allowed by the brief. The
`lean.note` fields explain the unusable compiled interface and its repair.
Definitions contain real constructions, and choices from postponed theorems
in the dependency chain are uniquely characterized constructions, not arbitrary
maps. Every theorem in the delivered sources remains `sorry`. The main theorem's
source/blueprint docstring carries all five node proof steps. No missing helper,
private copy, hollow definition or unbound universe was found.

Independent searches, with different wording from the author:

- LeanFinder: “An abelian category of modules over a ring sheaf carries scalars
  from compatible constant sections, and localization and full triangulated
  subcategories inherit these scalars.” Eight hits, including the generic
  derived linearity and Q-linearity instances and module-sheaf abelianity;
  none states this canonical completed-coefficient action.
- Loogle: `SheafOfModules, CategoryTheory.Linear`: zero hits.
- Mathlib grep through msearch: `Linear|scalar|homModule` in
  `Algebra/Category/ModuleCat/Sheaf`: ten hits concerning restriction of
  scalars, not the node's linearity theorem.
- Direct rg of Mathlib, upstream `WeilConjectures` and project `lean/Sheaf`
  for `completedIntegral.*[Ll]inear`, `Linear.*SheafOfModules`,
  `SheafOfModules.*Linear`, and both proposed declaration names found no
  duplicate. The `homLinear` results concern module sheaves on spaces;
  they neither state the general-site completed-coefficient action nor its
  derived/full-subcategory compatibility. I opened Mathlib's derived Linear,
  Q-linear, shift-linear and full-subcategory instances; these are reused.
- LeanSearch was attempted independently and returned Internal Server Error;
  msearch records it as unavailable. The other search kinds succeeded.

No Lean or mathematical mismatch was found. I normalized the four definition
records and the triangulation theorem record to the actual multiline signature
text; the main theorem's record already matched exactly. This is metadata only.
All six files have lines of at most 100 characters. The required compilation and
delivery checks are recorded below after their completion.

Independent validation: `scompile.py` compiled all six modules separately in
dependency order, with no errors or warnings. Times were 2.4, 2.6, 1.9, 1.6,
1.7 and 2.1 seconds respectively; each used nice 19, two threads and the
unchanged 60-second limit. This covers the separate t/u universes of the
repaired tower and completeness interfaces as well as the main specialization.

The mandatory `deliver2.py NU lem-weil-integral-constructible-linear --no-push`
returned OK: the packet passes server preflight and compiles, with nothing pushed.

## Final repair addendum (2026-10-16)

The immutable-head repair generalizes `IsKFlatResolution.{t+1,t,max u (t+1)}` in `IntegralReductionTowerWellDefined` and compiles it with the paired KFlat, IntegralDerivedReduction, tower, and completeness modules. The item finite quotient map explicitly names `CategoryTheory.GrothendieckTopology.toSheafify` with universe parameters `.{u+1,u+2,u,u+1}`, disambiguating the concrete sheafification map from the module-sheaf overload while preserving the quotient-section clause. The node Lean signature is synchronized verbatim.

## Final returned-delivery repair (2026-10-16)

The returned immutable head identified the stale fixed-universe K-flat interface
reached while compiling `IntegralReductionTowerWellDefined`. I repaired the full
chain by including `IntegralDerivedReduction.lean` as a dependency module and
specializing every `IsKFlat`/`IsKFlatResolution` occurrence there, as well as in
`IntegralReductionTowerWellDefined`, at site object universe `t+1`, morphism
universe `t`, and coefficient universe `max u (t+1)`. The existing K-flat module,
tower, derived-complete definition, and their node records retain their canonical
objects and statements; only the unusable compiled interfaces are repaired under
§1(B). The dependency record for `def-weil-integral-derived-reduction` records
this reason and the paired module.

The finite quotient clause in the item uses the existing canonical declaration
`WeilConjectures.integralScalarFiniteConstant` from
`Sheaf.Paper.IntegralScalarExtensionWellDefined`. It is exactly the
`toSheafify` section of the wrapped `integralCoefficientSheaf`; using the wrapper
is required because the direct sheafification term is not definitionally equal to
the coefficient sheaf's `sheafCompose` object. No clause or hypothesis changes.
The item node's `lean.statement` is synchronized verbatim with the theorem
signature after this elaboration repair.

The complete eight-file packet was compiled with
`scompile.py NU lem-weil-integral-constructible-linear` in dependency order:
`KFlat`, `IntegralDerivedReduction`, `IntegralReductionTowerWellDefined`,
`IntegralReductionTower`, `DerivedComplete`,
`DerivedCompleteIntegralDetailed`, `IntegralConstructibleTriangulated`, and
`IntegralConstructibleLinear`. All files compiled cleanly within the unchanged
60-second per-file limit; only postponed theorem proofs remain.

## Earlier second reading by NU (superseded by published NZ repairs)

Independent reading, 2026-10-16. This section describes the final packet and
supersedes the earlier packet inventories and earlier second readings. I opened
the item node, its blueprint source, the delivered signatures and bodies, the
recorded dependency nodes, and the actual published declarations. The item has
no statement correction and this delivery introduces no definition node.

The source is blueprint `def-weil-rationalization-karoubi`, order 1460: global
finite-field datum, prime ell distinct from p, finite E/Q_ell, arbitrary Y,
and the valuation-ring-linear triangulated integral category. I checked the
source context in Stacks `dga.tex` Definition 09MJ and its linear-functor
definition, `sites-modules.tex` Definition 03CW and Lemma 03DA, and `derived.tex`
Definition 05RU. These require no geometric finiteness assumption. I also read
Bhatt--Scholze Section 3.5, Proposition 3.5.1 and Definition 3.5.2, and Section
6.5, Definition 6.5.1 and the following triangulation sentence. Section 6.5 uses
qcqs X and a different finite-reduction formulation; the exact notion here is
the blueprint's arbitrary-scheme variant with all reductions and uniform
cohomological amplitude. Its scalar-linearity calculation needs no qcqs premise.

Object/hypothesis/conclusion list, independently matched:

1. Global characteristic and distinct prime: `D : FiniteFieldDatum.{d}`,
   `l : Nat`, `[Fact l.Prime]`, `hl : l != D.p`. Verdict: exact source convention;
   no condition that Y itself has characteristic p or is over the finite field.
2. Finite E/Q_ell: `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`. Verdict: exactly a finite field extension,
   not an algebra of finite type, and no supplied topology or valuation.
3. O_E and its quotients: `Padic.coefficientExtensionIntegers l E`,
   `coefficientExtensionIdeal l E (n+1)` and
   `coefficientExtensionRing l E (n+1)`. I opened their definitions: the spectral
   absolute value gives the valuation subring; the ideal is the power of the
   principal uniformizer ideal; the ring is its actual quotient. Verdict: the
   recorded coefficient datum, including arbitrary finite ramification.
4. Scheme and site: `(Y : AlgebraicGeometry.Scheme.{u})` and `Scheme.ProEt Y`.
   I opened Mathlib's small weakly-etale site and its topology and the project's
   framework note. Verdict: arbitrary Y, objects in u+1 and morphisms in u;
   no Noetherian, separated, nonempty or finite-dimensional hypothesis.
5. Ambient category: `DerivedCategory (scalarReductionSource.{u, u} l E Y)`.
   `CompletedIntegralCoefficients` defines the ring as the inverse limit of
   finite constant ring sheaves. The reused `scalarReductionSource` is exactly
   Mathlib `SheafOfModules` over that completion with commutativity forgotten;
   `scalarReductionSourceDerived` fixes its standard derived localization. Verdict: modules over the completed ring sheaf, as specified.
6. Constant scalar section map: `exists c : forall U, O_E ->+* Rhat(U)`.
   The first conjunct requires naturality for every opposite-site arrow. The
   second fixes every finite residue to `toSheafify.app U` of `ULift.up` of
   `Ideal.Quotient.mk ... a`. Verdict: the exact canonical constant sections,
   not an arbitrary ring map. Limit projections jointly determine c. At the
   terminal site object this is the stated map to global sections; naturality
   supplies its restrictions. The positive-level tower computes the same limit.
7. Action on sheaf Hom groups: the first existential `Linear O_E` and
   `(a • f).val.app U x = c U a • f.val.app U x` specify the action sectionwise
   for all M, N, f, a, U and x. Verdict: precisely the constant-section action.
8. Derived Hom action: the next existential `Linear O_E` concerns the exact
   ambient derived category, and `Functor.Linear O_E (DerivedCategory.Q ...)`
   requires compatibility with the componentwise action on complexes. Verdict:
   the induced action on every derived arrow. Q maps the scalar identity
   endomorphisms correctly; composition bilinearity then determines scalar
   multiplication of arbitrary localized arrows.
9. Bilinearity: Mathlib `Linear` has `homModule`, `smul_comp`, `comp_smul`,
   over the existing preadditive category. Verdict: every Hom is an O_E-module
   and composition is additive and homogeneous in both arguments.
10. Ambient shifts: `forall m : Int, Functor.Linear O_E (shiftFunctor ... m)`.
    Verdict: every integer shift, including zero and negative integers.
11. Integral full subcategory: `sfIntegralConstructible l E Y` and
    `sfIntegralConstructibleCategory l E Y`. I read the published definition:
    `IsSfDerivedComplete` and a single interval `[a,b]` containing the support
    of every positive canonical derived reduction, each intrinsically finite-
    torsion constructible. Verdict: exactly the node's full category; no new
    amplitude, stratification, rank, or finite-Tor-dimension condition.
12. Its triangulation and linear shifts: the helper instance extracts `.2`
    of `sfIntegralConstructible_isTriangulated`. This supplies Mathlib's
    inherited shifts and triangles. `Linear.fullSubcategory` gives the same
    Hom modules as the ambient category; the inclusion is asserted linear,
    and the final clause asserts linearity of every integer induced shift.
    Verdict: all clauses of the consequence, with the prescribed structures.

Quantifiers are in the required order: input data, canonical sections, compatible
sheaf linear structure, induced derived linear structure, then shifts and the
full-subcategory clauses. All variables and universes are bound explicitly.
The E/Y universe convention is the recorded integral-category convention;
one may choose a common ambient universe. The site object and morphism
universes remain distinct and the coefficient size is u+1 (more generally
max u (t+1) in the published dependencies).

Edge cases: the empty scheme and empty site objects are allowed; the zero
section ring still receives a unital ring homomorphism. Zero sheaves, zero
complexes and zero Hom groups are included. There is no variable indexing set
requiring a nonempty assumption. The fixed natural tower starts at exponent
n+1, so n=0 is the first positive quotient. The shifts include every integer.
Prime 2, E=Q_ell, all finite ramification and every permitted characteristic
are covered; no premise constrains the characteristic of Y.

Findings and repairs:

- The old packet re-recorded older finite-field-dependent dependency interfaces
  and copied a chain of eight source modules. Published unrestricted interfaces
  already provide the exact canonical constructions. I replaced the four
  dependency records by those existing declarations and removed their copied
  modules, the copied K-flat module, and the copied old well-definedness module.
  No published source is deleted or modified by the delivery.
- The consumer now uses the reused `sfIntegralConstructible` category. The old
  triangulation theorem concerned the old predicate, so section 1(B) supplies
  `IntegralConstructibleTriangulatedRecorded.lean` with the same closure theorem
  for the exact reused predicate. Its proof docstring retains all eight node
  steps and identifies the canonical units/transitions of the published tower.
  Its helper instance has no uninferable auxiliary finite-field parameters.
- The original signature imported an entire scalar-extension theorem module
  for `integralScalarFiniteConstant`. Compilation exposed unrelated stale
  coefficient-universe failures in that import's dependencies. The signature
  now displays the identical canonical sheafification/quotient term directly.
  There is no copied helper definition, arbitrary scalar map or new notion.
- Removing the unrelated scalar-extension import exposed an implicit
  `HasDerivedCategory` dependency and an ambient/full-subcategory instance
  mismatch. The theorem now uses the published `scalarReductionSource` and
  its standard `DerivedCategory` throughout, exactly as the recorded integral
  subcategory does. Its underlying coefficient ring is the same inverse limit,
  with commutativity retained and then forgotten; no ring or site changes.
- Main mathematical hypotheses, all scalar-action clauses, and the node's TeX
  remain unchanged. Every `lean.statement` is extracted through the actual
  body delimiter; the dependency notes explain each repair.

Dependency audit under H13: I read the exact published `scalarReductionDerivedExtension`
and its universal witness/counit: the ordinary tensor objects/maps and derived
universal property fix the reduction along the actual completed-ring projection.
I read `sfIntegralReductionTower` and its preceding transition and unit declarations:
transitions are uniquely normalized on K-flat representatives, units come from the
normalized derived adjunction, and the cone uses those units. I read
`IsSfDerivedComplete`: its first Roos arrow is exactly `Pi.lift` of those units,
its second arrow is 1-s, and its final arrow is existential, as the node requires.
I read `sfIntegralConstructible`: completeness plus all positive constructible
reductions in one common integer interval, with its actual full-subcategory alias.
No datum is chosen from an unconstrained existence theorem. These existing
interfaces retain independent coefficient/site universes. The supplied triangulation
statement asserts isomorphism closure and Mathlib `IsTriangulated`, covering zero,
all shifts and extension closure and giving the inherited triangulated category.

Independent searches, with different wording from the author's queries:

- LeanFinder: "An abelian category of modules over a commutative ring sheaf is
  linear over the ring of global sections, and the shifts of its derived category
  are linear." Eight hits, led by `DerivedCategory.instLinear`, Q-linearity and
  shift-linearity; no theorem for this canonical completed-coefficient action.
- Loogle: quoted `DerivedCategory.instLinear` found the generic derived-linear,
  localization and shift instances. I opened `DerivedCategory/Linear.lean` at
  lines 24-40 and `CategoryTheory/Linear/Basic.lean`, including the
  `Linear.fullSubcategory` instance. They are ingredients, not this statement.
- Mathlib grep through msearch: `Linear|homModule|scalar action` in
  `Algebra/Category/ModuleCat/Sheaf` gave no hits. Direct rg across upstream,
  Mathlib and project sources for scalar/module-sheaf linearity and all proposed
  names found no duplicate theorem. Project `Sheaf/HomModule.lean` is the general
  scalar-module infrastructure, not the completed-coefficient result.
- LeanSearch independently returned Internal Server Error; recorded unavailable.
  The completed LeanFinder, Loogle and direct searches supply the search evidence.

Both delivered theorem proofs are `sorry`; the instance merely projects the
named triangulation theorem. Source/blueprint docstrings and complete natural-
language proof plans are present. There is no hollow definition, private notion,
local notation, hidden statement `let`, target change, or additional axiom.

## Dependency modules

Final packet inventory (supersedes the earlier source-packet inventory):

`def-weil-integral-derived-reduction`: section 1(B), existing published
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`,
`WeilConjectures.scalarReductionDerivedExtension`. It is the universal left
derived change of rings along the actual completed coefficient projection,
with its specified K-flat counit; no source module is copied.

`def-weil-integral-reduction-tower`: section 1(B), existing published
`Sheaf.Paper.SfIntegralReductionTower`, `WeilConjectures.sfIntegralReductionTower`.
The tower has the same canonical quotient transitions and units, normalized
on K-flat representatives, with independent site/coefficient universes.
No source module is copied.

`def-weil-derived-complete`: section 1(B), existing published
`Sheaf.Paper.SfDerivedComplete`, `WeilConjectures.IsSfDerivedComplete`.
The first Roos-triangle arrow is the product of the canonical reduction
units, so this is exactly completeness in the node's triangulated formulation.
No source module is copied.

`def-weil-derived-complete-integral-detailed`: section 1(B), existing published
`Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`
and its full subcategory. It is completeness and constructibility of all
positive derived reductions with one common cohomological interval.
No source module is copied.

`lem-weil-integral-constructible-triangulated`: section 1(B), new dependency
module `Sheaf.Paper.IntegralConstructibleTriangulatedRecorded`,
`WeilConjectures.sfIntegralConstructible_isTriangulated`. The old theorem's
predicate is an older interface; the new statement supplies its exact closure
and inherited triangulation assertions for the reused published predicate.
The source proof plan and all eight node steps are retained. The theorem proof
is postponed, and all previous published modules remain available.

The final delivery has exactly two Lean modules and six node records. Metadata
dates use the actual UTC date from `date -u +%F` (2026-10-15); the reading took
place on 2026-10-16 in the local timezone.

Final validation: `scompile.py NU lem-weil-integral-constructible-linear` compiled
both delivered modules separately in the same dependency-ordered overlay, cleanly
with no errors and no warnings. The triangulation module took 1.8 seconds and the
linearity module 2.6 seconds; each retained nice 19, two threads and the unchanged
60-second per-file limit. The required published sf-category dependencies and
constant-completion proof dependency also compiled. Both delivered signatures
match their node records verbatim; the maximum Lean line lengths are 86 and 98.
The remaining checks are the prescribed dry run and delivery, which also compile
and check the existing declaration records.

## Second reading by NU

Independent reading, 2026-10-16. This section describes the final single-module packet and supersedes all
earlier packet inventories and earlier second readings. I opened
the item node, its blueprint source, the delivered signatures and bodies, the
recorded dependency nodes, and the actual published declarations. The item has
no statement correction and this delivery introduces no definition node.

The source is blueprint `def-weil-rationalization-karoubi`, order 1460: global
finite-field datum, prime ell distinct from p, finite E/Q_ell, arbitrary Y,
and the valuation-ring-linear triangulated integral category. I checked the
source context in Stacks `dga.tex` Definition 09MJ and its linear-functor
definition, `sites-modules.tex` Definition 03CW and Lemma 03DA, and `derived.tex`
Definition 05RU. These require no geometric finiteness assumption. I also read
Bhatt--Scholze Section 3.5, Proposition 3.5.1 and Definition 3.5.2, and Section
6.5, Definition 6.5.1 and the following triangulation sentence. Section 6.5 uses
qcqs X and a different finite-reduction formulation; the exact notion here is
the blueprint's arbitrary-scheme variant with all reductions and uniform
cohomological amplitude. Its scalar-linearity calculation needs no qcqs premise.

Object/hypothesis/conclusion list, independently matched:

1. Global characteristic and distinct prime: `D : FiniteFieldDatum.{d}`,
   `l : Nat`, `[Fact l.Prime]`, `hl : l != D.p`. Verdict: exact source convention;
   no condition that Y itself has characteristic p or is over the finite field.
2. Finite E/Q_ell: `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`. Verdict: exactly a finite field extension,
   not an algebra of finite type, and no supplied topology or valuation.
3. O_E and its quotients: `Padic.coefficientExtensionIntegers l E`,
   `coefficientExtensionIdeal l E (n+1)` and
   `coefficientExtensionRing l E (n+1)`. I opened their definitions: the spectral
   absolute value gives the valuation subring; the ideal is the power of the
   principal uniformizer ideal; the ring is its actual quotient. Verdict: the
   recorded coefficient datum, including arbitrary finite ramification.
4. Scheme and site: `(Y : AlgebraicGeometry.Scheme.{u})` and `Scheme.ProEt Y`.
   I opened Mathlib's small weakly-etale site and its topology and the project's
   framework note. Verdict: arbitrary Y, objects in u+1 and morphisms in u;
   no Noetherian, separated, nonempty or finite-dimensional hypothesis.
5. Ambient category: `completedIntegralDerivedCategory l E Y D hl`.
   `CompletedIntegralCoefficients` defines the ring as the inverse limit of
   finite constant ring sheaves, modules as `ringedSiteModules` (Mathlib
   `SheafOfModules`), and the derived category using standard localization.
   The current published `IntegralDerivedReduction` exposes its matching
   standard `HasDerivedCategory` instance. Verdict: modules over the completed ring sheaf, as specified.
6. Constant scalar section map: `exists c : forall U, O_E ->+* Rhat(U)`.
   The first conjunct requires naturality for every opposite-site arrow. The
   second fixes every finite residue to `toSheafify.app U` of `ULift.up` of
   `Ideal.Quotient.mk ... a`. Verdict: the exact canonical constant sections,
   not an arbitrary ring map. Limit projections jointly determine c. At the
   terminal site object this is the stated map to global sections; naturality
   supplies its restrictions. The positive-level tower computes the same limit.
7. Action on sheaf Hom groups: the first existential `Linear O_E` and
   `(a • f).val.app U x = c U a • f.val.app U x` specify the action sectionwise
   for all M, N, f, a, U and x. Verdict: precisely the constant-section action.
8. Derived Hom action: the next existential `Linear O_E` concerns the exact
   ambient derived category, and `Functor.Linear O_E (DerivedCategory.Q ...)`
   requires compatibility with the componentwise action on complexes. Verdict:
   the induced action on every derived arrow. Q maps the scalar identity
   endomorphisms correctly; composition bilinearity then determines scalar
   multiplication of arbitrary localized arrows.
9. Bilinearity: Mathlib `Linear` has `homModule`, `smul_comp`, `comp_smul`,
   over the existing preadditive category. Verdict: every Hom is an O_E-module
   and composition is additive and homogeneous in both arguments.
10. Ambient shifts: `forall m : Int, Functor.Linear O_E (shiftFunctor ... m)`.
    Verdict: every integer shift, including zero and negative integers.
11. Integral full subcategory: `boundedConstructibleDerivedCompleteIntegral D l hl E Y` and its
    `boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y`. I read the published definition:
    `IsDerivedComplete` and a single interval `[a,b]` containing the support
    of every positive canonical derived reduction, each intrinsically finite-
    torsion constructible. Verdict: exactly the node's full category; no new
    amplitude, stratification, rank, or finite-Tor-dimension condition.
12. Its triangulation and linear shifts: the helper instance extracts `.2`
    of `boundedConstructibleDerivedCompleteIntegral_isTriangulated`. This supplies Mathlib's
    inherited shifts and triangles. `Linear.fullSubcategory` gives the same
    Hom modules as the ambient category; the inclusion is asserted linear,
    and the final clause asserts linearity of every integer induced shift.
    Verdict: all clauses of the consequence, with the prescribed structures.

Quantifiers are in the required order: input data, canonical sections, compatible
sheaf linear structure, induced derived linear structure, then shifts and the
full-subcategory clauses. All variables and universes are bound explicitly.
The E/Y universe convention is the recorded integral-category convention;
one may choose a common ambient universe. The site object and morphism
universes remain distinct and the coefficient size is u+1 (more generally
max u (t+1) in the published dependencies).

Edge cases: the empty scheme and empty site objects are allowed; the zero
section ring still receives a unital ring homomorphism. Zero sheaves, zero
complexes and zero Hom groups are included. There is no variable indexing set
requiring a nonempty assumption. The fixed natural tower starts at exponent
n+1, so n=0 is the first positive quotient. The shifts include every integer.
Prime 2, E=Q_ell, all finite ramification and every permitted characteristic
are covered; no premise constrains the characteristic of Y.

Findings and repairs:

- The sandbox's eight-module dependency packet predates NZ's published
  independent-coefficient repairs. I read the current server node records and
  used `scompile.py --source` to open the actual current triangulation, detailed
  integral category, derived completeness and reduction source. These are now
  usable as recorded. Every obsolete dependency module and dependency node copy
  is removed from this delivery. The original five statement dependencies are
  retained, and no published dependency record is overwritten.
- The original signature imported `IntegralScalarExtensionWellDefined` solely
  for `integralScalarFiniteConstant`. Its transitive import exposed unrelated
  stale coefficient-universe errors in `IntegralOperationsWellDefined`. I wrote
  out that existing helper's exact canonical term: Mathlib `toSheafify` applied
  to `ULift.up` of the quotient class. There is no new helper definition, private
  scalar notion, arbitrary map or changed action.
- The ambient and constructible categories, the original triangulation helper,
  all hypotheses and conclusions, and the node's TeX are preserved. The node's
  `lean.statement` is re-extracted verbatim after expanding the finite constant
  section term. Metadata uses the actual UTC date, 2026-10-15.

Dependency reading: `CoefficientExtensionFinite` imports the actual recorded
valuation ring, chosen uniformizer, principal-ideal powers and quotient rings.
`CompletedIntegralCoefficients` forms the inverse limit of finite constant
ring sheaves and its actual limit projections; its modules are Mathlib's
module sheaves. In the current server `IntegralDerivedReduction`, ordinary
change of rings has fixed tensor/sheafification objects and maps, its derived
pair has the universal counit, and its computation uses
`IsKFlatIndependentCoefficients`/`IsKFlatResolutionIndependentCoefficients`.
The published tower's first maps are inverse augmentation followed by tensor
unit; transitions are the actual quotient maps. `IsDerivedComplete` asks for
a representative and that canonical augmented tower's Roos triangle, whose
first map is `Pi.lift` of its cone legs and whose second is 1-s. Finally the
recorded detailed predicate requires every positive reduction constructible
and all supports in one common interval. The published triangulation theorem
is exactly isomorphism closure and Mathlib `IsTriangulated` for this predicate,
with the same D, l, hl, E and Y binders. The inherited category, shifts and
triangles therefore are precisely the dependency's structures. No dependency
module or new definition node remains in the delivery.

Independent searches, with different wording from the author's queries:

- LeanFinder: "An abelian category of modules over a commutative ring sheaf is
  linear over the ring of global sections, and the shifts of its derived category
  are linear." Eight hits, led by `DerivedCategory.instLinear`, Q-linearity and
  shift-linearity; no theorem for this canonical completed-coefficient action.
- Loogle: quoted `DerivedCategory.instLinear` found the generic derived-linear,
  localization and shift instances. I opened `DerivedCategory/Linear.lean` at
  lines 24-40 and `CategoryTheory/Linear/Basic.lean`, including the
  `Linear.fullSubcategory` instance. They are ingredients, not this statement.
- Mathlib grep through msearch: `Linear|homModule|scalar action` in
  `Algebra/Category/ModuleCat/Sheaf` gave no hits. Direct rg across upstream,
  Mathlib and project sources for scalar/module-sheaf linearity and all proposed
  names found no duplicate theorem. Project `Sheaf/HomModule.lean` is the general
  scalar-module infrastructure, not the completed-coefficient result.
- LeanSearch independently returned Internal Server Error; recorded unavailable.
  The completed LeanFinder, Loogle and direct searches supply the search evidence.

The delivered theorem proof is `sorry`; the instance merely projects the
named triangulation theorem. Source/blueprint docstrings and complete natural-
language proof plans are present. There is no hollow definition, private notion,
local notation, hidden statement `let`, target change, or additional axiom.

Final single-module validation: `scompile.py NU
lem-weil-integral-constructible-linear lean/Sheaf/Paper/IntegralConstructibleLinear.lean`
passes with no errors and no warnings. The item took 2.1 seconds; the current
published tower, completeness, detailed category and triangulation imports also
compiled cleanly. The 60-second, nice-19, two-thread limits were unchanged.
The theorem's signature matches the node record verbatim; every Lean line is
at most 100 characters. The node retains its original five statement dependencies.
Only the item module, item node and this report will be delivered.
