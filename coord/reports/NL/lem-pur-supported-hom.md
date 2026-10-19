# Stage-2 statement: lem-pur-supported-hom

## Worker report

The delivery states `AlgebraicGeometry.ProEtale.supported_cohomology_hom` in
`Sheaf.Paper.SupportedCohomologyHom`. Its only proof is `by sorry`. It asserts the
existence of a natural isomorphism of additive-group-valued functors on the full
bounded-below subcategory of the ambient pro-etale module derived category. It adds
no definition, helper theorem, source correction or mathematical hypothesis.
The declaration docstring reproduces all six current DAG proof steps and their
cited nodes, including the coefficient-specific cokernel argument which avoids the
unrestricted pro-etale support comparison rejected during stage 1.

NC completed the stage-1 split, not stage 2. The shared node has `status: split`, no
`lean` record, and is in the stage-2 queue. The prior worker's claim that this
assignment was superseded was incorrect. The sandbox initially contained only
brief files, with no node, module or report; an initial deliver2 dry run confirmed
that the item node file was absent. This delivery supplies the missing stage-2 work.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed finite coefficient ring A=A_{E,n} is the binder
  `(P : WeilConjectures.PurityFiniteSetting.{u})` and its existing
  `P.Coefficient`. The latter is the standard u+1 lift of the actual quotient
  `P.Ring = O_E/(varpi_E^n)`, with `P.level_pos : 1 ≤ P.level`.
  Neither an arbitrary substitute ring nor a divisibility/Kummer-level condition
  is used. The field and finite-extension data are the convention's existing data.
- An arbitrary scheme X and a closed immersion i:Z→X are
  `{Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]`. There is no
  finite-type, separatedness, quasi-compactness or structure-map requirement.
- The complementary open immersion j is the canonical `i.openComplement.ι`
  inside the dependency's `ProEtale.supportRestrictionArrow i`. This is the open
  subscheme on the complement of the range of i. Writing this canonical complement
  introduces no additional assumption or choice of open support and represents
  every complementary open immersion up to its canonical isomorphism over X.
- The small pro-etale site is `Scheme.ProEt.topology X`, with objects in u+1 and
  morphisms in u, exactly as the recorded site interface. The ambient derived
  category is the existing `ModuleDerivedCategory X P.Coefficient`, whose body is
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X)
  (ModuleCat.{u + 1} P.Coefficient))`. No site universes are identified.
- The coefficient sheaf A_Z is exactly the dependency's `P.constant Z`, the
  canonical comparison inverse image of the constant etale module coefficient
  sheaf. This is the existing finite constant pro-etale sheaf, with its actual
  coefficient action, not a replacement parameter.
- The underived direct image i_* is the existing
  `lowerStar (ModuleCat.{u + 1} P.Coefficient) i`. Its value on `P.constant Z`
  has sections on V equal to the coefficient sections on V×_X Z. It is applied
  before the degree-zero embedding; no derived i_* occurs in the statement.
- The source i_*A_Z is placed in degree zero by
  `(DerivedCategory.singleFunctor
  (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).obj`.
- Bounded-below F ranges over the domain of `derivedSupportSections`, namely
  `DerivedCategory.Plus` of all module sheaves on this site. The right-hand
  `DerivedCategory.Plus.ι` is its full inclusion in the ambient unbounded
  derived category. Thus F need not be constructible or have finite Tor amplitude.
- Every integer a is the explicit binder `(a : ℤ)`. The left functor is
  `derivedSupportSections i P.Coefficient ⋙
  DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a ⋙
  forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}`.
  At F this is precisely the underlying additive group of the recorded
  `ProEtale.supportHypercohomology i P.Coefficient a F`:
  H^a(RΓ_Z(X,F)), rather than a new definition of supported cohomology.
- On the right, `shiftFunctor (ModuleDerivedCategory X P.Coefficient) a`
  shifts F after the ambient inclusion. Mathlib's cochain shift is
  `(F[a])^r=F^{r+a}`, including the signed differential. Then
  `preadditiveCoyoneda.obj (op S)`, with S the degree-zero object above,
  is the functor with value `AddCommGrpCat.of (S ⟶ F.obj⟦a⟧)` and map
  given by postcomposition with the shifted derived morphism.
- `Nonempty (leftFunctor ≅ rightFunctor)` is the stated existence of an
  additive group isomorphism, natural in F. The components of the natural
  isomorphism are the displayed group identifications; its naturality squares
  say that supported-cohomology maps correspond to postcomposition by f[a].
  A pointwise family of arbitrary bijections would omit this clause; the
  functor-category isomorphism includes it. No choice of an isomorphism is made
  into new definitional data and no arbitrary-map hypothesis is added.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, `.coefficientCommRing`, `.constantEtale`, `.constant`.
  Their full constructions and docstrings were read in the shared source and
  confirmed by `scompile.py --source Sheaf.Paper.PurityFiniteSetting`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  morphisms; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`. Their recorded signatures and the actual
  source definitions were read. The canonical complement is used by the support
  definition, not supplied as an unrelated open immersion.
- `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`:
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory`. Its implementation and
  size-convention docstring were read in the prescribed framework checkout.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `AlgebraicGeometry.ProEtale.supportRestrictionArrow`, `.supportSections`,
  `.derivedSupportSections`, `.supportHypercohomology`, and the generic
  `CategoryTheory.Sheaf.supportedSectionsFunctor`. The full definitions show
  the restriction kernel and its bounded-below right derived functor. Current
  server source was read using `scompile.py --source`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.DerivedCategory.Plus` and
  `TStructure`: `DerivedCategory.Plus` and its full inclusion; the standard
  `DerivedCategory.singleFunctor` and derived shift. Existing Grothendieck
  instances set the morphism universe to u+1, without extra instance hypotheses.
- Under §1(B), direct image is recorded as
  `AlgebraicGeometry.ProEtale.lowerStar` in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
  The full declaration, docstring and sectionwise formula were read locally and
  through `scompile.py --source`. See Dependency modules below.
- `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`:
  `CategoryTheory.preadditiveCoyoneda`, whose full definition shows additive
  Hom groups and postcomposition. This supplies the Hom functor without
  introducing any private or duplicate construction.

The module publicly imports the statement dependencies in their usable recorded
presentations. It also imports the published modules of the proof dependencies,
without `public`, including comparison, constant sections, localization,
extension/sheafification, Grothendieck K-injectives, and the generic derived-Hom
roof comparison. The recorded natural-language six-step proof is left for stage 3.

Edge cases checked before drafting:

- Empty X and empty Z: lowerStar of the constant sheaf from the empty site is
  the zero module sheaf, so both supported cohomology and Hom from the zero
  object vanish. With X empty, its entire module sheaf category is zero.
- Z=X: the complement is empty; supported sections are all global sections,
  and the right-hand coefficient object is the usual degree-zero constant unit.
- F=0: both functors give zero groups, with no unsupported `IsZero` predicate
  on a bare type.
- Arbitrary bounded-below shifts and negative a: the statement has integer
  indexing and does not assert spurious vanishing below zero. For an object
  concentrated in degree zero negative groups vanish, while shifted inputs
  are still included and can have nonzero negative supported cohomology.
- n=1 is included. n=0 is outside the explicitly positive-level convention.
  There is no ramification-index-divides-level hypothesis: that is needed for
  a later Kummer exponent, not for this statement.
- A closed immersion with non-quasi-compact open complement is included.
  `lowerStar` is defined for arbitrary morphisms; no `[QuasiCompact j]` is
  present. The DAG's repaired constant-coefficient proof covers this case.
- Coefficient data and schemes have universe u, coefficients/modules live in
  u+1, and the pro-etale site retains morphism universe u. No equality of these
  universes or smallness condition on the geometric object is imposed.

Searches performed for an existing statement:

- `msearch.py ... leanfinder` with “cohomology with supports in a closed
  subscheme as derived morphisms from the constant coefficient direct image”:
  8 hits, including `Scheme.Modules.restrict`, its functor, ordinary sheaf H
  and cohomologyPresheaf, and Zariski module restriction/pushforward lemmas.
  None states this pro-etale supported-derived-Hom identification.
- `msearch.py ... loogle 'Sheaf, cohomology'`: 0 hits, unknown identifier Sheaf.
  Repaired with the successful query `'"Sheaf", "cohomology"'`: 7 hits,
  ordinary cohomologyPresheaf/cohomologyFunctor and nonabelian H1 relations;
  none is the supported-Hom statement.
- `msearch.py ... grep
  'supportedSections|supportHypercohomology|supportedHom|cohomologyWithSupport'`:
  0 Mathlib hits. The already recorded project supported-cohomology definition
  is used rather than duplicated.
- `rg -n 'lem-pur-supported-hom|supportHypercohomology|supportedHom'` in
  the upstream `WeilConjectures` and shared `lean/Sheaf`: no matching theorem;
  hits in SupportCohomology and SupportLongExact are the definition and long
  exact sequence interfaces, not the derived-Hom identification. Upstream's
  etale `restrictSupportedHom` is a different operation on supported morphisms.
- Read-only search of available sources and earlier delivery/review records
  found an earlier Q28 scratch filename SupportedHom but no published module
  or current Lean record. `scompile.py --source Sheaf.Paper.SupportedHom`
  explicitly returned “Module source unavailable”. This is not evidence of
  an existing declaration to attach. The archived NC report concerns the
  stage-1 split only.
- The main declaration name `supported_cohomology_hom` was checked by source
  search before creation. The dependency repair reuses the published `lowerStar`
  rather than making a second direct-image definition.

No STATEMENT-DISPUTED flag or item statement correction is needed. The invalid
unrestricted arbitrary-sheaf comparison in the imported blueprint proof was
already removed by the reviewed stage-1 split, whose exact statement is retained.

## Dependency modules

`def-weil-proetale-module-direct-image` receives only a `lean` record repair
under §1(B), with `existing: true` and no new module. Its former declaration
`Scheme.proEtaleConstantModuleDirectImage` uses `SheafOfModules` over a lifted
constant ring sheaf with a Type u coefficient. That interface cannot be applied
to the recorded site's and support-cohomology's `Sheaf ... (ModuleCat.{u+1} A)`
objects for A:Type(u+1). The published
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`,
`AlgebraicGeometry.ProEtale.lowerStar`, specialized to `ModuleCat.{u+1} A`,
is the same direct image in that presentation: precomposition along the same
base-change functor. Its sections and morphisms are precisely the node's
formulas. A section of the constant coefficient ring sheaf is locally a constant;
its action is obtained from the sectionwise A-action by gluing. Under direct
image this is restriction through rho_A^f because rho sends each constant to
that same constant on the base change. This verifies the scalar-action clause,
as well as sections, restrictions, morphisms and additivity. No part of the
node's mathematical statement or other fields changes; the old construction
remains available to its existing users. The Lean metadata includes the reason
in `lean.note`. The delivery tool compiles a #check probe for this existing
attachment, in addition to compiling the new statement file.

## Validation

The initial `scompile.py NL lem-pur-supported-hom` check passed both the sandbox
compilation (25.9 seconds) and the module at its library path (49.1 seconds),
with no errors or warnings. The final source has the same statement and now
includes the six DAG proof steps verbatim in its docstring. The mandatory
`deliver2.py NL lem-pur-supported-hom --no-push` dry run checks that final
module, a real compiler probe of the existing direct-image attachment, and the
server preflight. No push is performed by this worker. The independent second
reader adds their own review after this package is READY.


The first complete dry run compiled the final statement and the existing-declaration
probe but preflight required the upstream attachment's branch metadata to be
`slopmaster2` instead of `newtargets-dag`. This was corrected, along with the
signature's normalized `def lowerStar : ...` spelling reported by preflight.
The only other preflight reason was the intentionally absent independent
second-reading section. The required dry run is repeated with the corrected
metadata; the mathematical statement and Lean source are unchanged.


## Second reading by NL

This is an independent reading of the stage-2 draft. I opened the current DAG
node, its eight statement-dependency nodes and their recorded declarations,
the full sandbox Lean file, and the source blueprint paragraph at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-pur-supported-hom.md`.
The shared checkout has only literature indexes; the launcher literature copy
contains the source text. The blueprint introduces a closed immersion, an
arbitrary bounded-below coefficient complex and the natural supported-Hom
identification, with no finite-type assumption. I also read Stacks
`proetale.tex`, section `section-morphism` (Tag 09A5), introductory paragraph,
and `sites-modules.tex`, Definition `definition-pushforward` (Tag 03D6), clause
(1), for the repaired direct-image attachment. These require an arbitrary
scheme morphism and restriction of the module action through the ring map;
no quasi-compactness hypothesis belongs to the definition. The following
comparison is against the current reviewed node, including its six-step
constant-coefficient proof, rather than the original exceptional-adjunction
proof's unrestricted support comparison.

Object, hypothesis and conclusion inventory, with the exact Lean rendering:

1. Fixed finite coefficient data A=A_{E,n}: the binder
   `(P : WeilConjectures.PurityFiniteSetting.{u})`, `P.Coefficient`, and
   `P.constant Z`. I read the full live source using
   `scompile.py --source Sheaf.Paper.PurityFiniteSetting`.
   `P.Ring` is the existing valuation-ring quotient, `P.Coefficient` its ULift,
   and `P.constant` is comparison inverse image of the actual constant etale
   module sheaf. `level_pos` supplies n>=1; the fixed field, distinct primes
   and finite subextension are bundled. Verdict: exact, without an extra
   ramification-divisibility or scheme-over-field hypothesis.
2. Arbitrary schemes Z and X: `{Z X : Scheme.{u}}`. The recorded `Scheme`
   declaration is the category of locally affine locally ringed spaces.
   Verdict: exact; no Noetherian, separatedness, finite-type or finiteness
   instance is present.
3. Closed immersion: `(i : Z ⟶ X) [IsClosedImmersion i]`. I read Mathlib's
   class: closed embedding of spaces and surjective stalk maps, as recorded
   in `def-weil-closed-immersion`. Verdict: exact.
4. Complementary open j: the recorded `supportRestrictionArrow i` uses
   `i.openComplement.ι` in the pro-etale site. I read its live construction
   in `SupportCohomology` and Mathlib's open-immersion definition.
   This is the canonical representative of the complement, and any open
   immersion onto that complement is isomorphic over X to it. The statement
   makes no assertion depending on a chosen presentation of j. Verdict:
   exact; an additional binder for an unrelated open would be wrong.
5. Small pro-etale site and ambient derived category: the sheaf category is
   `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)`;
   `ModuleDerivedCategory X P.Coefficient` is definitionally its unbounded
   `DerivedCategory`. I read the exact framework source and size docstring,
   and `coord/pefw-upstream-framework.md`. Verdict: exact, with site objects
   in u+1, site morphisms in u, and module/Hom sizes u+1.
6. Underived direct image i_*: `(lowerStar (ModuleCat.{u + 1} P.Coefficient)
   i).obj (P.constant Z)`. I read the definition and its section/map formulas
   in `FiniteCoefficient/UpperLowerStar/Defs.lean`. It is precomposition
   with base change, applied before any derived-category embedding.
   Verdict: exact, and the dependency's existing-record repair is justified.
7. Degree-zero source: `(DerivedCategory.singleFunctor
   (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
   0).obj` applied to that direct image. Verdict: precisely i_*A_Z[0],
   with neither Ri_* nor a shifted source substituted.
8. Arbitrary bounded-below F: the domain inferred from
   `derivedSupportSections i P.Coefficient` is
   `DerivedCategory.Plus` of all the above module sheaves. I read the full
   live support definitions with `scompile.py --source
   Sheaf.AlgebraicGeometry.SupportCohomology`, and Mathlib's Plus/inclusion
   interface. Verdict: all bounded-below inputs, with all derived morphisms;
   no constructibility or finite-Tor condition.
9. Every integer a: `(a : ℤ)`. Verdict: exact, including negative degrees.
10. Supported cohomology on the left: `derivedSupportSections ... ⋙
    DerivedCategory.Plus.homologyFunctor ... a ⋙ forget₂ ...
    AddCommGrpCat.{u + 1}`. The dependency defines the derived functor of
    the kernel of restriction X to its open complement. Evaluation is the
    underlying additive group of its recorded `supportHypercohomology`.
    Verdict: exactly H^a_Z(X,F), without an alternative definition.
11. Derived Hom on the right: `DerivedCategory.Plus.ι ⋙ shiftFunctor
    (ModuleDerivedCategory X P.Coefficient) a ⋙
    preadditiveCoyoneda.obj (op S)` for the degree-zero source S of item 7.
    I read Mathlib's `preadditiveCoyonedaObj` and `preadditiveCoyoneda`:
    they return the additive Hom group, with postcomposition on targets.
    The derived shift is the cochain shift r -> r+a with signed differential.
    Verdict: exactly the displayed ambient Hom group, with correct variance.
12. Isomorphism and naturality in F: `Nonempty (leftFunctor ≅ rightFunctor)`.
    A component is an additive-group isomorphism; its naturality square
    equates the cohomology map with postcomposition by the shifted morphism.
    F is the functor argument, rather than a binder hiding naturality.
    For each a there is one such natural isomorphism; the node demands no
    compatibility between different a. Verdict: exact quantifiers and clauses.

Edge cases: empty X and empty Z are allowed by the scheme binders and no
nonempty instance occurs. If Z is empty the source and supported sections are
zero; if Z=X the complement is empty and this becomes the usual coefficient
unit/global-sections formula. F=0 is included. Negative a and bounded-below
objects with negative nonzero cohomology are included, with no false vanishing
clause. n=1 is included and n=0 is excluded by the source convention itself.
No characteristic case beyond that fixed coefficient convention is removed,
and X need not be a k-scheme. Non-quasi-compact complements remain allowed.
There is no index set in the statement to restrict. All universe variables
and terms are explicitly bound; no site universe equality is imposed.

Independent H4 searches, using words different from the first worker's:

- `msearch.py NL lem-pur-supported-hom leanfinder` queried
  "Closed support hypercohomology is represented by the constant sheaf pushed
  forward from the closed subscheme in the derived category". Eight hits:
  ordinary `Sheaf.H`, `cohomologyPresheaf`, `cohomologyPresheafFunctor`,
  boundedness under Q, and an injective-target vanishing lemma; no match.
- `msearch.py ... loogle '"preadditiveCoyoneda", "homology"'` returned
  three lemmas on triangulated Hom connecting maps and preservation of
  homology for projectives. None is this supported-Hom comparison.
- `msearch.py ... grep 'cohomology.*supports|support.*[Hh]om|
  sectionsWithSupport|closedSupport'` returned unrelated support and
  complex-support lemmas. I also used `rg` on both upstream
  `WeilConjectures` and shared `lean/Sheaf` for "with supports",
  "cohomology with support", and both orders of "support/Hom".
  I opened the closest upstream `GeometricOperations.supportedClassHomEquiv`
  in `TraceFormula/Correspondence.lean`: it assumes bounded finite-Tor
  geometric objects and identifies two exceptional/tensor Hom sets; it does
  not identify kernel-defined supported cohomology. The recorded generic
  `RHomDerivedRoof` theorem is the proof tool, not this geometric statement.
  Thus the new theorem does not duplicate an existing statement.

There are no new definition nodes or sibling dependency modules to audit.
The one dependency-node change is lean-only: the old
`proEtaleConstantModuleDirectImage` has a Type u coefficient and a lifted
`SheafOfModules` presentation incompatible with the actual recorded module
sheaves here. Existing `lowerStar` is usable with the actual ModuleCat
coefficient and has precisely the node's sections, restrictions and morphisms.
The constant ring-sheaf action is locally the constant scalar action and glues;
precomposition therefore restricts it through the specified constant-ring map
rho, as Tag 03D6 requires. Its linear maps and additivity are sectionwise.
The existing-record repair introduces no new data or stronger assumptions.

H5/H6/H8/H9 checks: the delivered module contains exactly one theorem with
`by sorry`, and no definitions, axioms, local notation, private data or local
instances. Module and declaration docstrings name the source and blueprint id;
the theorem docstring carries every step and dependency of the six-step DAG
proof. Public imports supply the statement notions, and ordinary imports supply
its recorded proof dependencies. Every Lean line is at most 100 characters.
I compared the node's `lean.statement` byte-for-byte with the signature preceding
`:= by`: they are equal. No mathematical mismatch or source correction was
found, and no Lean or node content was rewritten. The change in this second
reading is this independent review and the final validation/delivery evidence.

Validation: the first compile invocation used a relative sandbox path from the
read-only repository and failed to locate the file before Lean ran. I corrected
the working directory to the sandbox and reran the prescribed wrapper. The
subsequent compile, dry run and delivery results are recorded below.

Final second-reader validation: `scompile.py NL lem-pur-supported-hom lean/Sheaf/Paper/SupportedCohomologyHom.lean` passed both sandbox (10.4 s) and library-path (13.7 s) checks without errors or warnings. `deliver2.py NL lem-pur-supported-hom --no-push` then printed `OK (dry run): commit 347322b3e6 passes the preflight and compiles; nothing pushed`, after compiling the statement and existing-attachment probe. The reviewed mathematical source and metadata are unchanged.
