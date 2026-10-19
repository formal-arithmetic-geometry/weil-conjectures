## Worker report

The repaired module `Sheaf.RingTheory.PuncturedCurveBranches` states
`punctured_curve_has_dvr_branches`, with `sorry` as its only proof.
It uses the published dependency module
`Sheaf.AlgebraicGeometry.LocalCurveBranches` (group Q34), read in full through
`scompile.py --source`. No definition is duplicated and no dependency record is
changed. The item's informal statement, dependencies, and proof remain unchanged.

Hypothesis correspondence:

- Commutative reduced ring: `(R : Type u) [CommRing R] [IsReduced R]`.
- Excellent: `hExcellent : IsExcellent R`, using the published
  `Sheaf.RingTheory.ExcellentRing.IsExcellent` (the declaration is at root namespace).
- Strictly henselian local: `[IsStrictlyHenselianLocalRing R]` from
  `WeilConjectures.Mathlib.RingTheory.Henselian`. The class extends
  `HenselianLocalRing`, which supplies locality.
- Dimension exactly one: `hDim : ringKrullDim R = (1 : WithBot ℕ∞)`.
- Algebraically closed residue field: `hAlgClosed : IsAlgClosed
  (IsLocalRing.ResidueField R)`.
- Positive residue characteristic: `(p : ℕ) (hp : Nat.Prime p)` and
  `hChar : ringChar (IsLocalRing.ResidueField R) = p`. This permits mixed
  characteristic rings.

Conclusion correspondence:

- Finitely many branches: `Finite (excLocalCurveBranchIndex R)`. The index type
  consists of every minimal prime, exactly once.
- Each branch ring is the prescribed integral closure: use
  `excLocalCurveBranchIntegralClosure R a`, whose carrier is the integral closure
  of `excLocalCurveBranchQuotient R a` in `excLocalCurveBranchFractionRing R a`.
  Restriction of scalars to R does not change its elements or ring operations.
  These are precisely the factors of the dependency's `excLocalCurveB`.
- Excellent strictly henselian DVRs: the three corresponding universal conjuncts
  assert `IsDiscreteValuationRing`, `IsStrictlyHenselianLocalRing`, and
  `IsExcellent` of each canonical integral-closure factor. The explicit existential
  `hLocal` supplies the locality needed to form each branch residue field.
- Same residue field: each branch has a ring equivalence to
  `IsLocalRing.ResidueField R`, compatible with residue maps on every `r : R`.
  The structural map used here is the published `excLocalCurveBranchAlgebraMap`.
- Their fraction fields: `IsFractionRing` identifies the branch fraction field
  with the fraction field of its integral closure using the canonical inclusion.
- Punctured spectrum: an open `U` of `Spec R` satisfies
  `x ∈ U ↔ x ≠ IsLocalRing.closedPoint R`.
- Finite disjoint union as schemes: `U.toScheme` is isomorphic to the coproduct
  of `Spec (excLocalCurveBranchFractionRing R a)` over the finite branch index.
  The equation with `Sigma.desc` requires this isomorphism to lie over `Spec R`.
  Each component morphism is `Spec.map` of the canonical `algebraMap R` into
  its fraction field, namely the quotient map followed by the field inclusion.

Dependency declarations read and used: `AlgebraicGeometry.excLocalCurveBranchIndex`,
`excLocalCurveBranchIntegralClosure`, `excLocalCurveBranchFractionRing`, and
`excLocalCurveBranchAlgebraMap` in `Sheaf.AlgebraicGeometry.LocalCurveBranches`;
`IsExcellent` in `Sheaf.RingTheory.ExcellentRing`; `IsStrictlyHenselianLocalRing`
in `WeilConjectures.Mathlib.RingTheory.Henselian`; `ringKrullDim` in
`Mathlib.RingTheory.KrullDimension.Basic`; `IsAlgClosed` in
`Mathlib.FieldTheory.IsAlgClosed.Basic`; `IsDiscreteValuationRing` in
`Mathlib.RingTheory.DiscreteValuationRing.Basic`; `AlgebraicGeometry.Spec` and
`Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`. The existing proof-dependency
imports and eight-step proof docstring are retained.

Edge cases: locality excludes the zero ring; dimension one excludes the field
case. The canonical minimal-prime index handles reducible rings as well as
single-branch domains; no irreducibility or extra Noetherian hypothesis is added.
The index is not required to be nonempty separately. Mixed characteristic is
retained, while residue characteristic zero is excluded by the node. Universe u
is explicit and arbitrary. `autoImplicit` is explicitly false. No arbitrary maps,
choices of normalization, or point-set substitutes for scheme isomorphisms occur.

Searches: the earlier LeanFinder queries found DVR and normalization ingredients
but no whole-item statement; the earlier LeanSearch service returned Internal
Server Error. During this repair, `msearch.py ... leanfinder` with the query
"punctured spectrum of a reduced excellent strictly henselian one-dimensional
local ring finite coproduct of fraction fields of discrete valuation rings"
returned eight ingredient hits (DVR criteria and related local-field lemmas),
none stating this theorem. `msearch.py ... loogle 'IsDiscreteValuationRing,
IsAlgClosed'` returned zero hits. Direct `rg` searches of Mathlib, upstream
WeilConjectures and shared lean/Sheaf for branch and punctured-curve names found
the newly published canonical branch module and the downstream uses, but no
existing theorem. The dependency's live source was confirmed with the required
`scompile.py --source Sheaf.AlgebraicGeometry.LocalCurveBranches`.

No STATEMENT-DISPUTED flag, new nodes, or statement correction.

## Return repair

The return at immutable head 6c5c3acdb5b3 reported unknown identifiers
`BranchIndex`, `branchRing`, `branchField`, and `branchFieldMap`. These names
belonged to the old sandbox-only `Sheaf.RingTheory.LocalCurveBranches` module.
The current published dependency uses the `AlgebraicGeometry.excLocalCurve*`
names. The repair replaces the import and every reference with the published
canonical declarations. The field structural map is its canonical `algebraMap`.
The obsolete sandbox dependency module and dependency-node override were removed.
This also avoids re-recording Q34's now-landed dependency with a duplicate API.
The item's lean.statement is re-extracted verbatim from the final signature.

## Earlier second reading (a previous round; superseded)

The following independent reading is retained from the preceding delivery as
historical review evidence. It predates this repair: its old `BranchIndex` and
`branchRing` names now refer to the canonical `excLocalCurveBranchIndex` and
`excLocalCurveBranchIntegralClosure` declarations; its dependency-module delivery
has been removed in favor of Q34's published module. A fresh second reader will
check this repaired delivery before pushing, as required by the dispatch brief.


This reading supersedes the earlier second reading and the worker's claims of
exactness. I opened the current shared DAG node, both dependency nodes, their
recorded declarations, the sandbox modules, and the blueprint sources 1917–1918.
I read the Stacks TeX at varieties.tex `lemma-pre-pre-delta-invariant` (0C3R)
and `lemma-pre-delta-invariant` (0C3S), algebra.tex
`lemma-characterize-dvr` (00PD), and the excellence definitions 07QT,
00NI and 00NL. The literature checkout is available in the read-only reference
checkout under work-bp/sheaf. There are no new DAG nodes or statement corrections.

Object/hypothesis/conclusion list and final correspondence:

1. A commutative ring R: `(R : Type u) [CommRing R]`; correct, with arbitrary u.
2. Reduced: `[IsReduced R]`; correct, allowing reducible rings.
3. Excellent: `(hExcellent : IsExcellent R)` from the now-published
   `Sheaf.RingTheory.ExcellentRing`; correct. I read the current server source
   through `scompile.py --source`. It defines quasi-excellence as Noetherian,
   G-ring and open regular locus for each finite type algebra, and excellence
   as quasi-excellence plus universal catenarity. Catenarity includes both
   bounded chain lengths and equal saturated-chain lengths. Same-universe
   test algebras suffice because finite type algebras admit presentations in
   the base universe. I dropped this delivery's duplicate ExcellentRing module
   and node record after Q21's complete implementation became available.
4. One-dimensional: `hDim : ringKrullDim R = (1 : WithBot ℕ∞)`;
   exactly dimension one, using the recorded Mathlib dimension.
5. Strictly henselian local: `[IsStrictlyHenselianLocalRing R]`;
   the upstream class extends HenselianLocalRing, which supplies locality,
   and requires separably closed residue field. I read its declaration.
6. Algebraically closed residue field: `hAlgClosed` is
   `IsAlgClosed (IsLocalRing.ResidueField R)`; correct.
7. Residue characteristic p>0: `p`, `hp : Nat.Prime p`, and
   `hChar : ringChar (IsLocalRing.ResidueField R) = p`;
   repaired. The original ringChar R = p wrongly excluded mixed characteristic.
8. Every branch, once: `BranchIndex R` is exactly all minimal prime ideals,
   and `Finite (BranchIndex R)` asserts finiteness. The original existential
   Fin n family merely matched each chosen ring to some minimal prime, so it
   did not enforce complete, unrepeated component indexing. Fixed by canonical
   indexing, with no arbitrary factor choice.
9. Branch rings: `branchRing R a` is precisely the integral closure of
   R/a in `branchField R a = FractionRing (R/a)`. These are the factors of
   `branchAlgebra R`, not a second normalization notion. The theorem asserts
   `IsDiscreteValuationRing`, `IsStrictlyHenselianLocalRing`, and `IsExcellent`
   for every such ring. The excellent-branch conclusion was missing and is
   now included. Mathlib's DVR class is exactly a local nonfield PID domain;
   its Noetherianity and dimension one follow, without extra hypotheses.
10. Same residue field: for each branch a the theorem gives a ring equivalence
    from its residue field to that of R, whose value on the residue of
    `branchRingMap R a r` is the residue of r. This missing clause is restored
    with compatibility, not merely an abstract field isomorphism.
11. Spec of the fraction fields of these DVRs: the theorem gives
    `IsFractionRing (branchRing R a) (branchField R a)` for every a, using
    the original integral-closure inclusion into the component field.
12. Punctured spectrum as a scheme: `U : (Spec (.of R)).Opens` with
    `x ∈ U ↔ x ≠ IsLocalRing.closedPoint R`, and a scheme isomorphism from
    `U.toScheme` to the coproduct of the canonical field spectra. Repaired
    the original bare equivalence of point types, which loses structure sheaves.
13. The decomposition is the canonical one over Spec R:
    `e.hom ≫ Sigma.desc (fun a ↦ Spec.map
    (CommRingCat.ofHom (branchFieldMap R a))) = U.ι`.
    The maps are the quotient maps R→R/a followed by fraction inclusions.
    This restores the branch-field identification in node proof steps 7–8;
    it cannot be satisfied by an unrelated permutation or arbitrary structure map.

Dependency-module reading (H13): `def-exc-local-curve-branches` originally supplied
only the carrier B(R), omitting Q(R) and the structural map and algebra structure.
The repaired LocalCurveBranches module supplies both dependent products, their
canonical component rings and fields, quotient-then-inclusion maps, and the
canonical R-algebra structure on B(R). The constructions use Mathlib's
`integralClosure`, `FractionRing`, quotient maps and `RingHom.pi`; no data is
chosen from an existence theorem. The minimal-prime instance is extracted directly
from membership in the minimal-prime set. The auxiliary declarations are listed
in the dependency's lean.declarations, with source and blueprint docstrings.
The constructions are defined for arbitrary commutative rings, restricting to the
node's reduced local Noetherian dimension-one rings when used here; their data is
identical on that domain, and no extra property is asserted outside it.

The worker's excellent-ring class had `jTwo : Prop` and
`universallyCatenary : Prop`, which stored propositions rather than proofs of the
required properties. It therefore did not express excellence. The published
`IsExcellent` definition removes that fault and the duplicate module is dropped.
The Mathlib matches for algebraic closedness and DVRs were opened and agree with
the node's notions; they need no private replacements. I also read the recorded
signatures for the proof's finite henselian algebra decomposition, semilocal
normalization and reduced total-fraction-ring decomposition. The item imports
published proof-dependency modules as non-public imports. Unstated proof inputs
remain steps in the proof docstring, rather than invented hypotheses.

Edge cases: Finite BranchIndex includes the empty set syntactically; the hypotheses
actually exclude the zero ring and force at least one minimal prime. DVRs exclude
the field case, matching the dimension-one conclusion. No irreducibility or
positive number of branches is assumed. Reducible examples such as
k[[x,y]]/(xy) have all branches, while k[[t]] has one. The mixed-characteristic
strictly henselian DVR case is retained by the corrected residue-characteristic
binder. Characteristic zero residue fields are excluded exactly by the stated
p>0 premise. No independent test universe, field hypothesis on R, or extra
Noetherian premise is imposed. All variables and universes are explicit; there
are no statement-level lets, private declarations or local notation.

Independent searches: msearch LeanFinder query "excellent strictly henselian DVR
branch same residue field punctured spectrum" returned only unramified/residue
field ingredients; the scheme-complement query returned SpecToEquivOfField and
residue-point facts, not the theorem. The normalization-product query returned
scheme normalization and normalizationCoprodIso. I checked that API: it normalizes
scheme morphisms, not the two ring products or this punctured-curve theorem.
Loogle `"integralClosure", "minimal"` returned zero hits. LeanSearch for
normalization of a strictly henselian excellent curve was unavailable (Internal
Server Error), not evidence of absence. msearch grep for the new names returned
zero hits. Direct rg searches in Mathlib, WeilConjectures and shared lean/Sheaf
for branchAlgebra/branchRingMap/branchTotalFractions/punctured-curve names found no
existing whole notion or statement. The spectrum and DVR APIs are reused.

No informal statement change was needed: the source already asks for the stronger
scheme and compatible branch conclusion and imposes characteristic only on the
residue field. The two downstream applications, thm-exc-curve-open-dimension-general
step 6 and thm-exc-curve-open-constructible-general step 5, use precisely the finite
field-spectrum decomposition and excellent strict-local DVR models with common
residue field; the repaired statement supplies those uses. Both modules are
compiled separately with the required scompile.py wrapper. The only postponed
proof is punctured_curve_has_dvr_branches, whose docstring now records all eight
DAG proof steps. The final node lean.statement is extracted verbatim from its
Lean signature.

## Second reading by NJ

This is an independent reading of the current repaired delivery, superseding the
historical reading above. I opened the shared node, the sandbox node and Lean
module, every statement-dependency record, and the corresponding declarations.
I also read blueprint orders 1917 and 1918 in the reference literature checkout,
Stacks varieties.tex `lemma-pre-pre-delta-invariant` (0C3R) and
`lemma-pre-delta-invariant` (0C3S), algebra.tex `lemma-characterize-dvr`
(00PD) and `lemma-finite-over-henselian` (04GH), and the excellence and
catenarity definitions (07QT, 00NI, 00NL). Stacks 0C3S assumes a reduced
Nagata local ring of dimension one; it does not assume a field base or equal
characteristic. Here excellence supplies Noetherianity and Nagata, and the
additional strict henselian and algebraically closed residue hypotheses are
exactly those of blueprint lemma 1918.

Object, hypothesis and conclusion correspondence, checked against the file:

1. Commutative ring R: `(R : Type u) [CommRing R]`. Verdict: exact; no field
   structure, coefficient field, or finiteness assumption on R is introduced.
2. Reduced R: `[IsReduced R]`. Verdict: exact; reducible rings remain covered.
3. Excellent R: `(hExcellent : IsExcellent R)`. Verdict: exact. I read
   `Sheaf.RingTheory.ExcellentRing` and its `IsGRing` dependency. Excellence
   is quasi-excellence and universal catenarity; quasi-excellence includes
   Noetherianity, regular formal fibres and openness of the regular locus
   for finite type algebras. The same-universe finite type tests cover all
   finite type algebras up to transport through a finite presentation. The
   statement needs no extra Noetherian instance to name its branch factors.
4. Strictly henselian local R: `[IsStrictlyHenselianLocalRing R]`. Verdict:
   exact. The recorded upstream class extends `HenselianLocalRing`, supplying
   `IsLocalRing`, and requires `IsSepClosed` of the residue field. I opened
   this declaration in `WeilConjectures.Mathlib.RingTheory.Henselian`.
5. Dimension exactly one: `(hDim : ringKrullDim R = (1 : WithBot ℕ∞))`.
   Verdict: exact. I read Mathlib's definition as the Krull dimension of
   `PrimeSpectrum R`; the equality is not merely an upper bound.
6. Algebraically closed residue field: `hAlgClosed : IsAlgClosed
   (IsLocalRing.ResidueField R)`. Verdict: exact. I read `IsAlgClosed` and
   `IsLocalRing.ResidueField`: the latter is R modulo its maximal ideal,
   and the former says all polynomials split, equivalently every nonconstant
   polynomial has a root. This does not ask that R itself be a field.
7. Positive residue characteristic: `(p : ℕ) (hp : Nat.Prime p)` and
   `hChar : ringChar (IsLocalRing.ResidueField R) = p`. Verdict: exact.
   The positive characteristic of a field is necessarily prime. The
   characteristic of R is unrestricted, so mixed characteristic is included.
8. Canonical branch objects: `excLocalCurveBranchIndex R`,
   `excLocalCurveBranchQuotient R a`, `excLocalCurveBranchFractionRing R a`,
   and `excLocalCurveBranchIntegralClosure R a`. Verdict: exact. I read
   the published `Sheaf.AlgebraicGeometry.LocalCurveBranches` in full and
   confirmed the current source through `scompile.py --source`. The index
   is all minimal prime ideals of the zero ideal, once each; the quotient
   is R/a, its field is `FractionRing (R/a)`, and its integral closure is
   the subalgebra of integral elements, with scalars restricted to R.
   The quotient-domain instance is constructed from primality. These are
   exactly the factors of `excLocalCurveB R`, not new choices of DVR models.
9. Finitely many branches: `Finite (excLocalCurveBranchIndex R)`. Verdict:
   exact; it excludes neither a single branch nor multiple components and
   never replaces all branches by a selected finite subfamily.
10. Excellent strictly henselian DVRs: the three universal conjuncts for
    `IsDiscreteValuationRing`, `IsStrictlyHenselianLocalRing` and
    `IsExcellent` on each integral closure. Verdict: exact. I read the
    Mathlib DVR class: a local principal ideal domain with nonzero maximal
    ideal. Its domain structure here is inherited by the actual subring
    of the canonical component field, not assumed on the base R. The
    existential `hLocal` lets the conclusion name residue fields; it is a
    conclusion, not an added hypothesis. Proof irrelevance identifies its
    locality proof with those furnished by the two classes.
11. Same residue field: for every a there is a ring equivalence from
    `@IsLocalRing.ResidueField ... (hLocal a)` to `IsLocalRing.ResidueField R`,
    taking the residue of `excLocalCurveBranchAlgebraMap R a r` to the
    residue of r for every r. Verdict: exact. The published algebra map
    is the quotient map followed by the canonical integral-closure map;
    the compatibility expresses the same residue field over R, rather
    than an unrelated abstract field isomorphism.
12. Fraction fields of those DVRs: `∀ a, IsFractionRing
    (excLocalCurveBranchIntegralClosure R a) (excLocalCurveBranchFractionRing R a)`.
    Verdict: exact. The algebra structure is the canonical subalgebra
    inclusion, so these are the fraction fields of the normalization
    factors and also the fields used in `excLocalCurveQ R`.
13. Punctured spectrum and disjoint union: `∃ U : (Spec (.of R)).Opens`
    with `∀ x, x ∈ U ↔ x ≠ IsLocalRing.closedPoint R`, followed by
    `∃ e : U.toScheme ≅ ∐ (fun a ↦ Spec (.of ...))`. Verdict: exact. I read
    Mathlib's closed-point definition, `Spec`, `Spec.map`, `Opens.toScheme`,
    and `Opens.ι`: this is the open subscheme complement of the maximal
    ideal. The coproduct is a scheme coproduct. The final equality
    `e.hom ≫ Sigma.desc (fun a ↦ Spec.map (CommRingCat.ofHom
    (algebraMap R (excLocalCurveBranchFractionRing R a)))) = U.ι`
    makes the decomposition lie over Spec R with the prescribed quotient-
    then-fraction-field maps. Thus every component is canonically the
    appropriate branch field, with its original map from R.

Edge cases: the zero ring cannot satisfy the local and dimension-one
hypotheses, and a field has dimension zero and is excluded precisely as in
the node. A dimension-one local ring has at least one minimal prime, so
an empty puncture or empty index set is not an additional case to exclude
by a premise. `Finite` nevertheless treats empty indices uniformly.
A domain has one branch; a reduced reducible curve has all its distinct
minimal-prime branches. No irreducibility or normality assumption on R is
added. A mixed-characteristic excellent strictly henselian DVR is allowed;
residue characteristic zero is excluded exactly by the node. Universe u
is arbitrary and binds R, its quotients, subrings, fields and the index,
which is the appropriate universe for the scheme coproduct. No independent
smaller test universe or unbound variable occurs; `autoImplicit` is false.

Independent searches (fresh queries, not just the first worker's names):

- LeanFinder: "normalization branches of a one dimensional reduced strictly
  henselian ring punctured affine scheme coproduct generic points" returned
  eight scheme-normalization declarations, including `Scheme.Hom.normalization`
  and `normalizationCoprodIso`. Their signatures concern normalization of a
  quasi-compact quasi-separated morphism, not the DVR models and canonical
  punctured-curve decomposition here. No whole-statement match.
- Loogle: `"IsDiscreteValuationRing", "IsStrictlyHenselianLocalRing"`
  returned zero hits.
- LeanSearch: "The punctured spectrum of an excellent henselian local reduced
  curve is a finite disjoint union of branch fraction fields" was unavailable
  with Internal Server Error. This is recorded as unavailable, not an absence
  result.
- Direct rg in pinned Mathlib RingTheory and AlgebraicGeometry, upstream
  WeilConjectures, and shared lean/Sheaf for `punctur`, `branches`,
  normalization/henselian and strictly/valuation combinations found generic
  normalization and puncture APIs, the canonical branch dependency, and
  downstream uses, but no theorem with these clauses. The upstream name
  index and source also have no `punctured_curve_has_dvr_branches` collision.

Findings and repairs: the repaired signature already says exactly what the
node and blueprint say, so I have not rewritten it. There is no informal
statement correction, new node, dependency module, hollow definition or new
proof. The only theorem remains `punctured_curve_has_dvr_branches`, with
`by sorry`. Its source/blueprint docstrings and all eight proof steps agree
with the node: finite minimal primes; finite normalization via Nagata;
semilocal normal dimension-one factors; henselian decomposition and residue
fields; DVR criterion; excellence; principal puncture and total fractions;
and the finite scheme coproduct. I added the now-landed proof dependency
`Sheaf.RingTheory.LocalCurvePrincipalTotalFractions` and explicit proof imports
`Mathlib.RingTheory.FiniteType` and `Mathlib.AlgebraicGeometry.OpenImmersion`,
which are named in proof steps 6 and 8. The excellence-localization node still
has no published module to import. No public interface or node field changed.
The single delivered Lean file has no lines over 100 characters, private
copies, local notation, or unbound variables; its stored `lean.statement`
is verbatim the theorem signature.

I also checked the two applications in `CurveOpenDimensionGeneral` step 6
and `CurveOpenConstructibleGeneral` step 5: both use the finite decomposition
and the excellent strictly henselian DVR models with the original residue
field, all supplied here. No citer is changed. The additional wrapper grep
query `punctured_curve_has_dvr_branches|excLocalCurveBranch|normalizationCoprodIso`
returned only the generic Mathlib normalization-coproduct API, not this theorem.

Validation: the final file, including all three added proof imports, passed
`scompile.py NJ lem-exc-punctured-curve-branches` cleanly (exit 0, no errors
or warnings), both as the isolated sandbox file and under its library module
name. The node's stored signature was compared directly with the source
and is verbatim equal. Exactly one named theorem has `sorry` as its proof.
