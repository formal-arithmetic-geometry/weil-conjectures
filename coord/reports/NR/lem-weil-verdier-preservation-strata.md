## Worker report

`Sheaf.Paper.WeilVerdierPreservationStrata` states the two clauses of
`lem-weil-verdier-preservation-strata`. The current source is blueprint main-20261015,
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.md`,
order 2414. `WeilConjectures.verdier_preservation_strata` gives bounded constructibility
and the quantitative interval. `WeilConjectures.verdier_preserves_boundedConstructible_finiteTor`
gives qualitative preservation without a preselected dimension bound or Tor interval.
Both theorem proofs are `sorry`, with the full five-step proof plan in their docstrings.
There is no statement correction, new DAG node, dependency module, or statement dispute.

`WeilConjectures.finiteStageDualizingComplex` is a real-data helper of this node. It
specializes the existing `Etale.dualizingComplex` to the structure morphism and coefficient
ring. It obtains the finite coefficient instance from the recorded finiteness theorem;
Nagata supplies `HasCompactification`; finite type over the field supplies local
Noetherianity and compactness of the source and the chosen proper compactification.
The recorded ambient exceptional-adjoint theorem then supplies the `IsLeftAdjoint`
instance. Thus the object is the existing right adjoint of ordinary compact-support
applied to the constant unit, with no arbitrary object or map as a parameter and no
`sorry` in the helper.

Every hypothesis and clause is rendered as follows:

- The fixed datum is `D : FiniteFieldDatum.{u}`. Its fields give the finite base field,
  characteristic `D.p`, and algebraically closed field `D.k`.
- The coefficient prime is `l : ℕ` with `[Fact l.Prime]` and `_hl : l ≠ D.p`.
- A finite extension of `Q_l` is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  and `[FiniteDimensional (Padic l) E]`.
- The positive level is `n : ℕ` and `hn : 1 ≤ n`. The ring is exactly the recorded
  `Padic.coefficientExtensionRing l E n`, lifted by `ULift.{u+1,u}` to the coefficient
  universe of the recorded constant-module-sheaf derived category. This changes no
  ring operations or coefficient objects. The `Finite` witness is transported by
  `Finite.of_equiv` and `Equiv.ulift.symm`.
- The separated finite-type `k`-scheme is `X : Scheme.{u}`,
  `[X.Over (Spec (.of D.k))]`, and instances `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` on `X ↘ Spec (.of D.k)`. The last two together mean finite type.
- The ordinary derived category is the recorded `Etale.DerivedCategoryModule`
  at that coefficient ring and `X`. There is no completion or adic category.
- The ambient object `omega_X = a_X^× A` is `finiteStageDualizingComplex D l _hl E n hn X`.
  Its compact-support functor is `Etale.rightDerivedLowerShriek`, whose definition uses
  the recorded `rightDerivedLowerShriekOfCompactification` at Nagata's compactification.
- The dual `D_X K` is `((Etale.derivedHom (ModuleCat A) X).obj (op K)).obj omega_X`.
  This is the existing derived internal Hom in the fixed-scalar sheaf encoding of
  `def-weil-pbc-derived-categories`. The recorded general ringed-site internal Hom
  module is imported; its `SheafOfModules` encoding and this constant-coefficient
  `Sheaf ... (ModuleCat A)` encoding are the two presentations distinguished by the
  project convention in brief-stage2 §2. `Etale.derivedHom` is the existing internal Hom of the derived monoidal closed
  structure, hence the canonical right adjoint to derived tensor (upstream
  `SixFunctors/Etale/Derived/Hom.lean`, lines 67–90). No duality operation is assumed
  as an additional parameter.
- Membership in `D^b_ctf` is the conjunction of the recorded
  `Etale.DerivedCategory.isBoundedConstructible` and finite Tor amplitude. In the
  quantitative theorem these are `_hK` and `_hTor` for the specified endpoints
  `a b : ℤ`. In the qualitative theorem `_hTor` is existential over `a b : ℤ`.
- The quantitative dimension assumption is `d : ℕ` with
  `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
- The quantitative conclusion is the conjunction of `isBoundedConstructible` of the
  displayed dual and `hasTorAmplitudeIn A X (-b - 2 * (d : ℤ)) (-a)` of the same dual.
  Its endpoints mention only `a`, `b`, and `d`, which expresses independence of `n`.
- The qualitative theorem concludes `isBoundedConstructible` of the dual and
  `∃ a b : ℤ, hasTorAmplitudeIn A X a b` of the dual. It assumes no chosen `d`,
  so it explicitly supplies the first preservation clause of the node.

The statement dependencies were opened at their full signatures and docstrings:

| Dependency | Module and declarations used |
| --- | --- |
| `def-weil-finite-field-fiber` | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` |
| `def-weil-l-adic-coefficient-extension` | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, with the imported `Padic.coefficientExtensionRing` |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated` (the separated clause recorded alongside `IsProper`) |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, `QuasiCompact` |
| `def-weil-pbc-derived-categories` | `Sheaf.AlgebraicGeometry.DerivedCategories`, publicly imported by the constructibility module: `Etale.DerivedCategoryModule` |
| `def-weil-pbc-constructible-complexes` | `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`: `Etale.DerivedCategory.isBoundedConstructible` |
| `def-kun-tor-amplitude` | `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: imported `Etale.DerivedCategory.hasTorAmplitudeIn` |
| `def-amb-etale-compact-support` | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.rightDerivedLowerShriekOfCompactification`, via `rightDerivedLowerShriek` |
| `thm-amb-etale-exceptional-adjoint` | `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`: `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` |
| `def-pur-derived-internal-hom` | `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: `CategoryTheory.derivedInternalHomOfUniverses`; the constant-coefficient operation is the existing `Etale.derivedHom` in `WeilConjectures.SixFunctors.Etale.Derived.Dualizing` |
| `def-kun-topological-krull-dimension` | `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` |

The module imports the recorded modules of the already stated proof dependencies,
including finite smooth stratification, ambient stratum Hom, ordinary unbounded
compact-support composition, smooth tensor duality, direct-image vanishing and Tor
amplitude, exactness of internal Hom and tensor, constructible Serre closure,
Noetherian facts, and composite-adjunction/right-adjoint uniqueness. The proof docstrings
follow the node's five steps rather than presupposing constructible biduality.

Edge cases checked before finalizing: `n = 1` is allowed; `n = 0` is deliberately
excluded by the node's own positive-level assumption. The empty scheme is allowed;
its dimension is bottom and the empty stratification gives the zero object. Empty
intervals `a > b` are allowed by the Tor predicate and force `K = 0` by testing with
the tensor unit. The zero complex is allowed in every interval. `d = 0` gives the
expected `[-b,-a]`. No smoothness, properness, nonemptiness, ordering of endpoints,
or extra dimension hypothesis is imposed on the qualitative clause. All universes
and variables are explicitly bound (`set_option autoImplicit false`).

Searches performed (actual launcher records are in sandbox `searches.jsonl`):

- `msearch.py leansearch` and `msearch.py leanfinder`, query
  `Verdier duality preserves bounded constructible etale complexes of finite Tor amplitude with interval [-b-2d,-a]`:
  eight hits each, consisting of generic derived-category, t-structure and order-dual
  declarations; no matching etale statement.
- `msearch.py loogle`, query `verdierDual, torAmplitudeIn, constructibleFiniteTor`:
  zero hits, with unknown identifier `verdierDual`.
- `msearch.py grep`, query `Verdier|dualizing|tor.?amplitude` over Mathlib:
  25 generic model-category/localization/triangulated/opposite-category hits; no match.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, and the item-id source search, located upstream
  `Etale.constructibleFiniteTor_verdierDual` in `Derived/Dualizing.lean` and
  `Etale.torAmplitudeIn_verdierDual` in `Derived/BoundaryDuality.lean`.
  Both signatures and docstrings were read. These use the upstream
  `DerivedCategory.boundedConstructible` / `constructibleFiniteTor` predicates,
  based on `Scheme.IsConstructibleSheaf`, rather than the dependency's repaired
  `DerivedCategory.isBoundedConstructible`, based on finite constant module values
  (`Scheme.IsConstructibleEtaleModuleSheaf`). The recorded dependency explicitly
  distinguishes these notions and leaves their comparison separate. Therefore the
  existing upstream theorems are not exact declarations of this node with its
  recorded dependencies, and this delivery states the node using those dependencies.
  The new declaration names were also searched and had no collision.

Validation: the prescribed `scompile.py` compiled this module and its side-project
imports. A long source-reference line was corrected before the final compile/dry run.
Only this node's `lean` field changes; the statement and dependency lists are unchanged.

Resumption audit (2026-10-16): reopened the current blueprint statement, all eleven
statement dependencies and their recorded interfaces, and checked the earlier attempt
against the current shared node. Only `lean` differs. The recorded main signature matches
the module verbatim; every Lean line is at most 100 characters. A fresh `scompile.py`
run compiled the sandbox and library form cleanly (6.6 s and 7.1 s respectively).
A fresh LeanFinder query, `Verdier duality preserves bounded constructible complexes of
finite Tor amplitude on the etale site`, returned eight generic derived t-structure
results and no matching statement. Searches of the project and upstream found no
collision for any of the three delivered names. No Lean or node changes were needed.
The independent second reading already present from the earlier attempt is retained
below for the next reader to verify.

## Earlier second reading (a previous round; superseded)

I opened the node statement, its blueprint source place, every recorded statement
dependency, and `WeilVerdierPreservationStrata.lean`. The fixed datum in the node is
rendered by `D : FiniteFieldDatum.{u}`; its `p` and `k` fields provide the characteristic
and algebraically closed finite-field fibre. The prime and coefficient hypotheses are
`l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E : Type u` with `[Field E]`,
`[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, and the positive level
`n : ℕ`, `hn : 1 ≤ n`. The coefficient object is exactly
`ULift (Padic.coefficientExtensionRing l E n)`, and finiteness is supplied by the
recorded `Padic.finite_coefficientExtensionRing`; no alternate coefficient ring is
introduced. The scheme and geometric hypotheses are `X : Scheme.{u}`,
`[X.Over (Spec (.of D.k))]`, `[IsSeparated (X ↘ Spec (.of D.k))]`,
`[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, and
`[QuasiCompact (X ↘ Spec (.of D.k))]`, exactly the separated finite-type convention.

The ambient object required by the source is rendered by the real-data definition
`finiteStageDualizingComplex D l _hl E n hn X`, which specializes the existing
`Etale.dualizingComplex` to the structure morphism and recorded compactification.
The derived category is `Etale.DerivedCategoryModule` over the displayed coefficient
ring. The hypotheses that `K` is bounded constructible and has Tor amplitude `[a,b]`
are `_hK` and `_hTor`; the former is the recorded
`Etale.DerivedCategory.isBoundedConstructible` and the latter is the exact recorded
`Etale.DerivedCategory.hasTorAmplitudeIn`. The displayed dual is the existing
`Etale.derivedHom` applied contravariantly to `K` and then to the helper dualizing
complex, so it is the node's `R\mathcal Hom_A(-,ω_X)`.

The qualitative conclusion “carries `D^b_ctf` into itself” is rendered by
`verdier_preserves_boundedConstructible_finiteTor`: it concludes bounded
constructibility and an existential finite Tor interval. The quantitative conclusion
is rendered by `verdier_preservation_strata`: it concludes bounded constructibility
and `hasTorAmplitudeIn ... (-b - 2 * (d : ℤ)) (-a)`. The dimension hypothesis is
`_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, and the endpoint expression is
independent of `n`, exactly as the node states. No extra smoothness, properness,
nonemptiness, ordering of `a,b`, or characteristic hypothesis is present.

I checked the source proof paragraphs against the theorem docstring: empty intervals
are handled in the first proof step, finite smooth stratification and localization
triangles supply the two induction ingredients, ambient adjunction identifies the
stratum dual, smooth purity gives the `2e` shift, direct-image vanishing gives the
uniform `[-b-2d,-a]` interval, and reverse induction preserves constructibility and
Tor amplitude. The helper has no hollow data or `sorry`; only the two statement
theorems have `sorry` proofs.

Edge cases checked independently are the empty scheme (dimension bottom and empty
stratification), the zero complex, `a > b` (the tensor-unit argument forces zero),
`d = 0`, `n = 1`, and the excluded `n = 0` case (`hn` is required). Empty strata and
no smooth stratum are permitted. No universe is left implicit: `E`, `X`, the module
category, and the `ULift` coefficient universe are explicit.

For H4 searches I reran the recorded LeanSearch, LeanFinder, Loogle, and Mathlib
grep queries in `searches.jsonl`, and searched both `lean/Sheaf` and upstream
`WeilConjectures`. The upstream declarations
`Etale.constructibleFiniteTor_verdierDual` and
`Etale.torAmplitudeIn_verdierDual` are not exact matches: they use the upstream
`boundedConstructible`/`constructibleFiniteTor` predicate rather than this node's
recorded `isBoundedConstructible`, so the module does not duplicate an existing
declaration. I found no repair note for this item and no missing or unusable
dependency record.

The only presentation difference from the prose is the project-mandated encoding of
“finite extension”, “finite-type over a field”, and the constant-module derived
category through their recorded Lean declarations and universe lift; these preserve
the source objects and hypotheses. I found no mismatch and made no statement or
dependency change. `scompile.py` compiles the module cleanly; the dry-run delivery
reaches preflight and reports only the stale-base notice and this report section,
which is now supplied.


## Second reading by NR

I independently read the current shared node and sandbox node, the master blueprint
source recorded by the node, and the main-20261015 statement and proof at order 2414.
The source here is a blueprint statement, not a Stacks lemma with additional standing
hypotheses. I also opened its unit and chapter settings. The node explicitly fixes
its ordinary etale finite-coefficient setting; the chapter's pro-etale layers are not
substituted for it. No repair note exists for this item. The sandbox changes exactly
`lean`, with no statement correction, new definition node, or dependency module.

My object/hypothesis/conclusion checklist, with the Lean file open:

1. Global finite-field datum: `D : FiniteFieldDatum.{u}`. I opened
   `Sheaf.Paper.FiniteFieldFiber`: its fields specify a finite field of cardinality
   `p^a` and a fixed algebraic closure `D.k`. Verdict: same fixed datum, including
   its prime characteristic; no descent of X to the finite field is assumed.
2. Prime different from the characteristic: `(l : ℕ) [Fact l.Prime]`
   and `(_hl : l ≠ D.p)` in all three declarations. Verdict: exact.
3. Finite extension E of Q_l: `(E : Type u) [Field E] [Algebra (Padic l) E]`
   and `[FiniteDimensional (Padic l) E]`. Verdict: exact, with no additional
   topology, valuation, normality, or ramification hypothesis.
4. Positive coefficient stage: `(n : ℕ) (hn : 1 ≤ n)` and
   `ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)`. I opened both
   CoefficientExtension and CoefficientExtensionFinite. The ring is the quotient
   of the recorded integer subring by the nth power of the uniformizer ideal.
   The displayed Finite proof is the recorded theorem transported along ULift.
   Verdict: A_(E,n), with an equivalent universe lift and no changed coefficients.
5. Separated finite-type k-scheme and its structure morphism: `(X : Scheme.{u})`,
   `[X.Over (Spec (.of D.k))]`, `[IsSeparated (X ↘ Spec (.of D.k))]`,
   `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, and
   `[QuasiCompact (X ↘ Spec (.of D.k))]`. I checked the Mathlib class signatures.
   Verdict: exact finite-type convention, without smoothness or properness.
6. Ordinary D(X_et,A): `Etale.DerivedCategoryModule A X`. I opened DerivedCategories
   and upstream Coefficients: this abbreviates the unbounded derived category of
   `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)`. Verdict: the recorded category.
7. Ambient right adjoint and omega_X: `finiteStageDualizingComplex D l _hl E n hn X`.
   I opened upstream LowerShriek, UpperShriek through Dualizing's interface, and
   EtaleExceptionalAdjoint. The helper supplies the actual IsLeftAdjoint instance
   for the chosen Nagata compactification, deriving the Noetherian and compactness
   instances from finite type over the field; its result is `Etale.dualizingComplex`
   for that same structure morphism. That definition applies the chosen right
   adjoint to the monoidal unit. Verdict: omega_X = a_X^times A, not a parameter
   assumed to have desired duality properties, and no hollow data.
8. Derived internal Hom: `((Etale.derivedHom (ModuleCat A) X).obj (op K)).obj omega_X`.
   I read DerivedInternalHomOfUniverses and upstream Derived/Hom. The former is the
   recorded ringed-site K-injective construction; the latter supplies the existing
   fixed-scalar sheaf presentation's internal right adjoint to derived tensor.
   Verdict: the intended R Hom_A, with the correct variance and the ordinary
   module-sheaf category, using the existing operation rather than a private copy.
9. D^b_ctf input: `_hK` uses the recorded `isBoundedConstructible`; `_hTor` uses
   `hasTorAmplitudeIn A X a b K` in the quantitative theorem and
   `∃ a b : ℤ, hasTorAmplitudeIn A X a b K` in the qualitative theorem. I read
   BoundedConstructibleComplexes and EtaleTorAmplitude, and the upstream bounded
   predicate's definition in Coefficients. Verdict: exactly bounded constructible
   cohomology and finite Tor amplitude against every module sheaf in degree zero.
10. Qualitative preservation: `verdier_preserves_boundedConstructible_finiteTor`
    concludes `isBoundedConstructible` of that same dual and an existential finite
    Tor interval. Verdict: every clause, with no dimension bound or chosen endpoints
    assumed. This is separate from the quantitative declaration, as lean.declarations
    records.
11. Quantitative data: `(d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))`
    and `(a b : ℤ)`. I checked topologicalKrullDim's strict-chain definition.
    Verdict: exactly dim X ≤ d; a ≤ b is not added.
12. Quantitative conclusion: `verdier_preservation_strata` concludes bounded
    constructibility and `hasTorAmplitudeIn A X (-b - 2 * (d : ℤ)) (-a)` of the
    same displayed dual. Verdict: [-b-2d,-a] exactly, and independent of n.
    Bounded constructibility repeats the first preservation clause, rather than
    strengthening the combined assertion.

Edge cases: n = 1 is included and n = 0 excluded exactly by the positive-level
hypothesis. The empty scheme and empty stratification are permitted; its dimension
is bottom. K = 0 is permitted. No nonempty index set is introduced. For a > b,
testing Tor against A forces K = 0, as the node's first proof step says, so retaining
all integer endpoints is correct. d = 0 gives [-b,-a]. The characteristic restriction
is exactly l != D.p. All variables and universes are explicitly bound, with
`autoImplicit false`. E, the field datum, and X use the common ambient u, and the
coefficient lift to u+1 is the project's recorded sheaf-size convention; it adds no
size equality between object and morphism universes and excludes no mathematical
finite extension or scheme after choosing a common ambient universe.

Independent H4 searches used different wording from the worker:

- LeanSearch: `Finite torsion coefficient etale Verdier dual sends an interval a b
  to minus b minus twice dimension and minus a` returned eight order-interval
  declarations, no matching etale theorem.
- LeanFinder: `Internal Hom into the exceptional inverse image of the constant ring
  preserves constructible complexes and has a dimension-dependent Tor bound`
  returned eight generic derived t-structure declarations, no match.
- Loogle: `AlgebraicGeometry.Etale.derivedHom` returned no match (unknown identifier
  in its Mathlib index). Launcher grep for
  `dualizingComplex|constructibleFiniteTor|hasTorAmplitudeIn` returned no Mathlib hit.
- Direct rg on Mathlib's AlgebraicGeometry and Algebra/Homology trees with
  `verdier|dualiz|tor.?amplitude|constructible.*hom` found generic references only.
  Direct rg on upstream WeilConjectures and project lean/Sheaf found the candidates
  in Derived/Dualizing and Derived/BoundaryDuality, which I opened. Their
  `constructibleFiniteTor_verdierDual` and `torAmplitudeIn_verdierDual` use the
  upstream `boundedConstructible` predicate, whereas the dependency explicitly
  requires the repaired `isBoundedConstructible` predicate. They are not exact
  signatures for this node. The project's EtaleGeometricBiduality and
  FiniteStageVerdierBiduality package preservation with biduality/anti-equivalence,
  without this quantitative bound; EtaleHomFiniteTorAmplitude is a theorem for
  two already constructible inputs with another bound. I opened those candidates;
  none is this statement. The three delivered full names have no collision.

The proof docstrings contain the node's five steps: empty-interval reduction and
finite smooth stratification; localization tower; ambient compact-support composition
and uniqueness of adjoints; local Hom calculation and direct-image interval; reverse
extension induction with the tensor and homology sequences. The qualitative docstring
also explains the choice of a finite dimension bound from the strata. Only the two
statement theorems have sorry proofs. The helper constructs real data using recorded
interfaces. Every declaration has its source and blueprint marker, and no line exceeds
100 characters. The node's lean.statement is verbatim the main theorem signature.

Mismatches found: none. Changes made: appended this independent second reading;
retained the worker's Lean, node record, and earlier report. A fresh prescribed
scompile.py run compiled the sandbox and library forms cleanly (11.8 s and 10.6 s).
