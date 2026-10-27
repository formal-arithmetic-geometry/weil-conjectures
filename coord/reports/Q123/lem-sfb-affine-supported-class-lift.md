## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSupportedClassLift` states
`AlgebraicGeometry.affine_supported_class_lift`, with proof `sorry`. It introduces
no definitions. The node is unchanged outside `lean`. Source checked directly:
`literature/stacks-project/perfect.tex`, Tag 08E3,
`lemma-represent-cohomology-class-on-closed` (lines 2157 onward), including its
finite-affine-cover argument and its nonpositively graded Koszul construction.
The declaration docstring contains all seven proof steps with their DAG references.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Affine scheme Y | `(Y : Scheme.{u}) [IsAffine Y]` |
| Closed subset T | `(T : Set Y) (hT : IsClosed T)` |
| U = Y minus T | Every occurrence uses `y ∉ T` or `Tᶜ` directly; no second open or equality is needed. |
| Nonnegative integer s | `(s : ℕ)`, cast to `ℤ` in the vanishing interval; this parametrizes precisely all nonnegative integers. |
| U is a union of s affine opens | `(V : Fin s → Y.Opens)`, `hV : ∀ i, IsAffineOpen (V i)`, and `hcover : (⋃ i, (V i : Set Y)) = Tᶜ`. The family is arbitrary; it need not be principal, distinct or nonempty. Making a witnessing cover explicit is equivalent to the asserted existence of such a cover. |
| E in D_QCoh(O_Y) | `(E : schemeDerivedQCohCategory Y)`, with underlying object `E.obj`. |
| H^j(E)_y = 0 for -s+1 ≤ j ≤ 0 and y in U | `hE` quantifies over all `j : ℤ`, assumes `-(s : ℤ) + 1 ≤ j` and `j ≤ 0`, then all `y : Y` with `y ∉ T`, and asserts `Subsingleton` of the underlying additive stalk of the j-th `DerivedCategory.homologyFunctor`. A module stalk is zero exactly when its underlying type is subsingleton. |
| Every c in Gamma(Y,H^0(E)) | `c` is an element of `((DerivedCategory.homologyFunctor ... 0).obj E.obj).val.obj (Opposite.op ⊤)`, ordinary global sections of the cohomology sheaf. |
| Some perfect K in D_QCoh(O_Y) | `∃ K : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y K.obj ∧ ...`. |
| Morphism a : K → E | `∃ a : K.obj ⟶ E.obj`; the quasi-coherent derived subcategory is full. |
| Section b in Gamma(Y,H^0(K)) | `∃ b` in the degree-zero cohomology sheaf of `K.obj`, evaluated at `Opposite.op ⊤`. |
| Gamma(Y,H^0(a))(b) = c | `((DerivedCategory.homologyFunctor ... 0).map a).val.app (Opposite.op ⊤) b = c`. This is the actual induced cohomology map evaluated on global sections. |
| H^i(K) = 0 for every i > 0 | `∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor ... i).obj K.obj)`. This is zero as a sheaf, not just vanishing global sections. |
| All cohomology stalks of K vanish on U | The final clause quantifies independently over every `i : ℤ` and `y : Y`, and assumes `y ∉ T` before asserting `Subsingleton` of the indicated stalk. |
| No pseudo-coherence assumption on E | There is no `IsPseudoCoherent`, boundedness, or perfectness assumption on E. |

The two `HasDerivedCategory.{w}` binders are the ambient derived-category choices
required by the existing definitions: on Y and on its localized open sites.
They use independent explicit universes `u w` and the shared coefficient size `u`.
All variables and universes are explicit; `autoImplicit` is disabled. There are no
file-local definitions, instances or notation and no `let` or `show` in the signature.

Statement dependency declarations read in full, including their docstrings:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`. Affineness and affine opens use Mathlib's
  `IsAffine` and `IsAffineOpen` from `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-pc-derived-category`: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`, in
  `WeilConjectures.AlgebraicGeometry.DerivedCategory`. The property means that
  every cohomology sheaf is quasi-coherent, with no boundedness restriction.
- `def-pc-perfect-complex`: `AlgebraicGeometry.Scheme.IsStrictlyPerfect` and
  `Scheme.IsPerfect`, in `WeilConjectures.AlgebraicGeometry.PerfectComplex`.
  Perfectness is the recorded local strictly-perfect-model predicate.
- Mathlib's `SheafOfModules` and `PresheafOfModules` object/morphism signatures
  were read to check that `.val.obj` gives module sections, `.val.app` is the
  actual induced section map, and `.val.presheaf` has the desired additive stalk.

All recorded proof-dependency modules are imported non-publicly. In detail:
`DerivedStructureSheafHomHypercohomology` (the recorded structure-sheaf Hom
identification), `Sheaf.Paper.QCohAcyclicDerivedSectionsComparison`
(`qcoh_acyclic_derived_sections_comparison`), `Cohomology.FiniteFibre`
(`Scheme.Modules.isZero_of_isZero_stalk`), Mathlib's derived `TStructure` and
triangulated `TStructure.Basic`, `UnboundedDerivedFunctorCohomologicalBound`,
Mathlib's `Pretriangulated` (Hom exactness), Mathlib's
`Spectrum.Prime.Topology` (principal-open basis and quasi-compactness),
`KoszulOpenSystem`, `KoszulOpenHomRestrictionEventuallyZero`,
`AffinePerfectOpenRepresentCohomology`, `AffineKoszulGeometricProperties`,
`KoszulComplex`, and `AffineQCohDerivedEquivalence`. Unless explicitly qualified,
these project modules have prefix `WeilConjectures.AlgebraicGeometry`.
The only proof dependency without a recorded statement at reading time was
`lem-sfb-affine-open-finite-cover-cohomology-bound`; it is not needed to type this
statement and is named in the proof docstring for the later proof stage.

Edge cases checked before writing:

- `s = 0`: `Fin 0` is empty, the cover equation forces `Tᶜ = ∅`, and the
  cohomological interval is `[1,0]`, hence empty. No `Nonempty` assumption was
  introduced. For arbitrary E, the class corresponds on the affine scheme to
  a map from O_Y, providing the expected perfect source in degree zero.
- `s = 1`: the assumed interval is exactly degree zero, with the expected
  vanishing of H^0 on the affine complement.
- `T = Y`, including a nonempty redundant cover of the empty complement:
  the stalk conditions are vacuous and O_Y can represent every global class.
- `T = ∅` and nonempty Y: a cover exists only with `s ≥ 1`; the hypothesis
  includes vanishing of H^0(E) everywhere, so `c = 0`. The zero object supplies
  the required perfect source with the stipulated empty support.
- Empty Y: all section modules and stalk conditions have the expected zero or
  vacuous form, and the zero object satisfies the conclusion.
- Zero E and zero c are included. E may be unbounded in either direction;
  only the stated finite interval is constrained.
- Repeated or empty affine opens are permitted. No relation is imposed between
  `s` and the number of principal opens chosen during the proof.

Searches (all through the prescribed tools or read-only source searches):

- `msearch.py ... leanfinder`, query: `A cohomology class of a quasi coherent
  derived object on an affine scheme lifts from a perfect object supported on
  a closed subset`. Eight hits: affine-limit section vanishing, cocycle-class
  maps and sheaf cohomology, none supplying a supported perfect source.
- `msearch.py ... loogle`, query: `"IsPerfect", "homologyFunctor"`.
  Successful search, zero hits.
- `msearch.py ... grep`, query:
  `Koszul.*(support|cohomology)|represent.*cohomology.*class|perfect.*supported`.
  Successful search, zero Mathlib hits.
- `msearch.py ... leansearch`, query: `A cohomology class lifts from a perfect
  complex supported on a closed subset of an affine scheme`. Eight hits,
  including `CochainComplex.HomComplex.CohomologyClass`, its quotient maps,
  ideal-sheaf support and abstract cycle lifts; none states this theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, queries
  `supported.*class|class.*lift|affine_supported|supported_perfect` and the
  narrower `affine.*(class|lift)|supported.*(class|lift)`. Related supported
  perfect generators and unrelated Kummer/cohomological class lifts occur;
  no existing declaration states this class-lifting assertion.
- `grep -rn 'lem-sfb-affine-supported-class-lift' lean/WeilConjectures`:
  no hit. `dag/lean_names_upstream.json` was also searched for affine and
  supported class/lift names: no matching theorem.

No statement correction, disputed statement, missing notion or unusable statement
dependency was found. No new nodes or dependency modules are delivered.

Validation: the prescribed `scompile.py Q123 lem-sfb-affine-supported-class-lift`
compiled this file as both the sandbox module and its eventual library module
against the server publication (7.8 s and 4.2 s respectively), with no errors or
unexpected warnings. The sole postponed proof is the named theorem above.

## Second reading by Q123

On a second pass, the written module and the original node were reopened and
compared clause by clause. This is a self-check by the dispatched worker; the
maintainer supplies the independent delivery review described in the brief.
The table above records the individual comparisons. In particular, the source
of `c` and `b` is sections of cohomology, the conclusion uses the actual map on
cohomology, and positive-degree vanishing is `IsZero` of the whole sheaf.
The two stalk clauses have the right quantifiers: a finite degree interval for
E, all integer degrees for K, and exactly the complement of T in both cases.
The cover uses `Fin s` without excluding zero. `K` is both quasi-coherent and
perfect; `a` is a derived-category morphism; E has no pseudo-coherence or
boundedness constraint. No mismatch or change was found in this pass.
