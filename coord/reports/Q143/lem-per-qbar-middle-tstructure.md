## Worker report

The module `Sheaf.Paper.QbarMiddleTStructure` states
`WeilConjectures.qbar_middle_tstructure`. Its sole proof is `by sorry`.
There are no new definitions, dependency repairs, or statement changes. The
node copy differs from its current shared base only in `lean`.

On resumption after the provider interruption the sandbox contained only its
brief markers: no module, report, node copy, or prior delivery result existed.
The shared Q06 delivery is the earlier stage-1 split, not a stage-2 statement.

### Hypotheses and objects

- The field in the statement is `(k : Type u) [Field k]`.
- The prime is `(l : ℕ) [Fact l.Prime]`; invertibility is exactly
  `(hl : IsUnit (l : k))`.
- The coefficient algebraic closure is `(Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. This spells out
  the coefficient convention inherited from `def-weil-pbc-qbar-category`.
- The scheme is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Separatedness is `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type is `[LocallyOfFiniteType (X ↘ Spec (.of k))]` together
  with `[QuasiCompact (X ↘ Spec (.of k))]`, the project's recorded
  convention. These imply the Noetherian and finite-dimensional domain
  conditions of the coefficient category. No such independent assumptions
  or equality of coefficient and scheme universes is added.
- The category is literally
  `generalAlgebraicallyClosedConstructibleCategory l Ω X`, the carrier
  of `intrinsicPbcQbarCategory` in the current dependency record. This
  is the intrinsic completed/rationalized finite-stage pair category,
  not an unrestricted derived category or a Weil-equivariant category.

### Every clause of the conclusion

- `∃ t : Triangulated.TStructure (...)` asserts all the Mathlib
  t-structure axioms, including isomorphism closure, shift inclusions,
  orthogonality and distinguished truncation triangles.
- `∀ n, t.le n = QbarPerverseLE l X Ω n` identifies every upper
  class with the recorded support predicate. That predicate is
  `QbarSupportCondition l X Ω (K⟦n⟧)`. Its finite representative
  uses the closure of the locus of nonzero *rationalized completed*
  geometric fibres of cohomology. The inequality in its definition is
  tested only for nonempty support; it also requires its integer upper
  bound to be nonnegative. Thus the empty-support value is -infinity.
  Since `H^(-i)(K[n]) = H^(n-i)(K)`, putting `j=n-i` gives exactly
  `dim Supp H^j(K) ≤ n-j`, in every integer degree.
- `∀ n, t.ge n = QbarPerverseGE l X Ω k hl n` identifies every lower
  class with the recorded relative cosupport predicate on `K[n]`.
  `QbarCosupportCondition` uses the actual integral internal Hom into
  each object representing the structure-map exceptional adjunction
  against the base coefficient unit. The representing property
  determines that object up to compatible isomorphism: it is the
  relative dualizing object, not a freely chosen dual. Rationalizing
  the fibres removes integral torsion. The input `k`, structure map,
  and `hl` are exactly this theorem's base data. The arbitrary-field
  duality dependency supplies this relative dual and its shift
  reversal; hence this is `D_X K ∈ pD^{≤-n}`, as the node requires.
  No finite-field or perfect-field dual is substituted.
- `∀ K, ∃ m n : ℤ, m ≤ n ∧ t.le n K ∧ t.ge m K` is precisely
  boundedness with the ordered indices in `def-weil-t-structure`.
- For every integer `n` and every object `K`, the penultimate conjunct
  is exactly `K ∈ pD^{≥n} ↔ ∀ A ∈ pD^{≤n-1}, Hom(A,K)=0`:
  `∀ f : A ⟶ K, f = 0` expresses the zero Hom group in the
  inherited preadditive category. It is an equivalence, not one implication.
- The final conjunct quantifies over each integer and each distinguished
  triangle. Membership of its first and third terms in the upper class
  implies membership of the second; the second implication says the
  identical assertion for the lower class. This is extension closure of
  both classes at every index, without any requirement that they be
  stable under all shifts.

### Dependency declarations read and used

1. `def-weil-scheme-morphism-properties` is a convention node: its
   record explicitly has no declaration. We use its constituent Mathlib
   `AlgebraicGeometry.Scheme`, `Scheme.Over`, `IsSeparated`,
   `LocallyOfFiniteType`, and `QuasiCompact`, with their usual meanings.
2. `Sheaf.Paper.IntrinsicQbarCategory`:
   `WeilConjectures.intrinsicPbcQbarCategory` aliases
   `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
   The latter's existing common-stage shifts, zero morphisms and
   triangulation are the ones used by `TStructure` and `distTriang`.
3. `Sheaf.SixFunctors.ArbitraryFieldVerdier`:
   `WeilConjectures.arbitrary_field_verdier_duality`, its
   `ArbitraryFieldVerdier.Datum`, `Datum.omegaX/omegaY`,
   `Datum.dualX/dualY`, `Normalization`, and `Properties` were read.
   They identify the exceptional adjoints, coefficient unit, evaluation
   biduality, relative transcendence-degree normalization and shift
   reversal over arbitrary fields. The theorem does not impose the
   whole package as an additional assumption.
4. `Sheaf.Paper.QbarPerverseSupportCondition`:
   `WeilConjectures.QbarSupportCondition`,
   `QbarPerverseAmbientSupportCondition`, `qbarPerverseAmbientSupport`,
   `QbarPerverseIntegralDualizingProperty`, `QbarCosupportCondition`.
   Their source code and docstrings were read in full. They are
   reexported by the next module.
5. `Sheaf.Paper.QbarPerverseSubcategories`:
   `WeilConjectures.QbarPerverseLE` and `QbarPerverseGE` are used
   directly. Its heart is not redefined or separately asserted here.
6. `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`:
   `CategoryTheory.Triangulated.TStructure` is the recorded Mathlib
   match for `def-weil-t-structure`; its full indexed fields and
   bounded/plus/minus definitions were read. We state the node's
   ordered-bound formulation explicitly.

The available proof-dependency modules are imported without `public`:
`Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds`,
`Sheaf.Paper.PbcVerdierAxioms`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
`Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`.
The latter supplies the recorded `TStructure.isLE₂` / `isGE₂` and
`isGE_iff_orthogonal`; the dimension module supplies
`AlgebraicGeometry.exists_topologicalKrullDim_le`. The fibre modules
are already public dependencies of the support predicates; representable
Hom exactness is provided by Mathlib's imported pretriangulated API.
The two genuinely unstated proof nodes `lem-per-qbar-dual-recollement`
and `lem-per-qbar-generic-duality-model` have no module to import; they
remain proof dependencies and are not needed to elaborate the statement.
The docstring follows all ten steps of the node proof, including these
future proof inputs, rather than proving anything at stage 2.

### Edge cases and sources

The empty scheme is permitted: empty support satisfies every inequality,
all objects there are zero, and all classes contain them. The zero object
on any scheme is permitted for the same reason. All indices are integers,
so negative degrees are not replaced by natural degrees. On a point,
the inequalities give the ordinary t-structure. On a pure d-dimensional
smooth component a lisse object shifted by d is in the heart; a punctual
object in degree zero is in the heart. These checks confirm the upper
shift sign, and shift reversal by relative duality confirms the lower
sign and the `n-1` in the orthogonality formula. Disconnected schemes
with components of unequal dimension are not excluded: no pure-dimension,
nonempty, smoothness, irreducibility or connectedness binder appears.
The field is not required to be finite, perfect or separably closed.

I read the current main-20261015 perverse unit and affine-curve ancestor,
the node's ten-step split and its stage-1 review, and BBD printed pp.
48 (1.4.9--1.4.10) and 101--102 (4.0, including (4.0.1')). The node
explicitly interprets the adic categories using Bhatt--Scholze and the
arbitrary-field duality node; BBD's older restriction on its coefficient
formalism is not silently reintroduced. No statement correction or
STATEMENT-DISPUTED flag is needed for this formalization.

### Searches

The actual `msearch.py` calls are recorded in sandbox `searches.jsonl`:

- LeanFinder, `bounded perverse t-structure support cosupport Verdier dual`:
  eight hits, including `DerivedCategory.TStructure.t`, `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`, and generic indexed t-structure predicates.
  None constructs the middle perverse t-structure on adic coefficients.
- LeanSearch, `middle perverse t structure support and Verdier dual cosupport`:
  eight hits, ordinary derived t-structure, supported-complex and module
  support results; no match.
- Loogle, `"perverse"`: no hits. The earlier attempted query
  `DerivedCategory.TStructure, perverse, support dimension` was rejected
  as an unknown identifier and is not evidence of absence.
- Mathlib grep, `perverse|Perverse`: no hits, both globally and under
  `CategoryTheory/Triangulated`. An initial mistaken subdirectory argument
  `WeilConjectures` returned no hits and is not used as evidence.
- Direct `rg` of the upstream project for perverse predicates found
  `WeilConjectures.SixFunctors.Etale.Perverse.Basic` and the curve-specific
  `DeligneLaumon.AffineLine.Perverse`. The former only defines the
  finite-coefficient-style predicates; the latter only gives the
  smooth-curve orthogonal description. Neither states this theorem.
- Direct `rg` for the item id upstream found no declaration.
- Direct `rg` of `lean/Sheaf` for `QbarPerverseLE|QbarPerverseGE` found
  the recorded subcategory module only. Searches for middle/qbar
  t-structure names found no existing theorem.
- The intended full name `WeilConjectures.qbar_middle_tstructure` is absent
  from Mathlib, upstream source, `dag/lean_names_upstream.json`, and the
  shared `lean/Sheaf` library.

### Validation

The required `scompile.py Q143 lem-per-qbar-middle-tstructure` compiled
`lean/Sheaf/Paper/QbarMiddleTStructure.lean` cleanly under both its sandbox
name and its library module name (4.7 s and 4.6 s). The only postponed proof
is the named main theorem, carrying the source and full natural-language
proof in its docstring. All universes and variables are explicitly bound;
`autoImplicit` and `relaxedAutoImplicit` are disabled. There are no
file-local notations, private definitions or local instances.

## Second reading by Q143

No second reading by a worker: this directly dispatched worker delivers
itself, and the maintainer's independent delivery review supplies the
independent reading. This section does not claim a separate agent review.
