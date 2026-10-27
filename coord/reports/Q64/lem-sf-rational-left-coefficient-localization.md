## Worker report

The module `Sheaf.Paper.RationalLeftCoefficientLocalization` states
`WeilConjectures.rational_left_coefficient_localization`, with its whole proof
`sorry`. It introduces no definitions and preserves the node's mathematical
statement, dependencies and proof. No new or repaired dependency nodes are needed.

Hypothesis and conclusion correspondence:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. Its prime, finite base
  field, algebraic closure and structure homomorphism are those in the recorded
  `Sheaf.Paper.FiniteFieldFiber` declaration. `l`, `[Fact l.Prime]`, and
  `hl : l ≠ D.p` impose exactly the coefficient characteristic restrictions.
- `X Y : Scheme.{u}`, the two `Over (Spec (.of D.k))` instances, and the pairs
  `LocallyOfFiniteType`/`QuasiCompact` on the structure morphisms express finite-type
  k-schemes. These are Mathlib's finite-type convention, as explicitly recorded by
  def-weil-scheme-morphism-properties and def-weil-finite-type-morphism.
  No absolute separatedness is imposed. `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f` express the separated finite-type
  k-morphism. `_c : Compactification f` is the stipulated fixed compactification.
- Each `E`, `L`, `M` is an arbitrary `Type u` with `Field`, `Algebra (Padic l)`
  and `FiniteDimensional (Padic l)` instances. All arrows are algebra embeddings
  `ι`, `κ`; their direct composite is `κ.comp ι`. Thus inclusions, arbitrary
  embeddings, identity embeddings and repeated fields are included.
- `sfIntegralConstructibleCategory l E X` and its Y version are precisely the
  recorded completed integral categories. Their definition includes derived
  completeness, all positive constructible reductions and a common cohomological
  interval. Reduction index n means exponent n+1, so no zero quotient is substituted
  for a positive finite level. The rings are the recorded
  `Padic.coefficientExtensionRing l E (n+1)`.
- `sfRationalConstructibleCategory` and `sfRationalConstructibleLocalization`
  are the recorded raw localization and R. Their objects are unchanged integral
  objects; `sfRationalHomCoordinates` identifies Hom with integral Hom tensor E.
  No Karoubi completion or alternative coefficient category is used. The ambient
  category behind these full subcategories is Mathlib's `DerivedCategory` applied
  to the completed small pro-etale module category, implementing def-sf-categories.
- `Fint` and `F` are the given families of integral and rational functors,
  quantified over every finite extension. `sfConstructibleIntegralScalarExtension`
  is the actual completed integral scalar extension restricted to this category;
  `sfRationalScalarExtension` is its recorded raw scalar extension. The imported
  recorded `integralScalarExtensionOfUniverses` interface exposes the same
  construction; neither construction is replaced by arbitrary functors.
- `sfIntegralScalarComp`, `sfIntegralScalarUnit`, `sfRationalScalarComp`, and
  `sfRationalScalarUnit` are the published normalized associators and unitors from
  `Sheaf.Paper.SfScalarExtensionComposition`. Their specifications use ordinary
  balanced tensor multiplication and the normalized ordinary/completed
  comparisons, and rational components are localized integral components.
- `qint E L ι` and `q E L ι` are natural isomorphisms from `F_E ⋙ T^Y` to
  `T^X ⋙ F_L`. This is the node's `T^Y F_E ≅ F_L T^X` in Lean's diagrammatic
  functor-composition order. `hq` identifies each rational hom component on an
  integral representative with the localized integral hom component. `HEq` records
  transport along the specified object equalities; it does not equate arrows
  in unrelated Hom groups without those equalities.
- `hobj` states `F_E(R_X K) = R_Y(Fint_E K)` for every integral K.
  `hmap` quantifies over K,K', every n, coefficients `a : Fin n → E`, and
  integral arrows `h : Fin n → (K ⟶ K')`. Applying F to the inverse Hom coordinates
  of `∑ h_i ⊗ a_i` equals, after the specified object identification, the inverse
  Hom coordinates of `∑ Fint(h_i) ⊗ a_i`. This is exactly the displayed finite-sum
  normalization, including the empty sum, with coefficients in E itself.
  There is no extra additive or linear-functor hypothesis.
- `hcomp` and `hunit` are the assumed integral composition and identity equations
  for all coefficient fields and all integral inputs, using those normalized
  associators and unitors. In Lean, `g ≫ h` means first g then h, hence the factors
  in each written equality occur in the reverse order from the node's usual
  functional notation.
- The first conclusion gives every rational K an integral Kint with
  `R_X.obj Kint = K` and `finiteTorConstructibleIntegral l E X Kint.obj`.
  This predicate includes one ordered Tor interval for every positive reduction.
- The second conclusion is precisely
  `T^Y_ML(q_LE) ≫ q_ML(T^X_LE K) ≫ F_M.map α_X = α_Y ≫ q_ME`.
  The third is `q_EE ≫ F_E.map u_X = u_Y`. Both quantify over all rational inputs.
- The fourth and fifth conclusions explicitly identify `F_M.map α_X` and
  `F_E.map u_X` with R applied to the corresponding integral functor-image arrows.
  They are stated on all integral representatives; the first conclusion covers
  every rational object. `HEq` allows exactly the specified object transports.
  No assertion that localization reflects equality appears.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`,
  `.Separated`, and `Mathlib.AlgebraicGeometry.Over`: `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `Scheme.Over`, `Scheme.Hom.IsOver`, as directed
  by the convention record of def-weil-scheme-morphism-properties.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, the
  current existing declaration attached to def-sf-categories; specialized via
  the already recorded intrinsic category definitions rather than copied aliases.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension` dependency: `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing` (in the category and reduction constructions).
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalHomCoordinates`,
  `sfRationalScalarExtension`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: the recorded
  `integralScalarExtensionOfUniverses`, retaining the same actual completed scalar
  construction. Its restriction is the published
  `sfConstructibleIntegralScalarExtension` in
  `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
- `WeilConjectures.Compactification.RefinementCategory` and its public `Defs`
  import: `AlgebraicGeometry.Compactification` and the recorded refinement category.
- `Sheaf.Paper.SfScalarExtensionComposition`: all four normalized scalar
  comparisons listed above. These existing declarations were read in full,
  including their normalization specifications and ordinary tensor formulas.
- Proof dependencies: `Sheaf.Paper.IntegralResidueTor.integral_residue_tor`
  (declaration namespace `WeilConjectures`); `Sheaf.CategoryTheory.ScalarLocalization`
  and the recorded raw localization are already exposed by statement imports.
  `finiteTorConstructibleIntegral` is reused from `Sheaf.Paper.FiniteTorAmplitude`.

Edge cases checked before writing and on rereading: empty X or Y and zero objects
are not excluded; the empty coefficient sum n=0 is included; finite levels are
always positive by the recorded n+1 indexing; arbitrary ramified embeddings are
not replaced by inclusions or identity maps; E=L, L=M and E=L=M remain allowed;
there is no equality-reflection assumption; there are no auto-implicit variables,
local aliases, extra linearity hypotheses or absolute separatedness assumptions.
The single universe u is arbitrary and common to the existing category APIs;
the small pro-etale site's object/hom universes retain their published distinction.

Searches for an existing statement:

- msearch.py LeanFinder: "Localizing normalized integral linear functors and scalar
  comparison maps preserves associativity and identity coefficient equations".
  Eight results, including `CategoryTheory.Localization.functor_linear_iff`,
  `CategoryTheory.Localization.linear`, and `IsLocalizedModule.map_linearCombination`;
  none states the geometric uniform finite-Tor domain with these given functors.
- msearch.py LeanSearch: "Integral linear scalar localization descends coefficient
  natural isomorphism composition and unit equations". Eight module-localization
  results (`IsLocalizedModule.map_comp`, `lift_comp_iso`, etc.); none is the item.
- msearch.py Loogle: `CategoryTheory.Functor.map_comp`. Six results; generic functor
  composition preservation and unrelated presheaf results do not state the item.
- msearch.py grep in Mathlib CategoryTheory:
  `localiz.*(associator|unitor)|scalar.*comparison.*cocycle`. Seven hits in
  localization LocalizerMorphism, Adjunction, Monoidal.Basic and Trifunctor;
  these provide generic localization machinery, not this full statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and names
  `rational_left_coefficient_localization|sfLeftCoefficient`: no matching statement.
  Concept searches for scalar associators/unitors found and reused the existing
  `SfScalarExtensionComposition` interface. Searches for `leftCoefficient`,
  `LeftCoefficient`, `left_coefficient`, `qInt`, `qint` found distinct exceptional
  composition/trace modules, not this localization lemma.

The released repair-note path for this item was checked: no file is present.
No statement fault or dispute was found. The proof docstring records all four DAG
proof steps. The latest blueprint source at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`
was read; the item records an extracted old normalized-coefficient argument.

Validation: prescribed scompile.py passed both sandbox and library compilation,
with no errors or warnings beyond the allowed sorry status. The initial compile
caught an unavailable bundled `FiniteType` name; it was replaced by the recorded
Mathlib conjunction `LocallyOfFiniteType` and `QuasiCompact` without changing the
mathematical hypotheses. Every theorem proof remains `sorry`.

## Second reading by Q64

An independent maintainer-side second reading (cc review service, 2026-10-25) replaces
the worker's self-check. I read the node, its eight stmt_deps, the module and the
declarations it uses (SfRationalizationKaroubi, SfScalarExtensionComposition,
IntegralScalarExtensionConstructibleIntrinsic, FiniteTorAmplitude, SfIntegralConstructible).

Node clauses and their Lean:

1. Prime l, finite-field datum k with char p ≠ l: `D : FiniteFieldDatum.{u}`,
   `[Fact l.Prime]`, `hl : l ≠ D.p`. Correct.
2. Finite-type k-schemes X, Y, no absolute separatedness: `Over (Spec D.k)` with
   `LocallyOfFiniteType` and `QuasiCompact` on the structure maps; no `IsSeparated` on
   them. Correct.
3. Separated finite-type k-morphism f: `f.IsOver`, `IsSeparated f`,
   `LocallyOfFiniteType f`, `QuasiCompact f`. Correct.
4. Fixed compactification c: `_c : Compactification f`. It is unused, as in the node.
5. C_{E,int}, C_E, R_E, Hom ⊗ E: `sfIntegralConstructibleCategory`,
   `sfRationalConstructibleCategory` (raw `ScalarLocalization`, no Karoubi completion),
   `sfRationalConstructibleLocalization`, `sfRationalHomCoordinates`. These are the
   def-weil-derived-complete-integral-detailed and def-weil-rationalization-karoubi
   records. Correct.
6. T_int and T: `sfConstructibleIntegralScalarExtension` (the completed integral
   extension restricted to constructibles) and `sfRationalScalarExtension`. The
   object spec of the latter is literally `⟨T_int K.obj⟩`. Correct.
7. α, u normalized by balanced tensors, with rational = localized integral:
   `sfIntegralScalarComp/Unit` (∃!.choose, pinned by the ordinary tensor associator/unit
   conjugated by the ordinary/completed comparisons) and `sfRationalScalarComp/Unit`.
   Their ∃! spec is `HEq (a.hom.app K) (R.map (α_int.app K.obj))`, which is exactly the
   node's "localized integral maps". Correct.
8. All Q_l-embeddings: arbitrary `E L M : Type u` with `ι, κ : _ →ₐ[Padic l] _` and the
   composite `κ.comp ι`. Correct.
9. Integral comparisons with the composition and identity equations: `qint`, `hcomp`,
   `hunit`. I checked the endpoints in diagrammatic order. Both are exactly the node's
   functional-order equations. Correct.
10. Rational q with localized components: `q`, `hq` (HEq). The endpoint types agree
    propositionally through `hobj` and the object spec of T, so the hypothesis is
    satisfiable and not vacuous. Correct.
11. Object equality and finite-sum arrow normalization: `hobj`, `hmap` (any n, including
    the empty sum, with a : Fin n → E through the Hom coordinates). The HEq endpoints
    agree through `hobj`. Correct; no extra linearity hypothesis.
12. Domain conclusion: `∃ Kint, R.obj Kint = K ∧ finiteTorConstructibleIntegral l E X
    Kint.obj`. That predicate gives one Tor interval [a,b] for all reductions n+1 ≥ 1.
    Correct.
13. Rational composition and identity equations: conjuncts 2 and 3, the node's
    equations in `≫` order. Correct.
14. "In particular" functor-image clauses: conjuncts 4 and 5 (HEq with R(Fint.map α_int))
    and (R(Fint.map u_int)). Correct. Equality reflection is not asserted.

Edge cases: empty X/Y and the zero object are allowed; n = 0 in hmap is allowed;
E = L = M and the identity embedding are allowed; every finite level is positive (n+1).
There is one universe u, common to the recorded category APIs.

Searches: I grepped the project lean/ trees for `rational_left_coefficient` and
`localiz.*associator` and found no existing statement. The worker's LeanSearch,
LeanFinder, Loogle and grep records are adequate.

Findings: none in substance. Advisory: the statement uses declarations owned by nodes
that are not in stmt_deps: lem-weil-scalar-extension-composition (∃!.choose canonical
isos), lem-weil-integral-scalar-extension-constructible (the T_int restriction that
def-weil-rationalization-karoubi's T already uses) and def-weil-finite-tor-amplitude.
stmt_deps are unchanged from stage 1, so this is advisory only. The only change is
this section, which replaces the worker's self-check (H11).
