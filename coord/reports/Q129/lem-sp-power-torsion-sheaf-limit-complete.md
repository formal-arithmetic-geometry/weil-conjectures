## Worker report

The module `Sheaf.Paper.PowerTorsionSheafLimitComplete` states
`WeilConjectures.PowerTorsionLimit.power_torsion_sheaf_limit_complete`.
The main theorem docstring records the source and all nine proof steps. The named
`unit_condition` theorem postpones the well-definedness of the canonical unit, with
its own source and full proof docstring; it is the cocycle condition for the inclusions
explicitly required by this node. The helper declarations give actual functors, the explicit
zero-homotopy completion unit, and coordinates of the existing mapping-cocone Roos model.
No definition contains sorry. There are no statement corrections or disputed statements.

Hypothesis and clause correspondence:

- Prime ell: `l : ℕ` and `[Fact l.Prime]`. Finite E/Q_ell and its valuation ring:
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`, using the recorded coefficient extension integers.
  The uniformizer is the existing
  `WeilConjectures.PrincipalKoszulStrictReplacement.uniformizer l E T`, the image of the
  coefficient uniformizer through the constant-to-completion map. It is imported, not
  defined a second time.
- The scheme is `T : AlgebraicGeometry.Scheme.{t}`. The coefficient category is the
  existing `integralTowerModules l E T`, over
  `completedIntegralCoefficientSheafUnrestricted l E T`. The coefficient-tower node's
  `sp_completed_coefficient_limit` and cofinality identify the completed ring with the
  blueprint convention. Site and coefficient universes remain independent.
- The strict inverse tower with linear transitions is
  `Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ`. Positive paper level n
  is Lean level n-1. All complexes are unbounded; no normalization, constructibility,
  or cohomological bound is a binder.
- Termwise power torsion is `hQ : ∀ n, ∃ r, 1 ≤ r ∧ ∀ a U x, ... ^ r • x = 0`.
  The exponent may depend on n, but is uniform across terms and sections at that n,
  exactly as required. It is not assumed uniformly bounded over the tower.
- H is the explicit `(roos l E T).obj Q`. The abbreviation reuses
  `integralOperationsRoosFunctor`, with its canonical countable products; the exact
  pro-etale product theorem and strict Roos comparison identify it with total Rlim.
- `tensorTower` reuses `principalKoszulTower` and `koszulTensorTower` for the two-term
  complex of multiplication by pi^(j+1), transitions (pi,1), and its degree-zero
  inclusions `koszulRepresentativeAugmentation`. It uses the symmetric left-tensor
  convention L_j tensor Q_n. The standard signed tensor symmetry identifies this
  with Q_n tensor L_j, including its degree-zero inclusion. No new tensor or Koszul
  complex definition is introduced.
- `completion` is `tensorTower ⋙ roos`. `unit P` is precisely the mapping-cocone lift
  of the product of degree-zero inclusions with zero homotopy. The existential natural
  transformation eta is fixed at every object by `η.app P = unit P`; its naturality
  supplies naturality in every strict tower. `∀ n, QuasiIso (unit ... (Q.obj (op n)))`
  states the levelwise derived isomorphisms.
- The isomorphism beta is between the two iterated strict Roos models. `columns` flips
  the two tower variables before applying Roos. For every degree, both indices and all
  four Bool pairs, its equation with `columnCoordinate` and `rowCoordinate` fixes beta
  to the double-product interchange, with minus sign exactly for p=q=1. These
  coordinates are the actual cone product projections, so the equation determines
  the map and its naturality, rather than leaving an arbitrary isomorphism.
- The next four coordinate equations explicitly give compatibility with the inclusions.
  For inner Koszul/Roos degree q=0 the coordinates are the outer Roos coordinates
  followed by the Koszul inclusion; for q=1 both are zero. The functor right unitor
  identifies the source of the whiskered eta with Q before applying Roos.
- `QuasiIso (unit ... ((roos ...).obj Q))` is the asserted completion-unit isomorphism
  for H. It concerns the explicit unit already defined, not a selected map.
- P is an existing `IntegralOnSlice.Good ... none` representative (K-flat, with flat
  terms); f is its quasi-isomorphism to H and `eP.hom = DerivedCategory.Q.map f`
  fixes its derived identification. This represents H without imposing any hypothesis
  on Q or H. The actual quotient tower is `IntegralOnSlice.tower ... none P.obj`,
  computed by the recorded scalar extension and restriction on this representative.
- The derived isomorphism s has the exact source and target of the Koszul-to-quotient
  limit comparison. Its full composite with the invertible explicit unit equals
  `eP.inv ≫ Q.map (IntegralOnSlice.roosUnit ... P.obj)`. Thus it is normalized by the
  existing strict quotient augmentation, including its zero homotopy. This equality
  determines s uniquely, and rules out arbitrary projection-compatible choices.
- The following equation for every j identifies the j-th projection with
  `eP.inv ≫ Q.map (((IntegralOnSlice.augmentation ...).app P.obj).app (op j))`.
  This augmentation is the actual scalar-extension x-to-1-tensor-x unit, not a
  hypothesized reduction map. `evaluation` uses the Roos first projection.
- The product structure is supplied existentially, not assumed. `IsDerivedLimitTriangle`
  on `IntegralOnSlice.derivedTower` gives the distinguished triangle, with its second
  map the existing one-minus-shift and its first map p satisfying these same canonical
  reduction projection equations.
- The final `IntegralOnSlice.IsComplete ... none (DerivedCategory.Q.obj H)` is
  definitionally the published integral `IsDerivedCompleteUnrestricted` predicate.

Recorded dependency interfaces used/read:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`:
  `AlgebraicGeometry.ProEtale.spCoefficientTowers`, `sp_completed_coefficient_limit`,
  and `sp_coefficient_ideals_cofinal`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, including
  the total derived functor, natural Roos triangles and pro-zero criterion.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `CategoryTheory.MonoidalCategory.curriedTensor`, as used by the Koszul tensor tower.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`. The finite quotient
  functors in the recorded integral operations use its ordinary scalar extension,
  derived on good representatives, with its canonical counit.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by these actual finite reductions.
- `Sheaf.Paper.DerivedCompleteOnSlices`:
  `WeilConjectures.IntegralOnSlice.derivedTower`, `derivedLeg`, and `IsComplete`.
- Added already-landed statement dependencies:
  `def-pur-principal-koszul-quotient-towers`, module
  `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`, declarations
  `CategoryTheory.principalKoszulTower`, `koszulTensorTower`, and
  `koszulRepresentativeAugmentation` (including its transition naturality);
  `def-pur-integral-derived-operations`, module
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, declarations
  `WeilConjectures.IntegralOnSlice.tower`, `Good`, `augmentation`, and `roosUnit`;
  `def-sp-completed-uniformizer-section`, module
  `Sheaf.Paper.PrincipalKoszulStrictReplacement`, declaration
  `WeilConjectures.PrincipalKoszulStrictReplacement.uniformizer` (existing: true).
  This new definition node owns precisely the section used by the statement. It replaces
  the previously added theorem dependency `lem-a1-principal-koszul-strict-replacement`.
  The original statement dependencies and the Lean file stay unchanged.

The imports include the recorded proof dependencies that have Lean modules: independent
K-flat resolutions and invariance, tensor/cone compatibility, acyclic-cone criterion,
complex short-exact triangles, exact countable pro-etale products and strict Roos
comparison. The proof-only coefficient-fiber node has no recorded Lean declaration.

Edge cases checked: zero complexes and the empty scheme impose no nonzero assumptions;
Lean index 0 means exponent/level 1, never the zero quotient; r=1 is allowed; r_n can grow
arbitrarily; transitions can be zero or identity when compatible with the torsion terms;
complexes can be nonzero in every positive and negative degree. The double total uses
only four Roos coordinates in each degree, and the sole negative sign is (1,1).
There is no site/coefficient universe equality: T has object universe t+1 and morphism
universe t, while coefficients/modules use max u (t+1), as in the existing interfaces.

Searches performed:

- `msearch.py Q129 lem-sp-power-torsion-sheaf-limit-complete leanfinder` with
  `Derived limit of power torsion sheaf complexes is derived complete via Koszul completion unit and double Roos interchange`:
  returned eight unrelated results, including local cohomology diagrams and BDeRhamPlus;
  none states this node.
- `msearch.py ... loogle` with `"DerivedCategory", "limit"`: zero results.
- `msearch.py ... grep` with `Roos|derivedComplete|[Pp]ower[Tt]orsion`: zero results.
- `rg` and the prescribed node-id grep in `lean/WeilConjectures`, and `rg` in
  `lean/Sheaf` for Roos, derived completion, and power torsion: existing framework
  and specialized completeness results, but no theorem with these hypotheses and
  all canonical interchange/unit/projection clauses.
- Read `TorsionLimitSheafCompleteness`, `StrictRoosComparison`, integral derived
  operations, derived completeness, and the principal Koszul tower interfaces;
  none duplicates the present statement.
- A focused `rg` for uniformizer/parameter definitions located
  `PrincipalKoszulStrictReplacement.uniformizer`; removed the draft's duplicate
  construction and imported that exact section. Read its full definition and the
  owning node's record.
- `rg 'PowerTorsionLimit|power_torsion_sheaf_limit_complete'` in Mathlib/project names
  and the upstream names index: no conflicting declarations. Matches on the broader
  PowerTorsionLimit substring concern the distinct `IsLocallyPowerTorsionLimit` notion.

The source completeness sentence was read in the current main-20261015 blueprint's
`sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`; the more detailed node proof
provides the canonical-model clauses. No source-based statement correction was needed.

Validation: server `scompile.py` compiles both sandbox and library module presentations
with no errors or warnings. The delivery dry run also checks preflight and compilation. Definitions use no
postulated data; the main theorem and its named unit well-definedness condition intentionally have
proof `sorry` for stage 2.

## New nodes

`def-sp-completed-uniformizer-section` defines the image of the chosen coefficient
uniformizer in the global sections of the completed integral coefficient sheaf. It
cites `def-weil-l-adic-coefficient-extension` for the chosen element and
`def-weil-completed-integral-coefficients` for the canonical constant-to-limit map.
Its source is the scalar used in the current blueprint reconstruction proof's
reduction-as-cone and completeness calculation. This node has an `existing: true`
record for `WeilConjectures.PrincipalKoszulStrictReplacement.uniformizer` in the
unchanged landed module `Sheaf.Paper.PrincipalKoszulStrictReplacement`. The returned
review explicitly required a definition owner for this helper; no second construction
is introduced. The definition is `sectionsMk` applied to the sheafification of the
constant chosen uniformizer and then `integralConstantToCompletionOfUniverses`.
Its compatibility proof uses naturality of these two actual maps, so the section
has no dependence on the strict-replacement theorem or an existential choice from it.
The explicit section type is the sections of the unit module over the completed ring.
The prime, finite coefficient extension and arbitrary scheme binders are exactly
those of the imported definition; site and coefficient universes remain independent.
On an empty site object it gives the unique section, and no nonvanishing or
nonempty-scheme hypothesis is added.

New-node searches (actual results are also in `mathlib_searches`): LeanSearch for
"Image of a chosen uniformizer of a finite extension of the l-adic numbers as a global
section of the completed integral coefficient sheaf on a scheme pro-etale site"
returned eight hits concerning valuation uniformizers, global-section restriction,
and padic equivalences; none constructs this section. LeanFinder for "The constant
uniformizer section of the inverse limit of constant quotient ring sheaves on the
pro-etale site" returned eight BDeRham and standard-etale-presentation hits, none
matching. Mathlib grep `uniformizer|integralConstantToCompletion` returned 25 DVR,
valuation and completion hits with no such coefficient sheaf section. Project/DAG
`rg` located the imported helper and references to it, but no definition node owning
it. `blueprint_refs.py search 'completed uniformizer section'` returned zero matches;
the broader uniformizer search found coefficient setups and their applications.
`blueprint_refs.py ancestor` confirms `sk-lem-sp-tower` as the ancestor.

## Returned review repair and self-check

The H2/H12 return at immutable head `5c013ff4bc98` is repaired by adding the above
definition node and replacing only the previously added
`lem-a1-principal-koszul-strict-replacement` statement dependency with it. The saved
Lean module, its theorem signature, the node's mathematical statement and all proof
steps are retained. The saved packet first passed the required initial dry run
(commit `5c8a1631fb7`); the dependency repair is an additional concrete change after
that check. I read the current live module through `scompile.py --source` and the
local constant-to-completion construction: the section is the concrete definition
identified by the maintainer. The section's coordinates are the chosen uniformizer's
constant residue classes because the constant-to-completion map is the limit lift of
the actual quotient cone. The original report's clause-by-clause correspondence and
the independent returned review of all other clauses continue to apply. This is a
worker self-check; the maintainer performs the independent delivery review.

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
