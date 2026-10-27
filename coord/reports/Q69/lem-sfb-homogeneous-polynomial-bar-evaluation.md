## Worker report

The item is stated by `Profinite.CondensedAction.HomogeneousPolynomialBar.homogeneous_polynomial_bar_evaluation`
in `Sheaf.CategoryTheory.HomogeneousPolynomialBarEvaluation`. Its sole proof is `sorry`.
The new specification module `Sheaf.CategoryTheory.HomogeneousPolynomialBarModel` has no
`sorry`, no chosen objects from existential theorems, and no new assumptions on the item.
Its `Data` type specifies all the complexes, actual internal coproduct presentations,
actual internal Hom identifications, maps and their normalization equations. The theorem
asserts that this type is inhabited for E and for Omega. It does not assume any of this data.

Hypothesis and clause correspondence, read against the unchanged item statement:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Algebraic closure with its extended norm topology: `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. No `CompleteSpace Ω` appears.
  NormedAlgebra supplies the compatible extended norm, and the finite intermediate field
  has its induced normed topology.
- Finite intermediate E: `(E : IntermediateField ℚ_[ell] Ω)
  [FiniteDimensional ℚ_[ell] E]`.
- Both coefficient choices: the two conjuncts `Nonempty (Data ell E r)` and
  `Nonempty (Data ell Ω r)`; each uses exactly `continuousScalarRing F`, whose sections
  are `ULift.{u+1} C(S,F)`, with no local-constancy or finite-subextension condition.
- Every rank including zero: `(r : ℕ)`; lattice is the recorded
  `Profinite.LadicLattice.Lattice.{u} ell r`, the product p-adic topology, universe lift
  and multiplicative tag of the additive lattice. `toAdd.down` recovers its coordinates.
- Internal modules and actions: `CondensedBar.Modules`, `CondensedBar.Equivariant` and
  actual `CochainComplex` maps in that category, using the recorded `Mod` and
  `CondensedAction.ActionModule`, not topological modules or discrete representations.
- Size convention: site, F and lattice are in u, section coefficients in u+1. All S,T,
  further base changes and profinite parameter powers in the formulas range over
  `Profinite.{u}`. Choosing a common universe containing F and the site loses no case.
- K^n is the internal monomial direct sum: `PolynomialComplex.ι` is indexed by
  `PolynomialBar.Monomial r (n+1)`, with `isColimit` of its `Cofan`. These are coproducts
  in internal modules, so the statement does not incorrectly impose global finite support
  on every section. Monomials are the existing finitely supported exponent vectors.
- K action: `PolynomialComplex.translation` for every S,g,m,c, using
  `translatedMonomial`, which substitutes X_v minus the F-valued coordinate of g in
  every block v. Coefficients of this finite polynomial multiply the original c.
- K differential: `PolynomialComplex.differential` uses the finite integer polynomial
  `deletionPolynomial`: sum over `i : Fin (n+2)` with sign `(-1 : ℤ)^i.val`, and
  `i.succAbove` omits coordinate i. The actual differential is equivariant because it
  belongs to the action-category complex.
- Zero negative degrees: all complexes are represented in nonnegative degrees and read
  on integers by the existing `CondensedBar.extend` (i.e. `.extend embeddingUpNat`).
  For K,R first use their `.underlying` definitions. The evaluation map extends by the
  same standard `HomologicalComplex.extendMap`. Thus no negative-degree data is omitted
  or allowed to vary; the zero extension is fixed by the definition.
- Augmentation a: `Data.a` is an equivariant degree-zero map from the existing
  `PolynomialBar.trivialScalar`; `a_zero` identifies it with `K.ι 0 0` and `a_cocycle`
  says its following differential is zero. This is precisely a map A[0] -> K. The
  action category currently lacks a registered `HasZeroObject`, so specifying the
  degree-zero map and cocycle avoids adding a zero-object/Abelian hypothesis.
- P: the reused `PolynomialBar.Complex` in `Data.P`. Its differential is fixed by
  `faceVariable` and `differentialPolynomial`: face zero shifts all variable blocks
  (drops the first input), face n+1 keeps them (drops the last input), an interior
  face replaces adjacent inputs by their sum. Coefficient signs are `(-1)^i`.
- R_A^n: `FunctionComplex.model n` is the recorded `HomogeneousFunctions` for the
  trivial scalar action, with equivariant `term n`. Its `internalHom` identifies the
  associated section-module sheaf with the actual underived internal Hom from the
  recorded free module, rather than an arbitrary family of functions.
- R action: the recorded `HomogeneousFunctions.action`, applied to trivial scalars,
  is diagonal inverse translation on all arguments over all slices.
- R differential: `FunctionComplex.differential`, evaluated using `evaluateModel` and
  the canonical free generators, is alternating deletion on all T -> S and tuples.
- b: `Data.b`, `b_cocycle` and `b_constant` specify the constant augmentation by every
  restricted c. The cocycle describes the full map A[0] -> R.
- Equivariant internal linear cochain map e: `Data.e : K.cochain ⟶ R.cochain`.
- ea=b: `Data.augmentation : a ≫ e.f 0 = b`; because both augmentations are the stated
  degree-zero cocycles, this is exactly the augmented cochain equality.
- Full homogeneous formula: `Data.monomial`, on every n,m,S,c,T,f,x,t, is restricted
  c times the product of coordinate powers, with the canonical Z_ell -> Q_ell -> F.
  Each x is a tuple of continuous maps T -> L; no global-point-only replacement occurs.
- Fixed subcomplex convention: `FixedComplex.inclusion` is sectionwise injective;
  its `image` is exactly `FixedAll`, which quantifies over every further profinite
  base change and every section of the lattice there.
- Consecutive differences: `Data.phi` is a cochain iso from the actual P to fixedK,
  pinned on generators by `phi_monomial` and `differencePolynomial`.
- Invariant homogeneous-function identification: `Data.chi` is a cochain iso from
  fixedR to the actual `CondensedBar.cochains bar` of the trivial scalar module. Its
  `chi_prefix` says on every slice that it is evaluation on `prefixTuple g`.
  `prefixTuple` is the finite product of all g_j with j<i; in the multiplicative
  lattice this is exactly (0,g1,g1+g2,...). This formula also pins the inverse iso.
- Restriction of e to invariant submodules: `fixedEvaluation` and `fixed_square`
  identify it with the actual e after the two fixed-subcomplex inclusions.
- Induced map equals polynomial evaluation: `Data.rho` reuses the existing
  `PolynomialBar.Evaluation`, including its all-slice coefficient-monomial equation.
  `normalization : rho.map = phi.hom ≫ fixedEvaluation ≫ chi.hom` fixes the map, rather
  than asserting existence of an arbitrary comparison.
- n=0: P has no variables; differences are empty, prefixTuple has one identity/zero
  entry, rho's product is empty and equals one. a and b are precisely the given
  constant augmentations. K^0 still has its r homogeneous variables, as in the source.
- r=0: both exponent index types have no variables; the group is terminal and every
  term is A. The unnormalized differential is the alternating sum of identities,
  zero in even source degree and identity in odd source degree. Empty products are one.
- No higher acyclicity claim: the theorem has no injectivity, derived-invariants,
  quasi-isomorphism or completeness condition/conclusion. The imported parent theorem
  is never used as a hypothesis or chosen to define any data.

Dependency declarations used, with their recorded modules:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse`, its canonical MonObj and commutativity,
  via the landed bundle `Sheaf.CategoryTheory.ContinuousScalarRing` /
  `Profinite.CondensedAction.continuousScalarRing`.
- `Sheaf.Topology.LadicLattice`: `Profinite.LadicLattice.Lattice`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `trivial`,
  `forgetAction`, `FixedAll`, section modules and the actual equivariant category.
- `Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective`:
  `homogeneousHom`, `homogeneousEvaluate`, `HomogeneousFunctions`; the injectivity
  theorem in this module is not used or assumed.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `InternalFunctions`, `BarDiagram`,
  `cochains`, `power`, `tupleMap`, `sections`, `Modules`, `Equivariant` and `extend`.
- `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`: the real `MvPolynomial`, monomials,
  `rename`, `eval₂Hom`, finite coefficient supports and algebra maps.
- Existing helper definitions in `Sheaf.CategoryTheory.PolynomialDerivedBarComparison`:
  `PolynomialBar.Monomial`, `polynomialArrow`, `faceVariable`, `differentialPolynomial`,
  `Complex`, `trivialScalar`, `Evaluation`, newly registered by the definition node
  below. No declaration from that file is copied or replaced.
- `def-weil-size-convention` has no Lean definiendum; explicit universes implement it.

The statement-dependency signatures/docstrings were read in their actual files. The
original example CompactObject module is withdrawn and contains no declarations; its
node now records the existing Mathlib notion, so the active nearby module headers were
also followed. The current blueprint was read under `literature/blueprint/latest`;
paragraph (3) delegates the open-image input. The detailed node is explicitly an
agent-formulated sub-obligation; no external proof reference has been invented.

Searches made through msearch.py (full machine results are in the new nodes' searches):

- LeanFinder: homogeneous polynomial evaluation into internal continuous group cochains
  and prefix-sum normalization. It returns topological continuous cohomology and plain
  polynomial evaluation; neither gives the required internal condensed slice statement.
- Loogle: `"MvPolynomial", "eval"`; returns evaluation API, reused.
- Mathlib grep: homogeneous polynomial / bar / cochain combination; no match.
- LeanSearch and LeanFinder: internal homogeneous polynomial complex with diagonal
  translation, alternating deletion and monomial coproduct generators. Returned plain
  polynomial homogenization and ordinary representation bar complexes, not these data.
- LeanSearch and LeanFinder: polynomial bar complex internal monomial coproduct and
  normalized evaluation on every profinite slice. No Mathlib internal condensed model.
- Mathlib grep: `polynomialArrow|differentialPolynomial|HomogeneousPolynomialBar|homogeneous_polynomial_bar`;
  no match. Direct rg on WeilConjectures and Sheaf finds exactly the reused parent-file
  polynomial helpers; no homogeneous model or evaluation theorem. The requested node-id
  search on WeilConjectures returns no declaration.
- DAG grep on homogeneous/polynomial/bar notions and `PolynomialBar.Complex|Evaluation`
  finds only the parent theorem record for those existing helpers, no definition node.
  `tools/blueprint_refs.py search 'homogeneous polynomial'` gives unrelated C_r forms and
  P1 monomials; `'polynomial bar'` gives no blueprint node.

Edge cases checked before writing: empty profinite S/T (equations quantified over t
are vacuous in the correct way), n=0, rank zero, the degree-zero constant monomial,
negative degrees under canonical zero extension, and genuinely varying all-continuous
coefficients including noncomplete Omega. Interior face indexing agrees with the source
signs; no bound is put on degree or on local sheaf supports. There is no statement dispute
or correction. All original non-lean fields remain unchanged except stmt_deps gains the
new model definition.

Validation: both delivered Lean modules compiled cleanly with scompile.py, separately in
dependency order in its private overlay. The initial augmentation probe failed for the
missing action-category zero-object instance; the repaired degree-zero cocycle interface
compiles without adding any hypothesis. Only the final evaluation theorem has sorry.

## New nodes

`def-sfb-polynomial-bar-cochain-model` registers the already existing helper definitions
`PolynomialBar.Complex` and `Evaluation` and their finite polynomial machinery, using
`existing: true` with the exact parent-file declaration and no delivered Lean module.
Its statement describes the inhomogeneous coproduct cochain model, the trivial scalar
action and all-slice evaluation specification, without the parent's derived-isomorphism
conclusion. This is definition ownership, not a second definition or a dependence on
the parent's theorem. Its statement dependencies are exclusively definition nodes.
The searches above found the existing declarations but no definition node carrying them.

`def-sfb-homogeneous-polynomial-bar-model` supplies the missing homogeneous polynomial
and function complexes, fixed-subcomplex and compatible augmented-evaluation
specifications, with their exact deletion, translation, difference and prefix formulas.
Its own module has real data throughout: structures and finite substitutions, never a
choice from existence. The same searches found no existing homogeneous counterpart.
Both nodes cite the source place of this item's agent-formulated sub-obligation and
use only definition dependencies. They are cited by the item, the first through the second.

Import-cycle note: PolynomialDerivedBarComparison contains the existing definition
helpers and a downstream theorem whose DAG proof uses this item. This delivery reuses
the definitions from that published module but creates no DAG dependency on that theorem.
Under stages/2-statements.md §3(7), the maintainer must omit a future proof-only import
of this evaluation module into that parent module because it would close an import cycle.
The same applies if the later invariant-coordinates module imports these specification
helpers and would otherwise be added as a proof-only import here. Neither theorem has
been assumed in any definition. The invariant-coordinates proof dependency currently
has no recorded Lean module and therefore has no proof-only import to add here.

Blueprint ancestry note: `tools/blueprint_refs.py ancestor` currently returns None, even
though the item's stored blueprint.from names the intended direct-images ancestor.
The new records use the actual computed chain and None, as required by the preflight,
and retain a precise place naming latest paragraph (3). No existing blueprint metadata
was changed.

## Second reading by Q69

Independent reading by the maintainer review (cc second reader, 2026-10-24) of delivery
d4d01e07f34d. The author's earlier note here was a self-audit; this section replaces it.
Nothing in the Lean or the node records was changed.

Node clauses and the Lean that states them (`HomogeneousPolynomialBarModel.lean`, `Data`):

- ℓ prime, Ω algebraic closure with extended norm, finite E, F = E or Ω: theorem binders
  `[Fact ell.Prime]`, `[NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`,
  `[FiniteDimensional ℚ_[ell] E]`. The conclusion has two conjuncts, one for E and one for Ω.
  There is no `CompleteSpace`. These binders are the same as those of the landed parent
  `polynomial_derived_bar_comparison`. OK.
- A = C(-,F) with all continuous maps: `continuousScalarRing F`. L = ℤ_ℓ^r with r ≥ 0:
  `LadicLattice.Lattice.{u} ell r`. Coefficients are in u+1, the site and F in u. This is
  the parent's convention. OK.
- K^n is the internal coproduct on monomials in (n+1)r variables:
  `PolynomialComplex.ι`/`isColimit` over `Monomial r (n+1)`, in the equivariant category. OK.
- Action (g·f)(y) = f(y−g): `translation` uses `translatedMonomial`, which substitutes
  X_v − g_{v.2}. With `HomogeneousFunctions.action` (ev(g·c)(x) = g·ev(c)(g⁻¹x), J trivial)
  the two conventions agree, so an equivariant e with the `monomial` formula is consistent
  and `Data` is not empty for a sign reason. OK.
- δ is alternating deletion: `deletionPolynomial`, sum over i of (−1)^i times renaming
  through `i.succAbove`. OK.
- a: A[0] → K is the constant inclusion: `a_zero : a.val = K.ι 0 0` (constant monomial),
  with `a_cocycle`. OK.
- P with its inhomogeneous differential: `PolynomialBar.Complex`. I checked
  `faceVariable` face by face: face 0 shifts every block, face n+1 keeps every block, and
  an interior face i replaces x_i by x_i + x_{i+1}. The signs are (−1)^i. OK.
- R_A^n = Hom_A(A[L^{n+1}],A) with diagonal action and deletion differential:
  `FunctionComplex.model/term` uses the recorded `HomogeneousFunctions` (internal Hom +
  action). `differential` is pinned on every slice. OK.
- b is the constant augmentation: `b_constant`, `b_cocycle`. ea=b: `augmentation`. OK.
- e is A-linear, equivariant and a cochain map: `e : K.cochain ⟶ R.cochain` in `Equivariant`. OK.
- e^n(c y^m)(s,g) = c(s)∏(g_a)_i^{m_{a,i}} after every base change T→S, for all tuples
  in C(T,L): `monomial`, quantified over S, c, T, f, x and t. OK.
- φ(p)(y) = p(y_1−y_0, …): `phi` iso with `phi_monomial` via `differencePolynomial`
  (X_{a,i} ↦ X_{a+1,i} − X_{a,i}) onto `FixedComplex`. Its image is exactly `FixedAll`, so
  every base change and every section are covered. OK.
- Invariant identification by evaluating at (0,g_1,g_1+g_2,…): `chi` with `chi_prefix`
  and `prefixTuple`, the product over j<i in the multiplicative tag. This is consistent
  with the `BarDiagram.face` formulas (face 0 acts trivially). OK.
- The induced map P→U_A is polynomial evaluation: `rho : PolynomialBar.Evaluation` (pinned
  by its `monomial` field), with `normalization : rho.map = phi.hom ≫ fixedEvaluation ≫ chi.hom`.
  `fixedEvaluation` is pinned by `fixed_square` and the injective inclusion. OK.
- No acyclicity or completeness claim. None appears. OK.

Every field of `Data` is either a pinned specification structure or an equation, so
`Nonempty (Data …)` is the node's existence statement and not a weaker one.

Edge cases. For n = 0, `Monomial r 0` is a singleton and prefixTuple has the single entry 1.
For r = 0, every exponent type is empty and every product is 1. Negative degrees come from
the ℕ-indexed complexes, which is the zero extension. For empty S or T the equations
hold vacuously. Noncomplete Ω is allowed.

Records. The item's stmt_deps gains def-sfb-homogeneous-polynomial-bar-model, whose
module and declarations are real structures with docstrings. It cites
def-sfb-polynomial-bar-cochain-model, which is delivered in the commit: an `existing: true`
owner of the helper definitions in PolynomialDerivedBarComparison. This follows the
HomogeneousFunctions precedent and closes no DAG cycle. The future proof-only import into
the parent module is omitted under §3(7), as the worker listed. The lean.statement is
verbatim the file signature. The only `sorry` is the theorem's proof.

Searches: side-live dag/nodes and lean/Sheaf contain no HomogeneousPolynomialBar,
homogeneous-polynomial-bar-model or polynomial-bar-cochain-model, so no parallel copy
exists. The parent module is unchanged between the delivery base and side-live.
