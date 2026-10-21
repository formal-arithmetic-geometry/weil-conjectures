## Worker report

This repairs return L/H2 at immutable head `642ade15deb5`. The retained module
`Sheaf.CategoryTheory.PolynomialDerivedBarComparison` states
`Profinite.CondensedAction.PolynomialBar.polynomial_derived_bar_comparison`, with
`sorry` as its only theorem proof. The mathematical statement and its proof plan
are unchanged. The saved packet was first dry-run as requested and passed at
`a000b88b747`; the ownership defect still required the following concrete repair.

The polynomial-complex and canonical-arrow helpers remain recorded in
`lean.declarations`. A new definition node now owns the bundled coefficient ring;
its small module only packages the already recorded continuous-map fields. No object is extracted from a mere
unproved existence theorem. `Complex` and `Evaluation` are specifications of data
uniquely determined up to their coproduct identifications; the main theorem
asserts their existence as well as the comparison. In particular, the comparison
is never supplied as an unconstrained map or a bare `Nonempty` isomorphism.

Hypothesis and clause correspondence:

- A prime ell is `(ell : ℕ) [Fact ell.Prime]`.
- The algebraic closure with its extended norm is `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. No completeness instance is
  assumed; `NormedAlgebra` fixes the extended scalar norm.
- The finite intermediate extension is `(E : IntermediateField ℚ_[ell] Ω)
  [FiniteDimensional ℚ_[ell] E]`. Its subtype norm/topology is inherited from Ω.
- Both choices F=E and F=Ω appear as the two conjuncts `Comparison ell E r` and
  `Comparison ell Ω r`. The rank is every natural `(r : ℕ)`, including zero.
- `continuousScalarRing F` is the bundled ALL-continuous coefficient ring. Its
  sections are the universe lift of `C(S,F)`; no locally constant, completed, or
  finite-subextension replacement occurs.
- `Lattice ell r` is `Multiplicative (ULift (Fin r → ℤ_[ell]))`. Its topology is
  the lifted product of the canonical ell-adic-integer topologies. Multiplicative
  is only the additive-to-multiplicative notation tag needed by the action API;
  the formula recovers additive coordinates using `.toAdd.down`.
- `trivialScalar` uses the recorded trivial-inflation functor on `Mod.regular A.X`.
- Internal modules are the recorded `CondensedBar.Modules`, hence Mathlib `Mod`
  on abelian sheaves over `coherentTopology Profinite`. `Comparison` asserts the
  action abelian/Grothendieck structures rather than adding them as hypotheses.
  It takes the standard `HasDerivedCategory` localizations in universe `u+2`.
  The site is `Profinite.{u}`, the coefficients are in `AddCommGrpCat.{u+1}`;
  Ω and E are in Type u, and the lattice is lifted to Type u. This is a common
  universe bound containing every profinite parameter set under consideration.
- `Monomial r n = (Fin n × Fin r) →₀ ℕ` indexes precisely the nr-variable
  monomials. `Complex.ι` and `Complex.isColimit` specify the actual coproduct of
  regular modules in each degree, rather than a product or a sectionwise direct
  sum wrongly assumed to be a sheaf. This permits locally finite polynomials.
- `faceVariable r n i` sends variable (a,j) to the appropriate shifted variable,
  or to `X(a,j)+X(a+1,j)` at the merged block. Face zero shifts all blocks;
  face n+1 shifts none. `differentialPolynomial` sums these substitutions with
  signs `(-1)^i`. `Complex.differential` fixes the cochain differential on each
  generator by the finite integer coefficient matrix `polynomialArrow`.
- `Complex.cochain` is nonnegative. `HomologicalComplex.extendMap` along
  `ComplexShape.embeddingUpNat` extends the objects and comparison by zero in
  negative degrees before applying the ordinary integer-indexed localization.
- The underived internal Hom complex is the dependency's `cochains M.bar`, with
  its recorded `bar.term` identification and `M.functions.internalHom`.
- `Evaluation.map` is a cochain map into that complex. `Evaluation.monomial`
  fixes its value at every profinite S, every coefficient c, every further base
  change T→S, every continuous lattice n-tuple g, and every t∈T. The right side
  is exactly c(f(t)) times the product of the embedded lattice coordinates to
  the powers m(a,i). Thus the internal map is the actual polynomial evaluation.
- `Comparison` supplies a compatible normalized derived bar model and quantifies
  over every such model and every equivariant `InjectiveResolution` of A. There
  is a canonical chain arrow eta whose `TotalComponents` are evaluation followed
  by `(cochains M.bar).map (I.ι.f 0)` and the (n,0) coprojection into
  `totalCochains M.bar`. The total is exactly the existing finite-diagonal
  compatible nonnegative derived-Hom bar model; no separate total is invented.
- The conclusion is `IsIso (DerivedCategory.Q.map (extendMap eta ...))`, for the
  specified arrow, in the ordinary derived category. It is not merely a family
  of cohomology isomorphisms. The source and target are explicitly fixed by the
  polynomial model and derived bar complex. It makes no individual underived
  internal-Hom term acyclic and adds no completion hypothesis.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`,
  `continuousMapRingObjOfUniverse`, its monoid structure and commutativity.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, and `trivial`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `def-weil-size-convention` is the recorded metatheoretic universe convention;
  its Lean record has no declaration and requires explicit universes here.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `monomial`,
  `coeff`, `support`, `eval₂Hom`; the recorded universal-property declarations
  `aeval` and `algHom_ext` were also read, and are not redefined.
- `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`:
  `CategoryTheory.CondensedBar.condensed_derived_invariant_bar`, proof import.
- The already landed `def-sfb-condensed-equivariant-bar-data` is added to
  stmt_deps for `InternalFunctions`, `BarDiagram`, `Model`, `cochains`,
  `doubleComplex`, `totalCochains`, `extend`, and `ActionAbelian`.
- The new `def-sfb-bundled-continuous-scalar-ring` is added to stmt_deps for
  `Sheaf.CategoryTheory.ContinuousScalarRing` and
  `Profinite.CondensedAction.continuousScalarRing`. The former added theorem
  dependency `lem-sfb-prime-to-ell-condensed-acyclicity` and its module import
  are removed. No acyclicity theorem is assumed or publicly imported.
- Additional Mathlib helper: `Homeomorph.ulift.symm.totallyDisconnectedSpace`
  transports the lattice property; `Ultra.TotallySeparated` gives it for
  ell-adic integers. The instance is a concrete application of existing facts.

The proof docstring reproduces all seven proof steps and names every proof
obligation. Only the derived-invariant-bar proof dependency currently has a
Lean record; its module is imported without public. The other four proof
nodes have no usable record at this reading, and their future proof imports
remain the maintainer's bookkeeping when those declarations land. They are
not needed to type this theorem and are not re-stated.

Edge cases checked by reading the finite formulas:

- n=0: there are no variables; the two substitutions are the same coefficient,
  with signs +1 and -1, so d^0=0. Evaluation is c and uses an empty product.
- r=0: every monomial set has exactly the zero exponent vector. The lattice is
  trivial. The polynomial complex is the unnormalized constant bar complex;
  differentials alternate 0 and identity, not all zero. The inserted-zero
  contraction in the source proof applies unchanged.
- n=1: the substitutions are f(x2), f(x1+x2), f(x1), with signs +,-,+.
- n=2: the face variables give exactly the two adjacent-block additions and
  the endpoint deletions, with signs +,-,+,-.
- The coproduct condition works on empty profinite test objects and locally
  finite sheaf sections. Generalized evaluation quantifies over every test
  object and every base change, so no global polynomial representability of
  sections is assumed.
- E=Q_ell and either coefficient-field choice are retained. No convergence,
  completeness, or cohomological acyclicity of individual underived terms is
  built into the statement. No STATEMENT-DISPUTED fault was found beyond the
  source's explicitly documented WANTED analytic reference.

Searches retained from the original saved packet (2026-10-21 UTC):

- msearch.py leanfinder: `Polynomial evaluation compares polynomial cochains on
  a p adic lattice to the derived internal condensed bar complex`: eight hits,
  including BDeRhamPlus and adic completion evaluation; no matching comparison.
- msearch.py loogle: `"Condensed", "Hom"`: twelve hits, condensed morphism
  extensionality and naturality; no matching comparison.
- msearch.py grep: `polynomial.*(cochain|bar|condensed)|(cochain|bar|condensed).*polynomial`:
  zero Mathlib hits.
- msearch.py leansearch: `Polynomial additive bar complex with monomial direct
  sums and normalized evaluation into condensed derived internal Hom`: eight
  hits (polynomial additive extensionality, eval and coefficient maps, additive
  homological functors); no matching construction or statement.
- rg in WeilConjectures and Sheaf with the same expression: unrelated Popescu
  fibre variables and Cech monomial cochains; none states this item. Searching
  the exact item id in upstream finds no existing declaration.
- rg in dag/nodes/sec-six-functors-basics found the existing rational-polynomial
  contraction node and its citers, but no Lean module or reusable polynomial
  bar construction. No duplicate node was created.
- tools/blueprint_refs.py search `polynomial.*bar|bar.*polynomial`: zero
  blueprint nodes. Ancestor lookup reports the inherited null ancestor;
  there is no blueprint-unit statement correction in this delivery.
- The source paragraph (3) was read in the main-20261015 blueprint: it delegates
  open direct image to open-coefficients; the item's seven-step analytic
  reduction honestly remains agent-formulated, as its source record states.

## Repair of return L/H2

The coefficient bundle had no definition-node owner and was reached through the
unrelated theorem node `lem-sfb-prime-to-ell-condensed-acyclicity`. The return
explicitly allows either an existing-definition binding or a new definition
node and module for this bundle. This packet takes the second option:
`def-sfb-bundled-continuous-scalar-ring`, module
`Sheaf.CategoryTheory.ContinuousScalarRing`, declaration
`Profinite.CondensedAction.continuousScalarRing`.

Its fields are exactly `continuousMapRingObjOfUniverse.{u,u} F`,
`continuousMapRingObjOfUniverseMonObj F`, and
`isCommMonObj_continuousMapRingObjOfUniverse F`. Thus no sheaf, multiplication,
or commutativity construction is copied. These are precisely the constructor
fields of the old unowned helper, with the same universes. The consumer now
publicly imports only this definition module for the bundle and has no import
of `PrimeToEllCondensedAcyclicity`. The theorem node is absent from stmt_deps.
Explicit Mathlib imports restore `IsAlgClosure` and normed-algebra interfaces
previously obtained transitively from that removed module.

The compiler confirmed that simply making the old import private cannot support
a public signature using `scalarRing`; it reports the identifier as privately
imported. A transparent alias has the same visibility problem. The final small
bundle module removes that import entirely and uses the existing fields directly,
as permitted by the return. No extra theorem, assumption, or object choice was
introduced. The advisory concerning `Nonempty Model` needs no statement change:
that conjunct supplies existence before the universal quantification over models.

## New nodes

`def-sfb-bundled-continuous-scalar-ring` owns the canonical bundling of the
existing all-continuous sheaf, its monoid structure and commutativity into
`CategoryTheory.CondensedBar.Ring`. The source is the final ring-object clause
of the main-20261015 continuous-map condensed-ring definition. The statement
cites exactly `def-sfb-continuous-map-condensed-ring` for these fields and
`def-sfb-condensed-equivariant-bar-data` for the target bundle. The universe is
`F : Type u`, site `Profinite.{u}`, coefficients `AddCommGrpCat.{u+1}`.
The constructor also handles the zero commutative ring and the empty profinite
set; it adds no field, nontriviality, norm, or completeness hypothesis.

Fresh searches for this node: LeanSearch for "Bundle the condensed ring of all
continuous maps from profinite sets into a topological commutative ring" and
LeanFinder for "Condensed commutative ring of continuous functions into a
topological commutative ring" each returned eight hits on continuous functions,
pointwise ring structures, and condensed modules, with no matching bundle.
Mathlib grep `scalarRing|continuousMapRingObjOfUniverse|continuousMapRingSheafOfUniverse`
returned ten unrelated scalar-ring-section/tactic hits. Local source grep found
the three existing continuous-map fields and the unowned `scalarRing` helper;
a DAG scan found no definition node owning that helper. `blueprint_refs.py search`
found no bundled scalar-ring node, and ancestor lookup retains the item's null
ancestor. Exact outputs and queries are recorded in the new node's
`mathlib_searches`. The new module is only the explicit bundle authorized by
L/H2; no underlying mathematical construction is repeated.

## Second reading by NA

Self-check in this dispatcher-started session; no other agents were started.
The maintainer's independent review remains the independent reading. I compared
the saved packet with the current read-clone item: only `lean` and the authorized
added stmt_deps differ. I read the current server source of
`PrimeToEllCondensedAcyclicity` with `scompile.py --source`; its scalar bundle has
exactly the same three fields as the new small module. All coefficient-ring uses
in the comparison now use `continuousScalarRing`, so the hypothesis-and-clause
mapping above is retained verbatim. The theorem signature still matches its Lean
record, and its only postponed theorem remains the comparison itself.

Validation: only scompile.py is used, compiling both delivered modules separately
in dependency order. Final compile and delivery dry run are recorded below.

Final scompile.py run: both actual library modules compiled cleanly, separately
in dependency order (`ContinuousScalarRing`: 3.1 s;
`PolynomialDerivedBarComparison`: 10.8 s), with no errors or unexpected warnings.
Both node signatures match their source verbatim, both files meet the 100-character
line limit, the item differs from the read-clone node only in `lean` and authorized
`stmt_deps`, and the unrelated theorem dependency/import are absent.
The repaired packet passed the server preflight and per-file compile:
`OK (dry run): commit 82a4074c875 passes the preflight and compiles; nothing pushed`.
