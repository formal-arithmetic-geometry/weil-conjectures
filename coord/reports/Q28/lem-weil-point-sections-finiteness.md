## Worker report

The module `Sheaf.Paper.PointSectionsFiniteness` states all three clauses of
`lem-weil-point-sections-finiteness` in `WeilConjectures.point_sections_finiteness`.
The sole postponed theorem is this theorem, with proof `sorry`; its docstring gives
all six proof steps from the node. Its eight supporting declarations contain real
data: constant scalar maps, evaluation functors, integral-to-field inclusion and
additivity instances inherited from the original functors or adjunction.

The current shared node has no Lean record. The previous attempt's claim that the
assignment was superseded is not evidence that this stage-2 statement exists:
`status: split` and the PASS split review concern its stage-1 proof decomposition.
The retained sandbox contained no node, Lean file or report, only dispatcher markers.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The fixed global datum is `(D : FiniteFieldDatum.{u})`, giving exactly p, a, q,
  the finite field and its algebraic closure, including their structure maps.
- The coefficient prime is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its valuation ring and the already chosen uniformizer
  are `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`.
- The positive exponent is `(n : ℕ) (hn : 1 ≤ n)`; the ring A_(E,n) is exactly
  `Padic.coefficientExtensionRing l E n`, not an arbitrary finite ring.
- The geometric point scheme is `Spec (.of D.k)` throughout. The site is the recorded
  small `ProEt.topology`, and evaluation is at `op (ProEt.mk (𝟙 (Spec (.of D.k))))`.
- Sections are `pointModuleSections` from the exact-sections dependency, followed
  by Mathlib `ModuleCat.restrictScalars` along the canonical coefficient homomorphism.
  For finite coefficients this map is the sheafification unit at the final object.
  For integral coefficients it is that unit followed by the final-object component
  of the recorded `integralConstantToCompletion`. Thus it sends an integral scalar
  to all of its compatible constant reductions and then their actual inverse-limit
  section, as required by the node's canonical map O_E → Γ(completed O_E).
- Clause 1: for EVERY cochain complex C in the finite coefficient sheaf module
  category, `intrinsicFiniteTorsionConstructible ... (DerivedCategory.Q.obj C)` implies
  `DerivedCategory.pointFiniteCohomology` of its termwise section complex, localized
  by `DerivedCategory.Q`. This predicate asserts finite cohomological support AND
  finiteness of the underlying set of every cohomology module.
- Clause 2: for EVERY cochain complex C over the completed coefficient sheaf,
  `sfIntegralConstructible ... (DerivedCategory.Q.obj C)` implies
  `DerivedCategory.pointFgComplete` of its termwise integral sections, for
  `Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}`.
  This includes all three required conditions: bounded cohomology, finite generation
  in every degree, and derived completeness for the uniformizer ideal.
- Clause 3 is the second conclusion of that same integral universal clause:
  `DerivedCategory.pointFiniteDimensional (ULift E)` of termwise
  `ModuleCat.extendScalars (pointIntegralToField l E)` applied to its integral sections.
  The scalar map is the original subring inclusion O_E ↪ E transported through ULift.
  This is ordinary termwise tensor with E, exactly as the node requests.

The assertion is written for every COMPLEX REPRESENTATIVE, without a bounded-termwise,
K-flat, injective or finite-term condition. This does not specialize the derived
statement: DerivedCategory is the localization of these complexes and Q is essentially
surjective. The recorded exactness theorem makes section complexes invariant under
quasi-isomorphisms; flatness of the coefficient fraction field does the same for
rationalization. Thus every derived object and every representative is covered.
Writing the localized termwise formulas avoids requiring consumers to install extra
exactness typeclass hypotheses merely to name `mapDerivedCategory`.

Coefficient `ULift.{u+1,u}` is the existing size convention for small pro-etale
module sheaves. It transports the rings by `ULift.ringEquiv`; these are the original
finite quotient, valuation ring, uniformizer ideal and field, with their original
scalar maps. No equality of distinct object and morphism universes is imposed.

Dependency declarations read in full and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `lem-weil-point-proetale-sections-exact`: `Sheaf.Paper.PointProEtaleSectionsExact`, `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-point-finite-cohomology-complexes`: `Sheaf.Paper.PointFiniteCohomologyComplexes`, `DerivedCategory.pointFiniteCohomology`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralCoefficientGerm`, `WeilConjectures.integralConstantToCompletion`.
- `def-weil-point-fg-complete-complexes`: `Sheaf.Paper.PointFgCompleteComplexes`, `DerivedCategory.pointFgComplete`.
- `def-weil-point-fd-complexes`: `Sheaf.Paper.PointFdComplexes`, `DerivedCategory.pointFiniteDimensional`.

The completed-coefficient dependency publicly imports its unchanged completion, so
`completedIntegralCoefficientSheafUnrestricted` and
`completedIntegralCommRingSheafUnrestricted` retain precisely the existing limit data.
`scalarReductionSource` is the source used by `sfIntegralConstructible`, not a private
integral derived category. Stated proof dependencies are imported without `public`;
`lem-weil-derived-complete-module-finite` has no recorded module and is not imported.

Source: read the original blueprint `def-weil-finite-coefficient-point.md`, order 1509,
in the installed literature copy. It states the three point evaluation equivalences
and the target bounded finite / derived-complete finitely-generated / finite-dimensional
categories. This node is their landing assertion, not their essential-surjectivity or
full-faithfulness assertion; none of those extra conclusions has been added.

Edge cases checked before writing: zero complexes are allowed, finite cohomological
support may be empty, arbitrary positive level including n=1 is covered, and arbitrary
negative and positive cohomology degrees are present through ℤ. There is no termwise
boundedness restriction and no demand for finite integral modules (only finite
generation). Completeness is retained, not dropped from the integral conclusion.
The n=0 zero coefficient ring is outside the node's expressly positive range, rather
than silently being substituted for the level. The finite-dimensional scalar-extension
conclusion uses the field E, never a quotient or an arbitrary field extension.

Searches for existing declarations:

- `msearch.py leanfinder`: “global sections constructible proetale point finite
  cohomology” returned eight unrelated algebraic-geometry statements (limits, etale
  locus, finite morphism fibers); no matching point finiteness statement.
- `msearch.py loogle`: “Module.Finite, FiniteDimensional” returned general integral
  closure, trace and lattice lemmas; none concerns constructible pro-etale sections.
- `msearch.py grep`: “constructible|derivedComplete” in Mathlib/AlgebraicGeometry/Sites
  returned zero hits.
- `rg` in the upstream WeilConjectures source for the item id returned no match.
  Searches for the target predicate names, point sections and sections finiteness
  found no statement of these three clauses.
- `rg` in `lean/Sheaf` found the three target predicates and exact-sections dependency,
  plus scalar extension and cohomology extraction modules. They supply interfaces used
  here but do not state this item's finiteness conclusion. Searches for constant
  scalar maps found the stalk germ, which targets a neighbourhood colimit rather than
  final-object sections; therefore it is not substituted for sections.

No statement correction, new node, dependency repair or STATEMENT-DISPUTED flag is needed.
The item's existing fields are unchanged apart from `lean`.

Validation: the final module passed the prescribed `scompile.py Q28
lem-weil-point-sections-finiteness .../PointSectionsFiniteness.lean` with exit 0 and
no warnings or errors. The actual-path check took 8.5 s. The delivery parser confirms
all nine declared names and that `lean.statement` matches the file verbatim.
The required `deliver2.py --no-push` checks compilation and preflight against the
current server base. The independent second reading is left to the next worker.


## Second reading by Q28

I independently read the item node, its entire Lean module, all eight statement
nodes and their recorded source declarations, and the actual blueprint source
`sec-smooth-purity/sk-def-sf-admissible/def-weil-finite-coefficient-point.md`
(order 1509), together with its unit `_section.md`. The source is installed under
`weil-launcher-nt/literature`, rather than the shared checkout's literature folder.
This node asserts the landing of sections in the three target categories, not the
full evaluation equivalences of its parent. The module states exactly that landing.
No statement correction or citer audit is needed. There are no new nodes or
repaired dependency modules in this delivery.

The node's complete object/hypothesis/conclusion checklist, matched independently:

1. The global datum consists of p, positive a, q=p^a, the finite field k_0 and its
   fixed algebraic closure k. Lean: `(D : FiniteFieldDatum.{u})`. I opened the
   structure in `Sheaf.Paper.FiniteFieldFiber`: its fields impose exactly these
   conditions, and its field/algebra/algebraic-closure fields are instances. Thus
   `D.k` really is the algebraically closed field in the node. Verdict: exact.
2. The coefficient prime is prime and distinct from p. Lean: `(l : ℕ)
   [Fact l.Prime] (_hl : l ≠ D.p)`. No invertibility, characteristic-zero geometry,
   or extra residue-characteristic assumption is added. Verdict: exact.
3. E is a finite extension of Q_l. Lean: `(E : Type u) [Field E]
   [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. This is finiteness as a field
   extension. The coefficient-extension module defines its actual valuation subring,
   chosen uniformizer and quotient by the nth power of the principal uniformizer
   ideal. It does not substitute a general finite ring. Verdict: exact.
4. The level is positive: `(n : ℕ) (hn : 1 ≤ n)`, with coefficient ring
   `Padic.coefficientExtensionRing l E n`. Verdict: exact, including n=1.
5. The geometric scheme and final object are s=Spec k and id_s on its small
   pro-etale site. Lean consistently uses `Spec (.of D.k)` and evaluation at
   `op (ProEt.mk (𝟙 (Spec (.of k))))`. I opened `pointModuleSections`: it is
   `SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _` at exactly this
   object. Its exactness theorem quantifies over every commutative ring sheaf,
   so it covers both constant quotients and the nonconstant completed ring.
   Verdict: exact; no big-site or geometric-stalk functor is substituted.
6. Clause 1 introduces every K in the bounded constructible finite-level category
   and concludes bounded cohomology whose underlying modules are finite sets.
   Lean quantifies over every cochain complex C in the recorded constant-ring
   module category, assumes `intrinsicFiniteTorsionConstructible ... (Q.obj C)`,
   and concludes `pointFiniteCohomology ... (Q.obj (...sections... C))`.
   I read the intrinsic predicate: finite support and constructible cohomology
   sheaves. I read the target predicate: a finite support witness and `Finite`
   for every cohomology object. It means set-finiteness, not merely finite
   generation. `pointConstantSectionMap` is the sheafification unit component,
   and `pointFiniteSections` restricts evaluation scalars along that actual map.
   Verdict: exact objects, action, hypothesis and both conclusion clauses.
7. Clause 2 introduces every integral constructible K over the completed sheaf,
   using the canonical O_E action on sections, and concludes bounded cohomology,
   finite generation and derived completeness for (uniformizer).
   Lean's source is `scalarReductionSource.{u,u} l E (Spec (.of D.k))` and its
   hypothesis is `sfIntegralConstructible ... (Q.obj C)`. I opened both: these
   are modules over the unchanged inverse-limit coefficient sheaf, and the
   predicate is derived completeness plus every positive constructible reduction
   and one common cohomological interval. `pointIntegralSectionMap` composes
   the constant-sheaf unit with `integralConstantToCompletion` at the final object.
   I opened that map's cone and limit lift: its components are exactly the quotient
   maps O_E -> A_(E,n+1), so this is the specified canonical action, not a chosen
   arbitrary homomorphism. `pointIntegralSections` retains it by restriction of
   scalars. The conclusion uses `pointFgComplete` with
   `Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}`.
   I read the predicate: finite support, `Module.Finite` in every degree and
   `DerivedCategory.IsDerivedComplete` for that ideal. Verdict: all three
   conditions and the canonical action are present, with no added hypothesis.
8. Clause 3 uses the SAME integral K and states bounded finite-dimensional
   rational cohomology. Lean pairs this conclusion with clause 2 under the same
   integral universal quantifier. `pointIntegralToField` is precisely the
   original valuation-subring inclusion, conjugated by `ULift.ringEquiv`.
   Mathlib `ModuleCat.extendScalars` tensors with E along this map, and
   `mapHomologicalComplex (.up ℤ)` applies it termwise before localization.
   The target `pointFiniteDimensional` is finite support and finite-dimensional
   cohomology in every degree, as checked in its source. Verdict: exact.

The representative formulation in clauses 1-3 does not add a condition on K:
DerivedCategory is the localization of all the indicated cochain complexes and
Q is essentially surjective. No representative is required bounded, injective,
K-flat or termwise finite. Exact final-object evaluation, followed by exact
restriction of scalars, preserves quasi-isomorphisms; fraction-field flatness
makes rationalization preserve them too. The target predicates are invariant
under isomorphism since they are stated through homology and derived completeness.
Consequently the formulas cover every derived object and every representative.
The positive level n is fixed before the two universal clauses, just as in the
node; the integral and rational clauses introduce no dependency on that level.

Edge cases: zero complexes and empty cohomological support are included; the
finite support finset may be empty, and the zero integral object admits a common
reduction interval. All negative and positive degrees are allowed by ℤ. n=0 is
expressly excluded by the source and the node, and is not a lost case. The scheme
is the spectrum of a field, so the empty scheme is not in this node's hypotheses;
no extra nonemptiness assumption on a varying scheme is introduced. Every prime
l distinct from D.p and every finite extension E are allowed. One arbitrary
universe u is the recorded common size of these field/scheme data; coefficients
are transported to u+1 by ULift, as required by the already recorded small-site
categories (object universe u+1, morphism universe u). No equality of those two
site universes or additional smallness binder is imposed. The signature binds
all variables and the sole universe explicitly, with autoImplicit disabled.

Independent H4 searches (different queries from the author's):

- LeanFinder: "bounded finite cohomology of global sections on a pro etale
  geometric point" returned eight unrelated affine-limit, cotangent, condensed
  sheaf and sheaf-cohomology construction hits; no matching assertion.
- Loogle: "SheafOfModules, Module.Finite" returned zero hits.
- LeanSearch: "Sections of a constructible proetale complex on an algebraically
  closed field have bounded finite cohomology" returned general bounded-derived
  representatives, proper structure-sheaf finiteness and condensed constructions.
  These neither assert pro-etale point sections finiteness nor supply the three
  stated coefficient conclusions. No exact match.
- `msearch.py grep` for "constructible.*sections|sections.*constructible|derived.*complete"
  in Mathlib/AlgebraicGeometry/Sites returned zero hits. Direct rg in Mathlib's
  Sites and Condensed files found site/cohomology/discrete-condensed constructions,
  not this theorem. The condensed site differs from the recorded small scheme site.
- Direct rg in upstream WeilConjectures and project lean/Sheaf for the new names,
  point/global sections, finite cohomology and the three target predicates found
  no existing theorem with this signature. I opened upstream
  `AlgebraicGeometry/Sites/PointCohomology.lean` (etale exact sections/constant
  sheaves) and `EtaleCohomology/PoincareDuality/PointPerfect.lean` (perfectness
  under finite Tor-amplitude assumptions): neither is this arbitrary constructible
  pro-etale assertion. The project's predicate, scalar-extension, section-exactness
  and cohomology-extraction modules supply the dependencies but not this conclusion.
- Helper checks: `ProEtaleConstantSheafStalk` takes a germ in a neighbourhood
  colimit, and `ProEtaleConstantRingMap` constructs the inverse-image coefficient
  comparison along a morphism. I opened both; neither is the final-object scalar
  map defined here. `FieldComplexScalarExtension` only extends scalars between
  two fields, whereas O_E here is the valuation ring. No duplicated notion found.
  The full-name search in `dag/lean_names_upstream.json` also found no collision.

H5/H6/H8/H9 checks: all helper definitions have concrete data; the three additivity
instances use existing additivity/adjunction constructions. The only theorem
has proof `by sorry`. Module and all nine declaration docstrings give their source
and the correct blueprint id. Its theorem docstring follows all six proof steps:
finite quotient/stalk origin, completeness of the coefficient DVR, integral Roos
bounds/completeness, principal-reduction cone, complete-module finite generation,
and flat rationalization. I also read the relevant source passages in Stacks
`more-algebra.tex` (091P, 091W, 09BA) and `sites-modules.tex` (093M); they introduce
no additional geometric hypothesis omitted by the node or Lean.

Mismatch found and repaired: the source module did not explicitly import four
already stated proof-dependency modules, relying on transitive imports instead.
I added proof-only imports for
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`,
`Mathlib.RingTheory.Flat.Basic` and `Mathlib.RingTheory.Flat.Localization`.
These supply the recorded long exact sequence, absolute-value/completeness,
flat-tensor and localization-flatness dependencies. No theorem signature, helper
construction, node statement or dependency list was changed. The unstated
`lem-weil-derived-complete-module-finite` has no module to import yet.


Second-reader validation: the final module, including the four added imports,
passed `scompile.py Q28 lem-weil-point-sections-finiteness` with exit 0 and no
warnings or errors, in both sandbox and actual-module-path checks. The single-file
60-second limit was unchanged. A direct byte-for-byte comparison confirms the
node's `lean.statement` equals the theorem signature in the file. All nine declared
names are listed in `lean.declarations`; every Lean line is at most 100 characters.

The required `deliver2.py Q28 lem-weil-point-sections-finiteness --no-push`
printed OK: the packaged delivery compiles and passes the current server preflight.
