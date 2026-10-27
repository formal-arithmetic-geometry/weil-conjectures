## Worker report

The module `Sheaf.RingTheory.PolynomialSquareBarNaturality` states
`Algebra.PolynomialSquareBar.data_nonempty`. Its `Data` proposition specifies all
constructions simultaneously, with polynomial, tensor, differential and derived
comparison normalization. Definitions contain actual data; the only postponed
proof is the owning node's existence theorem. The node statement is unchanged.

Hypotheses and clauses, in order:

- Universes U in V: `u` and `max (u + 1) v`. Small rings are
  `Arrow CommRingCat.{u}`. The recorded `PolynomialHomology.Category.{u,v}`
  includes every U-small polynomial augmented algebra, with no surjectivity
  restriction, and has all morphisms in the containing universe.
- A commutative ring square: `q : f ⟶ g` in the arrow category. Its components
  are alpha=`q.left`, beta=`q.right`; commutativity is `Arrow.w q`.
- The exact standard terms, faces, degeneracies and augmentations:
  `StandardData.standard_spec : IsStandard (augmented (standard f))` uses the existing
  `standardTerm`, `standardBase`, `standardFace`, `standardDegeneracy`, and
  `standardAugmentation`. These are the iterated free polynomial construction,
  not an arbitrary polynomial replacement. `standard_trivial` gives the required
  endpoint resolution property.
- Recursive t maps: `standardMap` is an `AugmentedMap`, hence includes the
  semilinearity and augmentation equations and a natural transformation of
  simplicial rings. `standard_formula` identifies every component with the
  existing `CotangentResolution.standardSquareMap`, whose degree zero uses beta
  on variable labels and whose successor uses the preceding map. Its coefficient
  map is alpha. `standard_id` and `standard_comp` are strict equalities.
- The categories D are the dependency's actual full presentation categories.
  `site` only transports their size lift and opposite encoding to the previously
  recorded full-site coefficient functor.
- F(T) and its maps: the parameter `F f : CotangentSheaf.SiteCoefficients f.hom`
  is the existing interface with term isomorphisms to
  `ModuleCat.extendScalars epsilon (CommRingCat.KaehlerDifferential base)`.
  Its `formula` gives dx tensor b -> d(vx) tensor b for every arrow.
  `coefficients` is its actual universe transport, not another differential
  construction. `generator` names the actual transported pure tensor.
- The functor u: `baseChange`, `tensorIso`, `tensor_base`, `tensor_aug`, and
  `tensor_map` specify its objects as the actual tensor algebras and specify
  augmentation and all arrows on pure tensors. `tensorRing` and `tensorElement`
  install only the algebra structures supplied by the given ring maps.
  The symmetric order A' tensor_A T is used. Thus the augmentation formula is
  beta(epsilon(x))*f'(a'), exactly the statement's formula. The image objects are
  polynomial by their membership in the full category; combined with `tensorIso`
  this also gives polynomial base change A[E] tensor_A A' = A'[E]. The existing
  `MvPolynomial.algebraTensorAlgEquiv` is imported for its canonical explicit
  polynomial-coordinate equivalence, not replaced by a second construction.
- Theta: `theta` is a natural transformation into restriction along the actual
  ULift of beta; `theta_formula` specifies dx tensor b ->
  d(x tensor 1) tensor beta(b) on every generator.
- Arbitrary augmented polynomial Q, Q', h: these are quantified in `factor`,
  `factor_formula`, `chainMap`, `chain_formula`, and `naturality`. They use the
  dependency's simplicial presentation categories. `augmented` retains their
  underlying rings, base and augmentation, so `AugmentedMap` is precisely the
  required alpha-semilinear augmented simplicial map.
- The map k: `factor` is simplicial and augmented because its components are
  arrows in the presentation category. `factor_formula` states k(a' tensor q)
  = h(q)*a'. No assumption that uQ is a resolution appears.
- K(Q): `evaluationComplex (Q ⋙ opOp _)` is the existing alternating-face complex
  extended from chain degree n to cochain degree -n and zero positive terms.
  `complexGenerator` supplies its actual differential-tensor coordinates.
  `chainMap` is a morphism of these complexes into degreewise restriction;
  `chain_formula` is the stated differential formula. `chain_id` and `chain_comp`
  give strict functoriality of the standard maps in every degree, including the
  zero positive degrees.
- The canonical a_Q: `D f : PolynomialHomology.ComputationData f.hom bar C`
  is the recorded presentation-homology interface, whose `normalization` fixes
  its comparisons to C's projective-resolution roof, rather than arbitrary
  isomorphisms. D and F are specified-model parameters, not extra mathematical
  hypotheses: the assertion holds for every supplied model with these exact
  normalization/formula fields. It neither chooses D/F from sorry theorems nor
  asserts naturality for unnormalized arbitrary maps.
- The equality in D(B): The concluding equation of `Data` is Q(chainMap) followed by the localization
  comparison for restriction and the restricted a_Q', equal to a_Q followed by
  the dependency's `derivedMap bar (baseChange q).op ... (theta q)`.
  This is exactly a_Q' K(h)=H(u,theta) a_Q in composition order.
- Bar-generator formula: `derivedMap` is the dependency's canonical actual bar
  map transported by its model isomorphisms; `Computation.forwardMap` fixes it
  on first-vertex bar generators as (u(string), theta(x)). The statement reuses
  this construction directly, so no unspecified H map enters the equality.
- The standard case follows by taking Q=`standard f`, Q'=`standard g`, and
  h=`standardMap q`, with endpoint hypotheses provided by `standard_trivial`.
  Neither flatness nor injectivity of alpha/beta nor a resolution property for
  uQ is present anywhere.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, realized by the explicit
  universes above; its lean record intentionally has no declaration.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
  accessed through the recorded `CommRingCat.KaehlerDifferential` tensor terms.
- `Sheaf.AlgebraicTopology.TrivialKanFibration`:
  `SSet.Enhanced.trivialKanFibration`, read with `scompile.py --source`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.RingTheory.PolynomialPresentationHomology`:
  `Category`, `diagram`, `rings`, `augmentation`, `ComputationData`, and
  its `comparison`/`normalization` fields, read from current server source.
- Proof dependency `Sheaf.CategoryTheory.SimplicialDerivedColimitComputation`:
  `evaluationComplex`, `evaluationTerm`, `Computation`, `derivedMap`, and its
  normalized comparison, naturality and first-vertex generator fields.
- Existing construction helpers reused from
  `Sheaf.RingTheory.CotangentResolutionCoherence` (standard recursive maps,
  `IsStandard`, `Augmentation`, `AugmentedMap`) and
  `Sheaf.RingTheory.CotangentDifferentialPresheafSes` (`SiteCoefficients`,
  `tensorD`). Their existence theorems are not assumed or called. These owning
  theorem nodes are not added as dependencies: coherence itself uses this item,
  and doing so would create a DAG cycle. This delivery only imports their
  already-defined construction interfaces. Likewise the unstated proof
  dependency `lem-trf-polynomial-augmentation-boundary` has no module to import;
  its required standard endpoint fact is included in the owning Data conclusion.

Source check: read `cotangent.tex` section-functoriality (08QL), lines 867-950;
its standard ring maps and tensor functor are exactly those specified here.
Read the full presentation category in section-compute-L-pi-shriek and the
projective-resolution double-complex proof in `sites-cohomology.tex`,
lemma-compute-by-cosimplicial-resolution (08Q9), as well as
remark-morphism-fibred-categories (08PD). The source omits the comparison
verification; the DAG's general naturality dependency supplies it.

Edge cases checked: identity and composite squares (strict equations); zero
ring as target (no nontriviality hypothesis); nonflat Z -> Z/2 coefficient
maps (only balanced tensors, no derived base-change isomorphism claimed);
empty and infinite polynomial generator types (the full category and tensor
construction allow both); arbitrary Q, Q' and h, not just standard endpoints;
positive cochain degrees are zero; the n=0 term and degree -1 recursion anchor
are the existing explicit formulas. No node fault or disputed statement found.

Searches performed with the prescribed msearch.py wrapper:

- LeanSearch, "Naturality of derived colimit comparison for simplicial polynomial
  algebra resolutions under change of base ring": eight generic derived-functor,
  Dold-Kan and ring-map-property hits, none states this ring-square comparison.
- LeanFinder, "Semilinear maps of standard simplicial polynomial resolutions and
  naturality of their derived colimit bar comparisons": eight Dold-Kan
  PInfty/QInfty naturality hits, no match for ring squares or bar comparisons.
- Loogle, "KaehlerDifferential.map, MvPolynomial.eval₂Hom": zero hits.
- Mathlib grep, "cotangent.*natur|simplicial.*resolution|bar.*comparison",
  subdirectory RingTheory: one CotangentBaseChange documentation hit, no match.
- `rg` on both project roots for polynomial-square-bar-naturality,
  polynomial presentation, standard square and coherence: the helper
  constructions listed above exist, but no declaration states the whole item.
  Read their complete signatures and docstrings rather than duplicating them.
- Checked `dag/lean_names_upstream.json` for the item: no attachment.

## Second reading by Q20

Author's second pass, without spawning another agent as required by the brief:
reopened the node and the complete module and checked the clauses in the order
listed above. The important checks are that Data uses the full small presentation
category, the given ring square, actual tensor algebras, formula-normalized F
and theta, an arbitrary augmented semilinear h, endpoint-only trivial Kan
hypotheses, and the dependency's canonical comparisons and actual derived bar
map. In particular the target comparison under `mapDerivedCategory.map` must
be a component morphism, not the unapplied `.hom.app` function; corrected its
parentheses. Tensor scalar structures were made explicit after Lean showed
that the projection types did not synthesize an Algebra structure automatically.
No mathematical hypothesis or conclusion changed in these elaboration repairs.
The displayed tensor order is systematically reversed by symmetry, including
all generator formulas. No independent review is claimed by this author's pass;
the maintainer's independent delivery review remains required.

The final interface factors the construction records into `StandardData`,
`TensorData` and `Maps` in the same file. `Data` is the proposition asserting
existence of M : Maps F together with its canonical comparison equation.
The report uses short field names: the access paths are M.S for standard fields,
M.tensor for tensor base-change fields, and M for theta, factor and chain fields.
Using an existential proposition for the final assertion avoids costly generated
dependent-record code without changing the mathematical assertion.

The harmless-universe linter is scoped off on StandardData and TensorData:
these quantify over all U-small ring maps but carry an independent V-size
lift, so v occurs only in max(u+1,v). This retains the full universe range,
without imposing an equality or a size constraint on rings or variable sets.

Validation: scompile.py compiled both the sandbox-name check and the real module
name, respectively in 7.4 and 7.9 seconds. Only the expected sorry warning is
allowed; no error, timeout or other warning remained.
