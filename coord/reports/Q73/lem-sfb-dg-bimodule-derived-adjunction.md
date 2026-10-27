## Worker report

The item is stated in `Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction`, declaration
`CategoryTheory.DgAlgebra.bimodule_derived_tensor_hom_adjunction`. Its sole proof is `sorry`.
The supporting module `Sheaf.CategoryTheory.DgBimoduleModels` contains real definitions and
structures only, owned by the new definition node `def-sfb-dg-bimodule-models`. No statement
correction was required. The item node changes only in `lean` and by adding two definition
statement dependencies, the new models node and the already landed DG category node.

Sources read: the full item and five proof steps; the recorded size convention; the current
blueprint `latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3); Stacks
`dga.tex`, the definitions of DG algebras and modules, bimodule tensor and Hom, and
lemma-tensor-hom-adjunction (09LN), lemma-tensor-hom-adjoint (09LT), derived tensor/Hom
constructions 09LS/09LI, and the sign-free shift remarks. The tags file confirms 0FQN is
source-tensor shift and 0FQR is target-Hom shift.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The size convention has `lean.convention: true`; it requires explicit universes, not an
  additional object. `universe u` bounds all component abelian groups, with categories and
  actual Gabriel--Zisman localizations at their resulting larger universe levels. There is
  no finite bound on degrees, sizes, resolutions, or numbers of summands.
- `A B : Algebra.{u}` are the published monoids in unbounded integer cochain complexes
  `ModuleCat (ULift ℤ)`. Their multiplication is associative and unital and a chain map;
  this gives exactly the differential and signed Leibniz conditions. ULift of ℤ changes
  only the universe presentation. Commutativity of A and B is not assumed.
- `RightModule A/B`, `underlying`, `act`, `quasiIsomorphisms`, `Derived`, `Q`, and
  `DerivedStructure` all come from the published `DgAlgebraDerivedCategory` module.
  In particular the category is the actual localization at cohomological quasi-isomorphisms,
  equivalently localization of the homotopy category. `DerivedStructure` is the existing
  interface for its standard shift, coproducts and precisely the dg mapping-cone triangles;
  it is structural data of the categories in the node, not a replacement or an extra
  flatness or generation assumption.
- `N : Bimod A B` is Mathlib's existing bimodule object in the cochain tensor category.
  `actLeft`, `actRight`, their unit and associativity laws, and `middle_assoc` give exactly
  the two commuting graded actions and their signed differential rules. There is no
  duplicate DG-bimodule definition.
- Existential `F` and `t : BalancedTensorModel N F` specify the ordinary balanced tensor.
  The two maps `tensorBalanceLeft/Right` are `(ma) tensor n` and `m tensor (an)` on the
  same reassociated source. `balance` and `colimit` impose their coequalizer. Its underlying
  tensor is Mathlib's direct-sum total cochain tensor, with differential
  `d(m) tensor n + (-1)^|m| m tensor d(n)`. The model's `right_action` fixes the quotient
  B-action to the one induced from N; `naturality` fixes the action on every input map.
- Existential `G` and `h : BimoduleHomModel N G` specify exactly the internal DG Hom in
  the node. `coordinate` is linear; `injective` and `range` make its degree-r image exactly
  all right B-linear degree-r cochains. The cochains include all integer source degrees,
  thus products rather than a bounded Hom convention. `differential` identifies the
  differential with `CochainComplex.HomComplex.δ r (r+1)`, namely
  `d_Y f - (-1)^r f d_N`. `action` fixes `(fa)(n)=f(an)` with no sign or symmetry inserted.
  `naturality` fixes postcomposition on maps of Y.
- `a : F ⊣ G` and `IsBimoduleCurrying N t h a` fix ordinary transposition on every
  pure tensor. In particular this does not merely choose some adjunction between abstract
  categories. The displayed equation is the node's chain-currying formula in degree zero,
  evaluated on arbitrary homogeneous m,n. HEq accounts only for commuting integer sums.
- Existential `T`, `U`, `α`, `β` and `T.IsRightKanExtension α`,
  `U.IsLeftKanExtension β` give total left and right derived functors, respectively.
  These are the universal Kan properties with comparisons of the required directions:
  `Q_A T -> F Q_B`, `G Q_A -> Q_B U`. Using direct localization rather than its equivalent
  homotopy presentation does not change these properties: F and G followed by Q identify
  dg homotopies. No arbitrary quasi-isomorphism preservation of ordinary tensor is assumed.
- For every DG B-module Y, the resolution conjunct provides `i : Y -> I` with
  `quasiIsomorphisms B i` and `IsHomotopicallyInjective B I`.
  The latter definition tests all acyclic right DG B-modules C and every integer degree:
  every closed right-linear Hom cochain is a right-linear boundary. This is exactly the
  acyclicity of the whole Hom complex, not injectivity of the underlying complex over ℤ.
- The next conjunct makes `β.app I` invertible for every homotopically injective I.
  Consequently for any resolution `i : Y -> I`, the canonical zigzag
  `Q_A(G I) --β_I--> U(Q_B I) <--U(Q_B i)-- U(Q_B Y)` consists of isomorphisms.
  This is precisely the stated injective representative for RHom. No injectivity of
  Hom(N,I) over A is asserted or assumed.
- `adj : T ⊣ U` supplies bijections on Hom for every pair of derived objects, natural in
  both arguments. The normalization equation at every ordinary `g : F M -> Y` states
  `adj.homEquiv (α_M ; Q_B g) = Q_A(a.homEquiv g) ; β_Y`, so these are the bijections
  induced by the already fixed chain currying. The Kan properties and resolution
  comparisons extend the normalization to all derived objects and arrows.
- `_sT`, `_sU` supply coherent integer shift comparisons. The tensor-shift conjunct
  provides the sign-free comparison on homogeneous pure tensors (`IsTensorShift`) and
  its square with α, Q's standard shift isomorphism and `T.commShiftIso`.
  The Hom-shift conjunct similarly provides the output-shift coordinate equation
  (`IsHomShift`) and its square with β and `U.commShiftIso`. Thus shifts are induced by
  the actual tensor and Hom constructions, not unrelated chosen natural isomorphisms.
- `adj.CommShift ℤ` states that both the unit and counit commute with those shifts;
  Mathlib's `Shift.Adjunction` defines exactly those two squares.
  `T.IsTriangulated` and `U.IsTriangulated` mean they carry every distinguished triangle
  to a distinguished triangle, with these comparisons. Hence both functors are exact.
- There are no flatness, boundedness, compactness, or quasi-isomorphism assumptions on
  N, A, or B. In particular the module has no ring map A -> B parameter.

Dependency declarations used:

- `def-weil-size-convention`: a convention-only existing record. The recorded upstream
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory` docstring was also read for its explicit
  universe convention; no pro-etale category is used in this DG statement.
- `def-sfb-dg-derived-category`: `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`,
  `CategoryTheory.DgAlgebra.Algebra`, `RightModule`, `underlying`, `act`,
  `quasiIsomorphisms`, `Derived`, `Q`, `ShiftComparison` and `DerivedStructure`, with
  their full signatures and docstrings read.
- The new models node supplies all twelve declarations listed in its lean.declarations.
- Mathlib: `CategoryTheory.Bimod` and its full action laws (Monoidal/Bimod),
  `CochainComplex.HomComplex.Cochain` and `δ` (HomotopyCategory/HomComplex),
  `Functor.IsRightKanExtension` / `IsLeftKanExtension`,
  `Functor.IsTriangulated`, `Adjunction.CommShift`, `Adjunction.homEquiv`.
- Stated proof inputs imported without `public`:
  `WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined`,
  `WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`,
  `Mathlib.CategoryTheory.Triangulated.Opposite.Functor`.
  Their declaration signatures and docstrings were read.
  `Adjunction.mkOfHomEquiv` is already available from the public adjunction import;
  its natural-bijection interface and unit/counit formulas were read.
- The record for lem-coef-dg-semi-free-homotopically-projective still names
  `Sheaf.CategoryTheory.SemiFreeDGModule`, absent locally; the prescribed
  `scompile.py --source Sheaf.CategoryTheory.SemiFreeDGModule` also answers
  `Module source unavailable`. No usable module is imported for that proof-only
  input. Its mathematical proof use remains documented in the theorem's five-step
  docstring. The other five DG proof inputs have no published Lean binding and are
  therefore not imported. None is needed to type the statement.

Edge cases checked by reading the definitions and all quantifiers:
zero DG algebra (the zero-ring unit convention), zero bimodule, zero input module,
unbounded modules with terms in positive and negative degrees, negative and zero shifts,
odd shifts and odd action degrees, a bimodule without flatness on either side,
noncommutative A/B with no map between them, and an arbitrary acyclic source in the
injectivity test. The cochain differential has the required sign because δ(r,r+1)
uses (-1)^(r+1) in its second summand. The left A-action in `action` evaluates
`N.actLeft` directly on a tensor `a tensor n`, with no braiding sign. The superseded
initial sandbox draft was not delivered: it had only an abstract adjunction and
insufficient representative clauses. Those were replaced by the complete models,
Kan properties, resolution clause and normalization equations above.

Searches (the raw msearch results are retained in the new node's mathlib_searches):

- LeanFinder, `Unbounded derived tensor Hom adjunction for arbitrary differential graded
  bimodules`: eight generic cochain tensor hits, no DG algebra adjunction.
- Loogle, `"Bimod", "Adjunction"`: zero hits.
- msearch grep, `DGAlgebra|DgAlgebra|Bimod|Homotopically` in CategoryTheory/Monoidal:
  seven hits including Mathlib's Bimod; this is reused directly.
- LeanSearch, `Differential graded balanced tensor and complex of homogeneous right linear
  maps for DG bimodules`: generic graded tensor hits and HomComplex.δ_hom; the latter's
  existing differential is reused.
- LeanSearch, `DG bimodule balanced tensor coequalizer homogeneous right linear Hom complex`:
  Bimod.tensorBimod and its coequalizer formulas. The model structure uses that same
  coequalizer universal property on the project's existing RightModule interface;
  it defines no second tensor object.
- LeanFinder, `Homotopically injective differential graded modules over associative
  differential graded algebras`: ordinary complexes' K-injective API, which does not
  impose DG-algebra linearity of the null-homotopies.
- rg in Mathlib, WeilConjectures and Sheaf for DGAlgebra/DgAlgebra, homotopically,
  Bimodule, the chosen names, and tensor/Hom. Existing Sheaf.Algebra.Homology.
  DerivedBimoduleTensorHom is for ordinary commutative rings in degree zero, not arbitrary
  DG algebras. The concrete DG-derived-category interface is reused. No existing exact
  statement or model interface found.
- grep for the item id in WeilConjectures/Sheaf and dag/lean_names_upstream.json:
  no declaration of this node.
- DAG search for balanced tensor and graded DG bimodules found theorem nodes and the
  published DG-derived-category definition, but no definition of these coordinate models.
  `tools/blueprint_refs.py search 'dg bimodule'`: 0 blueprint nodes match.
  `tools/blueprint_refs.py ancestor lem-sfb-dg-bimodule-derived-adjunction`: ancestor None,
  retained in the new node with the item's inherited place and full via path.

Validation: scompile.py compiled both files separately, including the private dependency
module and library path, with no diagnostics: models 13.3/17.7 seconds, statement 2.2/2.4
seconds. No tests, proofs, axioms, private definitions, local notation or local instances
were added. Dry-run and delivery are recorded by the prescribed wrapper.

## New nodes

`def-sfb-dg-bimodule-models` owns `Sheaf.CategoryTheory.DgBimoduleModels`. It introduces
only the coordinate/universal-property specifications needed to state the item on the
existing DG category interface, together with the homotopical-injectivity predicate and
sign-free shifts. It uses Mathlib's `Bimod`, cochain tensor, Hom cochains/differential and
coequalizer notion; it does not reimplement any of them. It does not assert existence of
a model, a resolution or a derived adjunction. Every definition has real data; the
existence of the specified ordinary functors belongs to the item's theorem. The full
search results, source locations, inherited blueprint path and declaration inventory are
in the new node. The node cites the published def-sfb-dg-derived-category.

## Second reading by Q73

This is the dispatcher's requested worker self-check; no additional agent was started.
The maintainer performs the independent delivery review. I reopened both files, the item,
the new node, and the source paragraphs and matched the hypothesis and clause list above.
I removed the first draft's unconstrained abstract adjunction and tautological Hom and
representative claims. The final statement fixes ordinary balanced tensor, all DG Hom
terms and actions, currying, universal total derivation, every injective resolution, and
canonical sign-free shift squares. I checked the directions of α and β and both shift
squares against their source/target objects. I corrected the draft Hom-action formula to
evaluate the left action directly on `a tensor n` (no braiding), and checked the shifted
index equalities. I also corrected the source tags: 0FQN is tensor shift and 0FQR is Hom
shift. These documentation corrections change no signature. The definition node's
statement matches every one of its twelve declarations; the item signature is verbatim
from `theorem` to before `:=`, and the new record is verbatim through before `where`.
All variables and the component universe are explicitly bound and all Lean lines are at
most 100 characters. No remaining statement dispute or source correction is claimed.

Dry-run metadata repair: preflight required `import_flags` on the new definition node;
added the empty list. The first dry run pushed nothing. No Lean signature changed.
