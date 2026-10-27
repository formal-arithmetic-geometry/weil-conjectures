## Worker report

The module `Sheaf.AlgebraicGeometry.CurveSmoothLocusDeformationTest` states two
clauses of this node, both with `sorry`: `exists_curve_coefficient_ring` and
`exists_curve_smooth_open_deformation_test`, in namespace
`AlgebraicGeometry.ProperCurveModuli`. There are no new definitions, no proved
statements, no dependency replacements, and no correction to the mathematical statement.

Source read: `literature/stacks-project/moduli-curves.tex`, section-smooth,
lines 1387–1462, especially Tag 0DZU, `lemma-in-smooth-locus`, and its preceding
coefficient choice. The six proof steps of the DAG are reproduced in the main
declaration's docstring, with the named prerequisites. The auxiliary existence
declaration's docstring gives the coefficient-choice argument from step 2.

Clause-by-clause rendering:

* Schemes over Spec Z use the terminal integer scheme
  `Spec (.of (ULift.{u} ℤ))`, with `specULiftZIsTerminal.from` its canonical structure
  map. The explicit universe `u` is shared by fields, coefficient rings, test rings,
  schemes and geometric fields; there is no smaller independent test universe.
* The curve groupoid is the existing `ProperCurveModuli.category`. Its objects
  are `ProperCurveFamily` and its arrows are the existing cartesian sheaf squares.
  `AlgebraicSpace.IsProperCurveFamily` supplies chartwise flatness and local finite
  presentation, separatedness by its closed-immersion diagonal, quasi-compactness,
  chartwise local finite type, universal closedness, quasi-compact diagonal, and
  dimension at most one on every algebraically closed field fibre. This is exactly
  the flat proper finitely presented algebraic-space curve family, without purity,
  stability, projectivity, connectedness, reducedness or nonemptiness restrictions.
  Universal closedness can be checked after scheme base changes: an etale atlas
  of any algebraic-space base change is surjective and open, so closedness of the
  image can be checked after its scheme cover. This is the existing interface,
  not an extra restriction on the node's algebraic-space base changes.
* Algebraicity is assumed by `hdiagonal : HasAlgebraicSpaceDiagonal ...` and
  `hatlas : ∃ U a, IsSmoothModuliAtlas ... U a`. These are precisely the node's
  representable diagonal and smooth surjective scheme atlas. There is no added
  descent hypothesis: curve descent is the cited proof input, as in proof step 1.
* The maximal open is `∃ M : OpenModuliSubstack ...`. Its smoothness is
  `IsSmoothModuliStack M.category`, namely a smooth atlas with smooth structural
  composite. Largest means `∀ N, IsSmoothModuliStack N.category → N.IsContainedIn M`.
  `OpenModuliSubstack.open_pullback` supplies exactly open subschemes on scheme tests;
  the full subcategory and pullback stability retain the arrows and restrictions.
* For every field `k`, `exists_curve_coefficient_ring` supplies `Λ`, its commutative
  ring, local, Noetherian and algebra structures, a surjective `algebraMap Λ k`, and
  `RingHom.ker (algebraMap Λ k) = IsLocalRing.maximalIdeal Λ`. The latter two clauses
  specify exactly the residue-field identification. `ringChar k = 0` together with
  `Function.Bijective (algebraMap Λ k)` identifies Λ with k by this same residue map;
  the witness in the proof is k itself. In positive characteristic the predicate is
  `0 < ringChar k ∧ IsCohenRing (ringChar k) Λ`. `IsCohenRing` includes primality,
  the domain and DVR structures, maximal ideal `(p)`, and adic completeness.
* The main theorem quantifies over EVERY `k Λ` with these same residue and
  coefficient conditions, not merely the witness of the existence theorem.
  `[IsNoetherianRing Λ]` and `[IsLocalRing Λ]` express the coefficient category's
  stated setting; every permitted coefficient ring has these structures, so no
  indicated ring is excluded. The algebra structure is its specified residue map.
* `ArtinDeformation.TestCategory Λ k` is the existing category of augmented
  Artinian local algebras. Its surjective augmentation with maximal kernel retains
  exactly `A / m_A ≅ k`; arrows preserve the augmentation, hence induce identity
  on k and are local. No coefficient-field embedding `k → A` is required. In
  particular, mixed-characteristic test rings are retained. Although its owning
  node is stated with finite-type residue field, the actual TestCategory signature
  does not require that instance. No finite-type assumption on k over Z is added;
  k is automatically finite type over its coefficient ring through the residue map.
* The proper k-scheme is `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))` with
  `IsProper f` and `topologicalKrullDim X ≤ 1`. The explicit structure map is
  necessary for the special-fibre and classifying comparisons in this statement.
* The left side of the iff is a classifying family `C`, an isomorphism `e` from
  its actual presheaf to the Yoneda presheaf of X over the integers, the equation
  `e.hom ≫ yoneda.map (...) = C.projection` fixing its k-structure, and
  `M.property ⟨..., C⟩`. This is factorization of the specified classifying point
  through the full open, not a test on an unrelated isomorphic abstract space.
* The right side quantifies over every test pair `A' A`, every arrow `q : A' ⟶ A`,
  and `Function.Surjective (ArtinDeformation.map q)`. It includes all surjections,
  including identity arrows, not only square-zero or small extensions.
* A deformation consists of arbitrary `Y`, `g : Y ⟶ Spec A`, `j : X ⟶ Y`,
  `Flat g` and `IsPullback j f g (Spec.map (residue A))`. A cartesian square with
  upper-left vertex X is exactly a specified special-fibre isomorphism. There is
  no properness or finite-presentation assumption on Y: those follow in the proof.
* The lift is `∃ Y' g' l, Flat g' ∧ IsPullback l g g' (Spec.map (map q))`.
  This retains the prescribed reduction isomorphism. Its special-fibre marking
  is `j ≫ l`; pasting the given cartesian squares, and the residue compatibility
  already imposed on q in TestCategory, proves it is the same marked X.
  Conversely, a lift with a marking-compatible reduction isomorphism supplies
  exactly such an l. Thus no marking or lifting-isomorphism condition is discarded.
  Marking-preserving isomorphisms of deformations are fully respected by this
  formulation; no quotient by isomorphism classes is substituted for lifts.

Existing dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property, expressed in the theorem using `IsPullback`.
* `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, representability and
  its chart conventions, used through the already defined curve predicate.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.Proper`,
  `.FiniteType`, `.Smooth`: `Flat`, `LocallyOfFinitePresentation`, `IsProper`,
  `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`, via the existing curve/atlas
  definitions and directly `Flat`, `IsProper` in the signature.
* Mathlib's `Field` and `IsNoetherianRing`; the metatheoretic size convention has
  no declaration and is expressed by explicit universe binders.
* `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, with its full definition read.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`, `category`,
  `IsProperCurveFamily`, and the cartesian-arrow `Hom`.
* `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`, `category`,
  `IsContainedIn` and `open_pullback`.
* `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsSmoothModuliAtlas`,
  `IsSmoothModuliStack`, using the already imported `HasAlgebraicSpaceDiagonal`.
* `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`: `TestCategory`, `ring`,
  `residue`, `map`, `IsTestAlgebra` and its local/Artinian structures.

The four already landed definition nodes for proper-curve moduli, open substacks,
algebraic stacks and Artinian tests are appended to stmt_deps under brief-stage2
§5 (STMT_DEPS MAY GAIN LANDED NODES). No private copy of any notion is introduced.
The existing downstream `IntegerSchemePointIn` declaration is deliberately not
imported: its owning theorem uses this item. Membership is written directly in
this theorem's signature, so there is no new definition or dependency cycle.

Proof-only imports include every currently recorded proof module, and the Mathlib
modules for the three Mathlib-matched proof prerequisites. The still unstated
maximal-open, stack-lfp, nilpotent-properness-reflection, flat-deformation-lfp,
thickening-of-scheme-space and stack-Artinian-smoothness nodes do not provide
modules to import. Their proof uses are recorded in the docstring; none is needed
as a statement definition here.

Edge cases checked before and after writing: the empty scheme has dimension bottom
and is included by `≤ 1`; disconnected, nonreduced, zero-dimensional and non-lci
proper schemes are not excluded; an arbitrary (possibly imperfect) field of positive
characteristic uses its Cohen ring; characteristic-zero fields need not be finitely
generated over Q; the test category imposes no finite dimension over k or embedding
of k; identity surjections and arbitrary-kernel surjections are included. The
marking-composition argument also works for identity base change. All tests live
in the same chosen universe as the objects they test, preventing vacuity caused by
a smaller independent test universe. No disputed statement or source fault found.

Actual searches:

* msearch leanfinder: “A proper curve lies in the smooth open substack of the stack
  of curves if and only if its marked Artinian deformation category is unobstructed”.
  Eight hits, all scheme/ring smoothness; no curve-stack statement.
* msearch leansearch: “Smooth locus of the stack of proper curves characterized by
  unobstructed flat deformations over Artinian local coefficient algebras”. Eight
  hits on `Algebra.smoothLocus` and formal smoothness of rings, no matching theorem.
* msearch loogle: `IsCohenRing`. Zero hits, unknown Mathlib identifier; the existing
  project declaration was found and read instead.
* msearch grep: `Unobstructed|ProperCurveModuli|CurveSmoothLocus`; zero Mathlib hits.
  Also `CohenRing|[Uu]nobstructed|[Dd]eformation` in `AlgebraicGeometry`: zero hits.
* rg on the entire project's `lean/WeilConjectures` and `lean/Sheaf`, including the
  node id, unobstructed, expected curve-stack names, and the proposed declaration
  names; only downstream documentation cited this item, no exact declaration.
  These searches did locate the reusable moduli, Artinian-test and marked-lift APIs,
  whose full signatures/docstrings were read. `dag/lean_names_upstream.json` was
  searched too. No existing exact match for either theorem was found.

Validation: prescribed scompile.py compiled both sandbox and library module modes
cleanly (initial run: 17.0 s and 6.2 s), with no error or warning. The final run, including
the proof imports, also compiled cleanly (3.3 s sandbox, 3.3 s library). The prescribed
`deliver2.py --no-push` passed preflight and compilation: dry-run commit 2786df3e372,
nothing pushed at that step.

## Second reading by Q117

I reopened the node and the completed Lean signature for a sequential second reading;
this is not represented as an independent agent review. The dispatcher explicitly
forbids starting other agents, and the maintainer performs the independent review.

I checked the diagonal/atlas assumptions against the first paragraph and confirmed
there is no stronger stack-descent binder. I checked that maximality compares ALL
smooth open substacks, not just the opens with the same field points. The separate
coefficient theorem covers existence, and the main theorem tests EVERY coefficient
ring, including k in characteristic zero and Cohen rings with the prescribed residue
map in characteristic p. The augmentation conditions fix the same field for both
tests and all test arrows. No finite-type-over-Z condition appears. I checked the
classifying isomorphism's projection equation and both orientations of the marked
pullback squares. Pasting supplies the lifted marking `j ≫ l`, so the omission of a
separate redundant marking variable loses no datum or compatibility. The family Y
is assumed only flat, as required. Empty/disconnected schemes and identity surjections
remain in the exact quantified ranges. I added the three Mathlib proof imports found
in the proof-dependency matches; no signature mismatch required a correction.
