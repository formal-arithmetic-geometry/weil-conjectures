## Worker report

The module `Sheaf.CategoryTheory.FormalExactProjectionMate` states exactly the formal
specified-data result. It defines the two morphism families
`CategoryTheory.formalProjectionBeta` and `CategoryTheory.formalProjectionAlpha` by actual
composition, then states `CategoryTheory.formalExactProjectionMate` with one `sorry`.
There are no new nodes, dependency repairs, or statement corrections. Only the item's
`lean` field changes. All variables and the four independent object/morphism universes
are explicitly bound; `autoImplicit` is false.

Source read: `literature/stacks-project/sites-cohomology.tex`, Projection formula,
Tag 0B56, equation-projection-formula-map: the displayed arrow is adjunct to the
pullback tensor comparison followed by counit tensor identity. Also read
`literature/stacks-project/derived.tex`, Tag 0A8D, lemma-adjoint-is-exact, and the current
blueprint `main-20261015` perfect-projection-formula statement and detailed proof:
its first paragraph uses exactness, shifts, cones and normalization at the unit.
The item's formal statement, with its seven explicit proof steps, was retained verbatim.

Hypotheses, in the order of the node:

- Triangulated categories C and D: explicit `Category`, `Preadditive`, `HasZeroObject`,
  `HasShift ... ℤ`, additive integer shifts, `Pretriangulated` and `IsTriangulated`
  binders. In particular the octahedral hypotheses are explicit theorem binders, so
  cannot disappear through section-variable inference.
- Tensor: `TC : C ⥤ C ⥤ C` and `TD : D ⥤ D ⥤ D` are curried bifunctors, not monoidal
  structures. Each `T.obj M` and `T.flip.obj N` has its specified `CommShift ℤ` and
  `IsTriangulated` structures. Exactness supplies additivity via Mathlib's
  `Functor.IsTriangulated` additive instance; thus no extra additive hypothesis is
  needed. `CommShift` includes coherence at zero and under addition.
- Naturality of both shift comparisons in maps of the fixed input is precisely the
  four instance families `NatTrans.CommShift (TC.map f) ℤ`,
  `NatTrans.CommShift (TC.flip.map f) ℤ`, and the corresponding two TD families.
  This includes the counit map used in proof step 3.
- The fixed units are `oneC`, `oneD`; natural right action isomorphisms are
  `ρC : TC.flip.obj oneC ≅ 𝟭 C` and `ρD : TD.flip.obj oneD ≅ 𝟭 D`.
  There is no left unit, associator, braiding or unit-shift assumption.
- Exact L and R: their `CommShift ℤ` and `IsTriangulated` binders. `adj : L ⊣ R`
  supplies the specified natural unit and counit and both triangle identities.
  `NatTrans.CommShift adj.unit ℤ` and `NatTrans.CommShift adj.counit ℤ` say exactly
  that these transformations commute with the induced composite comparisons.
- The tensor comparison is the iso family `μ M N`. `hμnat` is its simultaneous
  naturality in arbitrary `f : M ⟶ M'` and `g : N ⟶ N'`. Setting either map to
  an identity recovers separate naturality; conversely separate naturality gives
  this equation by bifunctoriality.
- `hμshift₁` and `hμshift₂` are the two composite-shift compatibility equations,
  for all M, N and all integers n. For example the second equation compares
  μ at `(M,N[n])`, then tensor applied to L's shift and TD's shift, with L applied
  to TC's shift, then L's shift and the shifted μ. These are exactly the source's
  comparisons for `L(M ⊗ -)` and `LM ⊗ L(-)`; the flipped equation handles M.
- `u : L.obj oneC ≅ oneD` is the given unit iso, and `hunit` is
  `μ(M,oneC) ≫ (1 ⊗ u) ≫ ρD(LM) = L(ρC(M))`, with no modified normalization.

Definitions and conclusions, in the order of the node:

- `F_E` is the existing functor `TC.obj (R.obj E)`. `H_E` is `L ⋙ TD.obj E`;
  `G_E` is `(L ⋙ TD.obj E) ⋙ R`. Composite `CommShift` instances supply the
  comparisons of these very functors, not extra independently chosen comparisons.
- `formalProjectionBeta ... E P` is `(μ (R.obj E) P).hom` followed by
  `(TD.map (adj.counit.app E)).app (L.obj P)`. This is exactly counit tensor
  identity after μ. `formalProjectionAlpha` is `adj.unit.app _` followed by
  `R.map` of that β. Both definitions have real data and no proof holes.
- First conjunct: for every E, F_E and G_E are `IsTriangulated`, with the specified
  comparisons on F_E and the induced composite comparisons on G_E.
- Second conjunct: simultaneous naturality for every `e : E ⟶ E'` and
  `p : P ⟶ P'`, explicitly `(R(e) ⊗ p) ≫ α(E',P') = α(E,P) ≫ R(e ⊗ L(p))`.
  Either variable may be unchanged, including identity maps.
- Third conjunct: for every E, n : ℤ and P, `α(E,P[n]) ≫ sG(n,P)` equals
  `sF(n,P) ≫ (shiftFunctor C n).map α(E,P)`. Lean's `≫` reverses the displayed
  functional composition in the prose; the two sides are exactly its shift equation.
- Fourth conjunct: for each distinguished `T : Triangle C`, both existing
  `mapTriangle` images are distinguished, and there exists a morphism between
  those image triangles whose three components are exactly α at `T.obj₁`,
  `T.obj₂`, `T.obj₃`. The recorded dependency `TriangleMorphism` defines all three
  commuting squares. Its `comm₃`, after substituting these specified components
  and the actual `mapTriangle` third arrow, is
  `F_E.map T.mor₃ ≫ sF(1,T.obj₁) ≫ α(E,T.obj₁)[1] =
   α(E,T.obj₃) ≫ G_E.map T.mor₃ ≫ sG(1,T.obj₁)`.
  This is exactly the requested connecting-arrow square, including the actual w.
- Fifth conjunct: `α(E,oneC) ≫ R.map ((TD.obj E).map u.hom ≫ ρD.hom.app E)`
  equals `ρC.hom.app (R.obj E)`. Its type is `RE ⊗ oneC ⟶ RE`, precisely the
  stated right-unit equation. There is no assertion that α is invertible, and
  no ringed-site data are constructed or presumed.

Dependency declarations read and used:

- `def-weil-triangulated-category`: Mathlib
  `CategoryTheory.Pretriangulated` in `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `CategoryTheory.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Triangulated`,
  and `Functor.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Functor`.
  Their signatures, class fields, docstrings and the exactness-to-additivity instance
  were read. These are the dependency's recorded Mathlib interfaces.
- `lem-weil-pbc-adjunction-of-natural-bijection`: Mathlib
  `CategoryTheory.Adjunction.mkOfHomEquiv` and `Adjunction.CoreHomEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. Read the full signatures and unit,
  counit and hom-equivalence formulas. The item's hypothesis is already a specified
  adjunction, so it uses `Adjunction` and its unit and counit directly; it need not
  reconstruct a second adjunction from its own hom equivalence.
- `lem-weil-pbc-commshift-nattrans-comp-whisker`: Mathlib
  `CategoryTheory.NatTrans.CommShift.comp`, `.id`, `.whiskerLeft`, `.whiskerRight`,
  `.associator` and `Functor.CommShift.comp` in `Mathlib.CategoryTheory.Shift.CommShift`.
  Read their signatures and `shift_app_comm`. The integer-shift assumptions and
  equations use these same definitions and composite instances.
- `def-weil-pbc-triangles-with-shift`: Mathlib
  `CategoryTheory.Pretriangulated.Triangle` and `TriangleMorphism` in
  `Mathlib.CategoryTheory.Triangulated.Basic`. Read the objects, the three morphism
  fields, all three squares, and the category instance. The theorem's existential
  triangle morphism uses exactly this dependency.
- Proof dependency `lem-weil-pbc-triangulated-functor-composite`: the recorded
  `CategoryTheory.Functor.IsTriangulated.instComp` instance in
  `Mathlib.CategoryTheory.Triangulated.Functor`. Read its statement and preservation
  argument; the module is imported, and the proof docstring explicitly names it.

Edge cases checked mathematically before writing:

- n = 0 and negative n are included without positivity assumptions. Coherence of
  every `CommShift ℤ` is built in. The proof uses the given equation at arbitrary n.
- E = 0, P = 0 and the zero triangulated category are allowed. Exactness supplies
  preservation of zero; neither object is required to be nonzero.
- The identity adjunction with identity comparison and u gives the expected unit
  normalization and the same naturality/shift identities.
- Contractible distinguished triangles and zero connecting arrows remain included;
  the actual connecting map is used, with its specified shift comparison.
- Units are arbitrary specified objects with the stated right actions. In particular
  nothing excludes degenerate unit data compatible with the bifunctor.
- Object and morphism universes of C and D are four independent levels. No equality,
  smallness, nonempty index restriction, or ring/site specialization was introduced.

Searches actually run:

- `msearch.py ... leanfinder "Exact tensor bifunctor adjunction projection mate
  compatible with integer shifts and normalized at the right unit"`: 8 hits,
  including `tensorRightAdjunction`, `tensorLeftAdjunction` and
  `Adjunction.unit_app_tensor_comp_map_δ`. These require monoidal/rigid data or
  state a component identity; none states this bifunctor-only exact mate theorem.
- `msearch.py ... loogle '"projection", "shift"'`: 0 hits.
- `msearch.py ... grep 'projection.*[Cc]ommShift|rightAdjointProjectionMap'
  CategoryTheory`: 0 hits.
- `msearch.py ... leansearch "The projection mate of exact tensor bifunctors and a
  shift compatible adjunction is natural compatible with shifts and the right unit"`:
  8 hits, including `Adjunction.CommShift.compatibilityUnit_unique_right`,
  `Adjunction.unit_app_commShiftIso_hom_app`, `Adjunction.CommShift.CompatibilityUnit`
  and `NatTrans.CommShiftCore.shift_app_comm`. They provide shift compatibility
  components, not this full projection theorem.
- `rg -n 'formalExactProjection|formal_exact_projection|projection.*[Mm]ate|ProjectionMate'
  lean/Sheaf lean/WeilConjectures`: found specialized ringed-site, module, monoidal
  and geometric projection theorems, including `Sheaf.Paper.ProjectionMateExact`
  and upstream `CategoryTheory/Monoidal/ProjectionMap.lean`. Read both relevant
  interfaces; they assume more structure or provide different conclusions.
- `rg -n 'lem-weil-pbc-formal-exact-projection-mate' lean/WeilConjectures`: no hits.
- `rg -n 'FormalExactProjectionMate|formalProjectionBeta|formalProjectionAlpha'
  lean/Sheaf lean/WeilConjectures lean/.lake/packages/mathlib/Mathlib`: no hits.
  The declaration names are new; the existing monoidal `projectionMap` requires
  associators absent from this statement and is not redefined or shadowed.

Validation: the delivered module compiles through the prescribed `scompile.py` on
both its sandbox and library-module passes, cleanly and within the 60-second limit
(about two seconds each). No tests or proofs were added. The final dry run and push
are recorded by the delivery wrapper.

## Second reading by NN

Worker's final clause audit, with the DAG statement and final module open: the
hypothesis/conclusion correspondence above covers both tensor inputs, naturality in
maps of the fixed input, the supplied adjunction, both μ shift conditions, every
integer, all three components of the morphism of the actual image triangles, and
the precise right-unit equation. The final audit made the `IsTriangulated C/D`
hypotheses explicit on the theorem rather than leaving them as inferable section
variables. It also removed the unneeded `Shift.Adjunction` import and directly
imports each recorded Mathlib statement-dependency module. There is no change to
the DAG statement. This is a worker self-check, not a claim of independent review;
the maintainer's independent review reads the delivery as specified by the brief.
