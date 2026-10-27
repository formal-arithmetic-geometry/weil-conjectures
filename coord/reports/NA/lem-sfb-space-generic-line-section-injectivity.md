## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGenericLineSectionInjectivity` states
`AlgebraicGeometry.AlgebraicSpace.generic_lineModule_section_injective`, with one
`sorry` and no new definitions. The source is Stacks 0DMZ, the generic nonvanishing
and local-field paragraph, together with 0ABV. I read both passages in the local
Stacks sources and the current blueprint unit. The theorem isolates the generic
argument before properness is used to control global functions.

Clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- An algebraic space over Spec k: `X : AlgebraicSpace (Spec (CommRingCat.of k))`.
  Its structural map is `f` to the representable base space
  `schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k))))`. That representable is
  terminal among spaces over Spec k, so this is the structural map, not extra
  variable geometric data.
- Separated: `hsep : MapIsSeparated f`, using the recorded closed-immersion
  diagonal predicate.
- Finite type: `hft : MapIsFiniteType f`, using the recorded conjunction of
  quasi-compactness and locally finite type on compatible charts.
- Reduced affine étale chart rings: `hred : X.IsReduced`. The landed predicate
  says all étale chart schemes are reduced, equivalently their affine open rings
  are reduced. Conversely an affine open of any chart is itself an étale chart,
  so the predicate and the node's affine-chart formulation agree.
- Nonempty and irreducible in the atlas topology:
  `[IrreducibleSpace (Point X.obj.obj)]`. Mathlib's class includes `Nonempty`,
  and its preirreducibility condition is equivalent to the closed-subset
  formulation. The topology is the recorded `pointTopologicalSpace`.
- A unique generic point:
  `∃! η : Point X.obj.obj, IsGenericPoint η Set.univ`.
- Any geometric point over that generic point: universally quantified
  `Ω`, `[Field Ω]`, `[IsAlgClosed Ω]`, the map `b` from Spec Ω to Spec k,
  and `x : yoneda.obj (Over.mk b) ⟶ X.obj.obj`. Its underlying point is
  `Quot.mk _ (⟨Ω, b, yonedaEquiv x⟩ : PointRepresentative X.obj.obj)`.
  `IsGenericPoint` of this point is the hypothesis that it lies above η;
  uniqueness in the first conjunct identifies it with η.
- The geometric local ring F is a field:
  `IsField (SingleComplex.stalkRing b x)`. This is the predicate for the
  existing commutative ring, not an unrelated chosen field structure.
- Every line module: `∀ M : X.Modules, X.IsLineModule M → ...`.
- Its stalk is one-dimensional over F:
  `Nonempty ((SingleComplex.stalkModel b x).modules.obj M ≃ₗ[F] F)`.
  Since the preceding conjunct says F is a field, a linear equivalence with F
  is exactly dimension one, without a separate arbitrary field instance.
- Injectivity of the germ homomorphism: for every pointed affine neighbourhood
  `V`, `Function.Injective` of the lambda that evaluates `σ : M.sections`
  on `neighbourhoodChart.obj V` and applies `(stalkModel b x).germs M` at V.
  These are the actual restriction and colimit maps. Compatibility of a global
  section and naturality of the cocone show that every V gives the same map:
  pass to a common pointed refinement. There is a pointed neighbourhood of
  every geometric point (the stalk model uses that filtered nonempty system).
  Thus quantifying over V expresses the single canonical germ map without
  a chart choice or an unnormalized arbitrary map.
- Geometric stalk means filtered colimit of pointed étale sections: exactly
  `SingleComplex.stalkModel`, whose `ringIsColimit`, `moduleIsColimit`, and
  `smul_germ` fix the ring, module and scalar structures. Its small affine
  neighbourhood basis computes the same colimit as all pointed neighbourhoods.
- No properness or regularity assumption appears.

Recorded statement dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `IsLineModule`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`; its dependency
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` supplies `Point` and
  `PointRepresentative`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`: `IsReduced`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.Neighbourhood`, `neighbourhoodChart`, `StalkModel`,
  `stalkModel`, `stalkRing`, including the germ and colimit fields.

The last two are already landed definition nodes; their IDs were added to
`stmt_deps` under the rule permitting landed dependencies. No new node or
replacement dependency module is needed. All already stated proof dependencies
are imported privately, including the relevant Mathlib match modules. Unstated
proof dependencies (sobriety, specified lifting, étale specializations) cannot yet
be imported; their exact roles are retained in the seven-step proof docstring.

Edge cases checked: empty X is correctly excluded by irreducibility's Nonempty;
no geometric irreducibility is assumed; an integral but not geometrically
integral space is allowed. Ω need not equal the separable closure of the chart
function field, and the theorem never identifies F with Ω. Every characteristic
and imperfect base field is allowed. The zero global section and a line with
no nonzero global sections are allowed. A line module over the nonzero generic
field is not the zero module. No properness, smoothness, normality, or regularity
is introduced. All fields and modules stay in the existing site's original
universe, with the whole statement universe-polymorphic. The generic point type
is the existing Type (u+1) quotient. No auto-bound variables or diagnostic commands
remain.

Searches performed:

- `msearch.py leanfinder`, query `Restriction of line module sections on an
  integral algebraic space to a geometric generic point is injective`: eight
  hits, headed by scheme results `instIsGermInjectiveOfIsIntegral`,
  `germ_injective_of_isIntegral`, `Scheme.germToFunctionField_injective` and
  `map_injective_of_isIntegral`. Their signatures concern scheme functions,
  not algebraic-space line modules. I read FunctionField.lean's candidates.
- `msearch.py loogle`, query `"IsIntegral", "germ"`: two scheme hits,
  `germ_injective_of_isIntegral`, `instIsGermInjectiveOfIsIntegral`; no match.
- `msearch.py grep`, query `AlgebraicSpace|germ_injective_of_isIntegral`,
  subdirectory `AlgebraicGeometry`: three lines, all using the scheme theorem.
- `msearch.py leansearch`, query `Geometric generic stalk of a line module on
  an integral algebraic space detects global sections`: eight hits, concerning
  scheme stalks and regular functions; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for generic-line injectivity,
  geometric stalks and global germs: the source has scheme and coefficient
  sheaf results; Sheaf has the canonical stalk model and the downstream
  `SpaceDualEffectiveLineTriviality` statement, not this theorem. The existing
  `InvertibleModuleGenericStalk` is for schemes, not algebraic spaces.
- Search for the item ID in `lean/WeilConjectures`: no occurrence. Search for
  the proposed declaration name in Mathlib, both library roots and
  `dag/lean_names_upstream.json`: no collision.
- `rg` of DAG records located the already landed reducedness and normalized
  stalk-model owners; these were reused instead of introducing definitions.

Validation: the prescribed `scompile.py NA <item> <file>` compiled both the
sandbox and the real module path cleanly. During elaboration I made the
`IsGenericPoint` ambient type explicit; otherwise Lean tried to infer a
quotient topology before unfolding the project's Point alias. This changes no
mathematical content. No statement dispute or source correction was needed.

## Second reading by NA

This is the author's second reading; the dispatch brief reserves independent
review to the maintainer and forbids starting other agents. I compared the final
signature with every sentence of the node and re-read the colimit and reducedness
interfaces. The unique-generic-point conclusion is separate from the universal
geometric-point clause, so uniqueness is genuine and no generic point is assumed
to exist. Nonemptiness is inside IrreducibleSpace. The geometric point's class is
formed using the actual Yoneda-equivalent value. The dimension clause uses the
existing stalk scalar action. The injective function applies the actual germ
cocone to the compatible global section on each chart. In particular no arbitrary
map, ordinary Zariski stalk, or residue fibre replaces the geometric stalk.
The only interface adjustment was the explicit ambient Point type noted above.
The TeX statement and proof are unchanged; only the two landed definition
citations and the Lean record are added.
