## Worker report

The module `Sheaf.Paper.SystemTensorPresentationIdentification` states
`WeilConjectures.SystemTensorMate.tensorPresentationIdentification`. Its two postponed statements are `tensorPresentationIdentification` and
`Realization.properOpenFactors`, both clauses of this same DAG node. The helper `TensorPresentationComparison` records the actual
natural isomorphisms and their normalization equations, rather than assuming those
equations as hypotheses. The main theorem starts from the actual
`SemilinearDerivedSectionsData` on every scheme, and concludes the existence of
a diagram package identified with that datum and with any supplied normalized
`TensorOperations`. The second theorem explicitly transports the proper/open
realization factors across the coefficient universe lift. No arbitrary maps, free propositions, or extra
flatness assumptions replace the canonical constructions.

Sources read: sites-cohomology.tex, equation-projection-formula-map (0B56), and
lemma-j-shriek-and-tensor (0GL1); sites-modules.tex,
lemma-j-shriek-and-tensor (0E8I). These give the two arrow normalizations; as the
node explains, the presentation comparison itself is the explicit nine-step
argument in its proof, reproduced in the theorem docstring.

Clause-by-clause rendering:

- The prime is `l : ℕ` with `[Fact l.Prime]`. The coefficient extension is
  `E : Type (u + 1)` with `[Field E] [Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]`. These are the actual recorded coefficient
  extension and chosen uniformizer, not a new abstract ring tower.
- Schemes are `Scheme.{u}`. The original small pro-etale site has object universe
  `u+1` and morphism universe `u`; no equality of these universes is imposed.
  The coefficient universe `u+1` accommodates both the site and coefficient ring;
  `D l E W` uses the standard derived universe `u+2`. This implements the recorded
  size convention in the existing APIs.
- The strict systems are the recorded `SemilinearSections.Systems` for
  `integralCoefficientCommRingSheaf l E W` and
  `coefficientSequenceCommRingTransition l E W`. Those definitions already realize
  strict semilinear systems as module sheaves on the vertical site. In particular
  the horizontal module-presheaf restriction is the actual quotient-semilinear
  transition; morphisms commute with it by module-presheaf naturality. There is
  no second definition of strict systems in this delivery.
- The positive level `n` is sequence index `n-1`: in the recorded ring at index
  `a`, the exponent is `a+1`. `presentationReindexing` has source the dependency's
  `DS` and target the diagram `D l E W`. They unfold to the same published module
  category localization, so the section-preserving reindexing is literally
  `CategoryTheory.Equivalence.refl`. Its functor and inverse keep every section,
  transition and morphism unchanged. This is not a choice of some equivalence.
- `o.P`, `pushDerived`, `o.J`, `o.derivedAdj`, and `o.derivedOpenAdj` are the recorded
  simultaneous exact pullback, total right derived direct image, exact open
  extension and canonical derived adjunctions. `TensorOperations.model` retains
  the ordinary and signed-total-representative normalization; `ordinary_unit`
  retains the adjunction transpose of the sectionwise lax tensor map.
- `TensorPresentationComparison.pull` gives `C_X P ≅ P_diag C_Y`, written in Lean
  functor composition order as `o.P f ⋙ C_X ≅ C_Y ⋙ d.P f`.
  `extension` is the analogous `j_!` comparison. Direct image is the same specified
  sectionwise functor and its same chosen right derived functor in this shared
  encoding: `presentationDirectComparison` explicitly inserts the two identity
  unitors to give `pushDerived f ⋙ C_Y ≅ C_X ⋙ pushDerived f`.
- `tensor` gives the natural comparison `o.T W ⋙ C_W ≅ (C_W.prod C_W) ⋙ d.T W`.
  `tensor_model` fixes it to the inverse source K-flat total-model isomorphism
  followed by the target model isomorphism, for every pair of K-flat complexes.
  Thus neither a sign twist nor an unrelated tensor isomorphism is possible.
- `unit` and `counit` are the two equations identifying the specified pullback/
  direct-image adjunctions. The direct-image identity comparison disappears
  definitionally from these equations. `open_unit` and `open_counit` identify
  the specified open adjunctions. The open unit itself has the section
  normalization and invertibility established in the recorded arrow module.
- `composition` compares the two canonical `pComp` maps for every pair of
  composable scheme maps. These are localized ordinary adjunction conjugates
  of the section-normalized direct-image compositor, not additional supplied
  compositors. The quantification includes identity maps and the two paths of
  a commutative square.
- `mu` is the commuting square comparing the specified `o.mu f` and `d.mu f`
  after the tensor and pullback comparisons. The two input slots are arbitrary
  `M N : D l E Y`.
- `projection` identifies `o.projection f H Q` with `d.projection f H Q`, with
  its target transported by tensor and pullback. These are exactly the
  `TensorOperations.projection` maps whose definitions are the adjunction
  transpose of `mu` followed by counit tensor identity, as in
  `def-exchange-projection`. There is no invertibility assertion for projection.
- `delta` identifies the canonical open tensor isomorphisms.
  `delta_inverse` also records the inverse-arrow equality. `deltaInv` is the
  published open-adjunction transpose of open-unit tensor identity followed
  by `mu.inv`; `delta` is its inverse using the published invertibility theorem.
- The source operations are now the actual `PresentationSections` datum `a`.
  `SemilinearPresentationComparison.systems` identifies its tensor calculus.
  `.geometric` applies `SemilinearDerivedSectionsData.geometric` to the actual
  pro-etale topos adjunction, with its actual inverse-image coefficients.
  `GeometricPresentationComparison.coefficients` supplies the canonical
  inverse-image coefficient isomorphism; `coefficient_unit` fixes it by the
  underlying set-sheaf adjunction unit and the diagram constant-section map.
  `coefficient_transition` preserves all quotient maps. `ringIso_sections`
  assembles exactly these coefficient maps on the vertical site. Pullback and
  direct image are compared after the actual `resD ringIso.inv`, not a free
  equivalence. The two tensor comparisons include `targetModel`, `target_pure`
  and `source_model`, retaining signed K-flat representatives. `unit`, `counit`,
  `mu` and `projection` identify the actual geometric operations.
- `OpenPresentationComparison` identifies the actual `a.localization` extension.
  `slice` reindexes along the published `ProEt.sliceTo`; `sections`, `maps` and
  `transitions` retain its underlying groups, morphisms and quotient-semilinear
  maps. `restriction` identifies actual slice restriction, and `extension` with
  `unit` fixes the open extension by its ordinary adjunction. Exact termwise
  descent gives the open comparisons subsequently compared to `d`.
- The final 'in particular' clause is stated by `Realization.properOpenFactors`
  and its `Realization.Comparison`. This uses the precise published realization
  interface with `E : Type u`, not an imagined specialization of the diagram
  operations. `liftedField E = ULift.{u+1} E` changes only the coefficient-field
  universe. `integers`, `quotients` and `representatives` fix the ring transport
  by identity on field elements and quotient representatives. `rings` and
  `constants` fix its sheafification on every constant section. The ordinary
  functor is restriction of scalars along the inverse ring isomorphism and the
  derived functor is termwise `resD`; `equivalence` asserts its equivalence.
  `chain`, `generators`, `kflat` and `tensor_model` normalize the signed total
  transport against the two published representative models, using their own
  coefficient-universe parameters. No arbitrary tensorator is accepted.
  `pull`, `push`, `extension`, `unit` and `open_unit` identify the actual
  realization adjoints. `mu` explicitly names `pullbackTensorSystemComparison`.
  `projection` explicitly names `IntegralSystemRealization.properProjection`;
  `delta` names the supplied `OpenComparisons.projection`; `tensor` names
  `(calculus l E W).systemClosed.tensor`; `composition` and `square` name
  `c.pullComp` and `c.square`, with their inverse orientations relative to
  `d.pComp` and `d.square`. For the theorem `properOpenProjectionMateSystems`,
  instantiate `c := z.compositors`, `OpenComparisons := z.openComparisons`.
  These equations apply to every factor in its displayed system identity,
  including both square paths. Their naturality compares tensor maps as well
  as objects; no faithfulness of evaluation is invoked.
- All comparison equations are morphism equalities on `D l E W` itself. No
  evaluation is applied. There are no normalized/cartesian input predicates,
  flat coefficient transitions, coefficient-flat modules, finite Tor intervals,
  or bounded cohomological intervals among the binders.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports the actual
  `Padic.coefficientExtensionRing`, chosen integer ring/uniformizer and
  `Padic.coefficientExtensionTransition`; its recorded primary declaration is
  `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, `AdjunctionEvaluation`, `evaluation_mate`;
  the reexported `Systems`, `DS`, `TensorComparisonModel`, `Data`, `Geometry`.
- `Sheaf.Paper.SystemTensorMateArrows`:
  `WeilConjectures.SystemTensorMate.R`, `S`, `D`, `Operations`, `TensorOperations`,
  `direct`, `pushDerived`, `Operations.P`, `Operations.J`, `Operations.T`,
  `Operations.derivedAdj`, `Operations.derivedOpenAdj`, `Operations.pComp`,
  `TensorOperations.projection`, `deltaInv`, `delta`.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization`, and its `Operations`/`Assertion`
  signatures, especially the `gamma_inverse` equation for arbitrary systems.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`:
  `AlgebraicGeometry.ProEtale.properOpenProjectionMate` and
  `WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems`;
  the latter's tensor/projection/open-comparison factors are the application.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and
  `compactificationProjectionFromData`, with the counit-defined projection word.
- The size-convention node is metatheoretic and has no declaration; explicit
  universes and the published standard localization implement it.
- Proof imports also include the recorded exact-monoidal total/K-flat theorem,
  cochain-model rigidity, exact-postcomposition K-injective descent,
  right-derived functor, semilinear operation existence, geometric-derived
  interface, cochain sheaf tensor, localization and adjunction-mate modules.

Edge cases checked: index zero gives exponent one, never the zero quotient
exponent; arbitrary prime including 2; empty scheme and zero input objects;
identity scheme maps, identity open immersion and empty open; arbitrary
noncartesian systems, nonflat quotient transitions, complexes unbounded in both
directions. None requires an excluded case or an additional hypothesis.
The comparison to any diagram package includes the case of the chosen source
package itself; the geometric datum is never replaced by an arbitrary package.
The coefficient universe transport leaves scheme universe u, site object
universe u+1 and morphism universe u unchanged, including identity maps and
all arbitrary unbounded inputs in the realization interface.

Searches actually run (2026-10-23):

- `msearch.py leanfinder`, query 'Equivalence strict semilinear coefficient
  systems ringed sequence site derived tensor projection operation comparison':
  eight hits about sheaf presentations and light condensed projectivity;
  none identifies these strict-system presentations or arrows.
- `msearch.py loogle`, query 'SheafOfModules, DerivedCategory, Equivalence':
  zero hits.
- `msearch.py grep`, query
  `semilinear.*(system|diagram)|system.*tensor|tensor.*system` in
  `Mathlib/CategoryTheory`: zero hits.
- `msearch.py leansearch`, query 'Strict coefficient system derived category
  equivalence tensor pullback projection normalization': eight hits including
  `SheafOfModules.pullbackComp`, unrelated derived truncation and free-monoidal
  normalization; no matching theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for presentation-identification names, the node
  id, and tensor-presentation names: only unrelated affine tensor presentations
  and a private K-flat scalar comparison helper. Read the actual semilinear
  system and system-arrow modules by their dependency-recorded names.

Repair searches additionally run:

- `msearch.py leanfinder`, query 'Derived strict semilinear coefficient systems
  canonical tensor presentation comparison under a coefficient universe lift':
  eight hits about algebra/module presentations and tensor relations, none
  comparing these strict-system calculi.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.leftAdjointUniq`:
  twelve hits in Mathlib's adjunction-uniqueness API; the generic uniqueness
  construction is already used by the recorded operation definitions.
- `msearch.py grep`, query `semilinear.*presentation|presentation.*semilinear`
  in `CategoryTheory`: zero hits.
- Read the recorded `SemilinearSystemModels.Models` and `TensorComparisonModel`,
  `CoefficientTensorModels.iso`, `pullbackTensorSystemModel`,
  `IntegralSystemRealization.Compositors` and
  `OpenComparisons`, and the entire displayed signature of
  `properOpenProjectionMateSystems`. This exposed the coefficient-model universe
  mismatch, now addressed by the explicit chain and localization equations.

The new definition node `def-pur-proetale-slice-to` records the existing canonical
`ProEt.sliceTo` construction. It replaces the previously added theorem dependency
`lem-weil-proetale-weakly-etale-localization`; no invocation or choice of that
theorem is needed. No dependency repair, statement correction or disputed
statement is introduced.
The compact-object example module is now a withdrawn stub; its node points to the
upstream definition, which was read together with the stage-2 format instructions.


## Repair of the independent return

H3(a): the source is now `a : ∀ W, PresentationSections W`. Its actual
`.geometric` Geometry and `.localization` OpenSystems appear in the conclusion.
The geometric coefficient change is fixed by the topos-unit equation, quotient
transitions and assembled ring components; all operations are transported along
that ring isomorphism. The original identity reindexing, adjunction-unit and
K-flat-model pins are retained.

H3(b): `Realization.properOpenFactors` supplies the missing application to the
precise realization factors. The field is explicitly lifted from Type u to
Type (u+1), and the canonical quotient/sheaf coefficient transport is normalized
on representatives and constants. The equations name every factor requested
by the return, including the square and its orientation. The node's mathematical
statement is unchanged; no case is removed by a size restriction.

This is the dispatched worker's self-check. The maintainer's independent reading
of the delivery remains the stage-2 review; no independent second reader is
claimed here.


Validation: the saved packet's initial `deliver2.py --no-push` passed at
`b25cb38b339`; it was retained and then changed to repair both mathematical
return points. Intermediate compiles exposed an incorrect model-type coercion
and expensive unfolding; the final formulation uses the two published models
with their original universes and explicit representative/localization equations.
Only named theorems have `sorry`; all helper definitions have complete data.


## New nodes

`def-pur-proetale-slice-to` records the existing definition
`AlgebraicGeometry.Scheme.ProEt.sliceTo` in
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, with `existing: true`.
Its binders `X : Scheme.{u}` and `W : X.ProEt` give precisely a scheme and a
weakly etale object. Its source `Over W` is the category of triangles over W,
and its target `W.left.ProEt` is the small pro-etale category of W. The body
`ProEt.mk T.hom.left` retains the structural arrow to W; `homMk f.left.left`
retains the same underlying scheme morphism. The permanence proof is already
provided by the published definition, whose real data are reused verbatim.
Sources read: Stacks Sites Section 00XZ and More on Morphisms Lemma 0951.
The node cites the recorded site definition and localized-site definition.
It claims no sheaf equivalence or coefficient comparison.

The exact-name DAG search finds the auxiliary declaration only in the larger
localization theorem node, not a node defining this plain functor. The return
explicitly requires this separate definition record. Blueprint searches for
`pro-etale slice` and `sliceTo` return zero matches. LeanSearch returns eight
related generic fiber/slice/site declarations; Loogle returns zero hits and an
unknown identifier for the project declaration; Mathlib grep returns zero.
Project grep locates the exact definition and its consumers, with no competing
upstream definition. Raw msearch output is retained in `mathlib_searches`.
The blueprint ancestor is `prop-pur-adic-reconstruction-trace-coherence`; the
new node serves its open-localization comparison along the item's existing via.

Edge cases: the functor applies to every pro-etale object, including the empty
scheme, the identity object and objects not given by open immersions. Its maps
are the underlying scheme maps, including identities and composites. Universes
are those of the existing source declaration; no new size hypothesis is added.

## Repair of return L at 247b1fa74a90

H2 is repaired by replacing the added theorem dependency with the new definition
node `def-pur-proetale-slice-to`, carrying the exact existing `ProEt.sliceTo`
record above. The Lean source stays identical, as the return permits. The
previously accepted H3(a)/(b) repairs, mathematical statement, docstrings and
clause-by-clause report are retained. Comparison with current main found only
the item's `lean` and the additional dependency differing before this repair;
the delivery wrapper rebases the retained packet on current main.

Self-check: the new node's statement matches the source signature and both body
fields; the item uses this functor in `OpenPresentationComparison.sections`,
`.maps` and `.transitions`. Its public import already exposes that exact module.
No added assumption, conclusion, proof or module is needed for this correction.
The saved packet first passed `deliver2.py --no-push` at `f426b02bd51`; this H2
repair is a concrete node/report change, not an unchanged re-push.

Validation after H2 repair: `scompile.py` compiled the retained module with no
errors or warnings. The first repaired dry run required the current node-schema
field `import_flags`; the new definition node now supplies the empty list.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
