## Worker report

The delivery states `AlgebraicGeometry.exists_nodal_multidegreeZero_openSubgroup` in
`Sheaf.AlgebraicGeometry.NodalMultidegreeZeroLocus`. There is one named theorem, with
`by sorry`, and no new definition, axiom or additional postponed helper theorem.
The original node is unchanged except for its Lean record.

Source checked: Deligne, Le lemme de Gabber, Astérisque 127 (1985), §2, printed
pp.135--136, specifically the paragraph on p.136 following the stable-family
extension at the foot of p.135. The Numdam primary PDF is
https://www.numdam.org/item/AST_1985__127__131_0.pdf (PDF page 7, counting its cover).
It constructs the open subgroup of componentwise degree-zero lines and says it
is separated and smooth of finite type. The node extracts openness,
quasi-compactness and separatedness. The PDF page offset explains the node's
p.135 reference; no statement correction is needed.

Clause-by-clause correspondence:

- The node's actual base S is `X.base.left`, with
  `[IsLocallyNoetherian X.base.left]`. The recorded `StablePointedModuli B g 0`
  gives the family `X.projection : X.curve ⟶ X.base.left`. The auxiliary B is
  merely the ambient scheme over which S is presented. Every S in the node is
  admitted by taking B = S and the identity structural map. Conversely the
  conclusion only concerns S and the stated family, so no assumption on B is used.
- Stability and genus at least two are the fields `X.stable`, `X.genus`, and
  `X.genus_at_least_two` of the dependency's actual structure. The label count 0
  makes the family unpointed. The geometric genus is the recorded dimension of
  degree-one `RingedSpace.moduleCohomology`, not an independent integer parameter.
- `P : AlgebraicSpace X.base.left` is a genuine fppf algebraic space. Its section
  sets lie in Type u; the existing Picard sheaf lies in Type (u+1). The natural
  isomorphism `e : P.obj.obj ⋙ uliftFunctor ≅ (picardFunctor X.projection).obj`
  is the representing identification, with no equality imposed on universes.
  It transports the canonical Picard group law to the representing space.
- The conclusion chooses an algebraic space D and a natural morphism `j : D ⟶ P`.
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom` means
  exactly that this inclusion is represented by open immersions on all scheme
  tests. Such a map of sheaves is a monomorphism, so its pointwise ranges specify
  the intended subfunctor rather than an unrelated surjection onto it.
- For every `T : Over X.base.left`, the existential `K : Subgroup
  ((picardFunctorGrp X.projection).obj (op T))` has membership precisely the
  inverse image of the range of j under e. Thus D is closed under the canonical
  tensor product, identity and inverse on every test scheme. Naturality of j
  and e supplies pullback compatibility. Together with the open inclusion this
  says open subgroup algebraic space, without assuming an arbitrary group law.
- The last equivalence quantifies over EVERY test scheme T and EVERY actual
  invertible `L : (pullback X.projection T.hom).Modules`. Its Picard class is
  `toPicardFunctor` applied to `Scheme.Pic.ofIsInvertible L`; `e.inv` followed
  by `.down` views that class as a point of P. Membership in the range of j is
  equivalent to degree zero on all geometric fibre components.
- For every algebraically closed Ω and `a : Spec Ω ⟶ T.left`, the geometric
  fibre is `pullback (pullback.snd X.projection T.hom) a`. The quantifier Z
  runs over its actual `irreducibleComponents`. The normalized scheme is
  `(fibre.reducedNormalizationComponent Z).normalization` and its canonical
  map is `fibre.normalizedComponentMap Z`. The tensor pullback along this map
  composed with the fibre's first projection restricts L to this normalization.
  The explicit `Scheme.Over` instance uses the same normalization map composed
  with the fibre's second projection, so all degrees are over Ω.
- `Scheme.Modules.degree` is the existing definition χ(L) − χ(O) from
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`. Its χ is the existing
  alternating sum of finite dimensions of coherent cohomology. We reuse this
  degree and do not introduce another Euler characteristic or cohomology
  definition. Its underlying H-based presentation is the project's existing
  degree convention; the recorded module-cohomology functor is also used by the
  dependency's stable-genus field. These are the established two cohomology
  presentations, with the comparison a library-level matter.
- Independence of local representative is included by the equivalence for every
  T and L: two representatives with equal Picard-sheaf class have identical
  left sides, hence identical multidegree-zero conditions. General Picard
  sections admit such representatives fppf locally by the sheafification
  defining `picardFunctor`. Since D and P are sheaves, their open inclusion
  and this local characterization specify exactly D(T), including classes that
  have no global representative. No global representability of a class is assumed.
- `IsQuasiCompactPresheafMap (terminal.from D.obj.obj)` is relative
  quasi-compactness over S via quasi-compact étale atlases on affine tests.
  `IsSeparatedPresheafMap (terminal.from D.obj.obj)` means representability of
  the relative diagonal by closed immersions. Neither is absolute compactness
  of the total space or a separation condition on P.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  `AlgebraicGeometry.StablePointedModuli`, including its full signature and fields.
- WeilConjectures.AlgebraicGeometry.Picard.Defs: `picardFunctor`,
  `toPicardFunctor`; upstream is recorded in sk-def-picard-pic's closed audit.
- WeilConjectures.AlgebraicGeometry.Picard.Group: `picardFunctorGrp` and
  `Scheme.Pic.ofIsInvertible`, using its canonical tensor group law.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith` (scheme tests and actual pullback squares).
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: `Scheme.Modules.IsInvertible`.
- Sheaf.AlgebraicGeometry.ReducedNormalization: `Scheme.reducedNormalizationComponent`;
  Sheaf.AlgebraicGeometry.StablePointedCurve: `Scheme.normalizedComponentMap`.
- WeilConjectures.Topology.RingedSpaceModuleCohomology: `RingedSpace.moduleCohomology`.
- WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar: `Scheme.Modules.degree`,
  with `Scheme.Modules.eulerChar` and `finrankH` read in Cohomology.Defs.
- WeilConjectures.AlgebraicGeometry.TensorPullback: `Scheme.Modules.tensorPullback`.
- Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal: `IsQuasiCompactPresheafMap`,
  `IsSeparatedPresheafMap` and its canonical relative diagonal construction.

The module imports every recorded available proof dependency (privately unless
needed in the statement). The seven-step docstring carries the node's complete
argument. Unstated proof nodes do not require restating them for stage 2.

Edge cases checked before writing: empty bases and empty test schemes are admitted;
there are no Nonempty assumptions on them. The geometric condition is universally
quantified and vacuous on an empty test, as required. The zero marking set is Fin 0;
no marked point is invented. Genus g = 0 and g = 1 are excluded by the original
stable genus-at-least-two structure, not by extra hypotheses. Reducible geometric
fibres, self-nodes and arbitrary characteristic are all admitted. Every geometric
component is tested, not only the total degree; normalization uses the reduced
component and not normalization of the possibly reducible whole fibre. Test bases
are arbitrary schemes, including nonreduced and non-Noetherian schemes. Ω lives
in the schemes' universe u, with the same size convention as the stable-family
interface; no independent smaller universe makes the geometric tests vacuous.
The universe lift of section sets is retained explicitly.

Searches for an existing statement (all done before writing):

- msearch leanfinder: "The multidegree zero relative Picard functor of a stable
  nodal curve is an open quasi compact separated subgroup algebraic space".
  Eight unrelated affine-space/projective-spectrum hits; no matching theorem.
- msearch loogle: "picardFunctor, IsAlgebraicSpace, multidegree".
  Zero hits; unknown identifier picardFunctor.
- msearch grep: "multidegree|Multidegree|picardFunctor", AlgebraicGeometry.
  Zero Mathlib matches.
- msearch leansearch: "The multidegree zero locus in the relative Picard algebraic
  space is open quasi compact separated". Eight unrelated Proj/zero-locus results.
- rg over lean/WeilConjectures and lean/Sheaf for multidegree, Multidegree,
  normalizedComponent and componentDegree. Found normalized-component maps,
  BalancedNodalTrait.componentDegree and the normalized-component ample criterion,
  but no theorem about the relative Picard multidegree-zero open subgroup.
- grep of the item id in lean/WeilConjectures found no declaration.
- Exact proposed-name rg found no prior declaration. The current blueprint was
  searched for multidegree/Gabber; no separate matching statement was found.

There is no STATEMENT-DISPUTED issue, statement correction, new node or dependency
repair. The only initial elaboration issue was Lean inferring the category of a
nested pullback as Type; explicit `(C := Scheme.{u})` resolves it without changing
universes or hypotheses. Long lines were reflowed after the first successful
elaboration. Final server compile and delivery preflight are recorded below.

## Second reading by Q05

The dispatcher's instruction forbids starting other agents. This is a separate
worker clause audit, not a claim of an independent agent's review; the maintainer
performs the independent delivery review. Reread the node and the final module
side by side. Verified the actual base X.base.left, the genus/stability fields,
unpointedness, the natural representing isomorphism with the explicit size lift,
all geometric components and canonical normalization maps, the structural Ω-map
used in the degree, open immersion on all tests, the canonical pointwise Picard
subgroups, and the relative quasi-compactness and separation predicates. Checked
that the representative equivalence is for every T and line, so fppf-local
representatives and non-globally-representable classes are covered by the sheaf
condition. No mathematical mismatch was found; only explicit category arguments
and line wrapping changed during compilation.

Validation: prescribed scompile.py completed both sandbox and library checks with
exit code 0 and no warnings. The required deliver2.py --no-push passed server
preflight and compilation, printing OK (dry run) for commit e4ccee5550e.
