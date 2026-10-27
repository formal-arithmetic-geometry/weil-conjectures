## Worker report

Q31 states `lem-sfb-equivariant-adic-fibre-realization` in
`Sheaf.Paper.EquivariantAdicFibreRealization`, namespace
`AlgebraicGeometry.ProEtale.EquivariantAdicFibre`. All mathematical proofs are
`sorry`. Input definitions are in `EquivariantAdicFibreData`, algebraic coordinate
records in `EquivariantAdicFibreCoordinates`, sheaf comparison records in
`EquivariantAdicFibreRealizationData`, and naturality records in
`EquivariantAdicFibreNaturalityData`. All definitions, module structures, topologies,
projections, coefficient maps, and canonical comparison arrows have real data.
The original node statement and proof are unchanged. The delivery adds the five
definition nodes described below and cites the recorded continuous profinite-action
definition.

The source was read in Bhatt--Scholze, *The pro-etale topology for schemes*,
Lemma 4.2.12, Definition 6.8.1, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),
and the node's twelve-step equivariant expansion. Proposition 6.8.4(1) leaves its
proof to the reader; the node supplies the projection and equivariance refinements.

Hypotheses, in order:

- Prime ell and the finite norm-topological extension are `(l : ℕ) [Fact l.Prime]`,
  `[NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `Integers l E` is exactly `Padic.coefficientExtensionIntegers l E` with its induced
  norm topology. The uniformizer, powers of its ideal, quotient rings and transition
  homomorphisms are the recorded Padic constructions, not new coefficient rings.
- `B X : Scheme.{u}`, `u : X ⟶ B`, `[WeaklyEtale u]` encode precisely an object
  of the small pro-etale site, with no extra qcqs, connectedness or nonemptiness.
- `G : Profinite.{u}`, `[Group G] [IsTopologicalGroup G]` is a profinite group.
  `a : ProfiniteCoefficientAction X G` uses the recorded action on the whole
  parameter scheme `coefficientParameter X G`. The equality `hu` makes it an action
  over B. Its unit and multiplication laws are on all continuous parameter families.
- `Data.module` is an internal module over the actual point pullback of continuous
  A-valued functions; `Data.lisse` is the recorded `IsLisseCoefficientModule`.
- `Data.quotient`, `quotientMap`, `zero` and `cokernel` present the ACTUAL scalar
  quotients N/varpi^(n+1)N and projections. The cokernel universal property is in
  abelian sheaves, with the internal A-module structure retained. `scalar` uses the
  module action and the pulled-back constant varpi^(n+1), not an arbitrary map.
  `transition_projection` identifies the actual successive quotient maps.
- Indices are shifted: Lean n means the positive exponent n+1. `FiniteData.rank : ℕ`
  permits d=0. `tower` is the given inverse diagram; `free` identifies each given
  level, A-linearly, with `(A/varpi^(n+1))^d`. This also records its quotient-ring
  action without introducing a second carrier. `quotient` states surjectivity and
  the exact kernel varpi^(n+1)Q_(n+2) for its specified transition.
- `FiniteData.action` gives the linear actions. `continuous` says all stabilizers
  are open, equivalent to joint continuity on each discrete level. `equivariant`
  is equivariance of the given transition, element by element.
- `Level` keeps the original module and gives it exactly the discrete topology.
  `Data.finiteModel` is a section-normalized presentation of its continuous module;
  for these finite discrete modules its scheme sections are precisely the finite
  constant sheaf. These presentations spell out the given underline-Q_n notation.
  They do not assume the desired reconstruction on Q or M.
- `Data.phi`, `finiteTransition`, `finiteTransition_formula` and `phi_transition`
  record the given finite isomorphisms and their actual projection squares.
- `Data.phi_action` is the equality of the actual descent endomorphism on EVERY
  section of EVERY object of the site of X[G]. `descentEnd` is constructed using
  the two actual inverse-image composition isomorphisms and equality `hu`.
  `SectionAction` evaluates the group label through the continuous parameter
  projection; labels may vary across the test scheme. This is stronger evidence
  of equality of sheaf maps than checking only constant g, and is precisely the
  node's full descent-arrow hypothesis.

Conclusions, in order:

- `Fibre D` is Mathlib's actual `ModuleCat.sectionsSubmodule D.tower`.
  `projection D n` is the original coordinate projection. `fibreTopology` is the
  topology induced by its inclusion in the product of the discrete original levels.
- `Coordinates.finite` and `free` give finite freeness (inherited by `Algebraic`). `basis`, `compatible`,
  `coordinates`, and `coordinates_projection` give compatible bases and Q ≃ A^d
  with its specified finite reductions. `projection_surjective` and
  `projection_kernel` give the induced isomorphism Q/varpi^(n+1)Q ≃ Q_n by the
  first isomorphism theorem, using the actual projection, not an unspecified iso.
- `coordinates_homeomorph` identifies the inverse-limit topology with the norm
  product topology on A^d; `adic` gives the neighborhood basis varpi^nQ, n>0.
- `Algebraic.action` and `action_projection` specify exactly the coordinate action;
  `continuous` is its joint continuity. `Rational D` is literally E tensor_A Q,
  with `moduleTopology E`, the finite-dimensional norm topology. `rho` is an
  E-linear group representation, `rho_tensor` fixes its extension on every pure
  tensor, and `rho_continuous` is joint continuity. In finite dimensions this is
  equivalent to norm continuity into GL (matrix entries and inverses, the latter
  obtained by g ↦ g^-1). No discrete E topology or finite-image assumption is used.
- `Realization.integral` and `.rational` are the section-normalized continuous
  module presentations for Q and M. `integralIso` and `rationalIso` are internal
  coefficient-module isomorphisms on the actual scheme X. `localize` is ordinary
  extension of scalars along the actual coefficient inclusion A → E. By Lemma
  6.8.2(2) and ell=unit*varpi^e it is precisely the stated N[1/varpi].
- `reduction_formula` fixes every coefficient reduction on all profinite sections;
  `reduction_normalization` says its composite with the integral isomorphism is
  exactly u^*(quotientMap n) followed by the prescribed phi_n.
- `integral_action` and `rational_action` assert the actual descent-arrow formula
  over the whole parameter scheme X[G], with the coordinate action and rho.
- `inclusion_formula` fixes q ↦ 1 tensor q on all sections.
  `localization_normalization` is the actual extension-of-scalars unit square,
  with the underlying-sheaf comparison isomorphisms written explicitly.
- `exists_realization` states all these conclusions simultaneously.
- `Morphism` encodes the compatible finite-data morphism over a pro-etale refinement
  r:X'→X and arbitrary continuous group homomorphism gamma:G'→G; it includes the
  actual finite quotient squares and equivariance of the scheme action.
  `realization_natural` supplies `Naturality`: the induced Q-map fixed on every
  projection, its tensor-extended M-map, continuity, equivariance, continuous-section
  maps and the two actual inverse-image naturality squares. Identity refinements
  are included. Ranks need not agree and gamma need not be onto.
- `compatible_bases_conjugate` quantifies over EVERY second compatible finite basis,
  lifts its change matrix to A and then E, and states both conjugacy equations.
  `realization_independent` gives the identity-on-continuous-sections isomorphisms
  between any two presentations and their comparison squares. The descent formulas
  make these isomorphisms equivariant, including for variable group labels.

The internal inverse-image functor used in the signatures is the existing
`cartesianCoefficientLift`. The recorded `cartesianCoefficientPullbackIso` identifies
it canonically with `CondensedRing.upperStar`. This spelling retains the actual
underlying abelian inverse image. `liftUnderlying`, `pointUnderlying`, `pointComp`
and `pullIso` use these existing functors and canonical composition comparisons.
No arbitrary comparison or assumed Cartesian isomorphism has been substituted.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`; and its construction module
  `CoefficientExtension`: `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`, `coefficientExtensionTransition`.
- Mathlib's `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `profiniteToProEtOf`, `condensedRingObj`, `upperStarFromPoint`,
  `upperStarFromPointComp`, `condensedPullbackHom`.
- Mathlib's `CategoryTheory.Mod` and its monoidal inverse-image and scalar-extension
  functors, `ModuleCat.sectionsSubmodule`, linear equivalences and tensor product.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, its underlying
  `continuousMapRingObjOfUniverse` and recorded monoid structure.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `continuousMapRingObjMapOfUniverse`, `isMonHom_continuousMapRingObjMapOfUniverse`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.IsLisseCoefficientModule` (finite locally free, including rank 0).
- `Sheaf.Paper.ProfiniteCoefficientLinearization`:
  `ProfiniteCoefficientAction`, `coefficientParameter`, `coefficientParameterProjection`,
  `profiniteTestProjection`, `coefficientParameterMap`; the full parameter scheme
  interface is reused, not privately redeclared.
- `Sheaf.Paper.CartesianCoefficients`: `cartesianCoefficientLift` and
  `cartesianCoefficientPullbackIso`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleFunctor` and `sectionRings` for the
  exact existing section scalar action.

The modules of recorded proof dependencies are imported plainly: integer tower,
pro-etale object restriction, Cartesian coefficients, exact localized restriction,
finite constants, continuous coefficient realization, integral completeness,
coefficient limit, point pullback and localization. The DVR construction is already
in the coefficient import chain. The valued-DVR finite-quotients node currently
has no recorded module, so no fictitious import is supplied.

Edge cases checked before and after writing: d=0 has empty coordinate bases and
zero Q and M; X=empty does not force d=0 and all scheme comparisons remain valid;
G trivial; n=0 means the first nonzero exponent, and no A/varpi^0 is mistakenly
used as the first free level; non-qcqs/nonconnected B is unrestricted; ramified
E uses its own uniformizer, not ell as a uniformizer; an infinite-image rank-1
character is allowed. Identity refinements, non-surjective continuous group maps,
and different ranks on source and target are retained. The positive-exponent
ideal basis also works for the zero module.

Searches for the item: LeanFinder on the finite-free equivariant adic realization
statement gave only general condensed/free objects; Loogle on
`Module.Free, Module.Finite, Profinite, MulAction` gave 0 hits; Mathlib grep
`inverseLimit|IsAdic|adicTopology|ContinuousSMul` in `Topology/Algebra` found the
standard topology primitives, no such theorem. LeanSearch on reconstruction of
an inverse system of finite free DVR-quotient modules gave AdicCompletion and
SheafOfModules.ιFree, not the prescribed finite charts and descent realization.
`rg` on `lean/WeilConjectures`, `lean/Sheaf`, and the item's blueprint tag found
no exact statement. `Sheaf.Paper.NormalizedTowerFree` gives finite freeness only;
`TameRootTowerExtension` is a specialized downstream consumer. Neither replaces
this node. New-definition searches are recorded verbatim in its JSON.

No statement correction or unresolved mathematical dispute is asserted.

Validation: all six delivered modules compiled cleanly through the prescribed
`scompile.py` wrapper, separately in dependency order, with the default 60-second
per-file limit and no unexpected warning. Diagnostic probes and diagnostic options
were removed. Only `lean` and additions to `stmt_deps` change in the original node.

## New nodes

`def-sfb-continuous-module-section-model`, module
`Sheaf.Paper.ContinuousModuleSectionModel`, defines the presentation of C(-,V)
as an internal module for a topological coefficient ring, together with the actual
scheme pullback charts normalized by the point adjunction. It reuses the existing
continuous ring, internal-module and sectionwise-module definitions and the
canonical point inverse image. Source: BS Lemma 4.2.12, Definition 6.8.1,
Proposition 6.8.4(1). LeanSearch and LeanFinder found `ContinuousMap.module'`
and topological module categories, which supply the scalar operations but no such
internal/scheme presentation; Mathlib Condensed grep gave 0 hits. DAG and project
searches found `ContinuousRepresentation.Realization`, which is specifically a
normed-field representation with profinite action, and a general internal-to-section
encoding. Neither defines integral coefficient presentations or normalized scheme
charts. Those existing primitives are reused. The new node asserts no existence
for arbitrary topological modules and introduces no postponed theorem.

`def-sfb-equivariant-adic-fibre-data`, module `Sheaf.Paper.EquivariantAdicFibreData`,
defines the finite tower and its discrete continuous actions, the actual compatible
sections Q with its inverse-limit topology, E tensor Q, the actual scalar-cokernel
sheaf data, full parameter descent, and compatible finite-data morphisms over
refinements. It reuses the recorded DVR rings, continuous coefficients, internal
modules and profinite actions. The topological additive-group fact is a named
construction theorem with its complete proof docstring. Source: steps 1--12 of the
item's BS 6.8 equivariant expansion. LeanSearch, LeanFinder, Mathlib grep, blueprint
search and both project Lean trees have no such combined data definition. Standard
compatible sections and scalar extension are reused, never replaced by chosen objects.

`def-sfb-equivariant-adic-fibre-realization-data`, module
`Sheaf.Paper.EquivariantAdicFibreRealizationData`, defines what the normalized
actual sheaf comparisons mean, using the separate algebraic coordinate data. It asserts no existence. The same three searches cover both the
input and normalized-comparison data, and their raw results are in each node.
There is no exact definition in the DAG or Lean trees; the existing finite-freeness
and continuous representation results lack the projection and actual slice data.
These modules separate the input data, the meaning of a realization, and the
reconstruction theorem. Smaller inherited records retain every original field.

`def-sfb-equivariant-adic-fibre-naturality-data`, module
`Sheaf.Paper.EquivariantAdicFibreNaturalityData`, defines the continuous equivariant
linear maps and the two actual sheaf naturality squares for a compatible finite-data
morphism. This is a separate definition of a morphism comparison, with no existence
claim. The recorded searches for finite-fibre and normalized-comparison data find
no existing such naturality record. Source: the item's expansion steps 10--11.

`def-sfb-equivariant-adic-fibre-coordinates`, module
`Sheaf.Paper.EquivariantAdicFibreCoordinates`, defines the projection-normalized
compatible bases, topology and coordinate actions, and the continuous equivariant
maps on Q and E tensor Q that represent a compatible finite-data morphism. It
asserts no existence. The same recorded three searches find general adic completion
and discrete condensed modules, but no such combined normalized-coordinate data.
The source is the item's equivariant expansion steps 1--5 and 10--12. This separates
the algebraic coordinate notion from the actual sheaf comparison notion; it changes
no field of the requested conclusions.

## Second reading by Q31

I reread the original node, all six modules, the source passages, and the declaration
signatures clause by clause. This is a self-review: the dispatcher instruction
explicitly forbids starting other agents, so I do not claim an independent worker
review. The maintainer's independent review remains required.

The rereading checked full parameter descent, the actual quotient projections,
localization-unit normalization, rank zero, empty schemes, infinite-image actions,
and refinement naturality. Canonical underlying-sheaf comparison arrows were made
explicit to avoid expensive definitional unfolding; this changes no mathematical
objects or hypotheses. All field and universe parameters are bound explicitly and
autoImplicit is disabled. No private notation or file-local instance is used.
