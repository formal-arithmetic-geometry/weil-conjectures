## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentRankOnePropertyIdeals` states
`AlgebraicGeometry.Scheme.Modules.coherent_rank_one_property_ideals` with `sorry`.
It introduces no definitions or helper theorems. The node is unchanged except for `lean`.
The source is Stacks Project `coherent.tex`, Tag 01YH,
`lemma-property-irreducible`, third and fourth proof paragraphs. I read the full
lemma and proof: the first nonzero ideal is extracted from the rank-one witness;
two comparison sequences then transfer the property to every nonzero ideal.
The node already isolates the previously established small-support hypothesis
and explicitly includes the zero case.

Hypothesis and conclusion correspondence:

- The scheme X is `X : Scheme.{u}`. `[IsNoetherian X]` is exactly locally
  Noetherian plus quasi-compact: Mathlib's class extends `IsLocallyNoetherian X`
  and `CompactSpace X`, rather than just assuming the underlying space Noetherian.
- The integral closed immersion is `Z : Scheme.{u}`, `i : Z ⟶ X`,
  `[IsClosedImmersion i]`, `[IsIntegral Z]`.
- The generic point eta is Mathlib's `genericPoint Z`, which exists and is unique
  for this nonempty integral scheme. T is written as `Set.range i.base` throughout,
  and xi is written as `i.base (genericPoint Z)` throughout. These are substitutions
  for the node's introduced names, with no additional hypothesis on a chosen point.
- Support is literally `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`.
  A module is zero exactly when its carrier is subsingleton. This is the existing
  stalk carrier underlying `RingedSpace.moduleStalkFunctor`, with its actual
  structure-ring action, rather than a new support or stalk definition.
- `P : X.Modules → Prop` represents the property. Its values away from coherent
  modules supported in T are immaterial: every property premise is restricted
  to that domain. The conclusion concerns coherent supported pushforwards, as
  supplied by the recorded coherent-pushforward and closed-stalk lemmas.
- Isomorphism invariance is `hiso`, restricted to coherent F,H supported in T,
  with `∀ (_ : F ≅ H), P F ↔ P H`. Thus no global isomorphism-invariance premise
  on arbitrary noncoherent modules is imposed.
- The zero hypothesis is `hzero : P (0 : X.Modules)`.
- `hshort` quantifies over `S : ShortComplex X.Modules` with `S.ShortExact`,
  requires coherence and support in T separately for all three terms, and has
  all three implications: `(P S.X₁ ∧ P S.X₂) → P S.X₃`,
  `(P S.X₁ ∧ P S.X₃) → P S.X₂`, and
  `(P S.X₂ ∧ P S.X₃) → P S.X₁`.
- `hsmall` quantifies over every coherent Q supported in T, with
  `Subsingleton (Q.presheaf.stalk (i.base (genericPoint Z)))`, and concludes P Q.
- `hG` existentially quantifies a witness G, requiring coherence, support equal
  to T (equality, not mere inclusion), and P G.
- The witness's annihilator clause quantifies over each a in
  `IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z)))`
  and each v in its module stalk, requiring `a • v = 0`.
- Its one-dimensional residue-field clause existentially supplies the
  `Module (X.residueField (i.base (genericPoint Z)))` structure on the same
  module stalk. Compatibility is the equality
  `a • v = (X.residue (i.base (genericPoint Z))) a • v` for every a,v.
  `@Module.finrank ... _ _ inst = 1` explicitly uses this very structure.
  Over a field finrank one implies finite dimensionality; infinite dimensional
  spaces have finrank zero, so they cannot accidentally satisfy this premise.
- The conclusion is `∀ J : Z.IdealSheafData, P ((pushforward i).obj J.toModules)`.
  This is the canonical quasi-coherent ideal module and ordinary module
  pushforward, not ideal-image pushforward. There is no nonzero restriction.

Dependency declarations read and used (including the dependency's recorded
module imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and `IsNoetherian`.
  The convention node fixes no separate declaration; compactness is built into
  the latter class.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, as recorded by the
  irreducible-components leaf. No irreducible-component decomposition is needed
  here. `Mathlib.AlgebraicGeometry.FunctionField` publicly supplies the integral
  scheme's standard generic-point interface.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the existing `SheafOfModules`; on schemes we use `X.Modules`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, and its scheme/sheaf specialization
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`. The stalk carrier is the
  existing abelian-group presheaf stalk in both cases.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the three recorded
  coherence notions; the actual coherence predicate used is
  `WeilConjectures.AlgebraicGeometry.Coherent`:
  `AlgebraicGeometry.RingedSpace.IsCoherent` (finite type and finite-type kernels).
  A direct public import is retained because the server's published version of
  the former module did not yet publicly expose this predicate.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Scheme.residue`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, using the existing right
  adjoint `Scheme.Modules.pushforward` from `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, the kernel ideal module.

All six stated proof-dependency modules are imported without `public`:
`CoherentPushforwardIdeal.coherent_pushforward_ideal`,
`ClosedPushforwardStalks.closedImmersion_pushforward_stalks`,
`RankOneGenericIdealInclusion.rank_one_generic_ideal_inclusion`,
`CoherentKernelCokernelLocallyNoetherian.isCoherent_kernel_cokernel_biprod_and_submodule`,
`ModuleStalkExact.module_stalk_exact`, and
`IntegralIdealsCommonGenericLattice.integral_ideals_common_generic_lattice`
(with their namespace prefixes as in the DAG). Their full declarations and
proof docstrings were read. The statement's docstring follows all four DAG proof
steps, including coherence, support, generic vanishing, and the zero ideal.

Edge cases checked before writing:

- J = bottom is allowed; its module and pushforward are zero and hiso/hzero apply.
- J = top is allowed; it is the structure module of Z pushed forward.
- G = zero cannot be a witness: the rank condition equals one and the integral
  closed image is nonempty.
- Empty Z is excluded by the node's integrality hypothesis, hence empty X admits
  no such immersion. No inhabitedness is added to X separately.
- If Z is a point, the small-support condition just handles zero modules; the
  witness is its residue-field line, and both zero and unit ideals are covered.
- For X = Z = an integral affine line and i the identity, the structure module
  satisfies the generic-line clauses and the usual common-ideal argument applies.
- Arbitrary characteristic is allowed. All objects use an explicit universe u;
  there are no smaller-universe test schemes, hidden local notation, or arbitrary
  replacement maps. All binders are explicit and `autoImplicit` is false.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder` with query
  `coherent sheaves two out of three property generic rank one witness ideal pushforward integral closed subscheme`:
  eight hits, on qcqs restriction/clearing-denominators and integral generic stalks;
  no property-transfer statement.
- `msearch.py ... loogle` with query `"IsCoherent", "stalk"`: zero hits.
- `msearch.py ... grep` with query
  `coherent.*property|rank.one.*ideal|generic.*ideal.*inclusion` in `AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch` with query
  `coherent sheaf property generic rank one witness gives all ideal pushforwards`:
  eight hits, on ideal-image functoriality and ordinary module pushforward, not this theorem.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf`, using
  `coherent.*property|rank_one.*ideal|generic.*ideal.*inclusion` and the item id:
  related results include `rank_one_generic_ideal_inclusion`,
  `coherent_property_irreducible`, and
  `coherent_property_integral_ideals_of_small_support`. I read the latter two.
  The first is an inclusion theorem; the second assumes properties on all smaller
  integral subschemes and concludes all coherent modules; the third is the
  higher-rank 01YL ideal-patching theorem with an additional finite-sum detection
  premise and a different witness condition. None has the item's exact statement.

No new nodes, dependency repairs, statement correction, or statement dispute.

## Second reading by Q108

The dispatcher explicitly prohibits starting other agents, and assigns independent
review to the maintainer. This section records a separate self-audit, not a claim
that another worker performed an independent review. I compared the node and
completed signature again: hiso is restricted to the intended coherent supported
objects; hshort has all three directions and all three support checks; hsmall
uses zero at precisely i(genericPoint Z); hG has support equality, P G,
annihilation, scalar compatibility and dimension one; the conclusion retains
both zero and unit ideals. No mathematical mismatch was found. Compilation
initially required a direct public coherence import and the standard `ZeroObject`
namespace for the categorical zero object. Neither changes the statement.
