## Worker report

The module `Sheaf.AlgebraicGeometry.AffineNormalConnectedGroupAmple` states
`AlgebraicGeometry.exists_isAmple_of_affine_normal_connected_group`, with one `sorry`.
There are no new definitions or helper theorems. No mathematical statement correction
is needed. The shared repository was only read; sandbox files were compiled exclusively
through the prescribed scompile.py wrapper.

Statement comparison, hypothesis by hypothesis and clause by clause:

- The given base scheme is `S : Scheme.{u}`.
- Affineness is `[IsAffine S]`.
- Noetherianness is `[IsNoetherian S]`, the existing conjunction of local
  Noetherianness and quasi-compactness; for affine S this is exactly the node's condition.
- Normality and integrality are `hS : IsNormalScheme S`. Read its full definition:
  `IsIntegral S ∧ ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`. Thus nonemptiness, reducedness,
  irreducibility and normal domain local rings are all retained. This is the existing
  notion, not a new normality predicate. Its owning already-landed definition node
  `def-sbc-normal-dominant-galois` is added to stmt_deps, as permitted by the standing
  brief's §5 STMT_DEPS MAY GAIN LANDED NODES rule. The original eleven dependencies remain.
- The given S-scheme and its structure morphism are `H : Over S` and `H.hom`.
  The total scheme is `H.left`; this re-bundling does not change the quantified objects.
- The multiplication, inverse, unit, associativity, unit laws and inverse laws are
  `[GrpObj H]`, the existing group-object structure in the Cartesian category of
  S-schemes. Its multiplication is a morphism from the relative product and its unit
  is from the terminal S-scheme. No commutativity instance is assumed.
- Smoothness is `[Smooth H.hom]`.
- Separatedness is `[IsSeparated H.hom]`.
- Finite presentation is `[LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom]
  [QuasiSeparated H.hom]`, exactly the convention in both recorded dependencies.
  Although smoothness and separatedness entail two of these properties, writing the
  conjunction preserves the explicit finite-presentation hypothesis.
- Geometrically connected fibres are `[GeometricallyConnected H.hom]`. The Mathlib
  definition asks all field-valued base changes to be connected and has the recorded
  fibrewise equivalence; it uses ConnectedSpace, which includes nonemptiness.
- The conclusion quantifies `∃ (L : H.left.Modules) (_ : L.IsInvertible), ...`.
  Thus L is an actual module on the entire original total scheme, locally free of rank
  one by the recorded IsInvertible predicate.
- `Scheme.Modules.IsAmple H.left L` is the existing absolute ampleness definition:
  quasi-compactness plus affine nonvanishing section loci of positive tensor powers
  around every point. The existential invertibility witness supplies its implicit
  instance. There is no base shrinking or covering in the conclusion.

Source checked: Ning Guo, Divisors on coherent schemes and homogeneous spaces,
March 31, 2026, Corollary 6.14, printed p.19, read online at
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf . Its second
conclusion covers affine integral S; specialize the homogeneous space to H with left
translation. The published proof localizes in case (ii); the accepted stage-1 proof
already isolates the global affine-transversal input as
lem-sfb-normal-group-affine-fibre-transversal. It is not silently replaced by the
existing local ample-line result. The theorem docstring records each of the five
accepted proof steps, including that global input, geometric irreducibility,
Cartier boundary, the canonical divisor section, and the supplied-section criterion.
No counterexample was found, so no STATEMENT-DISPUTED flag is introduced.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.AffineScheme: AlgebraicGeometry.IsAffine.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian and
  AlgebraicGeometry.IsNoetherian.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed, whose
  fraction-ring definition is the recorded normal-ring component.
- WeilConjectures.AlgebraicGeometry.NormalScheme: AlgebraicGeometry.IsNormalScheme.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.AlgebraicGeometry.Morphisms.Separated: AlgebraicGeometry.IsSeparated.
  The convention node records no independent predicate; its standard morphism
  properties are used directly.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, fst and snd, underlying the relative products.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, extending MonObj with
  inverse and its laws; Mathlib.AlgebraicGeometry.Limits supplies the Cartesian
  structures. The upstream GroupScheme.Defs docstring confirms this encoding.
- Mathlib.Topology.Connected.Basic: ConnectedSpace, the exact mathlib_match of
  def-weil-connected-scheme (which needs no lean-record repair).
- Mathlib.AlgebraicGeometry.Geometrically.Connected:
  AlgebraicGeometry.GeometricallyConnected, applied to H.hom.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  AlgebraicGeometry.Scheme.Modules.IsInvertible.
- WeilConjectures.AlgebraicGeometry.Ample:
  AlgebraicGeometry.Scheme.Modules.IsAmple and nonvanishingLocus.

The recorded proof-dependency modules are imported without public visibility:
WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
(Smooth.exists_geometricallyIrreducible_of_section),
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
(isEffectiveCartierCenter_iff_isInvertible_ker), and
WeilConjectures.AlgebraicGeometry.EffectiveCartier
(Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules).
Their complete signatures and docstrings were read. Other stated proof dependencies
are also statement dependencies and their imports are public. The three proof nodes
normal-group-affine-fibre-transversal, smooth-normal-affine-boundary-cartier and
group-affine-section-ampleness have no lean records in this checkout; they are proof
prerequisites, not missing objects needed to type this statement.

Edge cases checked before writing: the empty base is excluded by integrality, as in
the node; H cannot be empty over a nonempty S because it has a unit; the trivial group
H=S and relative dimension zero are included; affine H admits the expected trivial
ample line and empty Cartier boundary; proper connected groups are not excluded by
an affineness condition on H; noncommutative groups and all characteristics are allowed.
No independent universe for test schemes is introduced, and the existing geometrically
connected definition uses the same Scheme universe. The module has explicit universe u
and autoImplicit false; the compiler found no inferred undeclared variables.

Searches performed (actual queries and outcomes):

- msearch.py leanfinder: "A smooth separated connected group scheme of finite
  presentation over an affine normal integral Noetherian base has an ample line
  bundle". Eight results, including IsQuasiAffine, IsAffine, IsIntegral and affine
  integral criteria; none has this theorem's group/base hypotheses and conclusion.
- msearch.py loogle: `"AlgebraicGeometry", "ample"`. Zero hits.
- msearch.py grep: `group.*(quasiProjective|quasi_projective|ample)|Raynaud|homogeneous.*ample`.
  Sixteen text hits, mostly bibliography and unrelated group examples; no match.
- rg in lean/WeilConjectures and lean/Sheaf for group/ample, GrpObj,
  GeometricallyConnected and IsNormalScheme; direct search for this blueprint id in
  WeilConjectures found no declaration. Found and read GroupScheme.AmpleFamilySmooth:
  it treats groups over algebraically closed fields, not the present general base.
  Found NormalSmoothGroupLocalAmpleLine: its conclusion is on a base covering, so it
  is not a duplicate. AlgebraicGroupAmpleDifference is a different field-base result.
- rg in dag/nodes located the existing normal-scheme and group-scheme definition
  records; no new definition node was needed. rg for the proposed full theorem name
  in Mathlib/project names and dag/lean_names_upstream.json found no collision.

Validation: scompile.py N7 lem-sfb-affine-normal-connected-group-ample compiled both
its sandbox view and library module successfully (7.2 s and 5.5 s), with no errors or
warnings. All proofs remain sorry as required for this stage.

## Second reading by N7

This is a separate self-reading by the dispatcher worker; the task explicitly forbids
starting another agent. It does not claim an independent second worker. The maintainer's
independent delivery review remains the independent reading requested in the brief.

Reopened the node and final module and compared every binder and conclusion. Normality
includes integrality through the actual IsNormalScheme definition, rather than omitting
integrality or requiring normality on a larger class of bases. Noetherian means locally
Noetherian and compact, not just a finiteness condition on H. The finite-presentation
conjunction agrees with the convention node. GrpObj is over S and is not CommGrpObj.
The geometric condition applies to the structure morphism, not just the total space.
The module L and the IsAmple predicate both live on H.left. The conclusion has no
existential open base or point parameter. All five proof steps are in the docstring.
No mathematical mismatch was found; the dependency list gained the already-landed
owning node for the normality predicate. No dependency record or statement was changed.
