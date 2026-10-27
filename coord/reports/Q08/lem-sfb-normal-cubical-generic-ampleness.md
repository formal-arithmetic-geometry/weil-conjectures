## Worker report

The module Sheaf.AlgebraicGeometry.NormalCubicalGenericAmpleness states
AlgebraicGeometry.normal_cubical_generic_ampleness, with proof `sorry` only.
It formalizes the supplied-line assertion without constructing or asserting the
existence of a line extending a generic one. No statement correction is made.
The only change besides lean is adding the already landed definition node
`def-sfb-semiabelian-geometric-fibres` to stmt_deps, as authorized by §5.

Clause-by-clause comparison:

- The base scheme is `S : Scheme.{u}`, integral by `[IsIntegral S]`, locally
  Noetherian by `[IsLocallyNoetherian S]`. The binder `hS` says at every point
  its local ring is an integral domain and integrally closed, exactly normality
  in the node. No global Noetherian or quasi-compact base assumption is used.
- The supplied commutative group scheme is `G : Grp (Over S)` with
  `[IsCommMonObj G.X]`; `G.X.hom` is p. The bundled group laws supply addition,
  identity and inverse, including commutativity. Multiplicative notation in the
  group-object API denotes the source's additive notation.
- `[Smooth G.X.hom]` and `[IsSeparated G.X.hom]` render smoothness and the
  closed-diagonal condition. Finite presentation is
  `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]` together with
  the already assumed separatedness, which implies quasi-separatedness.
- `hG : HasSemiabelianGeometricFibres G` quantifies over algebraically closed
  fields `k : Type u` and all maps Spec k to S. Its data are a natural number r,
  the canonical split multiplicative torus, an abelian variety A, a kernel
  pullback square and fppf local surjectivity of the quotient. This is the
  exact fppf sequence specified inline in the item. The definition includes
  r = 0. The abelian-variety predicate supplies properness, smoothness and
  geometric connectedness. No extra hypothesis is introduced by this reuse.
- The generic point is the actual `genericPoint S` and the base map is
  `S.fromSpecResidueField (genericPoint S)`. `hproper` says that the second
  projection of its pullback with p is proper over the residue field.
- `B : CubicalRigidifiedLine G.X` is supplied on the whole group. Its `line`,
  `invertible`, `rigidification`, `sectionIso` and `compatible` fields are
  exactly (B,r_B,tau_B) of the dependency node.
- `hample` is absolute `Scheme.Modules.IsAmple` on the generic pullback of
  B.line along the first projection. The existential proof h of invertibility
  only supplies the proof argument required by IsAmple; invertibility of this
  pullback follows from invertibility of B. It supplies no new line or map.
- `hsymmetric` is Nonempty of an isomorphism from tensor pullback of that same
  generic line along the actual inverse `ι` of the base-changed group to the
  generic line. Thus symmetry is required only on the generic fibre.
- The conclusion quantifies over every `W : S.Opens` with `IsAffineOpen W`.
  It asserts absolute ampleness of tensor pullback of B.line along the
  inclusion of `G.X.hom ⁻¹ᵁ W`, precisely B on p-inverse W. Again the existential
  invertibility proof only fills IsAmple's proof argument. There is no extension
  existence assertion or replacement of the supplied B.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed,
  applied together with IsDomain to actual local rings, as the normal-ring
  node's recorded inline interface requires.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation; QuasiCompact and the existing
  separatedness encode the finite-presentation comparison clause.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper and IsSeparated.
- Sheaf.AlgebraicGeometry.CubicalRigidifiedLine:
  AlgebraicGeometry.CubicalRigidifiedLine (full structure and docstring read).
- Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres:
  AlgebraicGeometry.HasSemiabelianGeometricFibres (full definition read).
- WeilConjectures.AlgebraicGeometry.Ample: Scheme.Modules.IsAmple, using
  its actual affine nonvanishing-locus condition, and local invertibility from
  WeilConjectures.AlgebraicGeometry.Modules.Invertible.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: the recorded
  normalized tensor-pullback interface, publicly imported by CubicalRigidifiedLine;
  its upstream Scheme.Modules.tensorPullback is used throughout.

The stated proof dependencies SchemeRelativeAmpleBaseChange and
SchemeRelativeAmpleAffineCover are imported non-publicly. The invertible-module
module is also imported for that proof dependency. The remaining proof nodes
(raynaud-generic-ample-power-model, semiabelian-cubical-rigidification,
fp-module-limit-isomorphism-descent, normal-symmetric-cubical-extension)
have no lean records in the read DAG, so there are no modules to import for them.
Their eight proof steps, with all node names, are in the theorem docstring.

Edge cases checked before writing: an integral base is nonempty, so its generic
point is meaningful; no extra nonempty-base binder is needed. Empty affine opens
are included in the conclusion (absolute ampleness on the empty scheme has
vacuous point condition and compactness). The base may be non-quasi-compact.
Rank-zero tori, abelian fibres and the zero-dimensional trivial group are allowed.
No characteristic restriction is imposed, including characteristic two for inverse
symmetry. All schemes and field tests use the same arbitrary universe u, following
the shared semiabelian predicate; there is no independently smaller test universe.
The symmetry is an ordinary line isomorphism, not an additional global symmetry
or a cubical symmetry isomorphism requirement.

Searches actually run:

- msearch.py leanfinder: “A cubical rigidified line bundle on a smooth separated
  semiabelian group scheme over a normal integral locally noetherian base is
  relatively ample if its proper generic fibre restriction is ample and symmetric”.
  Eight hits: affine space and affine-transition-limit facts; no matching theorem.
- msearch.py loogle: `AlgebraicGeometry.Scheme.Modules.IsAmple, CommGrpObj`.
  Zero hits; service reports unknown identifier for the project-only IsAmple.
- msearch.py grep: `Cubical|[Ss]emi[Aa]belian|generic.*ample`, AlgebraicGeometry.
  Zero Mathlib hits.
- rg searches over lean/WeilConjectures for cubical/semiabelian and for the
  literal item ID found no theorem matching the item. Searches over lean/Sheaf
  found CubicalRigidifiedLine and the shared SemiabelianGeometricFibres predicate,
  which are reused; no normal_cubical_generic_ampleness declaration existed.
  dag/lean_names_upstream.json likewise had no matching declaration name.
- The example CompactObject module is withdrawn in this read clone; its node
  records the identical upstream declaration. Its header conventions and the
  current CubicalRigidifiedLine module were followed.

Source limitation: the original Moret-Bailly and Raynaud references are marked
WANTED in the node, as acknowledged in its accepted split. No new source claim
or theorem strengthening is made here. The current blueprint unit
literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md was read; this is a prerequisite, not that
unit's own statement. No STATEMENT-DISPUTED issue was found in the item.

Validation: scompile.py compiled the sandbox and final library module separately
against the published server build, with no errors or non-sorry warnings.

## Second reading by Q08

The worker reread the node and final file after compilation, checking each item
above against the explicit signature. In particular: generic properness uses the
second pullback projection; the generic line uses the first; inverse symmetry is
on the base-changed group; the conclusion restricts on the inverse image of each
affine base open. The semiabelian predicate uses the supplied group law. No
mismatch was found and no statement correction was needed. This is a worker
self-check, not a claim of independent review: the dispatcher forbids starting
other agents, and the brief assigns independent review to the maintainer.
