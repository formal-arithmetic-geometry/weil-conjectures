## Worker report

Stage 2 delivery for lem-sfb-moving-linear-series-zero. The earlier unchanged-split
failure was stage 1; the current node is reviewed and split, with no Lean record.
No repair note exists. The queue lists this item at stage 2. This delivery preserves
the accepted statement, proof, dependency lists and all maintainer fields, adding
only lean. No new nodes or dependency repairs are needed.

The module Sheaf.AlgebraicGeometry.MovingLinearSeriesZero states
AlgebraicGeometry.Scheme.Modules.exists_moving_linear_series_zero with one sorry.
Its two helpers construct the actual restriction image and residue value, with no
postponed data or extra theorem. restrictedLinearSeriesImage is the span of the
actual normalized pullback values: restriction is k-linear for a k-morphism, so
this is exactly im(V -> H0(C,i*L)), including when the restriction has a kernel.
sectionResidueValue is the actual tensor 1 tensor germ(s) along X.residue x;
it is not a supplied or chosen evaluation map. The tensor order is the canonical
extension-of-scalars order kappa(x) tensor L_x, equivalent by symmetry to L_x tensor
kappa(x) in the node.

Clause-by-clause correspondence:

- Algebraically closed field: (k : Type u) [Field k] [IsAlgClosed k].
- A k-scheme: (X : Scheme.{u}) [X.Over (Spec (.of k))].
- Nonempty, projective, reduced, pure dimension one: [Nonempty X],
  [IsHProjective (X ↘ Spec (.of k))], [IsReduced X], and hdim : X.IsPureDimension 1.
  IsHProjective is the exact finite-projective-embedding convention of def-kun-projective.
- Invertible module: L : X.Modules with [L.IsInvertible].
- Finite-dimensional subspace of global sections: V : Submodule k
  (ProjectiveSpace.fieldSections k L), with [FiniteDimensional k V]. fieldSections
  evaluates the sheaf at the whole space and restricts scalars along the k-structure
  map. Thus this uses actual H0/global sections, not a different cohomology carrier.
- Reduced component: C, its induced k-structure, [IsReduced C], i : C -> X,
  [IsClosedImmersion i], [i.IsOver (Spec (.of k))], and hC : Set.range i in
  irreducibleComponents X. A reduced closed subscheme with this image is precisely
  the reduced component structure. The induced k-structure and over condition merely
  express the specified restriction over k, not any additional geometric assumption.
- Restriction L|C: (tensorPullback i).obj L, using the prescribed tensor construction.
  The normalized adjunction unit is the actual section restriction. hV says
  2 <= Module.finrank k (restrictedLinearSeriesImage k i L V).
- Zero-dimensional closed subscheme: Z : Scheme, j : Z -> X,
  [IsClosedImmersion j], hZ : topologicalKrullDim Z <= 0. This includes the empty
  cluster (dimension bottom); every nonempty such Z has dimension exactly zero.
  No reducedness of Z is assumed, so nonreduced clusters are included.
- Finitely many proper linear subspaces of V: S : Finset (Submodule k V),
  forall W in S, W != top. A finite set of subspaces is equivalent to the finite
  list in the node; repetitions have no effect on its union.
- Includes zero: (bottom : Submodule k V) in S.
- Every section outside their union: forall s : V, (forall W in S, s notin W) -> ... .
- A closed zero outside the cluster on the component: exists x : X,
  IsClosed {x}, x in Set.range i, x notin Set.range j, sectionResidueValue L s.val x = 0.
  Closedness in X and on C coincide here, since C is a closed subscheme.
- The exceptional set is contained in the finite union: precisely the contrapositive
  of the preceding universal implication. No equality with the full bad set is asserted.
- Nonempty good complement: exists s : V, forall W in S, s notin W.
- Zariski open in any basis: for each n and b : Module.Basis (Fin n) k V, an open
  U of PrimeSpectrum (MvPolynomial (Fin n) k) has exactly those coordinate k-points
  corresponding to the good complement. The point is comap(eval(b.repr s)) of the
  unique prime closedPoint k. This expresses the usual Zariski topology on affine
  k-points by its induced topology from the affine scheme, without introducing a
  competing topology or an analytic field topology. Any finite-dimensional basis
  can be reindexed by Fin n, so every choice of coordinates is covered.

Dependency declarations read and used:

- def-kun-projective: WeilConjectures.AlgebraicGeometry.Morphisms.Projective,
  AlgebraicGeometry.IsHProjective (full finite coordinate embedding field read).
- def-kun-topological-krull-dimension: Mathlib.Topology.KrullDimension,
  topologicalKrullDim, defined by krullDim (IrreducibleCloseds X).
- def-pc-module-pullback: Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction,
  AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction and its canonical
  tensorPullback functor publicly imported from WeilConjectures.AlgebraicGeometry.TensorPullback.
  Read the explicit tensor data, unit normalization and adjunction definition.
- def-pc-reduced-scheme: Mathlib.AlgebraicGeometry.Properties,
  AlgebraicGeometry.IsReduced, sectionwise reducedness, with its stalk equivalence.
- def-sc-invertible-module: WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  AlgebraicGeometry.Scheme.Modules.IsInvertible, local rank-one trivializations.
- def-sc-ringed-space-module-cohomology:
  WeilConjectures.Topology.RingedSpaceModuleCohomology,
  AlgebraicGeometry.RingedSpace.moduleCohomology and globalSectionsFunctor.
  Only degree zero/global sections are needed, and fieldSections is literally its
  evaluation-at-top construction with k-scalar restriction. No H^p bridge is needed.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, IsAlgClosed;
  its splits formulation is equivalent to every nonconstant polynomial having a root.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  AlgebraicGeometry.IsClosedImmersion (closed embedding with surjective stalk maps).
- def-weil-irreducible-components: Mathlib.Topology.Irreducible, irreducibleComponents.
- def-weil-pure-dimension: Sheaf.AlgebraicGeometry.PureDimension,
  AlgebraicGeometry.Scheme.IsPureDimension, dimensions of all component subspaces.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  AlgebraicGeometry.Scheme.residueField and Scheme.residue (the local quotient map).

Additional existing APIs: ProjectiveSpace.fieldSections from
Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences; the stalk module
instance from WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk;
ModuleCat.extendScalars from Mathlib.Algebra.Category.ModuleCat.ChangeOfRings.
No independent notion is redefined: the two helpers only name the canonical
restriction image and residue value belonging to this statement.

Proof dependencies with available modules are imported privately: regular divisor
calculus, smooth connected curve local rings, finite zero-dimensional closed
subschemes, normalization, global functions, degree, finite linear avoidance and
finite morphism point finiteness. Projective properness, integral schemes, closed
immersion composition and pure dimension are already public via the statement
imports. The theorem docstring carries all seven accepted proof steps and sources.

Edge cases checked before writing: empty X is explicitly excluded; empty Z is
allowed; Z can be nonreduced; C can be singular or a component of reducible X;
large restriction kernel is allowed and its sections must be excluded; zero V and
one-dimensional restriction image fail hV as required; zero section is excluded by
the bottom subspace; negative or degree-zero normalized line bundle cannot have
two independent sections. On P1 with O(1) and a fixed finite support, exceptional
lines are exactly the sections whose single zero lies in that support. All field
characteristics are allowed. Universes and variables are explicit.

Searches actually run (2026-10-23 UTC):

- msearch leansearch: "A linear series on a projective curve with two independent
  sections has a zero away from any fixed finite set for general sections": eight
  hits, including Projectivization.Independent recursors, Scheme.zeroLocus and
  zeroLocus_mono/def. None addresses invertible-module restricted linear series.
- msearch leanfinder: "A finite dimensional linear series on a projective curve
  with at least two independent restricted sections has a zero outside a fixed
  finite set for general sections": eight hits, on elliptic curves, combinatorial
  Nullstellensatz and linear relations. None states this theorem.
- msearch loogle: '"Submodule", "zariski"': zero hits.
- msearch grep, AlgebraicGeometry: moving.*zero|linear.series|residue.*section|section.*residue:
  two hits in ResidueField, for structure-sheaf evaluation, not this theorem.
- rg over lean/WeilConjectures and lean/Sheaf for linear.series|moving.*zero|
  moving.*linear|MovingLinear: unrelated hits in comments and stable-curve series;
  no moving-zero declaration. grep for the exact item id in WeilConjectures gave
  no hit. rg of dag/lean_names_upstream.json and both libraries found no collision
  with restrictedLinearSeriesImage, sectionResidueValue or exists_moving_linear_series_zero.
- API searches for tensorPullbackSection, globalSectionsRingHom, fieldSections,
  stalk module actions and polynomial/Zariski topology found the reused definitions
  listed above; their signatures and docstrings were opened.

Sources opened: varieties.tex Tag 0B40 (lemma-check-invertible-sheaf-trivial) and
0BXR (lemma-normalization-locally-algebraic), the current latest blueprint unit
sk-thm-sf-ctf-stability, and the latest finite-linear-avoidance statement and proof.
No statement dispute or source correction is needed.

Validation: scompile.py compiles this file independently in both sandbox and library
module modes against the published live build, cleanly. No diagnostics remain.
The only postponed proof is exists_moving_linear_series_zero.

## Second reading by N5

The dispatcher explicitly prohibits starting another agent. This is therefore a
second pass by the same worker, not a claim of an independent reader; the
maintainer's independent review remains necessary.

Reopened the whole node and the final module, and compared the binders and each
of the five conclusion clauses. The reduced closed immersion with component
image encodes exactly the reduced component, not a smooth replacement. The
restriction image uses the actual normalized adjunction, not an arbitrary
linear map, and includes its possible kernel. Span of its values equals image
because the k-structure is compatible via i.IsOver. The stalk tensor is the
actual residue-fibre value; generic-stalk nonvanishing would not suffice and
is not substituted. The zero-dimensional condition allows the empty cluster.
The complement-open clause quantifies over every finite basis, and its
coordinate point is the polynomial evaluation kernel; nonemptiness is separately
asserted for that same complement. No conclusion clause is missing or strengthened.
During compiler-guided reading the canonical scheme-module stalk instance was
added by import, and TopologicalSpace.Opens was fully qualified to avoid the
Scheme.Opens name. No node content other than lean changed. No extra theorem or
hollow data was introduced.
