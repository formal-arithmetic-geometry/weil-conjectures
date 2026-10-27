## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveCurveNormalizationSectionDefect` states
`AlgebraicGeometry.ProjectiveCurveNormalizationSectionDefect.exists_bounded_section_defect`.
It contains ten explicit helper definitions/abbreviations and this one theorem, whose proof
is `sorry`. No definition has postponed data or an internal `sorry`. The mathematical node
statement is unchanged. The already landed definition node `def-weil-pbc-reduced-normalization` is added to
`stmt_deps` for the shared componentwise normalization. Scalar restriction, the degree-zero
identification and tensor comparisons reuse helpers for the already cited cohomology,
module-pullback and projective-twist notions; their owning statement nodes are not
statement dependencies. There are no new nodes or
dependency modules.

Hypotheses, objects, and clauses, in the order of the node:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The projective embedding is `j : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))`
  with `[IsClosedImmersion j]`. This is P^N, including N=0; the coordinate type is
  lifted into the scheme's universe rather than restricting the field or schemes.
- Connectedness is `[ConnectedSpace X]`; one-dimensionality is
  `hdim : topologicalKrullDim X = 1`. Nonemptiness follows from connectedness.
- Generic reducedness is `hgeneric`: for every irreducible component Z and every generic
  point η of that component, `_root_.IsReduced (X.presheaf.stalk η)`. There is no global
  reducedness, smoothness, nodality, nondegeneracy, or absence-of-embedded-points assumption.
- D is the existing `X.nilradical.subscheme`, with inclusion
  `X.nilradical.subschemeι`. The theorem asserts a factorization of the existing
  `X.fromReducedNormalization` through this exact D. No replacement of X by D is made.
- The component schemes are the existing `X.reducedNormalizationComponent Z`, whose
  construction is the reduced induced structure on each irreducible component of X.
  Reduction does not change irreducible components, so these are exactly those of D.
  `component X Z` is their existing function-field normalization, and `componentMap X Z`
  is its normalization morphism followed by the actual closed inclusion into X.
- The disjoint union and its map are the existing `X.reducedNormalization` and
  `X.fromReducedNormalization`. The theorem concludes `IsFinite` of this actual map.
  Its finite list is concluded as `∃ (t : ℕ) (c : Fin t ≃ irreducibleComponents X)`;
  no finite component list is assumed. Thus every component occurs exactly once.
- The clause for every `i : Fin t` concludes `IsConnectedCurve`, `Smooth`, and `IsProper`
  of `componentStructure j (c i)`. The recorded connected-curve class includes finite type,
  separatedness, nonempty connected underlying space, and dimension exactly one.
- `twistOn j m` is the recorded tensor pullback of the ambient O(m), so is precisely O_X(m).
  `line j Z` is the tensor pullback of O_X(1) along the normalized component map, exactly A_i.
  `componentDegree j Z` uses the recorded `Scheme.Modules.degree k` on this A_i, with the
  structural map `componentMap X Z ≫ j ≫ projection`; `0 < componentDegree j (c i)` is
  a conclusion, not an assumption. Its value is an integer, not a truncated natural degree.
- `sourceSections j m` is H_m: the existing scalar-restricted
  `RingedSpace.moduleCohomology X.toRingedSpace 0` of O_X(m).
  `componentSections j Z m` is T_i,m: the same right-derived Zariski module cohomology
  of `(line j Z).tensorPow m` on E_i, with the same structural field action used for degree.
  No abelian-sheaf H^0 or alternative module-cohomology construction is introduced.
- The finite direct sum is represented by `∀ i : Fin t, componentSections j (c i) m`.
  For a finite index this is canonically the direct sum, including its vector-space structure.
- The map is `ρ : ∀ m : ℕ, sourceSections j m →ₗ[k] (∀ i : Fin t, ...)`.
  The following equation for every m, every section s, and every component i fixes its value:
  identify both H^0 groups with actual global sections using the existing `zeroSections`;
  apply the section-normalized tensor-pullback adjunction unit, cast the preimage of top to
  top by the existing restriction map, and apply `componentTwistIso`. Thus the existential
  does not allow an arbitrary linear map: the formula determines it uniquely on every input.
- `ambientPower` constructs the power-to-twist identification recursively using the existing
  `unitIsoTwistZero` at zero and the chart-normalized `twistTensorIso` at successors.
  `componentTwistIso` applies the existing normalized pullback-power comparisons to that
  ambient identification and to the component map. These are actual constructions, with no
  choice of an unconstrained isomorphism. They give exactly nu_i^* O_X(m) ≅ A_i^m.
- The bounds are `∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ...`; natural binders express
  nonnegative integer constants, depending on k, X and its given embedding. There is no
  uniformity over X. The restriction map is defined in every nonnegative degree; only its
  estimates and finite-dimensionality are asserted above the common threshold.
- Finite-dimensionality of H_m and each T_i,m is `Module.Finite k ...` in the conclusion.
  Their finite sum, and hence the kernel and cokernel, are then finite-dimensional as well.
- The kernel bound is `Module.finrank k (LinearMap.ker (ρ m)) ≤ C`.
- The cokernel bound is the finrank of the actual target quotient by
  `LinearMap.range (ρ m)`, bounded by the same C.
- The component error is the absolute value in ℤ of
  `(Module.finrank k T_i,m : ℤ) - (m : ℤ) * componentDegree j (c i)`, bounded by C.
- The total error is the absolute value in ℤ of
  `(Module.finrank k H_m : ℤ) - (m : ℤ) * ∑ i, componentDegree j (c i)`, bounded by C.
  Integer subtraction avoids truncated natural subtraction and retains both inequalities.

Dependency declarations read and used:

- Mathlib: `Field` (Algebra.Field.Defs); `AlgebraicGeometry.Scheme` and scheme morphisms
  (AlgebraicGeometry.Scheme); `IsClosedImmersion` (Morphisms.ClosedImmersion), `IsReduced`
  (Properties), `IsProper` (Morphisms.Proper), `Scheme.nilradical` (IdealSheaf.Basic),
  `Scheme.IdealSheafData.subscheme` and `subschemeι` (IdealSheaf.Subscheme).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`,
  `unitIsoTwistZero`; `...ProjectiveSpace.TwistTensor`: `ProjectiveSpace.twistTensorIso`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `Scheme.fromNormalization` for the existing integral reduced component.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalizationComponent`,
  its integral instance, `reducedNormalization`, and `fromReducedNormalization`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve` and `IsConnectedCurve`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the existing `tensorPullback`
  is publicly imported, and `tensorPullbackSectionAdjunction` specifies the actual 1-tensor-s
  pullback of sections. Its normalized identity and composition comparisons are retained.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.Modules.degree`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`: `RingedSpace.moduleCohomology`
  and `globalSectionsFunctor`. The helpers `cohomology` and `zeroSections` in
  `Sheaf.AlgebraicGeometry.UniformProjectiveFibreVanishing` reuse these definitions, restrict
  scalars along the given structural map, and use `rightDerivedZeroIsoSelf` in degree zero.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `Scheme.Modules.boundaryPullbackPowIso`. Its signature is general: it assumes neither a
  square-zero ideal nor a closed immersion. This uses an existing canonical comparison,
  without importing any square-zero hypothesis into our statement.

The already recorded proof-dependency modules are imported privately, including normalization
properties, ampleness and pullback, coherent kernel/cokernel closure, the normalization quotient,
zero-dimensional-support Euler characteristic, proper coherent cohomology finiteness,
closed-immersion cohomology, the derived long exact sequence, degree tensor additivity and
Riemann--Roch. Unstated proof dependencies (closed-immersion-proper,
proper-field-invertible-coherent, proper-curve-normalized-component-cover) have no module to
import; none is needed to type this statement. Their mathematical roles are in the proof docstring.
The canonical constructions are backed by already existing nodes, and a source-only traversal
of both dependency-edge kinds verified that the added definition dependency has no path back to this item.

Edge cases checked before writing:

- Empty X and zero-dimensional X fail the stated connected dimension-one hypotheses.
  P^0 contains no such closed subscheme, so N=0 is a legitimate vacuous case, not excluded.
- A smooth irreducible curve has one component and an isomorphic normalization: the defect
  vanishes, while the component estimate is eventual Riemann--Roch. A line gives h^0=m+1.
- Reducible connected curves are retained, including nodes, cusps on a component, and higher
  singularities. The canonical component enumeration cannot duplicate or omit a component.
- Finite embedded nilpotents are retained. A closed nilradical support misses component generic
  points, hence is zero-dimensional; its H^0 is a constant finite kernel contribution.
  A generically nonreduced double curve fails hgeneric and is correctly excluded.
- m=0 is included in the map and tensor comparisons through the canonical unit, while the
  estimates require m≥m0. Degrees are positive integer conclusions, with no assumption on
  genus; negative values of 1-g cause no error because absolute values are taken in ℤ.
- Positive characteristic is retained: an algebraically closed field is perfect, so normalized
  one-dimensional components are smooth over it. No characteristic-zero assumption appears.

Searches performed:

1. `msearch.py ... leanfinder "Normalization of generically reduced projective curves bounds
   kernel and cokernel of global sections of high hyperplane twists"`: OK, eight hits.
   Hits include Proj.fromOfGlobalSections, Scheme.Hom.ker_toNormalization and relative
   normalization comparison maps. None states the bounded section defects or the asymptotic
   component/total dimensions. `ker_toNormalization` is a scheme ideal, not this section kernel.
2. `msearch.py ... loogle '"AlgebraicGeometry", "normalization"'`: OK, twelve hits, all
   relative normalization constructions/properties, no finite-dimensional defect assertion.
3. `msearch.py ... grep 'normalization.*(section|Section)|section.*normalization|hilbertPolynomial'
   AlgebraicGeometry`: OK, one hit at Mathlib/AlgebraicGeometry/Normalization.lean:217, an affine
   section-to-integral-closure isomorphism, not the requested theorem.
4. `rg` in the project's WeilConjectures and Sheaf AlgebraicGeometry trees for normalization
   sections, generic reducedness, tensor pullback sections, and pullback tensor powers found
   the shared constructions used here. A search for this blueprint id in WeilConjectures had
   no hit. Existing ReducedNormalization, UniformProjectiveFibreVanishing and canonical
   boundaryPullbackPowIso avoid introducing copies of those notions.
5. DAG inspection found their recorded owning nodes. The componentwise-normalization
   definition node is added to stmt_deps; the other helpers serve already cited notions.
   No independent notion
   is missing. `tools/blueprint_refs.py search reduced-normalization` returned zero blueprint
   matches; the explicit DAG node already exists and is used.

Sources opened locally: varieties.tex `lemma-normalization-locally-algebraic`,
`lemma-prepare-delta-invariant`, `lemma-chi-tensor-finite`, and curves.tex `lemma-rr`.
The proof docstring records all eight proof steps, including the finite-nilradical contribution.
No mathematical statement correction or STATEMENT-DISPUTED fault was found.

Validation: scompile.py compiled both sandbox and library module modes cleanly, including
the complete private proof-import plan. The first dry run rejected three added statement-node
dependencies and misparsed a leading absolute-value bar as an equation-style proof. The
statement-node dependencies were removed (their helpers serve already cited definitions);
parentheses around the final bound avoid that parser ambiguity. The mathematical statement
is unchanged. The corrected module and packet are compiled and dry-run checked again before
pushing. No diagnostic commands remain.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
