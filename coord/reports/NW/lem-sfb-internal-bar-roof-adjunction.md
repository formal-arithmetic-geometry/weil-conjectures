## Worker report

This delivery states `CategoryTheory.CondensedBarRoof.normalized_roofs` in
`Sheaf.CategoryTheory.InternalBarRoofAdjunction`. Its proof is `sorry`. Its
`Normalization` conclusion existentially specifies the canonical chain maps with the formulas
that determine them, the comparison for every injective resolution, and the
short-exact-sequence boundary assertion. No definition selects data from the
postponed theorem. No mathematical statement correction is proposed.

Hypotheses and clauses, read against the node:

- A commutative condensed ring on the coherent profinite site is `A : CondensedBar.Ring.{u}`.
  This is the bundled commutative version of `Profinite.CondensedRing`; its internal modules
  and actions are the recorded `Modules A` and `Equivariant A G` abbreviations.
- A profinite group is `G : Type u` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
  All profinite test objects have universe u, their abelian section groups have universe
  u+1, and the ordinary derived localizations use u+2, exactly as the compatible bar model.
  `HasDerivedCategory` binders select these ordinary localizations, not a new cohomology.
- The homogeneous resolution is the existing `InternalBar.Resolution A.toMon G`.
  Its `objects`, `freeIso`, `diagonal`, `boundary`, `augmentation`, and generator laws
  are used unchanged. `chain` is `ChainComplex.of` those objects and differentials.
  `complex` extends it using `ComplexShape.embeddingDownNat`, so degree -n is P_n,
  its differential is the deletion boundary, and all positive degrees are zero.
  `termIso` is the actual extension-by-zero degree identification.
- The compatible bar model is `M : CondensedBar.Model A G`, already supplied by
  `condensed_derived_invariant_bar`. `M.functions` is the specified internal Hom;
  `M.bar` has the first action face, adjacent multiplications, last deletion, and
  degeneracies. Thus `cochains M.bar` is exactly V with its inhomogeneous differential.
  `totalCochains M.bar` uses the existing finite-diagonal double total, with bar
  degree first and differential d_h + (-1)^p d_I.
- Each `I : InjectiveResolution N` is a nonnegative equivariant injective resolution.
  The row-components conjunct of `Normalization` fixes the map induced by I.ι into resolution row zero:
  apply the cochains functor to I.ι.f 0, then use the (n,0) total coprojection.
  Its localization in the comparison conjunct is j_N. No arbitrary map stands in for j_N.
- The invariant augmentation b and the isomorphism epsilon_N are the existing
  `M.totalAugmentation` and `M.computation.iso I`. The latter's `normalization` field
  fixes it to `resolutionComparison` followed by Q(b). The explicit inverse of
  `singleFunctorIsoCompQ` only changes between the existing single-object encodings.
- Every q >= 0 is `q : ℕ`; every equivariant f is `f : R.objects q ⟶ N`;
  `hf : R.boundary q ≫ f = 0` is exactly f partial_(q+1) = 0 in Lean's composition order.
  the homogeneous-component conjunct fixes the only nonzero component of bar f in degree -q.
  Its target is the single complex in degree -q, transported to N[0][q] by
  `shiftedSingle`, the existing canonical single/shift comparison.
- `inhomogeneous` is the actual cochain map from the single complex in degree q
  (the canonical A[-q]) to V. the coordinates conjunct evaluates its degree-q component on
  the regular unit at every profinite S and every tuple, using the recorded
  `M.functions.evaluate` and `InternalBar.basis`. Its equality is literally
  f[g0,...,gq] = g0 c(g0^-1 g1,...,g(q-1)^-1 gq). Quantifying over S includes all
  profinite base changes. Linearity on A makes evaluation on its unit determine
  the entire map, rather than just a global point.
- `roof` is inv(Q(e)) followed by Q(bar f) and the canonical target shift.
  `phi` is the recorded exact-trivial-inflation/invariants derived adjunction,
  after moving the target shift to the source using `shiftEquiv'` and the
  exact functor's canonical `commShiftIso`. By canonical shift compatibility,
  this equals taking the derived transpose first and then moving the shift.
  There is no inserted scalar in phi.
- the comparison conjunct is j_N Q(c_f) = (-1)^(q*(q+1)/2) • (Phi_q(rho_f) followed by epsilon_N).
  The initial Q/shift and single/shift isomorphisms express A[-q] in the two
  canonical encodings. At q=0 the displayed exponent is zero, and at q=1 it is one;
  hence the signs are exactly +1 and -1. The formula quantifies over every N, f,
  and I, so these signs do not depend on coefficients or resolution.
- the extension conjunct quantifies over all equivariant short exact sequences with quotient
  the trivial regular module, and all lifts l satisfying l ≫ p = R.augmentation.
  It asserts existence of f, uniqueness from f ≫ i = R.boundary 0 ≫ l,
  its cocycle condition R.boundary 1 ≫ f = 0, and the roof equality
  rho_f = -DerivedCategory.triangleOfSESδ. Here the original short exact sequence
  is mapped by the actual single functor and its exactness by `map_of_exact`.
  Mathlib's `triangleOfSESδ` is inv(Q(v)) followed by Q(-pr) and the canonical
  Q/shift comparison (ShortExact.lean:38–43); thus this is the specified cone
  normalization, not an unspecified distinguished-triangle boundary. The alternative
  delta-plus normalization is exactly the negative of this boundary.
- No projectivity, exactness of global sections, underived-Hom acyclicity, coefficient
  flatness, or topological presentation of A or N is assumed.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`,
  `trivial`, `Invariants` and the invariant-inclusion transpose formulas.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`:
  `InternalBar.Resolution`, `basis`, `onSections`, `regularOne`, `exists_resolution`.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Model`, `InternalFunctions`,
  `BarDiagram`, `cochains`, `doubleComplex`, `totalCochains`, `TotalAugmentation`,
  `resolutionComparison`, `Computation.iso` and `Computation.normalization`.
- `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`:
  `condensed_derived_invariant_bar` supplies these compatible normalized models.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` and its public
  `CondensedDerivedInvariants` API: exact trivial inflation, Grothendieck action
  category, and the normalized derived adjunction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, its canonical shifts.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`: the recorded double-total
  infrastructure; the finite total itself is the existing HomologicalComplex₂ total.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: `triangleOfSESδ`.
  The remaining recorded proof dependencies are imported with plain `import`,
  including enough injectives, K-injectives, the internal-section tensor comparison,
  closed tensor, module sheafification, extension-by-zero flatness, first-quadrant
  comparison, injective-target localization bijectivity, the bounded-below derived
  adjunction and the canonical unbounded shift theorem.

The existing landed definition node `def-sfb-condensed-equivariant-bar-data` is
added to stmt_deps because its `Model` and compatible bar constructions are used
explicitly. No new node or dependency replacement module is introduced.

Edge cases checked: q=0 has an empty tuple of inhomogeneous coordinates and the
invariant inclusion; q=1 has the negative sign; the zero coefficient ring and
zero module give zero maps; the trivial group is retained; split extensions give
zero boundary and zero roof. Positive degrees of P vanish by extension by zero.
All total diagonals are finite, including degree zero and vanishing negative degrees.

Searches made using the prescribed msearch wrapper:

- LeanFinder: "Internal homogeneous bar cocycle roofs and normalized derived
  adjunction for condensed module invariants". Eight hits, including condensed
  locally-constant adjunctions, internal Hom points, and topological homogeneous
  cochains; none is this internal arbitrary-coefficient roof comparison.
- Loogle: `"barResolution", "extIso"`. The sole hit `Rep.barResolution.extIso`
  is the discrete representation/projective-resolution theorem, not internal modules.
- Grep: `barResolution|groupCohomologyIsoExt` in RepresentationTheory. Fifteen
  hits in discrete group homology/cohomology and the projective bar resolution.
- LeanSearch: "Internal condensed group homogeneous bar roof normalized derived
  invariants adjunction sign". Eight hits include generic derived adjunctions,
  discrete Rep invariants, and condensed set/abelian free adjunctions; no exact match.
- Local rg over WeilConjectures and Sheaf for `internal-bar-roof-adjunction`,
  `roofAdjunction`, and `barRoof`, plus the node-id search in WeilConjectures:
  no prior declaration of this statement. The original compact-object example
  is withdrawn; its node points to the identical upstream definition, which was read.

## Second reading by NW

A second in-thread reading compared the node statement, the module, and the
recorded dependency declarations. No separate worker was started, as the
current dispatcher brief explicitly prohibits starting agents; the maintainer's
independent delivery review remains separate. The checks above record the
hypothesis and clause comparison rather than asserting an independent review.
The negative triangle boundary and triangular exponent were retained throughout.
The elaboration probes diagnosed the regular-module category inference issue;
explicit localization/category annotations preserve the recorded categories and sizes.

`Normalization` is a fully written existential proposition. The family abbreviations
name its four kinds of maps; the six predicates `augmentationEquation`, `rowEquation`,
`homogeneousEquation`, `coordinateEquation`, `comparisonEquation`, and `extensionEquation`
state the six clauses described above. They are helper declarations of this node and
are listed in its Lean record. `coefficientUnit` is exactly Mathlib's `Mod.regular`,
with its type fixed to the recorded `Modules A`; no coefficient object is changed.
There is no chosen map, existence-based definition, or added mathematical hypothesis.
The primary theorem is the only declaration with a postponed proof.

Validation: the prescribed scompile check passed both the sandbox module (57.4 seconds)
and the library-named module (57.2 seconds), with no errors or unexpected warnings.
