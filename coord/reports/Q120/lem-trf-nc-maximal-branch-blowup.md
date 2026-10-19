## Worker report

The delivery states `AlgebraicGeometry.Scheme.IdealSheafData.nc_maximal_branch_blowup`
in `Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup`. Its proof is `sorry`. No theorem is
proved. The other declarations construct the branch-count interface and the defining
ideal of the existing canonical scheme-theoretic strict transform.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII 4.1.6 and 4.1.8,
printed p. 118, and 4.2.8--4.2.9, printed pp. 120--121. The extracted source explicitly
stratifies the old divisor by multiplicity, blows up the closed deepest stratum, and
computes the drop on blowup charts. The five proof steps of the DAG are preserved in
the theorem docstring, including the reduced scheme structure and closure base change.
There is no statement correction and no STATEMENT-DISPUTED finding.

Hypotheses, one by one:

* The scheme is `{X : Scheme.{u}}`. No field, characteristic, dimension, separation,
  excellence or global branch labelling is added.
* Noetherian is `[IsLocallyNoetherian X] [CompactSpace X]`, exactly the locally
  Noetherian plus quasi-compact convention in the node.
* Regular is `hX : ∀ x, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U)`.
  This is precisely the scheme clause prescribed in the recorded
  `def-weil-regular-scheme` Lean note, using its `IsRegularRing` declaration.
* The closed divisors are `B D : X.IdealSheafData`. `hB : B.IsNormalCrossingsDivisor`
  reuses the landed normal-crossings definition: an effective Cartier ideal with
  pointed etale stalk equations that are subproducts of a regular parameter system.
  The empty subproduct gives the complement of the boundary; there is no global SNC
  or component-smoothness hypothesis.
* Reduced D is `hDred : IsReduced D.subscheme`; nonempty D is
  `hDne : Nonempty D.subscheme`.
* The reduced component-union condition is `hcomponents`. The chosen set `C` is a
  subset of `irreducibleComponents B.subscheme`, and `D.support` is the union of
  their images under the actual closed immersion `B.subschemeι`. With `hDred`,
  equality of support specifies the reduced union as a closed subscheme. Thus this
  retains every allowed component union and implies D is contained in B. It does
  not assume that the components themselves are regular or geometrically irreducible.

Conclusions, one by one:

* The number of branches at a geometric point over x is `D.ncBranchCount x`.
  `HasNCBranchChart D x n` refines the already landed normal-crossings parameter
  presentation by recording the sublist length n. It uses the germ of the
  pulled-back ideal, so the local equation is scheme-theoretic. All sublist members
  belong to the maximal ideal; unit factors from an affine equation have been
  discarded, exactly as in Step 1 of the node.
* `ncBranchCount` is the natural-number infimum of all these lengths. In a
  normal-crossings presentation, the distinct parameter primes are exactly the
  geometric branches, and etale refinement preserves their number (the argument
  of `lem-trf-nc-coordinate-max-stratum`). Hence the set of possible lengths is a
  nonempty singleton, so its infimum is exactly the prescribed count. This defines
  actual data, without `sorry`, coordinate choices, or a new assumed branch function.
  D is locally such a subproduct because it is a reduced union of B's components.
* For a geometric point `p : Spec Ω ⟶ X`, the function is evaluated at
  `p (IsLocalRing.closedPoint Ω)`. Every algebraically closed extension gives the
  same count. Quantification over underlying scheme points in the statement is
  equivalent to the geometric-point quantification: every underlying point has a
  geometric lift, and the count is independent of the chosen lift. A residue-field
  algebraic closure fits in the same universe as X; no geometric point is excluded.
* `∃ (m : ℕ) (T : Closeds X), 1 ≤ m ∧ (∀ x, D.ncBranchCount x ≤ m) ∧ ...`
  gives a finite upper bound at least one. The equality
  `(T : Set X) = {x | D.ncBranchCount x = m}` and `(T : Set X).Nonempty`
  make it an attained maximum, rather than just a bound, and give closedness and
  nonemptiness of the maximal locus.
* The center M is always the canonical `(vanishingIdeal T).subscheme`; its inclusion
  is `(vanishingIdeal T).subschemeι`. Mathlib's `vanishingIdeal` constructs precisely
  the reduced induced closed structure. The theorem gives the same affine-regular
  criterion for M as `hX` gives for X. Nonemptiness of T gives nonemptiness of M
  since the range of the canonical inclusion is T. No arbitrary center is chosen.
* The local-equation clause quantifies over every `x ∈ T`. It produces an affine
  pointed etale neighborhood `e : W ⟶ X`, `w : W`, with `e w = x`. The full family
  `t : Fin d → Γ(W, ⊤)` has germs forming a regular system of parameters at w,
  `hmr : m ≤ r`, and `hrd : r ≤ d`. The equations are equalities of ideal sheaves:
  `D.comap e = ofIdealTop (Ideal.span {∏ j : Fin m, ...})`,
  `B.comap e = ofIdealTop (Ideal.span {∏ j : Fin r, ...})`, and
  `(vanishingIdeal T).comap e = ofIdealTop (Ideal.span (Set.range ...))`.
  These are D = V(t_1 ... t_m), B = V(t_1 ... t_r), and
  M = V(t_1,...,t_m). The parameter assertion is at the chosen stalk, and neither
  the affine chart ring nor the global section ring is assumed local.
* The modification is exactly `(vanishingIdeal T).blowup`, with its published
  `.blowupMap`. The helper `.ncStrictTransformIdeal D` is the kernel of
  `AlgebraicGeometry.strictTransformMap D.subschemeι ...`, so its closed subscheme
  is the canonical scheme-theoretic strict transform up to its unique over-blowup
  closed-immersion isomorphism. In particular this is not topological closure or
  an arbitrary divisor with the same support.
* `IsEmpty (...).subscheme ∨ (...).IsNormalCrossingsDivisor` is the empty-or-normal-
  crossings assertion. The last clause is the branch inequality at every point
  y of the blowup: `(...).ncBranchCount y ≤ m - 1`. As above this is exactly the
  inequality at every geometric point, including all geometric residue extensions.

Dependency declarations used:

* `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing`, and the regular-local
  ring API used in the parameter definition. The recorded regular-scheme node
  explicitly prescribes the inline affine-neighborhood scheme clause used here.
* `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
* `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`, via the landed NC predicate.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `.blowupMap`.
* `WeilConjectures.Compactification.StrictTransform`:
  `AlgebraicGeometry.strictTransform` and `.strictTransformMap`.
* `Sheaf.AlgebraicGeometry.NormalCrossingsDivisor`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsNormalCrossingsDivisor`, from the
  landed `def-trf-normal-crossings-divisor`, added to the item's statement dependencies.
* `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, reused through the NC module.
* Mathlib's existing `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme`,
  `.subschemeι`, `.comap`, `.ofIdealTop`, and `Scheme.Hom.ker` supply the ordinary
  constructions; there is no copy of them.

The theorem additionally imports the recorded modules of all already stated proof
prerequisites. Unstated proof prerequisites need no module to type the statement:
these are the blowup flat-base-change map/theorem, the two coordinate branch lemmas,
and the etale-base-change, flat-base-change, and flat-lfp-open lemmas. No import cycle
is introduced. The recorded `lem-pc-closed-imm-base-change` declaration is
`IsVeryAmple.pullback_of_field`, which does not itself express general closed-immersion
base change; its module is retained as a recorded proof import, but this is a proof-
interface fault for the maintainer to review before stage 3. It is not used to invent
any hypothesis or construction in this statement.

Edge cases checked:

* Empty X or empty B cannot satisfy nonempty D. C empty also cannot satisfy hDne
  with its support equation. Thus positive m is asserted only in the intended case.
* Away from D the chart sublist is empty, its product is 1, and the count is 0.
* If m = 1 the reduced center is D; blowing up its invertible ideal is an isomorphism
  and its strict transform is empty. Natural subtraction gives the required bound 0.
* If m > 1, coordinate blowup charts have at most m - 1 remaining factors. Chart
  factors that are units at y do not contribute to the count.
* A divisor can have a global irreducible component with several geometric local
  branches. The count uses etale local parameter factors, never the cardinality of
  the global component set; such self-intersections remain included.
* No uniform global dimension or global parameter family is assumed. The chart
  dimension d and factor number r can vary with x.

Searches made (all service queries ran via msearch.py):

* LeanFinder: "The maximum geometric branch locus of a normal crossings divisor is
  regular and blowing it up decreases the number of branches". Eight hits concern
  smooth/etale loci and normalization, not this assertion.
* Loogle: "IsNormalCrossingsDivisor, strictTransform". Zero hits; the Mathlib service
  does not know the side-library NC identifier.
* LeanSearch: "Number of geometric local branches of a normal crossings divisor in
  an etale regular parameter chart". Eight hits concern finite irreducible components,
  etale maps and meromorphic divisors; none defines this geometric local branch count.
* LeanFinder: "Count geometric branches of a normal crossings effective Cartier
  divisor using etale local regular parameter equations". Eight hits concern etale
  loci, standard etale presentations and Weierstrass degree; none supplies the count.
* Loogle: `"branch"`. Twelve hits concern Lean internals, not geometric branches.
* Mathlib grep: `normalCrossing|normal_crossing|branchCount`, zero hits.
* Direct rg in `WeilConjectures`, `lean/Sheaf`, the DAG and upstream declaration
  names found no existing theorem or branch-count definition. They found the landed
  NC predicate and regular-parameter predicate, which are reused. Searching the item
  id in upstream sources found no declaration of this statement.
* `tools/blueprint_refs.py search branch` found four unrelated branch units;
  `search 'normal crossings'` found no blueprint units. DAG searches also found the
  coordinate branch-count theorem nodes, whose statements are not definitions of the
  global branch function and whose Lean records are absent.

Validation: both modules compiled separately through scompile.py in dependency order
without warnings on the first pass. The final imports are compiled again and the
prescribed delivery preflight is run before pushing. Auto-implicit variables are
explicitly disabled in each module; all variables and the universe u are bound.

## New nodes

`def-trf-normal-crossings-branch-count` defines the pointed etale parameter-chart
predicate and the natural-number branch function in
`Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount`. Its source is ILO VIII 4.1.6
and 4.1.8. The search records contain the actual LeanSearch, LeanFinder and Mathlib
grep responses; direct DAG/project/upstream searches found no existing global count.
The existing normal-crossings and regular-parameter predicates are reused. Taking
the infimum of the coordinate lengths is a total, explicit construction, and on the
normal-crossings locus it equals the uniquely determined coordinate branch count.
The new node is cited in the item's `stmt_deps`, with its own module and Lean record.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
