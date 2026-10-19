## Worker report

The delivery states geometric projective-space cohomology in
`Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology`. Every theorem has proof
`sorry`; the hyperplane class, its powers, and the diagonal component are actual
constructions from the published Kummer and derived-tensor interfaces.

Hypothesis and clause correspondence:

- The arbitrary algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  There is no characteristic-zero exclusion, finite-field algebraicity assumption,
  or transcendence-degree bound.
- The prime is `(l : ℕ) [Fact l.Prime]`. The condition that it differ from the
  characteristic is `hl : IsUnit (l : k)`, equivalent for a prime in a field.
- The positive exponent is `(n : ℕ) (hn : 1 ≤ n)`. The coefficient ring is
  `ULift.{u + 1} (ZMod (l ^ n))`: the canonical universe lift of exactly Z/l^n.
  This lift permits ModuleCat in the prescribed site coefficient universe.
  `CharP.cast_eq_zero` supplies the required annihilation equality.
- The dimension is any `(m : ℕ)`. Projective space is the recorded
  `ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k))`: exactly m+1
  homogeneous coordinates, including m=0.
- The positive degree-one twist is `ProjectiveSpace.twist ... 1`. Its Picard
  class is `Scheme.Pic.ofIsInvertible ...`, using the existing invertibility
  instance. `Etale.kummerFirstChern` is the unique derived realization of the
  actual frame-torsor Kummer boundary, not an unspecified generator.
- `geometricProjectiveExponentUnit` states the technical invertibility needed
  to apply that Kummer construction. This follows from the existing field-unit
  hypothesis by the structure map, for every n and m; its docstring gives that
  proof. It introduces no additional hypothesis on the main theorem.
- `geometricProjectiveHyperplanePower` applies the published
  `WeilConjectures.projectiveBundleCupPowerRaw` to this exact Chern morphism.
  Its zero stage is the identity of the constant module, and its successor
  tensors the preceding class with h after the inverse unit diagonal.
- The first conjunct quantifies over all `a : ℕ` with `a ≤ m` and asserts
  `Function.Bijective (fun b : ULift (ZMod (l ^ n)) ↦ b • ... a)`.
  Scalar multiplication is the native linear structure of the module-derived
  category. Thus bijectivity is exactly the isomorphism of Lambda-modules
  b -> b h^a. No arbitrary basis or unit multiple of h is chosen.
- The second conjunct quantifies over all `q t : ℤ`. Its hypothesis is exactly
  `Odd q ∨ (2 * m : ℤ) < q ∨ q < 0`. The group is derived Hom from the constant
  coefficient object to `singleFunctor` of `finiteEtaleTateSheaf ... t`, shifted
  by q. This is ordinary small-etale module cohomology in all integer degrees.
  `Subsingleton` expresses its vanishing; it includes negative twists and degrees.
- `geometricProjectiveDiagonal ... a` is the same ordinary-derived Hom with
  the published `affineLinearBaseCoefficient` target. This target is the ordered
  derived tensor product of a shifted root lines, hence Lambda(a)[2a]. The
  locally free rank-one property of these root sheaves identifies it with the
  preceding signed-sheaf cohomology model; no primitive root is chosen.
- The third and fourth conjuncts express the diagonal algebra presentation in
  homogeneous polynomial coordinates. The third says every finite-support
  diagonal class x has components `p.coeff a • h^a` for a polynomial p. The
  fourth says that all these components vanish if and only if
  `Polynomial.X ^ (m + 1) ∣ p`. These are surjectivity of the canonical polynomial
  evaluation and kernel exactly `(X^(m+1))`, respectively. Evaluation is formed
  from the actual associative derived cup powers; consequently it is the graded
  algebra evaluation at positive h. This presentation avoids transporting an
  arbitrary ring structure onto the direct sum. It records all components,
  including a>m, and exactly the stated quotient relation.

Statement-dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, its structure-map instance, with the
  homogeneous-coordinate convention checked in the source.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `AlgebraicGeometry.ProjectiveSpace.twist` and `isInvertible_twist`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, ordinary module-derived categories.
  The former current source was also read through `scompile.py --source` because
  the older checkout lacks that file.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback` and its published root-sheaf
  construction `finiteEtaleTateSheaf`, including negative twists as internal Hom.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, as used by the ordered-power construction.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `AlgebraicGeometry.Scheme.kummerSequence_shortExact` and its Kummer boundary,
  as used by the published Chern definition.
- `def-asd-ordinary-finite-p1-kummer-class`, module
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `ordinaryFiniteUnit` in
  the main statement and diagonal Hom, and `ordinaryFiniteLine`,
  `ordinaryFiniteClass`, `ordinaryFiniteRootMap` inside the Kummer construction.
- New existing-definition owner `def-per-ordinary-kummer-first-chern`, module
  `Sheaf.Paper.KummerAdditivity`: `AlgebraicGeometry.Etale.kummerFirstChern`
  and `kummerFirstChernAbelian`. The first is the inverse of the canonical
  realization bijection, applied to the second, exactly the scalar Kummer
  boundary of the frame-torsor class. The pre-existing named helper
  `kummerFirstChernRealization_bijective` supplies that bijection; the
  conclusion of `kummer_additivity` is not used to state this item.
- New existing-definition owner `def-per-ordered-shifted-tate-powers`, module
  `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`:
  `AlgebraicGeometry.Etale.affineLinearBaseCoefficient`. Its recursion starts
  at the constant unit and tensors on the right with the shifted Tate line.
  The affine trace invariance theorem is not used to define these objects.
- New existing-definition owner `def-per-ordered-tate-cup-powers`, module
  `Sheaf.Paper.ProjectiveBundleFormula`: `WeilConjectures.projectiveBundleOrderedCup`,
  `projectiveBundleUnitDiagonal`, and `projectiveBundleCupPowerRaw`.
  These are actual ordered tensor-morphism constructions, independent of the
  theorem `projectiveBundleFormula`. The new node cites the shifted-power owner
  and the existing `ordinaryFiniteTensor` owner `def-asd-ordinary-finite-p1-arrows`.

The original six statement dependencies are retained. The rejected additions
`lem-pur-kummer-additivity` and `thm-pur-projective-bundle-formula` are removed from
`stmt_deps`. Neither main theorem is used in this item's proof plan, so neither
is added to `proof_deps`. Imports of their containing modules now refer to the
canonical definitions explicitly owned by the new definition nodes.

The available proof-dependency modules are imported without `public`: standard
charts, EffectiveCartier, proper morphisms, ordinary supported Cartier Kummer,
support long exactness, module-restriction kernel comparison, affine smoothness,
and Noetherianity. The proof dependencies geometric affine-space acyclicity,
smooth-divisor Kummer purity, and Noetherian supported product calculus currently
have no recorded Lean module, so there is no proof-module import for them yet.
They are proof prerequisites only and are not needed to elaborate this statement.

Edge cases checked against the construction and Milne Example 16.3:

- m=0 uses a single homogeneous coordinate. Only a=0 occurs in the first clause;
  h=0, all nonzero-degree cohomology vanishes, and the polynomial kernel is (X).
- a=0 is the identity/unit, giving b -> b. a=m includes the top positive class.
- q=2m+1 is covered by both oddness and the strict upper bound; q=2m is retained.
- All negative q and all negative t are included; t=0 is the constant coefficient
  sheaf. Odd negative integers do not cause a missing case.
- n=1 is included, n=0 is excluded exactly as in the source. l=2 is included.
- No choice of root, sign ambiguity, or restriction on k's transcendence degree
  occurs. The first Chern class uses the positive O(1), not its inverse.

Searches made (2026-10-18 UTC), with no exact match found:

- msearch LeanFinder: `Etale cohomology of projective space generated by Kummer
  hyperplane class`. Eight hits: projective point classes, representation
  resolutions, projective spectrum, and cotangent-complex lemmas; none is this theorem.
- msearch Loogle: `"ProjectiveSpace", "cohomology"`. Zero hits.
- msearch grep: `projectiveSpace.*[Cc]ohomology|[Cc]ohomology.*projectiveSpace|hyperplane.*[Cc]lass`.
  Only the unrelated measure-theoretic pi_hyperplane theorem.
- msearch LeanSearch: `Etale cohomology projective space truncated polynomial
  algebra hyperplane Kummer class`. Eight hits about algebraic etaleness,
  standard smoothness, and separability, not cohomology of projective space.
- rg over upstream WeilConjectures and side lean/Sheaf for hyperplane,
  projectiveSpace/cohomology, Kummer Chern, and ordinary cup. Found the reusable
  general Kummer and ordered-power constructions cited above. The specialized
  PurityFiniteSetting cohomology interfaces were inspected and not used.
- rg for this node id in upstream WeilConjectures: no match. Searches for the
  new declaration-name prefix in upstream, side Lean and dag/lean_names_upstream.json
  found no collision.

Source checked locally: Milne LEC Section 16 opening, Theorem 16.1, Corollary 16.2,
Example 16.3 (printed pages 108-109), and Section 23, proof of Theorem 23.2
(printed page 139). These cover arbitrary algebraically closed k and identify
T with the positive hyperplane class. No statement correction or dispute.

Validation: scompile.py checked both the sandbox module and the library-path module
cleanly in approximately five seconds each. Two sorry proofs remain, the main
statement and the technical invertibility lemma required by its Kummer definition.

## Second reading by N5

Self-audit with the node and final Lean file open: checked every hypothesis and
conjunct against the correspondence above. Corrected the exponent cast so it is
`((l ^ n : ℕ) : Γ(P, ⊤))`, rather than a field-global cast of l followed by a
syntactically different power. Checked m+1 coordinates, all integer q and t,
positive O(1), the exact Kummer boundary, and evaluation on every homogeneous degree.
Replaced a Prop-valued definition by the named postponed technical theorem, with
its source and complete natural-language proof. No independent worker was started:
this dispatched brief assigns independent review to the maintainer.

## New nodes

`def-per-ordinary-kummer-first-chern` records, with `existing: true`, the two
existing ordinary Kummer definitions in `Sheaf.Paper.KummerAdditivity`; no module
is copied or new declaration introduced. For every scheme T, coefficient A,
annihilating exponent N invertible on T, and Picard class M, it defines precisely
the scalar-root image of the actual boundary of M's frame torsor, realized as
the unique derived map. The signature has no finite-field, Noetherian, finite
ring or prime-power assumption. Its source is Milne LEC Section 23's
codimension-one construction and the canonical realization cited in the
existing docstrings (Stacks 03PL, 03FD, 08JA). It states no additivity theorem.

`def-per-ordered-shifted-tate-powers` records, with `existing: true`, the existing
`affineLinearBaseCoefficient` in `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`.
It defines K(0)=ordinaryFiniteUnit and K(d+1)=K(d) derived-tensor L[2], matching the
right-tensor functor in its source. The source is the shifted coefficient A(d)[2d]
in the current blueprint linear-trace lemma and its ordered-power use in the
projective-bundle computation. The definition works without invertibility of N;
no flatness or rank-one assertion is added for such general inputs.

`def-per-ordered-tate-cup-powers` records, with `existing: true`, the existing
ordered-cup recursion, unit diagonal, and raw Tate cup powers in
`Sheaf.Paper.ProjectiveBundleFormula`. The generic recursion covers arbitrary
categories and bifunctors, with explicit zero/successor identifications and
unit diagonal. Its actual ordinary-etale specialization uses the inverse
constant-unit unitor and the previous new node's ordered targets. This is
exactly the construction of the tuple (1,h,...,h^n) in the current blueprint
projective-bundle theorem and Milne Theorem 23.2. It asserts no bundle formula.

Searches for all three nodes (2026-10-18 UTC): msearch LeanSearch query
`Kummer first Chern class as derived morphism and ordered cup powers of shifted Tate sheaves`
returned eight general cochain/derived-shift declarations, no such construction;
Loogle `"kummerFirstChern", "cup"` and Mathlib grep
`kummerFirstChern|projectiveBundleCupPowerRaw|affineLinearBaseCoefficient` returned
zero hits. The exact emitted JSON records are copied verbatim into each new
node's `mathlib_searches`. The same rg over upstream returned no hits; the side
project search found precisely the existing definitions reused above. DAG
search found only the three theorem-node records as owners, with no definition
node for these interfaces; mentions in unrelated review notes are not owners.
`blueprint_refs.py search 'ordered tensor'` found zero nodes; search
`'first Chern class'` found only the projective-line trace, tower classes and
projective-line decomposition. The already-landed P1 definition supplies the
unit, line, scalar-root map and realization map, and is cited rather than copied.

## Returned delivery repair

Return L on immutable head `d301f65e260a`, H2, is repaired point by point:
canonical Kummer and ordered cup definitions now have definition-node owners;
the shifted Tate-power definition formerly owned only by a theorem now has its
own definition node; `def-asd-ordinary-finite-p1-kummer-class` is cited directly;
and the two unused theorem nodes are absent from `stmt_deps`. No mathematical
statement, hypothesis, proof plan or proof dependency was changed. Compared with
the current shared base, the item changes only `lean` and `stmt_deps`; the latter
keeps the original six entries and adds the existing unit owner plus the three
new definitions. The saved packet initially passed dry run as `e16525326c`, but
the return's ownership fault still required this repair.

Repair self-reading by N5: opened the three full existing definitions and their
source docstrings, all four new/fixed node records, and the complete retained
item statement. Checked the Kummer map uses `Equiv.ofBijective` of the named
realization comparison rather than the additivity theorem. Checked the raw cup
map uses only ordered recursion and the inverse constant-unit unitor, with the
same ordered right-tensor targets in `geometricProjectiveDiagonal`. At a=0 these
maps are the identity, and the target is the ordinary constant unit. The existing
field, prime, exponent, dimension, vanishing, positive hyperplane, and polynomial
clauses remain as matched in the Worker report; m=0 and all integer q,t remain
included. Checked the new dependency closure is acyclic. No second agent was
started, as the dispatched brief forbids delegation and assigns independent
review to the maintainer.
