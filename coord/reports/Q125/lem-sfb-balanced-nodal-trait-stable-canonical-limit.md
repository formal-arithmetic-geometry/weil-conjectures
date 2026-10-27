## Worker report

The module `Sheaf.AlgebraicGeometry.BalancedNodalTraitStableCanonicalLimit` states
`AlgebraicGeometry.balanced_nodal_trait_stable_canonical_limit`, with `sorry` as its only
postponed proof. Its eight helper declarations construct the actual geometric closed point,
fibre, structure morphism, restricted line, normalized component degree, component union,
boundary, and coordinate-section map. These are expressions in existing notions belonging
to this statement, rather than new independent mathematical notions. There are no new DAG
nodes, dependency repairs, or changes to the item's informal statement or dependencies.

Source read: Morrison, [arXiv:0810.2340](https://arxiv.org/pdf/0810.2340), printed pp.16--17,
Proposition 10, equation (6), and Corollary 11(1); local Stacks `moduli-curves.tex`,
`lemma-gorenstein-dualizing` (Tag 0E6R) and `lemma-stable` (Tag 0E74).
Morrison's proof motivates the extremal-twister argument; the accepted DAG explicitly uses
the separately stated singular-total-space twister input rather than imposing Cartier
components. The Lean statement follows that accepted formulation.

Hypothesis-by-hypothesis correspondence:

- A DVR R: `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`. The class explicitly
  excludes fields. The fraction field K is `[Field K] [Algebra R K] [IsFractionRing R K]`.
- The family is the actual `f : X ⟶ Spec (.of R)` with `[IsProjective f] [Flat f]` and
  `[LocallyOfFinitePresentation f]`. Projectivity supplies quasi-compactness, so the last
  condition gives finite presentation as required. No regularity, smooth generic fibre,
  normality of X, or Cartier property of a component is assumed.
- `hnodal : HasNodalGeometricFibres f` is the recorded nonempty connected geometric-curve
  and ordinary-double-point predicate. `hgeometric` additionally gives reducedness and
  pure dimension one at every geometric point. This is the unmarked convention of the
  reconstruction statement; no marking divisor or marking sections are introduced.
- `omega : X.Modules` and `dualizing : NodalDualizingDatum f omega` use the existing
  Jacobian/adjunction-normalized relative dualizing datum. This is the specified canonical
  relative dualizing line, not an arbitrary invertible module. Its restriction to C is
  `BalancedNodalTrait.line f Ω omega`; reconstruction identifies that with omega_C.
- `L : X.Modules` with `[L.IsInvertible]` is the invertible module. `hgeneric` is its
  isomorphism with `omega.tensorPow 10` after actual tensor pullback to X_K, along
  `pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))`.
- Ω has the residue-field algebra and `[IsAlgClosure (IsLocalRing.ResidueField R) Ω]`.
  `closedPoint` is Spec of the residue homomorphism composed with that algebra map.
  `fiber f Ω` is exactly X_Ω, and `projection` its actual structural map.
- `g : ℕ`, `hg : 2 ≤ g`, and `hchi` render genus at least two and χ(O_C)=1-g, using the
  recorded Euler characteristic with its structural `Over` instance explicit. Natural g
  covers exactly the integer range in the node.
- The given embedding has a finite coordinate type I, map i, `hi : IsClosedImmersion i`,
  and `hover` saying it lies over Spec Ω. `e` identifies its pulled-back O(1) with L_C.
  `hcomplete` says the actual map from coordinate linear forms to Γ(C,L_C) is bijective.
  The map uses the normalized tensor-pullback adjunction unit, the existing twist-one
  coordinate sections, and the structure homomorphism for Ω-scalars. This renders both
  very ampleness and the complete embedding; no subsystem of sections is substituted.
- `hrational` takes each canonical reduced normalized component of C with genus zero
  and requires at least two preimages of the nonsmooth locus. `encard` counts branches
  on the normalization, so a self-node contributes two points.
- `htwopoint` takes the reduced component itself, requires its structural map to be
  smooth and its normalization genus to be zero, and requires its intersection with
  the complementary component union to have exactly two points. Its normalized degree
  of L_C is then one. For such a smooth rational component the normalization is the
  component itself, so this is precisely the node's degree clause.
- `hbalanced` ranges over every nonempty finite subset S of the irreducible components
  whose union is proper. Proper curves over a field are Noetherian, so this ranges over
  every reduced component union, including disconnected ones. `componentDegree` is the
  recorded Euler degree on each canonical normalization with its induced Ω-structure.
  The sums are taken on S for L_C and omega_C. The absolute-value inequality is in ℚ,
  with coefficient exactly 10 and boundary count divided by 2, without integer rounding.
  `boundary S` intersects S's component union with the union of the omitted components;
  on this nodal fibre these are exactly the nodes counted by k_Y.

Conclusion-by-conclusion correspondence:

- The existential `c : line f Ω L ≅ (line f Ω omega).tensorPow 10` is the required
  L_C ≅ omega_C^10, using dualizing base change from the recorded reconstruction theorem.
- `IsStablePointedCurve (projection f Ω)` with `Fin 0` sections and the corresponding
  empty section equations is exactly unpointed stability. Unfolding the recorded
  predicate gives genus-zero branch bound three and genus-one branch bound one on every
  normalized component at every geometric point. Its self-node convention is the same
  canonical normalized-component map used by `hrational`.
- The next universally quantified clause is verbatim the geometric genus field in
  `StablePointedModuli`: `Module.finrank F` of degree-one `RingedSpace.moduleCohomology`
  after the actual structural scalar restriction equals g. It tests every algebraically
  closed F and every Spec F → Spec Ω, including identity and extension points.
  Together with `hg` and the preceding stability clause this is the recorded genus-g
  unpointed moduli convention, without existentially choosing another curve.
- The final coordinate-section bijection uses the same i and the comparison `e ≪≫ c`.
  Thus the given complete closed immersion is itself the complete tenth-canonical
  embedding; the theorem does not merely assert existence of some other embedding.

Dependencies used, with source signatures and docstrings read:

- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`,
  `AlgebraicGeometry.Scheme.Modules.degree`: χ(L)-χ(O), with explicit structural Over.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar`: alternating finsum of finrankH.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`: Zariski-local rank-one trivializations.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`, `AlgebraicGeometry.IsStablePointedCurve`,
  `Scheme.normalizedComponentMap` and `Scheme.normalizedComponentGenus`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`,
  `AlgebraicGeometry.StablePointedModuli`: its stable and genus fields are the conclusion.
- `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction`,
  `AlgebraicGeometry.exists_nodal_log_canonical_reconstruction`, and its existing
  `NodalDualizingDatum`, `HasNodalGeometricFibres` and canonical normalization interfaces.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`,
  `AlgebraicGeometry.IsVeryAmple`/`IsAmple`: the existing finite projective-space,
  O(1)-pullback, closed-immersion convention is expanded with the complete section map.
  No replacement ample or very-ample predicate is defined.

The modules of the recorded, stated proof dependencies are imported non-publicly when
not already public. The twister proof dependency has no recorded Lean module in the base
and is not a statement prerequisite; no missing or invented module is imported for it.
The theorem docstring carries all six proof steps, including that twister input.

Edge cases checked: irreducible special fibre (no proper nonempty component union),
reducible and disconnected subcurve unions, self-nodes, smooth rational bridges, elliptic
components, empty marking family, g=2, mixed and equal characteristic, persistent generic
nodes, singular total space, arbitrary algebraically closed extension points. Empty C is
excluded by the source's nonempty connected geometric-fibre condition. Empty or zero
coordinate systems cannot satisfy the given closed complete embedding of a nonempty curve;
they are allowed in the binder and are not silently removed. The finitely many normalized
components make all degree sums and boundary ncard operations the intended finite ones.
All rings, fields, schemes, finite coordinate types and geometric test fields use the
scheme universe u, the project's size convention. No auxiliary universe equality is added.

Searches actually run:

- `msearch.py ... leanfinder`: “Balanced nodal family over a discrete valuation ring with
  generically ten canonical polarization specializes to a stable ten canonical curve”.
  Eight elliptic-reduction hits; no exact theorem.
- `msearch.py ... loogle`: `IsVeryAmple, IsStablePointedCurve, IsDiscreteValuationRing`.
  Zero hits; unknown identifier `IsVeryAmple` (project declaration, absent in Mathlib).
- `msearch.py ... grep`: `twister|pluricanonical|balanced.*polarization|stable.*nodal`
  in Mathlib AlgebraicGeometry. Zero hits.
- `msearch.py ... leansearch`: “balanced pluricanonical line bundle on nodal curves
  specializes to canonical polarization”. Eight unrelated root-system/elliptic hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the item id: no existing statement. Searches for `CompleteLinear`, `completeLinear`,
  `componentDegree`, `boundaryNodes`, `Subcurve`, `subcurve`, and `BalancedNodal`
  found normalization, complete-linear-system, and Gieseker potential-stability material,
  not this trait theorem. The newly landed `GiesekerPotentialStability.lean` was also
  read from the server with `scompile.py --source`; it states the different
  semistable-Hilbert-point implication, not this specialization result.

Validation: the final module compiled cleanly with `scompile.py` on the server, both as
sandbox module (6.1 s) and under its delivered module name (7.8 s). The initial compilation
identified the need to expose the actual fibre/projection expressions for instance
synthesis; those two views are now explicit abbreviations. No proof was filled.

## Second reading by Q125

This is the author's second pass; no independent worker was started, as the dispatch brief
forbids starting agents. The maintainer supplies the independent delivery review.

I reopened the node and final module and checked the binders in order. The actual fraction
field map and residue-field closure map land over the same R; hgeneric compares the tenth
power before restriction and c the tenth power after restriction, as required by canonical
base change. I checked hchi's sign and explicit Ω-structure. I checked that the complete
section bijection is not replaced by very ampleness of an arbitrary subsystem, and that the
conclusion retains the same i. I checked htwopoint uses smoothness of the reduced component,
not of its normalization, and that hrational counts preimages rather than singular points.
I checked that proper nonempty component unions include disconnected S, that the complement
is all omitted components, and that the division by 2 occurs in ℚ. I unfolded
IsStablePointedCurve to verify both branch bounds and reopened StablePointedModuli.genus to
verify the cohomology/scalar-restriction expression in the conclusion. No hypothesis or
clause mismatch remained. No statement correction or STATEMENT-DISPUTED flag is needed.
