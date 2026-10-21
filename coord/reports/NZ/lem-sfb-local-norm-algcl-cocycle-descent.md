## Worker report

The module `Sheaf.RepresentationTheory.LocalNormAlgclCocycleDescent` states
`Representation.local_norm_algcl_cocycle_descent`, with its sole proof `sorry`.
It introduces no definitions, instances, or additional theorems. The node is
copied without changes except for `lean`; its mathematical statement and all
statement and proof dependencies are preserved.

The previous worker's stale-assignment objection confused the completed stage-1
split with completion of stage 2. The live node has Q06's reviewed split but no
`lean` record, and no module or existing declaration states this assertion.
This delivery supplies that missing statement and does not split the node.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- The algebraic closure with its extended norm is `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. A normed algebra between
  normed fields makes the scalar embedding isometric: its norm is exactly the
  given p-adic norm on the base. No completeness instance on Ω is requested.
  Ω is an arbitrary algebraic closure, not the completion or one fixed model.
- A finite intermediate coefficient field is `(E : IntermediateField ℚ_[l] Ω)
  [FiniteDimensional ℚ_[l] E]`. Its topology is the norm subspace topology
  inherited from Ω. Uniqueness of the extended absolute value identifies this
  with the coefficient node's spectral norm topology.
- The arbitrary profinite group is `(G : ProfiniteGrp.{v})`. No generation,
  cohomological dimension, countability, or normal-subgroup restriction is added.
- The vector space is `(W : Type w) [AddCommGroup W] [Module E W]`, and the
  linear automorphism action is `(ρ : G →* (W ≃ₗ[E] W))`.
- `hρ : Representation.IsContinuousCoefficient l E G W ρ` is precisely the
  recorded representation dependency's clause (2): it asserts both
  `FiniteDimensional E W` and joint continuity of the action in the canonical
  finite-dimensional module topology over the spectral-norm topology of E.
  Thus finite dimension and continuity are genuine hypotheses and not omitted.
  The topology on W needs no independent parameter because the specified
  finite-dimensional norm topology is canonical.
- The scalar extensions are the actual tensor products `Ω ⊗[E] W` and
  `F ⊗[E] W`. Their topologies are specified explicitly as
  `moduleTopology Ω (Ω ⊗[E] W)` and `moduleTopology F (F ⊗[E] W)` in the
  `@ContinuousMap` arguments. A finite basis identifies this module topology
  with the product topology on the scalar field's finite power, also for
  incomplete Ω. The construction does not complete any tensor product.
- `Representation.coefficientScalarExtension E L G W ρ` for `L = Ω` or `F`
  is the recorded scalar-extension action: it fixes the scalar factor and
  acts by ρ on W. For the open subgroup the same action is evaluated at
  `(g 0 : G)`, giving exactly restriction of the original action.
- `(n : ℕ)` denotes the node's positive degree `n + 1`. Every integer degree
  at least one occurs, with no upper bound. This avoids truncated predecessor
  expressions and preserves the degree-one case.
- `z : @ContinuousMap (Fin (n + 1) → G) (Ω ⊗[E] W) ...` is the continuous
  degree-(n+1) cochain. The hypothesis `hz` is exactly `dz = 0`, evaluated at
  every tuple `g : Fin (n + 2) → G`.
- In `hz`, the term `coefficientScalarExtension ... (g 0)
  (z (fun i ↦ g i.succ))` is the first action term. The sum over
  `j : Fin (n + 2)` uses `(-1 : ℤ) ^ (j.val + 1)` and
  `Fin.contractNth j (· * ·) g`. For j below the last index this multiplies
  adjacent entries. At the last index it deletes the last entry. Thus this
  is the node's full alternating inhomogeneous differential, with all signs.
  Integer scalar multiplication equals the signed E-linear scalar action.
- `∃ H : OpenSubgroup G` supplies a subgroup open in the original profinite
  topology. Its type carries the induced subgroup topology; it need not be normal.
- `∃ F : IntermediateField E Ω, ∃ _ : FiniteDimensional E F` supplies a field
  containing E inside Ω, finite over E and consequently over ℚ_[l]. Conversely
  every finite intermediate extension containing E is represented in this form.
- The existential `u` is a bundled continuous function from `H^(n+1)` to the
  actual `F ⊗[E] W` with its specified product topology.
- The first conjunct after the existential binders is the identical cocycle
  equation for `u`, evaluated on `Fin (n + 2) → H`. It says `du = 0` in
  `F ⊗[E] W` itself, rather than merely after scalar inclusion.
- The existential `b` is a bundled continuous function from `H^n` to
  `Ω ⊗[E] W`, exactly a cochain one degree below z and u.
- In the final equation, `z (fun i ↦ (g i : G))` is restriction to `H^(n+1)`.
  `TensorProduct.map (IsScalarTower.toAlgHom E F Ω).toLinearMap
  (LinearMap.id : W →ₗ[E] W) (u g)` is the canonical coefficient inclusion,
  explicitly sending `a ⊗ w` to `(a : Ω) ⊗ w`; no arbitrary map is supplied.
- The remaining parenthesized action term and alternating sum are precisely
  `db` in the same pointwise differential. Therefore the conclusion is the
  actual equality `z|H = inclusion(u) + db` requested by the node.
- No quotient or topological closure is used: the equality supplies an actual
  primitive, hence equality of classes in the ordinary kernel modulo image.
  There is no condensed or derived-invariants identification in the signature.

Dependency declarations read and used:

- `Sheaf.RepresentationTheory.LAdic`:
  `Representation.IsContinuousCoefficient` and
  `Representation.coefficientScalarExtension`. I read their full signatures,
  bodies, and docstrings. The node's main declaration `Representation.IsLAdic`
  is also read; this item uses its finite-E clause, not an arbitrary Ω-action.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, whose module publicly imports the
  unchanged `Sheaf.NumberTheory.Padics.CoefficientExtension` constructions.
  I read both files, including `Padic.coefficientExtensionAbsoluteValue` and
  its spectral norm specification. The finite-ring theorem is not an additional
  hypothesis; the item only needs this dependency's coefficient-field norm.
- Mathlib `Mathlib.LinearAlgebra.FiniteDimensional.Defs`:
  `FiniteDimensional`, the recorded `mathlib_match` of
  `def-weil-finite-dimensional-subspace`, is `Module.Finite` over a division ring.
  It appears on E and F and in the continuous-representation predicate.
- Mathlib `moduleTopology`, `ContinuousMap`, `OpenSubgroup`, `IntermediateField`,
  `TensorProduct.map`, `IsScalarTower.toAlgHom`, and `Fin.contractNth` supply
  the standard notions and canonical maps directly. No private copies are made.
- The proof dependency `lem-sfb-baire-closed-cover-interior` has Mathlib match
  `nonempty_interior_of_iUnion_of_closed`, whose signature and docstring I read
  in `Mathlib.Topology.Baire.Lemmas`; its local-compactness Baire instance is in
  `Mathlib.Topology.Baire.LocallyCompactRegular`. Both are plain proof imports.
  The three other proof dependencies have no Lean record or Mathlib match, so
  there is no module to import yet. Their full statements were read and are
  included by name in the five-step natural-language proof docstring.

Edge cases checked before writing the statement:

- Original degree one is `n = 0`: `Fin 0 → H` is the one-point empty tuple
  space, so b is one vector. The sum defining its differential has the sole
  last face with sign -1, yielding `g b - b`.
- Original degree two has faces `g1 z(g2,g3) - z(g1*g2,g3)
  + z(g1,g2*g3) - z(g1,g2)`, confirming the index and sign conventions.
- Rank-zero W gives zero tensor spaces and zero continuous cochains, with no
  positivity or nontriviality restriction on W.
- The trivial profinite group and finite profinite groups are permitted.
  The subgroup quantifier permits H = G and non-normal open subgroups.
- The finite extension may be E itself (`F = ⊥` as an E-intermediate field).
- Group, coefficient field, and W have independent universes v, u, w; there
  is no extra equality of unrelated universes.
- Ω need not be complete. Its topology is the extended norm topology, and
  neither W nor the coefficient extensions are given discrete topologies.

Searches for an existing statement or construction (2026-10-21 UTC):

- `msearch.py ... leanfinder` query: "A continuous cocycle on a profinite group
  with algebraic closure of a p adic field coefficients becomes cohomologous
  to a finite extension valued cocycle on an open subgroup". Eight hits:
  Hilbert 90 and ordinary group-cohomology induction/cocycle declarations;
  no local finite-field descent theorem.
- `msearch.py ... leansearch` query: "A continuous cocycle with algebraic
  closure of a p adic field coefficients descends on an open subgroup to a
  finite extension valued cocycle". Eight hits, including
  `groupCohomology.cocycles₁`, `PadicAlgCl`, its algebraicity instance, and
  continuity of Galois/cyclotomic maps; no matching theorem.
- `msearch.py ... loogle` query `ContinuousCohomology.cocycles,
  ContinuousCohomology.inhomogeneousCochains` initially returned zero hits
  with unknown second identifier. Corrected query `"cocycle", "Continuous"`
  returned eight hits headed by `ContinuousCohomology.cocycles` and its
  functoriality and degree-zero comparison. These homogeneous cocycle APIs
  do not state the asserted local descent result.
- `msearch.py ... grep` query
  `(cocycle|coboundary).*(Padic|IntermediateField)|(Padic|IntermediateField).*(cocycle|coboundary)`:
  zero hits in Mathlib.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for continuous cochains,
  inhomogeneous differentials, local/finite cocycle descent, and the node id:
  no declaration for this item. The parent
  `Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison`
  names this obligation in its proof docstring. Discrete cochain APIs impose
  a different coefficient topology. Mathlib's `inhomogeneousCochains.d`
  supplies the same standard tuple formula for abstract cochains, but its
  bundled `Rep` interface fixes field/group universes together. I write the
  node's displayed equations directly using the existing tuple operations,
  rather than introduce a second differential definition or restrict universes.
- `rg` for the new full declaration name across Mathlib, `WeilConjectures`,
  and `Sheaf`: no name collision. The existing `moduleTopology` and tensor
  scalar-extension action make additional definition nodes unnecessary.

Validation: `scompile.py NZ lem-sfb-local-norm-algcl-cocycle-descent` compiled
this file cleanly in sandbox mode (10.4 s) and library module mode (10.9 s).
An initial nonexistent Mathlib intermediate-field import was corrected to
`Mathlib.Analysis.Normed.Algebra.Basic` before the successful compile.
There are no warnings, implicit universe variables, auxiliary proofs, or
postponed definitions. The only `sorry` belongs to the named item theorem.
No statement correction or disputed statement is proposed. The node's source
already marks the exact literature reference WANTED; its full agent proof
plan is retained in the theorem docstring for stage 3.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
