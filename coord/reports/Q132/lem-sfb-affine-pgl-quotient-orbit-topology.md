## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePGLQuotientOrbitTopology` states
`AlgebraicGeometry.SchemeAction.affine_pgl_quotient_orbit_topology`, with its sole
proof postponed by `sorry`. No mathematical statement is corrected. Three helper
declarations belong to this same node: the algebra structure on the already defined
invariant ring, the equalizer on the actually base-changed action diagram, and the
image of the full orbit scheme. Definitions contain real data, without postponed
defining data or choices. The source was checked online at
https://arxiv.org/pdf/1005.2398, especially Theorems 5.3.1 and 9.1.4,
Remark 9.1.5 and Proposition 5.2.9. The module docstring carries all six proof steps.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The algebra is `(E : Type u)
  [CommRing E] [Algebra k E]`, with `[Algebra.FiniteType k E]` on the theorem.
  `affineActionScheme k E` is the recorded Spec E with its given structure map.
- The rank is `r : ℕ`, `hr : 2 ≤ r`. The group is `H : Grp (Over (Spec (.of k)))`.
  The binders π, j and `_hP : ProjectiveMatrixCentralCover.Presentation k r hr H π j`
  identify H as the actual fpqc scalar quotient and central-cover presentation in
  the dependency. They are a presentation of the named PGL group, not added
  smoothness, reducedness, torsor triviality or stabilizer assumptions.
- `[ModObj H.X (affineActionScheme k E)]` is exactly a scheme morphism giving the
  action, with unit and multiplication diagrams. The invariant ring is the existing
  `affineInvariants k E H.X`; its defining equalizer uses pullback along the action
  (in swapped order) and first projection. The recorded `affineInvariants_mem_iff`
  identifies it with `affineTensorCoaction e = e ⊗ 1`, including nilpotents.
- `affineInvariantAlgebra` uses precisely `affineInvariantConstants.toAlgebra`.
  The first conclusion `Algebra.FiniteType k (affineInvariants k E H.X)` is finite
  generation of that specified algebra. It does not assume this finite generation.
- `Surjective (affineInvariantProjection k E H.X).left` states surjectivity of
  the recorded canonical Spec-of-inclusion arrow p to `affineInvariantSpectrum`.
- In both closed-image clauses, `D : Set ...`, `IsClosed D`, and equality of
  inverse images along `ModObj.smul` and `snd` express exactly an invariant closed
  subset, with no condition on an arbitrarily chosen defining ideal. The conclusion
  `IsClosed (p.left '' D)` is closedness of its image.
- The geometric clause quantifies over every `Ω : Type u` with `[Field Ω]`,
  `[Algebra k Ω]`, `[IsAlgClosed Ω]` and every `y : Spec Ω ⟶ Y` over k. The
  existential x is an Ω-point in its fibre, by `x ≫ p = y`.
  `affineGeometricOrbit` is the set-theoretic image of the entire scheme Ω ×_k H
  in U ×_k Ω under `(g,t) ↦ (g x(t),t)`. Thus nonclosed orbit points are retained;
  it is not merely an abstract orbit of Ω-valued points.
- `IsClosed (affineGeometricOrbit ... x)` states the closed orbit. For every z
  with `z ≫ p = y`, inclusion of this orbit in the closure of the z-orbit states
  the orbit-closure assertion; closedness of the z-orbit implies equality and
  gives uniqueness as an orbit, rather than uniqueness of a representative x.
  These closedness/closure operations are in U_Ω: the fibre over the Ω-rational
  point of Y_Ω is closed, so they agree exactly with those inside U_y.
- The extension clause quantifies over every field K/k, without an algebraicity,
  separability or algebraic-closedness assumption. `extendedAffineInvariants`
  is the ring equalizer of pullbacks on global functions of the actual base-changed
  action and projection. Strong monoidal pullback identifies their common source
  with G_K ×_K U_K; the affine product identification gives
  Γ(U_K)=K ⊗_k E. Thus this is exactly `(K ⊗_k E)^(G_K)`.
- The ring equivalence from `K ⊗[k] affineInvariants` is specified on *every* pure
  tensor: `c ⊗ a` maps to the product of the pullback of c by the K-projection and
  the pullback of a by the E-projection. These generators fix the canonical map;
  no arbitrary equivalence replaces it. This also makes it a K-algebra equivalence.
- The following scheme isomorphism identifies Y_K with Spec of those extended
  invariants and requires the base-changed p to become the actual invariant
  inclusion map. `toSpecΓ ≫ Spec.map (CommRingCat.ofHom ...subtype)` is precisely
  that map. This normalization and the pure-tensor formula give the same canonical
  comparison: pullback of functions along p_K is injective, since K/k is flat and
  A ↪ E is injective, so the arrow equation determines the affine comparison.
- Finally `p_K.left '' (pr_U ⁻¹' D) = pr_Y ⁻¹' (p.left '' D)` is the requested
  equality of subsets. The source and target maps are the actual categorical
  pullbacks, not merely maps supplied as hypotheses.
- No `IsReduced`, restriction on stabilizer schemes, characteristic, inverse to r,
  domain assumption on E, or nonemptiness assumption appears anywhere.

Dependencies used and read:

- `Field`, Mathlib.Algebra.Field.Defs; `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, from the two Mathlib statement dependencies.
- `AlgebraicGeometry.ProjectiveMatrixCentralCover.Presentation`, `extension`,
  `exists_presentation` in Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover.
  Read the full presentation and normalized field-extension comparison.
- `AlgebraicGeometry.SchemeAction.affineInvariants`, `affineInvariantConstants`,
  `affineInvariantSpectrum`, `affineInvariantProjection`, the coordinate coaction,
  `affineProductCoordinates`, and `affineInvariants_mem_iff`, in
  Sheaf.AlgebraicGeometry.AffineActionStackPresentation. The equalizer, constants,
  spectrum and projection are owned by the landed definition node
  `def-sfb-affine-action-invariant-spectrum`, which is cited in `stmt_deps`.
  `def-sfb-affine-action-quotient-stack` is also cited as owner of
  `AlgebraicGeometry.affineActionScheme` in
  Sheaf.AlgebraicGeometry.AffineActionQuotientStack. The theorem
  `lem-sfb-affine-action-stack-presentation` stays in `proof_deps`, since these plain
  definitions do not depend on choosing any of its conclusions. No new definitions
  or dependency modules are needed.
- All already stated proof-dependency modules are imported privately: PGLGeometricReductivity,
  SmoothPresentationClosedSubsets, GroupScheme.SmoothGroupOrbitGeometry,
  WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme. The two adequate
  quotient/topological-image proof dependencies have no Lean records and so no
  corresponding proof imports yet; they are not needed to state the current theorem.
- Mathlib proof leaves: `Module.Flat.of_free`, `Module.Free.of_divisionRing`,
  `Module.Flat.lTensor_exact`/`rTensor_exact`, `IsClosed.exists_closed_singleton`,
  `residueFieldIsoBase` and `SpecMap_residueFieldIsoBase_inv`, imported in their
  recorded Mathlib modules. Read their signatures; they impose no unwanted
  characteristic or reducedness hypotheses.

Edge cases checked before finalizing:

- E = 0 gives empty U and Y: surjectivity is empty-to-empty; there is no geometric
  y and no false existential orbit requirement. The empty D also gives empty images.
- A trivial action gives A = E, p = identity; each geometric fibre is a single
  point, so its singleton orbit is closed and unique. No orbit-representative
  uniqueness is asserted when stabilizers are nontrivial.
- For a nontrivial action whose orbit is not closed, the closure inclusion has
  the correct direction: the unique closed orbit is contained in that closure.
- Nonreduced E and nonreduced μ_r in characteristic dividing r are admitted by
  the recorded presentation and all set/subring constructions. No reduced orbit
  or stabilizer assumption was introduced.
- K = k and inseparable K/k are included; tensor flatness holds for every field
  extension. The pullback of the reduced structure on D need not be reduced:
  the final assertion is on its underlying inverse-image subset.
- All rings, schemes, fields and tests have the common arbitrary universe u.
  There is no independent test universe below the coefficient universe, nor a
  quantifier restricted to finite extensions or rational k-points.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder "An affine PGL invariant quotient has a unique closed
  orbit in each geometric fibre and commutes with extension of the base field"`:
  8 unrelated hits (OnePoint.instGLAction, Projectivization.instMulAction,
  NumberField.InfinitePlace.orbitRelEquiv and abstract-action results), no match.
- `msearch.py ... leansearch "invariants affine algebraic group quotient unique closed orbit"`:
  8 abstract orbit, finite-group invariant or representation hits; no affine PGL
  invariant-quotient theorem. In particular Algebra.IsInvariant.isIntegral needs finite G.
- `msearch.py ... loogle "RingHom.eqLocus, Algebra.TensorProduct.map, Scheme.Spec"`:
  zero hits, with unknown identifier Scheme.Spec; inspected `AlgebraicGeometry.Spec`
  directly instead. No proposed theorem was returned.
- `msearch.py ... grep "invariant.*quotient|closed.*orbit|orbit.*closed" AlgebraicGeometry`:
  no Mathlib hits. Direct rg in the full Mathlib and both project Lean roots found
  no helper names or theorem name defined by this delivery.
- `rg` of invariant and orbit names in lean/WeilConjectures and lean/Sheaf found
  the reused scheme-action equalizer, AffinePGLAction and the finite-stabilizer
  quotient theorem. The last has the extra closed-orbit and finite-stabilizer
  hypotheses, so cannot replace this unrestricted topological statement.
- Searching this node id in lean/WeilConjectures found nothing; the occurrence
  in HilbertPluckerPGLLinearization is a proof-plan citation, not its statement.
- `scompile.py --source Sheaf.AlgebraicGeometry.AffinePGLQuotientOrbitTopology`
  returned source unavailable, confirming no current server module at this path.

Validation: `scompile.py Q132 lem-sfb-affine-pgl-quotient-orbit-topology <module>`
compiled both its sandbox form and its actual library module cleanly in 11.6 s and
10.1 s respectively. No warnings or errors remain. Maximum Lean line width is 95.
There is no STATEMENT-DISPUTED issue, node correction, new node, or dependency repair.

## Repair of returned delivery 79239bbc3784

H2 repaired exactly as requested by L. Replaced the statement dependency
`lem-sfb-affine-action-stack-presentation` with the landed definition node
`def-sfb-affine-action-invariant-spectrum`, whose existing Lean record owns
`affineInvariants`, `affineInvariantConstants`, `affineInvariantSpectrum` and
`affineInvariantProjection`. Added `def-sfb-affine-action-quotient-stack`, whose
record owns `affineActionScheme`. Read both definition-node records and the
recorded definitions in their modules. The presentation theorem remains in
`proof_deps`. The four equalizer/quotient definitions are plain definitions,
not choices from the presentation theorem, so that theorem is not a statement
dependency. Updated the dependency explanation above and the Lean record note.
Rebased the node copy on the current main-branch metadata; its mathematical
statement and proof plan are unchanged. The Lean module is byte-identical to
the returned delivery. This repair changes the dependency ownership records,
not merely the delivery base. The maintainer's independent reading of the
returned immutable head accepted the statement and all edge cases; no other
substantive repair was requested.

Repair validation: the required `scompile.py` invocation again returned clean
sandbox and library results. Lean source hash remains
`7a95d1fdb53567d6afc82439c93e2648f1dcba7de0fc3c9a1ea2149d666adfcc`.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
