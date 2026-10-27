## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalDiagonalizableClopenLift` states
`AlgebraicGeometry.strictLocalDiagonalizableClopenLift`. Its sole proof is `sorry`.
No definition or additional theorem is introduced. The statement and proof plan of the
node are preserved. The already landed definition node
`def-weil-pbc-strict-henselization-structural-map` is added to `stmt_deps` to name the
canonical map used in the base change; no other existing field changes except `lean`.

Source checked online: Conrad, *Reductive group schemes*, Theorem B.4.1 proof, printed
pp.298--299, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf.
In particular, the paragraph constructing the clopen lift explicitly distinguishes its
special-fibre-only hypothesis from the hypotheses used subsequently to prove the lift
surjective. The module docstring carries all five steps of the node's actual proof plan,
including its henselian G-ring approximation route in place of the later all-fibres
torsion-map argument. No statement correction or disputed statement is needed.

Clause-by-clause translation:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme S and group scheme over S, with all group diagrams | `{S : Scheme.{u}} (G : Grp (Over S))`; `G.X` is the underlying object over S and `G.X.hom` its structure map. Mathlib's `Grp` allows arbitrary group objects, including noncommutative ones. |
| Affine structure morphism | `[IsAffineHom G.X.hom]` |
| Flat structure morphism | `[Flat G.X.hom]` |
| Finite presentation, with precisely the stated meaning | `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]` |
| Arbitrary geometric point with algebraically closed field Omega | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barS : Spec (.of Ω) ⟶ S)` |
| Finitely generated additive abelian group M0 | `(M₀ : Type u) [AddCommGroup M₀] [AddGroup.FG M₀]` |
| An isomorphism of Omega-group schemes G_Omega with D_Omega(M0) | `hgeom : Nonempty ((Over.pullback barS).mapGrp.obj G ≅ ringDiagonalizableGroup Ω M₀)`; this is an isomorphism in `Grp (Over (Spec (.of Ω)))`, retaining the group operations. |
| C is the specified pointed-neighbourhood coordinate-ring colimit, not a replacement strict localization | `Scheme.strictHenselizationRing barS`; its `Spec` is definitionally `Scheme.strictHenselizationScheme barS`. |
| T maps canonically to S | `Scheme.strictHenselizationStructuralMap barS`, the existing map characterized by the common composites of the neighbourhood limit legs. |
| k is C modulo its unique maximal ideal | `@IsLocalRing.residue (Scheme.strictHenselizationRing barS) _ (Classical.choose (strictHenselizationLocalStructure barS))`. Its codomain is exactly `IsLocalRing.ResidueField C = C ⧸ IsLocalRing.maximalIdeal C`. The explicit chosen value is a proof of locality supplied by the recorded theorem, not chosen ring or field data. Proof irrelevance makes the quotient independent of that proof. |
| There is a finitely generated additive abelian group M | `∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M), ...` |
| A T-group homomorphism j from D_C(M) to G base changed to T | `∃ j : ringDiagonalizableGroup (Scheme.strictHenselizationRing barS) M ⟶ (Over.pullback (Scheme.strictHenselizationStructuralMap barS)).mapGrp.obj G, ...` |
| j is an open immersion and a closed immersion | `IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left` on its underlying scheme morphism. |
| The special-fibre homomorphism of this very j is an isomorphism | `IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (@IsLocalRing.residue ...))))).map j.hom.hom).left)`. This is the actual pullback of j along `Spec k → Spec C`, not an unrelated isomorphism between its fibres. |
| Source and target of that fibre map | Its source is `(D_C(M))_k`, canonically `D_k(M)` by `k ⊗_C C[M] ≅ k[M]`, with basis map `a ⊗ e_m ↦ a e_m`. Its target is `(G_T)_k`, canonically `G ×_S Spec k` by pullback associativity. These are the same fibre objects in the node, represented using the existing pullback construction. Scalar extension preserves the Hopf operations on every basis element. Since j is already a group homomorphism, invertibility of its underlying special-fibre scheme map is equivalent to invertibility as a k-group homomorphism. |
| No additional hypotheses | No hypotheses about other fibres, torsion orders, smoothness, commutativity or Noetherianity occur. No algebraicity condition on Omega occurs. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions` has a convention record, not a new definition;
  its finite-presentation convention is rendered using the preceding property together
  with `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated`, from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `...QuasiSeparated`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric-point node's
  inline convention is used without requiring a bundled point or an algebraic closure.
  The recorded `Scheme.SpecToEquivOfField` signature was also read.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`, the recorded Hopf spectrum construction
  for arbitrary coefficient rings. Its signature, docstring, and real body were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`; `CategoryTheory.Over.pullback` from
  `Mathlib.CategoryTheory.Comma.Over.Pullback` packages the same fibre product, and
  `Functor.mapGrp` from `Mathlib.CategoryTheory.Monoidal.Grp` carries its group structure.
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` provides the monoidal pullback instance.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationRing` and
  `AlgebraicGeometry.Scheme.strictHenselizationScheme`; the ring remains the specified
  colimit over all representative affine pointed neighbourhoods.
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`:
  `AlgebraicGeometry.strictHenselizationLocalStructure`, exactly the recorded interface
  giving a proof of locality and strict henselianity for that colimit ring.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, whose recorded
  docstring and signature identify the quotient by a maximal ideal. For the already local
  ring C the rendering uses `IsLocalRing.residue` from
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs`, the underlying local-ring construction.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- Added landed node: `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`,
  `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap`; the existence theorem's
  full characterization and the definition were read as well.

The recorded non-Mathlib proof modules `Sheaf.Paper.StrictHenselizationPointedMap` and
`WeilConjectures.RingTheory.AdicCompletionNoetherian` are plain proof imports. Mathlib
proof inputs on completion, flat base change, finite presentation and finitely generated
abelian groups are imported as well. The three immersion/permanence inputs and affine
fibre-product input are already supplied by the public geometric imports. The four
group-theoretic lifting/splitting/approximation proof nodes have no recorded module yet;
their names and mathematical uses are retained in the proof docstring, with no fabricated
imports or extra claims in this delivery.

Edge cases checked before writing:

- The trivial character group is allowed (for example `ULift PUnit`); no positive rank,
  nontrivial torsion, or faithfulness hypothesis was introduced.
- Torsion of order divisible by the residue characteristic is allowed: no smoothness or
  reducedness is required of the diagonalizable fibre.
- G need not be commutative away from the chosen fibre, and its other fibres can vary.
- The geometric point can have transcendental algebraically closed coefficient field:
  no `Algebra.IsAlgebraic` or equality with an algebraic closure is required.
- Empty S has no geometric point, so there is no omitted case there; the chosen C is
  local by the recorded theorem, without an extra user-supplied local-ring hypothesis.
- Quasi-compactness and quasi-separatedness are kept explicitly as the node requests;
  affineness may imply them, but this does not strengthen the hypotheses.
- The single explicit universe `u` is the standard scheme/coefficient universe. Every
  finitely generated abelian group has a small representative here; no independent test
  universe makes a geometric-point or algebra hypothesis vacuous. `autoImplicit` is false.

Searches performed (through the prescribed msearch wrapper where applicable):

- `leanfinder`, query: `A flat affine finitely presented group scheme with diagonalizable
  geometric special fibre has a clopen diagonalizable subgroup over the strict
  henselization`. Result: 8 hits, including
  `HasAffineProperty.diagonal_affineProperty_isLocal`,
  `FormallyUnramified.isOpenImmersion_diagonal`, and related diagonal properties. None
  states the clopen lifting result.
- `loogle`, query: `"Grp", "IsOpenImmersion"`. Result: 0 hits.
- `grep`, query: `diagonalizable|Diagonalizable|clopen` under Mathlib
  `AlgebraicGeometry/Group`. Result: 0 hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, query:
  `diagonalizable|Diagonalizable|strictLocal.*[Ll]ift|strict.*[Cc]lopen`. Found the ring
  and field diagonalizable-group definitions, antiduality and unrelated clopen restriction
  results; no theorem matches this node. A further search of
  `ringDiagonalizableGroup|strict.*[Cc]lopen|strictLocalDiagonal` located the ring
  definition and different special-kernel lifting statements, not this result.
- Search for the exact node id in `lean/WeilConjectures`: no hits.
- Name collision check `strictLocalDiagonalizableClopenLift` in the upstream name index,
  Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no hits before the sandbox file.

Validation: `scompile.py Q26 lem-sfb-strict-local-diagonalizable-clopen-lift` compiled
the delivered file in both sandbox and library module mode without errors or warnings.
The sole postponed proof is the named theorem corresponding to the delivered DAG node.
All writes are confined to the assigned sandbox; server compiles and delivery use only
the prescribed wrappers. The maintainer supplies the independent review, as requested
by the dispatcher brief; no second worker or sub-agent was started.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
