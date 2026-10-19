## Worker report

The module `Sheaf.RingTheory.FiniteHenselianAlgebraLocalModel` states
`AlgebraicGeometry.Scheme.finite_henselian_algebra_local_model`, with proof `sorry`.
No definition is introduced and the mathematical statement is unchanged.
The proof docstring records all nine steps of the node, including the residue-field
identification, locality detected by completion, descent, neighbourhood-leg compatibility,
and the strict-local comparison over the specified base.

Hypotheses and clauses, checked individually against the node:

- Commutative Noetherian D: `(D : Type u) [CommRing D] [IsNoetherianRing D]`.
- Finite-type commutative D-algebra R₀: `[CommRing R₀] [Algebra D R₀]`
  and `[Algebra.FiniteType D R₀]`. This is the instance form of the recorded
  `RingHom.FiniteType`, related by `RingHom.finiteType_algebraMap`.
- Maximal q with separably closed residue field: `(q : Ideal R₀) [q.IsMaximal]`
  and `[IsSepClosed q.ResidueField]`. The ring residue field is Mathlib's
  `Ideal.ResidueField`, canonically the scheme residue field through
  `Spec.residueFieldIso`; no replacement residue-field construction is introduced.
- H is the local henselization: `[Algebra (Localization.AtPrime q) H]`,
  `[HenselianLocalRing H]`, and `hH : Algebra.IsHenselizationAtPrime' R₀ q H`.
  This is precisely the recorded universal-property interface, not an extra
  henselianity assumption: the interface takes that structure as part of its data.
- The completion is literally `AdicCompletion (IsLocalRing.maximalIdeal H) H`.
- Finite commutative H-algebra C: `[CommRing C] [Algebra H C] [Module.Finite H C]`.
- Nonzero local completed tensor: `[IsLocalRing (AdicCompletion
  (IsLocalRing.maximalIdeal H) H ⊗[H] C)]`. Mathlib's `IsLocalRing` extends
  `Nontrivial`, so this includes the node's nonzero condition explicitly through
  the standard definition; it is not silently dropped.
- First conclusion: `IsNoetherianRing C ∧ IsStrictlyHenselianLocalRing C`.
  The upstream strict-henselian class extends the henselian local-ring class
  and asserts separably closed residue field; no local instance on C is assumed.
- Finite-type R₀-model: existential F with `CommRing F`, `Algebra R₀ F`,
  and `Algebra.FiniteType R₀ F`.
- Maximal point z over q: `(z : Ideal F) (_ : z.IsMaximal)` and
  `z.comap (algebraMap R₀ F) = q`.
- Geometric point supported at z: existential Ω with `Field Ω`, `IsAlgClosed Ω`,
  and `barZ : Spec (.of Ω) ⟶ Spec (.of F)` satisfying
  `(barZ (IsLocalRing.closedPoint Ω)).asIdeal = z`.
- Isomorphism over R₀: existential `e : C ≃+* strictHenselizationRing barZ`.
  Its additional equation uses `Spec.map` of `e.symm` followed by the canonical
  strict-henselization structural morphism and Spec of R₀ → F. The result is
  exactly Spec of the composite R₀ → (R₀)_q → H → C. Contravariance and faithfulness
  of Spec identify this equation with the R₀-linearity condition for e.
  In particular no arbitrary algebra structure on the strict local ring is chosen.
- The final finite-type clause is
  `((algebraMap R₀ F).comp (algebraMap D R₀)).FiniteType`.
  For this affine morphism this says exactly that Spec F → Spec D is finite type.
  The specified image of z in Spec R₀ is already the contraction equation above.

All objects live in arbitrary universe u. There is no finite/countable carrier
restriction, no independent smaller test universe, no `let` in the signature,
and no auto-bound implicit. The henselization interface tests rings in the same
common universe; Ω can be an algebraic closure of the finite residue extension
in that universe. The existential rings have their structures bound explicitly.

Dependency declarations read and reused:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; companion declarations `isNoetherianRing_iff`
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`, `RingHom.FiniteType`
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`; companion declarations `AlgebraicGeometry.Scheme.residueField`, `AlgebraicGeometry.Scheme.Hom.residueFieldMap`
- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosure`; companion declarations `IsSepClosed`, `IsSepClosure`
- `def-weil-pbc-henselization-at-prime`: `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`, `Algebra.IsHenselizationAtPrime'`
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`; companion declarations `AdicCompletion`, `IsAdicComplete`
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, `Mathlib.LinearAlgebra.TensorProduct.Defs`; the algebra ring structure is imported through `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-henselian-terminology`: `WeilConjectures.Mathlib.RingTheory.Henselian`, `IsStrictlyHenselianLocalRing`; companion declarations `HenselianRing`, `HenselianLocalRing`, `IsStrictlyHenselianLocalRing`
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`; companion declarations `IsAlgClosed`, `AlgebraicGeometry.Scheme.SpecToEquivOfField`
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`; companion declarations `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`
- `def-weil-pbc-strict-henselization-limit`: `Sheaf.AlgebraicGeometry.StrictHenselization`, `AlgebraicGeometry.Scheme.strictHenselizationRing`; companion declarations `AlgebraicGeometry.Scheme.strictHenselizationRing`, `AlgebraicGeometry.Scheme.strictHenselizationScheme`, `AlgebraicGeometry.Scheme.strictHenselization_properties`
- `def-weil-pbc-strict-henselization-structural-map`: `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`, `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap`; companion declarations `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap`, `AlgebraicGeometry.Scheme.exists_strictHenselizationStructuralMap`

The existing landed node `def-weil-pbc-strict-henselization-structural-map` was added
to stmt_deps because its canonical map expresses the R₀-algebra compatibility.
Its current server source was read with `scompile.py --source`; the upstream module
is imported to avoid duplicate names from an older local wrapper. Every already
recorded proof dependency with a module (including Mathlib matches) is imported
without `public`, unless it is already a statement import. There are no new nodes or dependency repairs.

Edge cases checked: the zero algebra C cannot satisfy the completed tensor's
`IsLocalRing` instance, and a product of two nonzero factors is excluded by its
nontrivial idempotent. A zero D or R₀ cannot supply the required maximal ideal.
A separably closed field base with C = H gives the identity example. Nonreduced
finite local algebras are allowed. Finite purely inseparable residue extensions
are allowed: Ω is algebraically closed, whereas q.ResidueField is required only
to be separably closed. Neither perfectness nor reducedness nor flatness of C
is assumed. A maximal ideal over the specified q is retained rather than an
arbitrary prime or a point merely over Spec D.

Source reading: ILO Expose V proof 2.2.7 (PDF pp. 65–66), finite presentation and
filtered-colimit descent; Stacks algebra.tex `lemma-finite-over-henselian`
(Tag 04GH), and `lemma-quasi-finite-henselization` (Tag 05WP).
The source proof and the node's expanded proof agree with the statement.
No statement correction or disputed statement was needed.

Searches for an existing statement (all negative for an exact match):

- msearch.py LeanFinder: “finite algebra over henselization local model strict
  henselian local ring”: eight hits on `HenselianLocalRing`, fields, and residue
  finiteness, with no finite-type strict-local-model theorem.
- msearch.py Loogle: `IsStrictlyHenselianLocalRing, IsHenselizationAtPrime`:
  zero hits; the first identifier is unknown to the Mathlib-only search service.
- msearch.py LeanSearch: “A finite algebra over a henselization whose completed
  base change is local is a strict henselian local ring and has a finite type
  local model”: eight hits, chiefly henselian definitions and TFAE, no match.
- msearch.py grep `henseli.*(finite|model)|(finite|model).*henseli` in RingTheory:
  zero hits. Initial grep `IsStrictlyHenselianLocalRing|IsHenselizationAtPrime|Algebra.FiniteType`
  with the WeilConjectures subdirectory also returned zero (Mathlib search only).
- Direct rg of `IsHenselizationAtPrime|finite_henselian.*model|henselian.*local.*model`
  in project Lean and source WeilConjectures found existing henselization consumers
  and the recorded generalized definition, but no theorem matching this node.
- Direct rg of the item id in source WeilConjectures returned no hit.
- Direct rg of `finite_henselian_algebra_local_model` in the upstream-name index,
  source WeilConjectures and project Lean returned no hit before writing the module.

Validation: scompile.py compiled both its sandbox probe and the real module cleanly
(2.4 s and 2.7 s respectively), without errors or warnings. The first compile caught
Spec contravariance and the absence of a scheme `FiniteType` predicate; the equation
now correctly uses e.symm and the affine finite-type consequence uses RingHom.FiniteType.
The theorem proof remains exactly `by sorry`.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
