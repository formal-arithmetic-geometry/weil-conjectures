## Worker report

Delivered `Sheaf.TraceFormula.FiniteEtaModificationSpreading`, containing the single
statement `AlgebraicGeometry.exists_finite_eta_modification_spreading`, with proof
`sorry`. There are no definitions, helper theorems, new nodes or dependency repairs.
Only the item's `lean` field changes. No statement correction or disputed statement.

Source read: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
Theorem 3.5.5 Step 5 (printed p. 24); §3.1 and Remark 3.1.1(i) (pp. 14–15);
the opening definitions of §3 (pp. 13–14). The PDF at the node's huji URL timed out;
the identical v3 was read at https://arxiv.org/pdf/0707.3953 . Step 5 spreads the finite
generic modification to a generically etale affine quasi-alteration. Section 3.1
provides finite-presentation/map approximation and eventual flatness; the remark
provides descent of reduced geometric fibres. Temkin's quasi-alteration requires an
integral source, separated finite type, and a finite function-field extension; it
does not require an integral morphism or surjectivity. The Lean spells out these
conditions rather than introducing a second definition.

Hypothesis-by-hypothesis correspondence:

- `R` is a commutative domain: `[CommRing R] [IsDomain R]`.
- `F = Frac R`: `[Field F] [Algebra R F] [IsFractionRing R F]`. This retains an
  arbitrary model of the fraction field, with its actual structure map.
- `L/F` is separable algebraic: `[Field L] [Algebra F L] [Algebra.IsSeparable F L]`.
  The last class includes algebraicity (as its Mathlib docstring states).
  `[Algebra R L] [IsScalarTower R F L]` merely record the composite embedding.
- `V` is the specified valuation subring of `L`: `V : ValuationSubring L`. Its
  `mem_or_inv_mem` is the stated valuation condition; the zero case adds no condition
  since zero is in every subring. The canonical `IsFractionRing V L` instance is
  supplied by Mathlib. `[Algebra R V] [IsScalarTower R V L]` say that the inclusion
  `R -> L` factors through `V`. This map is automatically injective: `R -> F` is
  injective, and the field map `F -> L` is injective. No extra injectivity hypothesis.
- `A` is a commutative flat finitely presented `R`-algebra:
  `[CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]`.
- The specified `A_V`-algebra `B` is `[CommRing B] [Algebra V B]` together with
  `u : (V ⊗[R] A) →ₐ[V] B`. We use the canonical symmetric left-factor convention
  `V ⊗[R] A` for the node's `A ⊗[R] V`; tensor symmetry identifies their structure
  maps. Giving `u` is precisely giving the algebra structure over this ring,
  compatibly with the `V`-algebra structure. `(hu : u.Finite)` means module-finite
  for this actual map, not for an unrelated module structure.
- `B` is flat and finitely presented over `V`: `[Module.Flat V B]` and
  `[Algebra.FinitePresentation V B]`.
- The given map on generic fibres is an isomorphism: `hgeneric` is bijectivity of
  `Algebra.TensorProduct.map (AlgHom.id L L) u`. Its source is
  `L ⊗[V] (V ⊗[R] A)` and target is `L ⊗[V] B`. Associativity/base-change
  cancellation gives exactly the node's map. Bijectivity of an algebra homomorphism
  is equivalent to being an algebra isomorphism; an arbitrary replacement map is
  not quantified or chosen.
- Every algebraically closed field-valued base change is reduced: `hgeom` quantifies
  `Ω`, `[Field Ω] [IsAlgClosed Ω] [Algebra V Ω]` and asserts
  `_root_.IsReduced (Ω ⊗[V] B)`. The root qualification selects reduced rings,
  rather than `AlgebraicGeometry.IsReduced` for schemes.

Conclusion clause-by-clause:

- `∃ R' : Subalgebra R V, R'.FG`: the actual finitely generated subalgebra inside
  the given valuation ring, with its inherited `R`-algebra structure and inclusion.
- `F'` comes with a field structure, `Algebra R' F'`, and `IsFractionRing R' F'`:
  it is exactly the fraction field of the selected subalgebra. `Algebra F F'`,
  `Module.Finite F F'`, and `Algebra.IsSeparable F F'` render finite separable
  extension. The displayed equality on each `r : R` ensures that this is the
  canonical extension of `F = Frac R`, by uniqueness in the fraction-field
  universal property. There is no arbitrary unrelated field-extension structure.
  The inclusion `R' -> V -> L` extends uniquely to an embedding `F' -> L`, which
  automatically agrees with the given embedding of `F`.
- `∃ B', CommRing B', Algebra R' B', u' : (R' ⊗[R] A) →ₐ[R'] B'`: the required
  commutative algebra over `A'`, using the same symmetric tensor convention.
- `u'.Finite ∧ u'.FinitePresentation`: finite as an `A'`-module and finitely
  presented as an `A'`-algebra, for the specified structure map `u'`.
- `Module.Flat R' B' ∧ Algebra.FinitePresentation R' B'`: flat finitely presented
  over the selected base subalgebra.
- The universal `Ω` clause repeats exactly the algebraically closed field test
  over `R'`, asserting `_root_.IsReduced (Ω ⊗[R'] B')`.
- `Function.Bijective (Algebra.TensorProduct.map (AlgHom.id F' F') u')`: the actual
  descended generic structure map is an isomorphism, with its source identified
  by tensor cancellation with `F' ⊗[R] A`.
- `∃ e : (V ⊗[R'] B') ≃ₐ[V] B` and the equation
  `∀ a : A, e (1 ⊗ₜ[R'] u' (1 ⊗ₜ[R] a)) = u (1 ⊗ₜ[R] a)` render the required
  isomorphism of `A_V`-algebras. This equation is sufficient on all of `A_V`:
  `e` is already `V`-linear, and the tensors `v ⊗ a` generate the base-changed
  algebra additively. Thus it is not just a `V`-algebra isomorphism. After base
  change to `L`, the same equality states that `e_L` composed with the descended
  generic structure map is the given generic structure map `u_L`. Since both
  structure maps are invertible, it forces `e_L = u_L ∘ (u'_L)⁻¹`. This is exactly
  the specified generic identification, including its inverse, without an extra
  arbitrary isomorphism. All identifications here are canonical tensor symmetry,
  associativity, or base-change cancellation; none is a new notion.
- `IsIntegral (Spec (CommRingCat.of R'))`: integral source. The fraction field
  displayed earlier is its function field and its generic point maps to the
  generic point since `R -> R'` is injective.
- `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of the actual
  `Spec.map (algebraMap R R')`: separated and finite type, exactly the recorded
  meanings. Together with the integral source and finite separable function-field
  extension these spell out Temkin's generically etale quasi-alteration.
- The final equality composes `Spec` of `R'.val` with `Spec` of `R -> R'` and
  identifies it with `Spec` of `R -> V`: precisely the required factorization.

Dependency declarations read and used (all eleven statement dependencies):

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`
  and `Module.Flat` (the latter defined in `Mathlib.RingTheory.Flat.Basic`).
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation`; the same module's `AlgHom.FinitePresentation` is
  defined by this class for the actual ring map.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite`; `AlgHom.Finite`/`RingHom.Finite` unpack exactly to that class.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, together with `QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  the recorded `IsSeparated` part (definition in `Morphisms.Separated`).
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`.
- `def-weil-pbc-module-tensor-product`: `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct`; its canonical algebra structures and map are supplied by
  `Mathlib.RingTheory.TensorProduct.Maps`.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`, the recorded
  `RingHom.FiniteType` and its underlying `Algebra.FiniteType`/`Subalgebra.FG`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`.

All stated proof dependencies are imported non-publicly, including Mathlib matches:
`LimitAffineTransition`, `Morphisms.QuasiSeparated`, `Pullbacks`, upstream
`Mathlib.Algebra.Category.Ring.FinitePresentation`, `FiniteStability`,
`ColimitCategoryFpAlgebras`, `FiniteMapColimitDescent`, `ColimitFlatRingMap`,
`Nilpotent.GeometricallyReduced`, `GeometricallyReducedFibreLocus`, upstream
`LimitContainedInConstructible`, `SeparatingTranscendenceBasisFiniteSubextension`,
and `FunctionField`. Statement dependencies already imported publicly also serve
as proof imports. The declaration docstring carries all ten DAG proof steps.

Edge cases checked:

- `A = 0`, `B = 0`, and empty geometric fibres are allowed: no domain or nonempty
  assumption is placed on these algebras. Reducedness includes the zero ring.
- When no generators are needed, `R' = R` is allowed; no positive generator count
  is imposed. No strict extension of fields or subalgebras is required.
- Valuation rings of every height, the valuation field itself, and `L = F` are
  allowed. The valuation condition at zero is automatic. There is no Noetherian,
  finite-height, integral-ring-map, or surjectivity assumption.
- All algebra data live in a common arbitrary universe `u`; fraction fields and
  finite-presentation descents have representatives in that universe. Field tests
  use `Type u`, not a possibly smaller independent universe: algebraic closures of
  residue fields exist there. These tests are equivalent to tests in larger
  universes since any nilpotent witness in a field-valued tensor product uses
  finitely many field elements and can be detected over a small subfield and its
  algebraic closure. No characteristic is excluded.
- Each hypothesis has mathematical content; the tower instances record exactly
  the inclusions already present in the statement. All variables/universes are
  explicitly bound. The final factorization is explicitly requested by the node.

Searches performed with the prescribed `msearch.py Q145 <item>` wrapper:

1. `leanfinder`: "A finite generic modification over a valuation ring descends to a
   finitely generated subalgebra with flat geometrically reduced fibres".
   Eight hits: smooth/etale subalgebra descent, standard-smooth descent and
   `Algebra.IsGeometricallyReduced.of_forall_fg`; none states this finite generic
   modification descent with its simultaneous properties and specified map.
2. `loogle`: `Algebra.FinitePresentation, Module.Flat, Module.Finite`.
   Successful request, zero hits.
3. `grep`: `spreading|exists_subalgebra_fg|geometricallyReduced`, subdirectory
   `RingTheory`. Ten hits: smooth/etale descent and geometrically reduced algebra
   definitions; no matching statement.
4. `leansearch`: "A finite algebra generically isomorphic to a finitely presented
   algebra over a valuation subring descends with flatness and geometrically
   reduced fibres". Eight hits, including `RingHom.FinitePresentation`,
   `AlgHom.Finite`, `AlgHom.FinitePresentation`, flat descent and geometric
   reducedness; none is the requested statement.
5. `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the exact node id and proposed declaration
   name: only the proof-plan citation in `ReducedFibreModification.lean`; no
   existing declaration. A concept search for quasi-alterations also found no
   existing matching theorem. Read that consumer and the recorded dependencies.
6. DAG definition-title search for valuation rings/fraction fields/quasi-alterations
   found no separate matching definition needed for this statement. The already
   available Mathlib `ValuationSubring`, `IsFractionRing`, `Subalgebra`, and tensor
   operations suffice; no private copies are introduced.

Validation: `scompile.py Q145 lem-trf-finite-eta-modification-spreading` compiled the
sandbox and the named library module cleanly (4.0 s and 3.2 s). The initial diagnostic
was namespace resolution of reduced rings versus reduced schemes; this was repaired
with `_root_.IsReduced`, followed by the clean compile. No extra tests or proofs.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
