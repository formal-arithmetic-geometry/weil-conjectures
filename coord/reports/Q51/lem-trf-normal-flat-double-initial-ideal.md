## Worker report

The new module `Sheaf.RingTheory.NormalFlatDoubleInitialIdeal` states
`Hironaka.normalFlatDoubleInitialIdeal`, with proof `by sorry`. Nine auxiliary
constructions supply the actual coefficient action, tensor fibre, homogeneous
classes, and the three specified polynomial parameter maps. Their data contain
no `sorry`. No node statement, statement dependency, or proof dependency changes.
The item's JSON changes only in `lean`.

### Hypotheses and objects

- The nonzero commutative regular local ring T is `{T : Type u} [CommRing T]
  [IsRegularLocalRing T]`. Mathlib's class extends both `IsLocalRing T` and
  `IsNoetherianRing T`; localness already supplies nontriviality. There is no
  extra field, completeness, excellence, reducedness or characteristic assumption.
- `r s : ℕ`, `x : Fin (r + 1) → T`, and `y : Fin s → T` give exactly the
  x_0,...,x_r and y_1,...,y_s lists, with the latter indexed from zero in Lean.
  `hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y)`
  uses the recorded parameter definition, including generation of M and the
  equality of list length and Krull dimension.
- P is literally `Ideal.span (Set.range x)`. The ideal a and its containment
  are `(a : Ideal T) (ha : a ≤ Ideal.span (Set.range x))`.
- R is literally `T ⧸ a`; I is `P.map (Ideal.Quotient.mk a)`; m is
  `(IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a)`. Thus the tangent
  filtration is exactly M/a, without assuming another local structure on R.
- The coefficient ring is written as `(T ⧸ a) ⧸ P.map (Ideal.Quotient.mk a)`.
  `DoubleQuot.quotQuotEquivQuotOfLE ha` is the canonical identification with
  `T ⧸ P`. This is the node's A=R/I=T/P, with no new object chosen.
- G is the recorded `Ideal.associatedGraded I`, not a replacement associated
  graded ring. The hypothesis `[Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]`
  is exactly flatness over A through its recorded degree-zero algebra structure.
- k is `IsLocalRing.ResidueField T`, definitionally T/M. The coefficient map
  `normalFlatResidueMap` is the composite of the above third-isomorphism map
  with `Ideal.Quotient.factor` for P ≤ M. That containment is computed from
  the recorded `hparams.1`; it is not an additional hypothesis.
- S is `normalFlatParameterFibre x y hparams a ha`: the actual tensor
  `k ⊗[R/I] G` with this coefficient action. Tensor symmetry canonically
  identifies it with the node's G ⊗_A k, taking `[x] ⊗ 1` to `1 ⊗ [x]`.
  Its ring structure and k action are the existing tensor product instances.
  Its degree-n piece is the k span of `normalFlatParameterClass ... n`, the
  classes `1 ⊗ DirectSum.of ... n [b]`, b ∈ I^n.
- B is `MvPolynomial (Fin (r + 1)) k` and k[X,Y] is
  `MvPolynomial (Fin (r + 1) ⊕ Fin s) k`. `MvPolynomial.IsHomogeneous n` is
  the usual total-degree convention, giving every x and y variable degree one.

### Every conclusion and its specified maps

1. `normalFlatBeta` is polynomial evaluation with coefficient map `c ↦ c ⊗ 1`
   and X_i mapped to `normalFlatParameterClass ... 1 ⟨q(x_i), ...⟩`.
   This is exactly `[x_i]_1 ⊗ 1`, after the stated tensor symmetry. The first
   conjunct is `Function.Surjective (normalFlatBeta ...)`.
2. `normalFlatTangentCoefficient` descends the actual composite
   `T → T/a → gr_m R` through T/M, using the recorded
   `Ideal.associatedGradedRingHom_ker`. Thus no arbitrary coefficient map or
   coefficient-field section is supplied. `normalFlatGamma` evaluates at the
   degree-one classes of q(x_i) and q(y_j), with this coefficient map. The
   second conjunct asserts its surjectivity.
3. `normalFlatAmbientMap` evaluates constants by the recorded degree-zero
   algebraMap `T/M → gr_M T`, and each variable by the initial class of its
   specified x_i or y_j. The third conjunct asserts its bijectivity, so this
   actual parameter map identifies k[X,Y] with gr_M T.
4. The fourth conjunct sends each homogeneous degree-n polynomial under beta
   into the degree-n tensor subspace described above. The fifth conjunct puts
   gamma's image of each homogeneous degree-n polynomial in the actual
   `DirectSum.of ... n` summand. The sixth does the same for the ambient map.
   These are precisely the gradedness clauses. Bijective degree-preserving
   maps of these direct-sum graded rings have degree-preserving inverses.
5. The final equality is
   `RingHom.ker (normalFlatGamma ...) =
   (RingHom.ker (normalFlatBeta ...)).map (MvPolynomial.rename Sum.inl)`.
   Renaming along `Sum.inl` is exactly k[X] → k[X,Y], so ideal map is C k[X,Y].
   The final informal 'in particular' is this same equality, with the
   parameter maps fixed by their actual evaluation definitions.

### Dependency declarations and searches

Read all eight statement-dependency nodes and their recorded modules/signatures.
The definitions used are:

- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the exact
  ring clause of `def-weil-regular-scheme`'s retained `mathlib_match`. The
  recorded scheme wrapper is not the object in this ring-only statement.
- `Mathlib.RingTheory.LocalRing.ResidueField.Defs` and `.Basic`:
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`. These are the literal local
  ring quotient used by the recorded `Scheme.residueField`; no scheme is needed.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `WeilConjectures.RingTheory.AssociatedGradedRing`:
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedRingHom`, `Ideal.associatedGradedRingHom_ker`, and
  `Ideal.associatedGradedAlgebra`, with their real direct-sum multiplication.
- `Mathlib.RingTheory.RingHom.Flat`: `Module.Flat`, `RingHom.Flat`; the node's
  algebra form is Module.Flat for its degree-zero algebraMap.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and
  `Mathlib.RingTheory.TensorProduct.Basic`: `TensorProduct`, pure tensors,
  commutative ring and coefficient algebra structures.
- `Mathlib.Algebra.MvPolynomial.Basic`/`.Eval` and
  `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `MvPolynomial`,
  `MvPolynomial.eval₂Hom`, `MvPolynomial.rename`, `MvPolynomial.IsHomogeneous`.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard` was read for the node's standard grading convention;
  here its polynomial grading is expressed by the total homogeneous predicates.

Read the stated proof inputs and import their modules without `public`:
`IsRegularLocalRing.isRegular_and_quotients_of_generators`,
`Ideal.regularSequence_gradedPolynomial`,
`LinearMap.lTensor_injective_of_exact_of_flat`, and
`Ideal.normal_flat_hilbert_convolution`. The proof's
`lem-trf-maximal-adic-graded-length-bridge` has no Lean record and is not imported.
The statement docstring reproduces all six proof steps, with the coefficient
lifting and the degreewise finite-dimensional comparison explicit.

Searches actually run with `msearch.py Q51 lem-trf-normal-flat-double-initial-ideal`:

- LeanFinder: "The tangent initial ideal of a normally flat quotient of a regular
  local ring is extended from its normal cone residue fiber equations" — eight
  hits, concerning cotangent ideals and formal smoothness, not this theorem.
- Loogle: `Ideal.associatedGraded, RingHom.ker` — zero hits; it reported
  `unknown identifier 'Ideal.associatedGraded'` because that is a project name.
- Mathlib grep: `normal.?flat|double.?initial|tangent.*kernel`, subdirectory
  `RingTheory` — zero hits.
- LeanSearch: "normal flat quotient of regular local ring tangent cone kernel
  equals extension of normal cone fiber relations" — eight cotangent/extension
  hits, no normal-flat comparison.
- Mathlib grep: `associatedGraded|normal.?flat|double.?initial`, `RingTheory` —
  zero hits.
- Project `rg` in both `lean/WeilConjectures` and `lean/Sheaf` searched
  associatedGraded, normalFlatDouble, doubleInitial, normal-flat initial kernels,
  normalFlatParameter and normalFlatFibre; no exact statement or proposed name
  existed. The item-id search in WeilConjectures had no hit. Related existing
  results were `SmoothLocalTangentConeExtension` (essentially smooth maps,
  not normally flat pairs), `RegularSequenceGradedPolynomial`,
  `NormalFlatHilbertConvolution`, and the chart relation-removal theorem.

Read the existing `Ideal.normalConeFibre` and its owning node
`def-trf-normal-cone-residue-fibre`. It uses the residue field of a supplied
local ring R. This statement instead specifies the ambient field k=T/M and
writes R as the literal quotient T/a with its literal image ideals. The helpers
in this delivery perform the canonical coefficient transport to that specified
field, using the same TensorProduct and the same associatedGraded data. They
are constructions belonging to this node's three parameter maps, as authorized
for canonical coefficient transports; they add no independent mathematical
notion or replacement for the associated graded/tensor constructions.

### Source and edge cases

Opened Hironaka's original article at
https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf,
section 2, printed p.153: the normal-flat comparison identifies the tangent cone
with the normal-cone fibre times the tangent space of the regular centre after
a splitting of the ambient tangent-space sequence. The chosen parameters are
that splitting, giving exactly the maps here. Read the current blueprint
`literature/blueprint/latest` (2026-10-24 snapshot), including the local-term
ancestor and the unit's Frobenius local vanishing statement. This is the
inherited supporting algebra node; no unit statement is changed.

Checked these mathematical edge cases before finalizing:

- s=0: no Y variables, A=k, and the equality compares the two specified kernels
  in the same polynomial ring; all Fin 0 types are allowed.
- r=0: one x-variable, as the node requires. No unrequested empty x-list is
  imposed or excluded.
- a=0: beta and the ambient presentation have zero kernel; the assertion reduces
  to the regular-parameter polynomial presentation.
- a=P: I=0, G=A and S=k, beta kills all X variables; gamma has exactly the X
  ideal as kernel and preserves the Y variables.
- Nonreduced R, for example k[[x,y]]/(x^2) with P=(x): normal-flat G has the
  x^2 relation in the fibre and the same tangent relation, with no reducedness
  hypothesis introduced.
- Degree zero: pure classes include the unit; every coefficient map is the
  canonical quotient degree-zero inclusion, so constants have the correct image.
- Mixed characteristic: T=Z_p[[y]], P=(p), with a=0 or a=(p^2). The maps use
  quotient coefficients, not a nonexistent coefficient-field embedding into T.
- Without flatness the statement can fail: in k[[x,y]] with P=(x), a=(xy),
  the normal-fibre beta has zero kernel but gamma has the relation XY. The
  degree-one normal module A/(y) is not flat over A=k[[y]], as required.

No statement correction, disputed statement, new node, or dependency repair is
needed. The sole postponed theorem is `Hironaka.normalFlatDoubleInitialIdeal`.

Validation: the final module compiled in both sandbox and module modes through
`scompile.py`, with no errors and no warnings. The prescribed dry run and
actual delivery are run after this report is written.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
