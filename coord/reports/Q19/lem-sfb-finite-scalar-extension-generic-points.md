## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteScalarExtensionGenericPoints` states
`AlgebraicGeometry.Scheme.finite_scalar_extension_generic_points`, with `sorry` as
its whole proof. Its five supporting declarations are transparent abbreviations
for the existing pullback, its first projection, and the fibre tensor algebra,
and real constructions of the base-field-to-residue map and its pure tensors.
They only name the canonical objects needed to read this node's statement; they
introduce no independent mathematical notion. Their data contain no `sorry`.
No node statement or dependency field is changed.

Hypotheses and clauses, in order:

- The finite extension F ⊆ K is `(F K : Type u) [Field F] [Field K]
  [Algebra F K] [Module.Finite F K]`. Finite means module finite, as recorded on
  def-pc-field-tower. Its degree is the recorded `FieldExtension.degree`.
- An arbitrary F-scheme V is `(V : Scheme.{u}) (f : V ⟶ Spec (.of F))`.
  The explicit structure morphism is appropriate because the statement involves
  its base change. `finiteScalarExtension (K := K) f` is literally the recorded
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap F K)))`, and
  `scalarExtensionProjection` is literally its `pullback.fst`.
- Every affine open Spec R ⊆ V is quantified as a commutative F-algebra R and an
  open immersion `i : Spec (.of R) ⟶ V` with
  `i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F R))`. This compatibility
  specifies the induced F-algebra structure; it does not restrict the affine
  open. Every affine open can be given this structure using its composite to
  Spec F and the affine adjunction.
- Its inverse image is `pullback (scalarExtensionProjection f) i`.
  The existential scheme isomorphism `e` identifies it with `Spec (.of (R ⊗[F] K))`.
  The equation `e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[F] K))) =
  pullback.snd ... i` identifies its projection with the canonical ring map
  r ↦ r ⊗ 1. Thus the isomorphism is over Spec R, not an unrelated isomorphism.
- Finite free of rank [K:F] is `∃ n : ℕ, FieldExtension.degree F K =
  (n : WithTop ℕ) ∧ Nonempty (Module.Basis (Fin n) R (R ⊗[F] K))`.
  A basis on Fin n gives both freeness and module finiteness, including R = 0.
  Flatness is the recorded `(algebraMap R (R ⊗[F] K)).Flat`.
- Component generic points are Mathlib's `genericPoints`, whose definition is
  `closure {x} ∈ irreducibleComponents X`. This is exactly a generic point
  (`IsGenericPoint`) of an irreducible component. The second conjunct says that
  every such y maps into `genericPoints V`.
- The residue assertion quantifies over every y, with x written explicitly as
  `scalarExtensionProjection f y`. `scalarExtensionFiberAlgebra f x` is
  `V.residueField x ⊗[F] K`, with the F-action given by
  `(fieldToResidue f x).toAlgebra`. `fieldToResidue` is the canonical composite
  F → Γ(V, ⊤) → κ(x), using `ΓSpecIso`, `f.appTop`, and `Γevaluation`.
- The ring homomorphism ψ is specified on every pure tensor by
  `ψ (scalarExtensionFiberTmul f x a b) = pr.residueFieldMap y a *
  fieldToResidue (pullback.snd ...) y b`. This characterizes exactly the canonical
  fibre-algebra map into κ(y), so `RingHom.ker ψ` is the prime corresponding to y
  in its fibre (Stacks 01JT). There is no arbitrary map or arbitrary prime.
- `Module.Finite (V.residueField x) (scalarExtensionFiberAlgebra f x)` states the
  finite dimension of that algebra for its canonical left tensor-factor action.
  `(RingHom.ker ψ).IsPrime` and `IsField (... ⧸ RingHom.ker ψ)` state that the prime
  quotient is a field. An existential ring equivalence e from this quotient to
  κ(y), with `e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker ψ)) = ψ`, states
  that the canonical induced quotient map is an isomorphism. Since ψ has the
  displayed pure-tensor formula, the equivalence respects the residue map from
  κ(x). `pr.residueFieldMap y |>.hom.Finite` is finiteness of κ(y)/κ(x) for the
  actual induced map, not for an unspecified algebra structure.
- The last conjunct quantifies over arbitrary `B : Scheme.{u}` and `v : V ⟶ B`.
  Its premise says for every component generic x both that v(x) is component
  generic and that `(v.residueFieldMap x).hom.Finite`. Its conclusion says those
  same two things for every component generic y and the composite `pr ≫ v`.
  No property is asserted only for one chosen component.
- There are no assumptions of normality, separability, finite type, Noetherianity,
  or reducedness. A common arbitrary universe u is the usual scheme-universe
  convention: all fields and schemes may be enlarged to that common universe.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.Algebra.Algebra.Defs: `Algebra`
  and `RingHom.toAlgebra` (def-weil-field, def-pc-field-extension).
- Sheaf.FieldTheory.FieldTower: `FieldExtension.degree`, including its complete
  definition using `Module.Finite` and `Module.finrank` (def-pc-field-tower).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (def-pc-scheme, def-weil-affine-spectrum).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`,
  `pullback.fst`, `pullback.snd` (def-pc-fibre-product); scheme instances from
  Mathlib.AlgebraicGeometry.Pullbacks.
- Mathlib.Topology.Sober: `IsGenericPoint` and `genericPoints`;
  Mathlib.Topology.Irreducible: `irreducibleComponents`
  (def-sc-generic-point, def-weil-irreducible-components).
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.Γevaluation` and its functoriality
  (def-weil-residue-field).
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`
  (read the recorded scheme-flatness interface); the affine clause uses the
  ring-flatness declaration below, as the node explicitly requires.
- Mathlib.LinearAlgebra.TensorProduct.Defs/Basic: `TensorProduct`, pure tensors
  and their universal property; the commutative-algebra structure and left
  inclusion are Mathlib.RingTheory.TensorProduct.Basic
  (def-weil-pbc-module-tensor-product).
- Mathlib.LinearAlgebra.FreeModule.Basic: `Module.Free`, and the `Module.Basis`
  it contains (def-weil-pbc-free-module).
- Mathlib.RingTheory.RingHom.Flat: `RingHom.Flat`, defined via `Module.Flat`
  (def-weil-pbc-flat-ring-map).

The stated proof dependencies are imported for the seven-step proof plan:
`pullbackSpecIso` and the open-pullback lemmas (Mathlib.AlgebraicGeometry.Pullbacks),
`Scheme.Pullback.carrierEquiv` and `range_map`
(Mathlib.AlgebraicGeometry.PullbackCarrier),
`PrimeSpectrum.zeroLocus_minimalPrimes`
(Mathlib.RingTheory.Spectrum.Prime.Topology),
`Algebra.HasGoingDown.of_flat` (Mathlib.RingTheory.Ideal.GoingDown), the scheme
fibre declarations (Mathlib.AlgebraicGeometry.Fiber),
`fieldOfFiniteDimensional` (Mathlib.LinearAlgebra.FiniteDimensional.Basic), and
`Scheme.Pullback.exists_residueField_equiv_ofPointTensor`
(WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField).
The complete seven steps are included in the theorem docstring.

Edge cases checked before stating: V or W empty (generic-point and point
quantifiers are vacuous); R the zero ring (Fin n still indexes a basis of the
zero module over the zero ring); K = F; inseparable extensions; nonreduced
schemes and nonreduced tensor fibre algebras; arbitrary, possibly infinitely
many components; B empty when a map exists. A prime quotient of the fibre
algebra is a nonzero domain even when the fibre algebra itself has nilpotents.
The field extension degree cannot be zero, but no extra positivity hypothesis
was imposed.

Searches on 2026-10-24 through the prescribed msearch.py wrapper:

- LeanFinder: "Finite field scalar extension of a scheme preserves component
  generic points with finite residue field extensions" returned 8 hits,
  headed by `Scheme.SpecToEquivOfField`, `SpecToEquivOfField_eq_iff`,
  `range_fromSpecResidueField`, and individual residue-field interfaces.
  No hit states the simultaneous affine, generic-point, residue and composition
  assertions of this node.
- Loogle: "AlgebraicGeometry.Flat, AlgebraicGeometry.Scheme.Hom.residueFieldMap"
  returned zero hits.
- LeanSearch: "finite scalar extension scheme generic points finite residue
  field" returned 8 hits: `IsLocalRing.ResidueField.finite_of_finite`,
  `Scheme.residueField`, quasi-finite algebra residue-field instances,
  `SpecMap_residue_apply`, `fromSpecResidueField`, a finite-field extension
  instance and `evaluation.congr_simp`. These are ingredients, not the statement.
- Mathlib grep: "finite.*residue|genericPoints|Spec.*[Tt]ensor" in
  AlgebraicGeometry returned 25 hits including `pullbackSpecIso`,
  PullbackCarrier and quasi-finite fibre statements. Read the relevant source
  signatures and projection identities; these supply constructions rather
  than the full statement.
- Local rg over lean/WeilConjectures and lean/Sheaf, and the upstream name index,
  for finite_scalar_extension, finiteScalarExtension, the item id,
  componentGeneric and genericPoints.*finite found generic-point ingredients,
  an unrelated derived-sheaf `finiteScalarExtension` in a different namespace,
  and no copy of this assertion. Further name searches for all new helper names
  and the theorem name found no conflicts.
- Read the existing statement dependency records and their complete source
  signatures/docstrings; read Stacks algebra.tex lemma-flat-going-down (00HS),
  schemes.tex lemma-fibre-product-affine-schemes (01I4) and
  lemma-points-fibre-product (01JT), and the current blueprint unit section.
  The requested example CompactObject module is withdrawn; read its node's
  current existing-declaration record instead and followed the module-mode
  example in the standing brief.

Validation: scompile.py compiled this file separately under both sandbox and
library module names with no errors or warnings after adding the explicit
return type `: Type u` to the fibre-algebra abbreviation. All variables and the
universe are explicitly bound. No statement correction, new node or dependency
repair was necessary. No STATEMENT-DISPUTED issue remains.

## Second reading by Q19

This is the author's separate clause-by-clause re-reading, not a claim of an
independent worker review: the dispatch brief prohibits starting other agents,
and the maintainer supplies the independent review of this direct delivery.
Re-opened the node and the final Lean file. Checked the finite-field hypotheses,
structure morphism, pullback order, affine open quantifier and compatibility,
projection identity, degree-indexed finite basis, ring flatness, every generic
point, every residue field and its canonical tensor kernel, quotient-map
normalization, and the two parts of the composition assertion. In particular,
requiring a ring equivalence alone would have lost compatibility with κ(x);
the explicit pure-tensor formula and quotient normalization retain it. An
unrelated ideal would not have specified the fibre point; using `ker ψ` retains
it. No mismatch or node correction was found. The compile repair only supplied
an explicit return type on the tensor-algebra abbreviation. All auxiliary
declarations are actual constructions and all postponed proof content belongs
to the one named theorem. The zero ring, empty schemes and inseparable cases
remain covered.
