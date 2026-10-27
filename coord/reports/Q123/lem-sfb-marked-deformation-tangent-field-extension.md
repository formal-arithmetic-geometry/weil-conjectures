## Worker report

The module `Sheaf.AlgebraicGeometry.MarkedDeformationTangentFieldExtension` states
`AlgebraicGeometry.StackDeformation.markedDeformation_tangent_field_extension`.
Its only postponed theorem is that declaration. Its four helpers are concrete
constructions or predicates for the canonical objects of this same node; no data
are chosen from a theorem with `sorry`. The source statement is unchanged.

Hypotheses and clauses, in the order of the node:

- The commutative Noetherian base is `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`; `S` is `Spec (.of R)`. The finite-type residue field is
  `{k : Type u} [Field k] [Algebra R k] [Algebra.FiniteType R k]`.
- Schemes and their maps are Mathlib `Scheme.{u}`, `Spec`, and `Spec.map`.
  `BasedCategory.{v,w} (Over (Spec (.of R)))` allows independent fibre-object and
  fibre-morphism universes. `Marked` has object universe `max v w`, so its
  coherent presentation uses `CofibredGroupoids.{u,v,max v w}`. All universe
  parameters and mathematical variables are explicitly bound.
- The category fibred in groupoids is `F` with `hF : IsFibredInGroupoids F`.
  This is the existing total-category formulation: every base arrow lifts, and
  every arrow is strongly cartesian. It is equivalent to the chosen coherent
  pullback presentation in the node; no topology or descent hypothesis is added.
- The pushout assumption is exactly
  `hRS : CategoryTheory.ArtinFamily.IsRimSchlessinger (.of R) F`.
  Its full signature quantifies over four Artinian local spectra of finite type
  over R, the nilpotent surjective ring map, the scheme pushout, and any compatible
  pair of objects with their specified overlap arrows. The total-category
  pushout conclusion retains both existence and unique gluing of arrows, i.e.
  the specified iso-comma equivalence, rather than a fibre product of class sets.
- The marked point is `x : Functor.Fiber F.p (affine (CommAlgCat.of R k))`.
  The existing `Marked F x A` has exactly objects with a marking and arrows
  respecting it. `HasMarkedPredeformation F x` asserts a coherent groupoid
  presentation `D`, equivalences `E A` with these exact categories, and
  `IsPredeformation D` and `IsRimSchlessinger D` from the recorded dependency.
  Its last clause supplies actual marking-preserving cartesian arrows for
  transport; its final equation is naturality on every arrow. Consequently the
  presentation cannot replace the actual pullback by an arbitrary functor.
  Coherence of D and uniqueness in hF give identity/composition compatibility.
- `Tangent F x` is the existing quotient of the marked dual-number groupoid.
  The existential `AddCommGroup` and `Module k` are structures on this exact set.
  `IsZeroClass ↔ t = 0`, `IsScalarClass c t s ↔ s = c • t`, and
  `IsSumClass t s r ↔ r = t + s` characterize each operation by the constant
  object, epsilon-scaling, and the two-direction gluing and sum map of the node.
  In particular these are the canonical structures furnished by the tensor
  theorem, not arbitrary vector-space structures on an equivalent carrier.
- Every finite field extension is covered by the universal `l` with `[Field l]`,
  `[Algebra k l]`, and `[FiniteDimensional k l]`. `[Algebra R l]` together with
  `[IsScalarTower R k l]` merely supplies its induced R-action: it forces the
  composite action. There is no separability assumption.
- `xl` and `a : xl.val ⟶ x.val`, with the `IsHomLift` condition over the actual
  field map, range over every choice of the pullback x_l. Under hF all these
  arrows are cartesian and such choices exist. The conclusion first supplies
  `Algebra.FiniteType R l`; this is a conclusion, not an extra hypothesis, and
  allows the recorded finite-type Artin test interface to be used over l.
- `HasMarkedPredeformation F xl` and the same three operation characterizations
  over l state the same assertions for F_(x_l).
- The auxiliary k-module structure on `Tangent F xl` is accompanied by
  `IsScalarTower k l`, which forces exactly restriction of the l-action.
  `rho : Tangent F x →ₗ[k] Tangent F xl` is therefore a k-linear map to that
  restricted module. Its equation on marked representatives says precisely
  pullback along `dualNumberFieldMap`, the actual coordinatewise map
  `(b,v) ↦ (algebraMap k l b, algebraMap k l v)`.
  `PullsBackField` requires the actual lifted arrow and the commuting square
  with the two markings, so the field map is not an unconstrained parameter.
- `e` is an l-linear equivalence from `TensorProduct k (Tangent F x) l` to
  `Tangent F xl`. Its source module is explicitly `rightTensorModule`: the
  right l-action transported along Mathlib's tensor symmetry. The formula
  `e (t ⊗ₜ[k] c) = c • rho t` uniquely specifies it on tensor generators.
  It states the exact orientation and formula in the node.
- No `FiniteDimensional k (Tangent F x)` assumption appears, nor algebraicity,
  finite type, separation, or an atlas for F. The six proof steps in the
  declaration docstring follow the node's marked gluing and residue-restriction
  proof, and cite its proof dependencies.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`; these are
  the finite-type hypotheses inside the reused geometric RS predicate.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`: `TensorProduct`,
  `TensorProduct.comm`; `Mathlib.Algebra.Module.TransferInstance`: `AddEquiv.module`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `TestCategory`, `CofibredGroupoids`, `fibre`, `push`, `IsPredeformation`,
  `IsRimSchlessinger`, `squareZeroAlgebra`, `squareZeroTest`, `tangentSet`.
- `Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`:
  `artinRS_tangent_tensor`, `squareZeroMap`, `isoClassesMap` (proof plan).
- Added landed statement dependency `def-sfb-marked-stack-deformations`, module
  `Sheaf.AlgebraicGeometry.MarkedStackDeformations`: `affine`, `affineMap`,
  `Marked`, `Classes`, `classOf`, `Tangent`, `PullsBack`, `IsZeroClass`,
  `IsScalarClass`, `IsPairLift`, `IsSumClass`.
- Added landed statement dependency `def-sfb-artin-family-lifting-data`, module
  `Sheaf.AlgebraicGeometry.ArtinFamilyLiftingData`:
  `CategoryTheory.ArtinFamily.IsRimSchlessinger`.
- `IsFibredInGroupoids` is exposed through these existing moduli imports, with
  its full definition read in `StablePointedModuliGroupoids`.
- Proof-only modules: `ArtinLocalTestAlgebra.artin_local_test_algebra` (in
  `AlgebraicGeometry.ArtinDeformation`),
  `Sheaf.RingTheory.ArtinianFiniteTypeResidueCriterion` with
  `RingHom.finiteType_iff_residue_of_isArtinianRing` and its affine variant,
  `Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout` with
  `AlgebraicGeometry.isPushout_spec_pullbackCone_of_surjective`, and
  `Sheaf.RingTheory.ArtinianFiniteResidueRestriction` with
  `RingHom.artinian_finite_residue_restriction`.
- `Mathlib.RingTheory.HopkinsLevitzki` gives Noetherianness from Artinianness
  and `isArtinianRing_iff_isNilpotent_maximalIdeal`.
- `def-weil-size-convention` is metatheoretic; the explicit u,v,w,z levels
  implement it. It supplies no declaration or import.

Edge cases checked before writing: the zero tangent space permits the zero
module and the zero tensor equivalence; l=k gives the identity comparison for
an identity pullback and the standard tensor-unit map. Nonidentity but
isomorphic pullback choices are covered by arbitrary xl,a. Finite inseparable
extensions are admitted. Tangent spaces of infinite dimension are admitted.
The zero ring R has no map to a field and hence no instance of the hypotheses;
no extra nonzero assumption was inserted. The general gluing hypothesis retains
nilpotent kernels, including the zero kernel. Zero scalar transport and empty
bases in the imported tensor theorem agree with the stated zero operation.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: `Marked deformation groupoids and tangent spaces commute with finite
  residue field extension`: 8 cotangent-space/formal-etale hits, no marked
  groupoid statement.
- Loogle: `TensorProduct, LinearEquiv`: 12 tensor-product symmetry, compatible
  scalar, and linear-equivalence hits. Reused the tensor symmetry API; none
  states the deformation result.
- Mathlib grep: `predeformation|Predeformation|Schlessinger|markedDeformation`:
  0 hits.
- rg of the same pattern in `lean/WeilConjectures` and `lean/Sheaf` found the
  existing Artin definitions and `MarkedStackDeformations`. Reused them and
  their landed DAG nodes. No upstream occurrence of this item's id was found.
  Additional inspection found the reusable `ArtinFamily.IsRimSchlessinger`.
- Read the source directly in `literature/stacks-project/artin.tex` at
  equation-predeformation-category, lemma-deformation-category, and
  lemma-change-of-field; and `formal-defos.tex` at
  lemma-tangent-space-change-of-field. The example CompactObject module is
  withdrawn in this checkout; current module-mode Artin files supplied the
  required header conventions.

No statement correction, disputed mathematical statement, new node, or dependency
repair is needed. The two added dependencies already have landed Lean records.

## Second reading by Q123

The dispatcher forbids starting another agent and specifies independent review
by the maintainer after delivery. This section records my separate rereading,
not an independent worker review. I compared the final file against each clause
of the node and the complete dependency signatures, in particular: total-category
RS keeps arbitrary specified isomorphisms; the marked presentation is natural
on arrows; xl is any genuine pullback; finite type over R for l is a conclusion;
canonical vector operations and the pure-tensor formula fix the structures and
comparison map. The l-action on the tensor product uses the right factor, and
the k-action on the target is forced by IsScalarTower. No additional geometric
or finite-dimensional tangent hypothesis was found. Independent maintainer
review remains pending.
