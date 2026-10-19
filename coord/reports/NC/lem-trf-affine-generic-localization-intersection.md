## Worker report

The module `lean/Sheaf/Paper/AffineGenericLocalizationIntersection.lean` defines
`AlgebraicGeometry.affineFiberGenericPrime` and states
`AlgebraicGeometry.injective_to_pi_affineFiberGenericLocalization` with proof `sorry`.
The helper is the canonical inverse image of the zero prime of the tensor fibre.  Its
`IsPrime` proof uses the `IsDomain` hypothesis for the fibre and
`Ideal.IsPrime.comap`; it does not choose an arbitrary prime. The maintainer replacement
uses `p.asIdeal.Fiber B` and `Algebra.TensorProduct.includeRight`, the standard fibre convention.

The theorem renders the node statement as follows.

- `R` and `B` are commutative rings, with `[Algebra R B]`, representing the homomorphism
  `R → B`.
- `hflat : RingHom.Flat (algebraMap R B)` is the flatness hypothesis.
- `[Algebra.FinitePresentation R B]` is the finite-presentation hypothesis.
- `hgeom` quantifies over every `p : PrimeSpectrum R` and every field `K` in
  `Type (max u v w)`, with an independent universe `w`, carrying the residue-field extension structure
  `[Field K] [Algebra p.asIdeal.ResidueField K]`, together with the canonical tower
  structures `[Algebra R K] [IsScalarTower R p.asIdeal.ResidueField K]`; its conclusion
  `IsDomain (K ⊗[R] B)` is exactly the required domain condition after every such field
  extension.
- `affineFiberGenericPrime R B hgeom p` is the inverse image under
  `Algebra.TensorProduct.includeRight` of `⊥` in
  `p.asIdeal.Fiber B`, i.e. the inverse image of the zero prime of the
  fibre.  The helper's `PrimeSpectrum` value supplies the prime ideal needed for
  localization.
- The displayed map is the function sending `b : B` to the family indexed by
  `p : PrimeSpectrum R` whose `p`-component is
  `algebraMap B (Localization.AtPrime (affineFiberGenericPrime R B hgeom p).asIdeal) b`.
  The theorem conclusion is `Function.Injective` for this map, which is the natural map
  `B → ∏ p B_{q_p}` and says precisely that its kernel is zero.

The dependency declarations used are the recorded Mathlib declarations:

- `def-weil-pbc-flat-ring-map`: `RingHom.Flat` (and `Module.Flat`) from
  `Mathlib.RingTheory.RingHom.Flat`.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation` from
  `Mathlib.RingTheory.FinitePresentation`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and the associated
  residue-field constructions from `Mathlib.AlgebraicGeometry.ResidueField`; the tensor
  fibre is represented by `p.asIdeal.ResidueField`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` / `PrimeSpectrum`, with
  `PrimeSpectrum.asIdeal` for the prime indexing.
- `def-weil-pbc-module-localization`: `Localization.AtPrime`, the canonical localization
  at a prime ideal.

Edge cases checked: the index `PrimeSpectrum R` may be empty (the conclusion then says
that the map into the empty product is injective, which is the stated assertion); the zero
ring is permitted by the commutative-ring binders and the domain hypothesis rules out a
nonzero zero fibre; tensor fibres are used at arbitrary residue-field extensions, including
`K = p.asIdeal.ResidueField`; and no finite-generation or characteristic restriction was
added.  The helper is noncomputable because the residue-field field instance is
noncomputable, as expected for this canonical construction.

Searches made before writing:

- `msearch.py ... leanfinder "flat finitely presented algebra fibre generic prime localization product injective"`:
  eight general flat/localization hits (`instFlatAtPrime`, going-down, and related maps),
  no exact theorem.
- `msearch.py ... loogle "PrimeSpectrum.toPiLocalization_injective, Localization.AtPrime, IsDomain TensorProduct"`:
  no matching result (the query also reported that `TensorProduct` needs explicit
  parameters).
- `msearch.py ... grep "toPiLocalization_injective|generic.*fibre.*localization|affineFiberGenericPrime" RingTheory`:
  hits only for localization at all maximal primes and unrelated topology declarations;
  no fibre-generic product injection.
- `rg` over `WeilConjectures/`, `lean/Sheaf/`, and `dag/nodes/` for
  `affineFiberGenericPrime`, `injective_to_pi_affineFiberGenericLocalization`, and
  generic-fibre localization terms found no existing project declaration or duplicate.

No statement correction or dependency module was needed.  There are no new DAG nodes;
the helper belongs to the item's module and is recorded in the item's `lean.declarations`.

## Second reading by NC

I reread the item node, its six-step proof, and all five statement dependencies.  The
Lean binders preserve the flatness, finite-presentation, all-prime/all-field-extension
domain hypotheses, and the product-localization injectivity conclusion clause by clause.
The only elaboration-specific additions are the explicit algebra and scalar-tower
instances required to express a residue-field extension and the named canonical helper
for the zero-prime inverse image.  No hypothesis or conclusion was weakened, and no
proof content was added beyond `sorry`.


Maintainer independent reading of immutable delivery
`f8bfff39443673f87c33fa3615e8f0d60d11bc9b` (2026-10-18):

- The commutative rings and their unital homomorphism are the two `CommRing` binders
  and `Algebra R B`; their universes remain independent.
- Flatness is precisely `RingHom.Flat (algebraMap R B)`; finite presentation is precisely
  `Algebra.FinitePresentation R B`. No Noetherian, reduced-base, or finite-module
  assumption occurs.
- Every prime is indexed by `PrimeSpectrum R`. The field extension is encoded by
  `Field K`, `Algebra p.asIdeal.ResidueField K`, and the compatible base algebra and
  scalar tower. Field algebra maps are injective, so no extra extension assumption occurs.
- The helper constructs the actual inverse-image ideal of zero using `includeRight`,
  and obtains its prime proof from the fibre-domain hypothesis. Its data is not postponed.
- Each component of the product map is the canonical localization `algebraMap` at that
  very prime, and `Function.Injective` is the whole conclusion.
- Tensor symmetry identifies the original `B ⊗[R] K` with `K ⊗[R] B` and carries
  `b ⊗ 1` to `1 ⊗ b`, so normalization to `Ideal.Fiber` preserves the prime and map.
- The field-extension quantifier is polymorphic in an independent universe `w` and uses
  `Type (max u v w)`, so it covers arbitrary extension universes and is large enough for
  `K ⊗[R] B`. The helper applies the hypothesis to the `ULift` of the residue field and
  transports `IsDomain` across the canonical tensor-product algebra equivalence. No
  equality between `u`, `v`, and `w` is imposed.
- The zero base ring forces the algebra to be zero; its spectrum is empty and the map
  into the empty product is injective. Over a nonzero base, zero fibres are excluded by
  `IsDomain`. Nilpotent bases, positive characteristic, non-domain bases, and arbitrary
  cardinalities of `B` remain allowed; for example `R[x]` over the dual numbers fits.

Findings repaired: H8, the original proof docstring omitted the six-step plan and
incorrectly inferred the unit ideal from containment in every prime. It now gives the
node's correct maximal-ideal contradiction and all six steps with their dependencies.
H9, the standard fibre convention is now `Ideal.Fiber` with `includeRight`; the two
available statement modules in `proof_deps` are imported as ordinary imports. The report
recordkeeping is supplemented here with actual compiler evidence and the detailed
independent clause comparison. The node's mathematical statement, dependencies and
proof are unchanged; only `lean.statement` is synchronized with the normalized signature.
No new nodes or dependency repairs are required.

Independent searches used `rg` in Mathlib, `WeilConjectures`, and the group `lean/Sheaf`
tree for `fiberGeneric`, `fibre.?generic`, `toPiLocalization_injective`, and generic
localization variants. The closest declaration is
`PrimeSpectrum.toPiLocalization_injective` in
`Mathlib/RingTheory/Spectrum/Maximal/Localization.lean:172`; it indexes all primes of
one ring, not the specified fibre-generic primes. The existing worker's LeanFinder,
Loogle, and grep searches are recorded above. No duplicate helper or exact theorem was
found. Read `RingHom.Flat`, `Algebra.FinitePresentation`, `Scheme.residueField`,
`Spec.residueFieldIso`, `Spec`, `Ideal.Fiber`, `includeRight`, `LocalizedModule`, and
`Localization.AtPrime` in their source files, as well as the exact projectivity and
local residue-injectivity dependency statements.

Compiler evidence: invoked the prescribed `scompile.py NC
lem-trf-affine-generic-localization-intersection <file>` separately on the immutable
file and the complete replacement. The immutable library check exited 0 (1.9 s).
An intermediate replacement had a docstring whitespace warning, which was repaired.
The final replacement exited 0 without errors or warnings: sandbox 2.1 s, library
`Sheaf/Paper/AffineGenericLocalizationIntersection.lean` 2.0 s, private overlay
`/dev/shm/nt-tmp/nt-local-compile-7c7aodsf/.lbuild`. The installed wrapper currently
runs its side-overlay compiler on the server; no direct SSH or global build was run.
The original delivered report contained no reproducible compile transcript; the fresh
checks supply that evidence. Both original and corrected JSON `lean.statement` fields
were checked verbatim against their respective file signatures. The final module has
one theorem, proved only by `sorry`, and a real canonical definition; all lines are at
most 100 characters and automatic implicit variables are disabled.

## Returned-delivery repair by NC

Applied all three complete replacement files from the independent review of immutable
head `f8bfff39443673f87c33fa3615e8f0d60d11bc9b` to this retained sandbox packet. The
return's `--apply-fixes` error came from repository-relative paths in the reviewer's
fixes directory; these fixes are now part of the ordinary stage-2 delivery itself.
The Lean module now uses `Ideal.Fiber` / `includeRight`, has explicit `Type (max u v w)` field binders with an independent universe `w`, imports the available proof-dependency modules, and gives the full
six-step proof docstring with the correct maximal-ideal argument. The node's `lean`
record matches that signature; no mathematical statement or dependency was changed.

Fresh worker compile via `scompile.py NC
lem-trf-affine-generic-localization-intersection
lean/Sheaf/Paper/AffineGenericLocalizationIntersection.lean` passed with no errors or
warnings: sandbox 7.9 s, library 4.4 s, overlay
`/dev/shm/nt-tmp/nt-local-compile-_4fx8cd6/.lbuild`.


## Returned-delivery repair H3

The immutable delivery was returned because its `hgeom` binder used `K : Type u`,
which omitted field extensions in larger universes despite the node saying “every field
extension”. The theorem and helper now quantify with an independent universe `w` and
`K : Type (max u v w)`, matching the established affine generic rank interface. The
helper applies the hypothesis to `ULift.{max u v w}` of the residue field and transports
the resulting domain instance along `Algebra.TensorProduct.congr`; this keeps the
canonical fibre prime construction data-filled without adding a hypothesis. The item’s
natural-language statement, dependencies, and citer `lem-trf-affine-generic-rank-blowup`
remain valid. The recorded `lean.statement` was synchronized to the repaired signature.
