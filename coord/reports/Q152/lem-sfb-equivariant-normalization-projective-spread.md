## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantNormalizationProjectiveSpread` defines the
canonical generic normalization (`NormalizationProjectiveSpread.genericNormalization`) and
its two structural maps `toCurve` and `toField`, then states
`AlgebraicGeometry.exists_equivariant_normalization_projective_spread` with proof `sorry`.
The theorem has the following direct rendering of the node.

* `k`, `Y`, and `C` are the field and integral schemes; `pY` is the structure morphism,
  with `IsHProjective`, `LocallyOfFiniteType`, and `QuasiCompact`, while `g` is proper,
  dominant, locally finite type, and quasi-compact. `hnormal` says every local ring of `Y`
  is a domain and integrally closed. The generic fibre is the explicitly typed pullback
  `pullback (C := Scheme.{u}) g Y.fromSpecFunctionField`, with dimension one and geometric
  integrality.
* The function-field map is the algebra structure on `C.functionField`; `hK` identifies
  it with the map induced by `g` on the generic points. `H`, `σk`, `σY`, and `σC` are a
  finite group and actions by automorphisms; `hY`, `hC`, and `hg` state the semilinear
  compatibility with `k`, `Y`, and `g`, allowing nonfaithful actions and actions on `k`.
* `K₀` is a field with a finite purely inseparable extension structure over `Y.functionField`
  (`Module.Finite` and `IsPurelyInseparable`), and `σK₀` with `hK₀` specifies its extended
  action. `F₀` is a field equipped with the two coefficient algebras and the ring
  isomorphism `eF : TensorProduct ... ≃+* F₀`; `heF` gives the required pure-tensor formula.
  `σF₀`, `hF₀`, and `hσF₀` specify the compatible tensor action.
* `genericNormalization g K₀` is the reduced normalization of the generic pullback. The
  hypotheses `[Smooth (toField g K₀)]` and
  `[GeometricallyIntegral (toField g K₀)]` render smoothness and geometric integrality.
  `σN`, `hNC`, and `hNK` give its compatible action over `C` and `K₀`.
* `D` is represented by a closed immersion `d` into the generic normalization, with
  finite and étale composite to `Spec K₀`; `σD` and `hD` express stability.
* The first conjunction gives `Y.normalizationIn K₀` with integrally closed domain stalks,
  integrality, Noetherianity, excellent affine coordinate rings, finite-type and
  quasi-compact structure morphism, finite dominant normalization map, and
  `IsHProjective` over `k`. The displayed `e : Spec K₀ ≅ ...functionField` is the specified
  function-field identification.
* The next conjunction gives the analogous stalk, integral, Noetherian, excellence,
  finite-type, quasi-compact, finite, dominant data for `C.normalizationIn F₀` and its
  specified function-field identification.
* The existential `f₀`, `σS₀`, `σC₀` gives the canonical proper equivariant map, its
  commuting square with `g`, its generic function-field map, the two semilinear spectrum
  identities, and equivariance with the extended actions.
* `j₀` is a Cartesian generic-fibre square; its composite with the normalization map is
  exactly `toCurve`, and it is equivariant. The existential `T`, `q`, `σT`, `jT` gives an
  integral Noetherian model with excellent affine charts, finite-type/quasi-compact
  structure, proper equivariant birational modification data (`Dense` open and `IsIso`),
  `IsHProjective` over `k`, over `C.normalizationIn F₀`, and over `S₀`, plus the Cartesian
  generic-fibre square and `jT ≫ q = j₀`.
* Finally `L`, `iL`, `dL`, and `σL` give a closed schematic closure. The affine kernel
  equality is exactly the definition by restriction kernels. The four action equations
  give stability and equivariance, the factorization is `dL ≫ iL = d ≫ jT`, and the final
  `IsPullback` identifies its generic fibre with `D` as a closed subscheme. This includes
  the empty marking because no nonemptiness hypothesis occurs.

The statement dependencies used are: `Field` (Mathlib); `AlgebraicGeometry.IsIntegral`
(Mathlib.AlgebraicGeometry.Properties); `AlgebraicGeometry.IsHProjective`
(WeilConjectures.AlgebraicGeometry.Morphisms.Projective); `LocallyOfFiniteType` and
`QuasiCompact` (Mathlib.AlgebraicGeometry.Morphisms.FiniteType/QuasiCompact);
`IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper);
`Scheme.functionFieldOfComponents` and `Scheme.functionField`
(WeilConjectures.AlgebraicGeometry.FunctionField and Mathlib);
`FieldExtension.degree` (Sheaf.FieldTheory.FieldTower); `Scheme.reducedNormalization`
(Sheaf.AlgebraicGeometry.ReducedNormalization); `Scheme.normalizationIn` and
`Scheme.fromNormalizationIn` (WeilConjectures.Mathlib.AlgebraicGeometry.Normalization);
`GeometricallyIntegral` (Mathlib.AlgebraicGeometry.Geometrically.Integral);
`topologicalKrullDim` (Mathlib.Topology.KrullDimension); `Smooth` and `Etale`
(Mathlib.AlgebraicGeometry.Morphisms.Smooth/Etale); `IsFinite` and
`IsClosedImmersion` (Mathlib.AlgebraicGeometry.Morphisms.Finite/ClosedImmersion);
`pullback` (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback);
`IsExcellent` (Sheaf.RingTheory.ExcellentRing); `IsLocallyNoetherian`
(Mathlib.AlgebraicGeometry.Noetherian); and `IsPurelyInseparable` plus `Module.Finite`
(Mathlib.FieldTheory.PurelyInseparable.Basic and Mathlib.RingTheory.Finiteness.Defs).

The proof-plan imports are the recorded interfaces for finite-over-projective, projective
properness, relative normalization, dimension after field extension, semilinear equivariant
Chow modification, closed irreducible dimension/trdeg, proper birational normal-curve
isomorphism, excellence of fields and finite type localizations, and excellence on affine
covers. Several proof dependencies have no published Lean declaration yet; their modules
are intentionally named in the node's proof plan but are not fabricated in this statement
module.

Edge cases checked: `H` may be trivial or nonfaithful; `σk` need not fix the ground field;
`K₀ = Y.functionField` and characteristic zero are allowed; `F₀` is specified through the
pure-tensor isomorphism rather than by choosing a different field; dimension-one generic
fibres are retained; the empty scheme and zero-dimensional/empty marking are not excluded;
no hypothesis requires `D` to be nonempty.

Searches made before writing: `msearch.py ... leanfinder` for equivariant normalization and
projective spreading (eight unrelated projective-curve hits, no match); `msearch.py ...
loogle` for `Scheme.normalizationIn`, `IsHProjective`, and scheme-image APIs (zero hits and
unknown `Scheme.normalizationIn` in the search service); `msearch.py ... grep` for
`[Ee]quivariant.*[Nn]ormali|[Ss]emilinear.*[Cc]how|[Nn]ormali.*[Pp]rojective` (zero hits);
`msearch.py ... leansearch` for the normalization construction (normalization API hits only,
no equivariant spreading theorem); `rg` through `lean/Sheaf`, `lean/WeilConjectures`, and
Mathlib for normalization, semilinear Chow, scheme images, and the node id (no declaration
matching this theorem). The existing normalization, reduced-normalization, projective,
and scheme-image declarations were read and reused; no second definition of those notions
was introduced.

No `STATEMENT-DISPUTED` flag or node correction was needed.

## Second reading by Q152

I reopened the node and the completed module and matched every binder and conjunction above.
The original generic fibre is represented by the explicit pullback and its dimension-one
hypothesis; the tensor field is constrained by `eF` and `heF`; action compatibility is
present for every displayed map; both generic structural maps are preserved in `j₀`, `jT`,
and the final pullback; projectivity is stated over `k`, over the normalization base, and
for `q`; the kernel equality and final pullback retain the marking scheme structure and
allow the empty case. No mismatch or omitted hypothesis was found.
