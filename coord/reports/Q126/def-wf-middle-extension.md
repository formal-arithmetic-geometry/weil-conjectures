## Worker report

The new module `Sheaf.Paper.CurveMiddleExtension` defines
`AlgebraicGeometry.Scheme.curveMiddleExtension` and
`AlgebraicGeometry.Scheme.shiftedCurveMiddleExtension`. The output is the actual
`pbcQbarCategory`, not the generic small-etale coefficient category of the
upstream `Etale.middleExtension`. No node statement is changed.

Hypotheses and clauses, in the order of the node:

- The finite field, cardinality p^a, and its chosen geometric algebraic closure
  are the existing `D : WeilConjectures.FiniteFieldDatum`. The coefficient prime
  is `l`, with `[Fact l.Prime]` and `hl : l ≠ D.p`; `Qbar` has `[Field Qbar]`,
  `[Algebra ℚ_[l] Qbar]`, and `[IsAlgClosure ℚ_[l] Qbar]`. Thus the fixed choice of
  algebraic closure is an input, not replaced by a particular algebraic closure.
- `MiddleExtensionCurve D` bundles exactly the geometric inputs.
  Its `U` and `C` are schemes over `Spec D.k₀`; `j : U ⟶ C` in `Over` includes
  the condition that j is a morphism over the base field. Finite type is the
  pair of existing classes `LocallyOfFiniteType` and `QuasiCompact` on each
  structure morphism. `IsSeparated` is on each structure morphism.
- `IsOpenImmersion c.j.left` is the open immersion. `c.dense : DenseRange
  c.j.left.base` says precisely that the closure of its image is the entire
  target. `Smooth c.C.hom` and `c.pureDimension : c.C.left.IsPureDimension 1`
  give the stipulated smoothness of the structure map and pure dimension one.
- `F : c.LisseSheaf l hl Qbar` unfolds to the recorded
  `LisseAlgebraicSheaf l c.U.left Qbar`. Its integral/rational model is extracted
  with `lisseAlgebraicPair` and `lisseCoefficientPairModel`, with no choice of
  a new representative. The auxiliary category abbreviations merely install
  noetherian, finite-dimensional, and coefficient-unit proofs derived from the
  given geometric and finite-field hypotheses. They add no input hypotheses.
- `middleExtensionLevelFunctor` starts with `Etale.lowerStar` for the actual
  integral coefficient ring. Consequently its sheaf sections at V are those of
  the input at V times_C U, its restrictions are induced by base change, and
  on a map u its components are u at that same fibre product. This is the
  module-valued specialization of the recorded ordinary direct image. The
  scalar action remains the original coefficient action throughout.
- The subsequent `ProEtale.comparisonUpperStar`, `Sheaf.restrictScalars`,
  `pbcAssociatedModule`, and `pbcExtend` change only the site/coefficient
  presentation of each torsion level. `middleExtensionIntegerMap` is the
  integral-normalized Shrink field identification, restricted to integral
  elements. `pbcCompletedScalar` is the actual constant-to-completed-ring map;
  no arbitrary coefficient isomorphism or arbitrary functor is assumed.
- `middleExtensionIntegralSheaf` is the ordinary categorical `limit` of the
  diagram of these levels and their actual transition maps. In particular no
  adic reduction-isomorphism is imposed on the direct-image tower. Torsion
  finite-level comparison and preservation of limits by ordinary direct image
  identify this with ordinary pro-etale module direct image of the original
  completed lattice. Completion acts through the quotient at each level.
- `middleExtensionIntegralComplex` applies `DerivedCategory.singleFunctor _ 0`
  to this sheaf. `curveMiddleExtension` then applies `pbcStageLocalization` at
  the model's original finite coefficient field and forms the pair with that
  exact stage. Its type `c.CoefficientCategory l hl Qbar` is definitionally the
  recorded `pbcQbarCategory` with the derived domain proofs installed.
- `shiftedCurveMiddleExtension` applies the existing shift `⟦(1 : ℤ)⟧` only
  after the preceding construction. The `PbcCommonStageCones` and
  `PbcQbarCategory` imports give the published stagewise cohomological shift.
  This is (j_*F)[1]. It never invokes `rightDerivedLowerStarPlus` or any
  unbounded right-derived direct image, so it does not discard the higher
  cohomology of Rj_* in derived adjunction or duality formulas.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  coefficient conventions. The chosen Qbar is separately explicit to allow
  the module universe required by the recorded lisse interface.
- `def-weil-pbc-scheme-conventions` is a convention record, with no single
  declaration: use Mathlib's `Scheme`, `Over`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, and `IsOpenImmersion` directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.Paper.LisseAdicSheaves`: `AdicIntegralDiagram`, `LisseIntegralSheaf`,
  `LisseAlgebraicSheaf`, `lisseAlgebraicPair`, `lisseCoefficientPairModel`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and
  `Etale.BoundedConstructibleDerivedCategory` supply the finite-level convention;
  the lisse condition itself is the recorded finite-locally-constant condition
  used by `LisseIntegralSheaf`. The current source was read with
  `scompile.py --source` because the older local checkouts lack that file.
- `Sheaf.Paper.PbcQbarCategory`: `pbcQbarCategory`, `qbarStageFieldEquiv`, and
  the actual pair-category shift and triangulation through its imports.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the ordinary
  identified-coefficient module operations. The finite-level realization above
  uses the same adjoint coefficient action, via the actual constant-to-completion
  map; there is no second definition of ringed module direct image.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  the signature, section formula and ordinary/derived separation were read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `DerivedCategory.singleFunctor`.
- `Sheaf.Paper.PbcCommonStageCones`: the published stagewise shift used in the
  actual pair category. No alternative pair shift is constructed.

The auxiliary proofs are all postponed as named theorems, each tagged with this
node and carrying a natural-language construction proof. They are
`MiddleExtensionCurve.baseProperties`, `MiddleExtensionCurve.coefficientUnits`,
`middleExtensionIntegerMap_mem`, and `middleExtensionIntegralComplex_mem`.
These discharge domain/coefficient/well-definedness obligations of this very
construction. They do not choose any unspecified object or map: all objects,
ring maps, limits and the final pair are explicit before their properties are
asserted. There are no additional independent notions, new DAG nodes, or
replacement dependency modules.

Edge cases checked before writing and again against the final definitions:

- j = identity: each level is ordinary identity pushforward; the construction
  is the original completed lattice in degree zero, then rationalized.
- F = zero: limits, associated-module functors and degree-zero insertion give
  the zero object, and its shift is zero.
- Empty C: pure dimension one and density are vacuous; an immersion forces U
  empty. None of the definitions requires a geometric point, nonempty scheme,
  connected component, or positive rank. The inverse-limit and pair definitions
  remain available.
- Disconnected smooth curves and different ranks on components are included.
- Nonfree integral lattices and torsion are permitted. No flatness of F is
  assumed; derived reductions can occupy degrees -1 and 0. There is no claim
  that the finite-level direct-image tower itself remains adic.
- Universe sizes are the recorded small site sizes: schemes in u, module values
  in u+1. Each finite coefficient field is moved through the existing
  `pbcFiniteField`/`qbarStageFieldEquiv` interface; no equality between site
  object and morphism universes is imposed.

Searches for an existing notion:

- `msearch.py ... leanfinder` query "ordinary sheaf theoretic middle extension
  of lisse adic Qbar_l sheaf on dense open of smooth curve": 8 hits, including
  BDeRham rings and tilde module sheaves; none is this adic middle extension.
- `msearch.py ... loogle '"middleExtension"'`: 0 hits.
- `msearch.py ... grep 'middleExtension|intermediateExtension|middle.extension'`:
  0 Mathlib hits.
- `msearch.py ... leansearch` query "ordinary direct image lisse adic sheaf
  coefficient inverse system proetale limit": 8 hits, including inverse systems
  and condensed locally constant presheaves; none defines this construction.
- `rg` of the upstream WeilConjectures tree for middle extension and of the
  exact node id found `Etale.middleExtension` in RealSheaves/Boundary.lean and
  special affine-line Weil-sheaf constructions. Reading the full abbreviation
  shows its domain is arbitrary small-etale A-valued sheaves. It supplies no
  adic finite-stage completion/rationalization, so it is not an exact match.
- `rg` of `lean/Sheaf` for `middleExtension`, `LisseAlgebraic`, and
  `LisseIntegralSheaf` found the recorded lisse interface and its fibre/tensor
  users, but no middle-extension or lisse-to-PBC realization bridge.
- `rg` of Mathlib, upstream sources, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no collision with any new full name.

Validation: the required `scompile.py Q126 def-wf-middle-extension` passed both
its sandbox and library single-file compilation, with no errors or warnings
(other than the permitted postponed-proof warnings, which the wrapper suppresses).
No global build or direct git mutation was run.

No STATEMENT-DISPUTED issue was found. There is no statement correction.

## Second reading by Q126

This is a second self-audit, not an independent worker review: the dispatcher's
explicit instruction prohibits starting other agents. The maintainer performs
its independent review of the delivered statement.

Reopened the node, current blueprint definition, boundary unit, and final Lean
module. The geometric structure has exactly two finite-type separated schemes
and their base-compatible dense open immersion; it retains smoothness of the
structure morphism and pure dimension one, without connectedness or nonemptiness.
The coefficient binders are prime l distinct from p and a freely chosen algebraic
closure, and the input category is the actual recorded adic lisse category.
The ordinary direct-image component is `Etale.lowerStar`, not a derived functor.
The completed lattice, degree-zero insertion, finite-stage rationalization and
pair construction are explicit data. The final shift is the recorded pair shift.
The only compiler correction was replacing the nonexistent `FiniteType` class
by Mathlib's `LocallyOfFiniteType` and `QuasiCompact`, which expresses exactly
finite type. No hypothesis or clause was changed. The four helper theorems
state only the properties needed to type this construction and have full proof
docstrings; none asserts an arbitrarily chosen object exists. Every new
signature has explicitly bound variables and universes, and all lines are at
most 100 characters. No new node or dependency repair is required.
