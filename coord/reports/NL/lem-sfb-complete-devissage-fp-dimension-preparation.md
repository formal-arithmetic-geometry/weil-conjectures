## Worker report

The delivery adds the stage-2 statement module
`Sheaf.AlgebraicGeometry.CompleteDevissageDimensionPreparation`, whose main
public declaration is
`AlgebraicGeometry.completeDevissage_fp_dimension_preparation`.  Its proof is
exactly `sorry`; the helper definitions use canonical tensor extension of
scalars, with no choice or hollow data.  The node's statement, source, proof,
proof dependencies, and status are unchanged.  The inherited stage-1 BLOCKED
ending was an unchanged-item refusal; the current stage-2 handoff explicitly
allows this statement to be recorded.  No repair note exists.

The helper `completeDevissageLocalizedAlgebra f C` is the canonical algebra
`Localization.Away f ⊗[R] C`, with the right tensor inclusion giving its
`C`-algebra structure.  `completeDevissageLocalizedModule f C M` is Mathlib's
`ModuleCat.extendScalars` along that inclusion.  The helper
`completeDevissageLocalizedUnit` is the pure tensor `(1 : Localization.Away f
⊗[R] C) ⊗ₜ[C] m`.  The localized structure map and arbitrary-base-change fibre
are `Spec.map` and the corresponding pullback fibre; the residue-field map is
Mathlib/WeilConjectures' `Scheme.Hom.residueFieldAlgebraMap`.

### Hypotheses and clauses

- `R` and `S` are commutative rings, with `Algebra R S` and
  `[Algebra.FinitePresentation R S]`; these are the explicit binders at the
  start of the theorem.  The finite presentation hypothesis is the node's
  `R → A` hypothesis with `S` as its Lean name.
- `N` is an additive commutative group, an `S`-module, and has
  `Module.FinitePresentation S N`.  This is the node's finitely presented
  module hypothesis.
- `p : Ideal R` with `[p.IsPrime]` is the node's prime.
- `D : CompleteAlgebraDevissage R S p N` reuses the recorded dependency and
  supplies the complete sequence, finite modules, ring maps, smoothness,
  geometrically irreducible fibres, prime extension, generic-fibre alpha
  isomorphisms, first/cokernel isomorphisms, and terminal zero condition.
- The first conjunct, for every `i : Fin D.n`, says that `D.A i` and `D.B i`
  are finitely presented `R`-algebras, that `D.bToA i`, every first map
  `D.sToA i hi`, and every successor map `D.bToAnext i j hij` are finitely
  presented ring maps, and that `D.M i` is finitely presented over both
  `D.A i` and the restricted `D.B i`-module.  The final conjunct says that
  the quotient by `LinearMap.range (D.alpha i)` is finitely presented over
  `D.B i`, rendering `Q_i = coker(alpha_i)`.
- The existential `f : R` has `f ∉ p`.  A prime `p'` of
  `Localization.Away f` is required to be the extension of `p`; an explicit
  `Module.Finite` witness supplies the localized module instance needed by
  `CompleteAlgebraDevissage`, and `E` is the complete localized dévissage.
  The equivalence `e : Fin D.n ≃ Fin E.n` with equal values preserves length
  and order, including the empty sequence.
- Algebra equivalences `a` and `b` identify every `E.A` and `E.B` with the
  canonical localized `D.A` and `D.B`; linear equivalences `m` identify every
  `E.M` with the canonical localized module, and `hr` preserves each free
  rank.  The next three conjunctions identify `E.bToA`, `E.sToA`, and
  `E.bToAnext` with the localized original ring maps on pure tensors.
- The alpha conjunction identifies each `E.alpha` on every free basis vector
  with the localized `D.alpha`; the next conjunction identifies the first
  module isomorphisms, and the final conjunction identifies the successive
  cokernel isomorphisms.  These equations make the existential data the
  localization of the fixed dévissage rather than an unrelated one.
- The final existential chooses `a : Fin D.n → ℕ`.  For every index, the
  localized `Spec(B_i)` morphism is `Smooth`, `Flat`, locally of finite
  presentation, quasi-compact, quasi-separated, geometrically integral, and
  `SmoothOfRelativeDimension (a i)`.
- For every scheme `T` over `Spec (Localization.Away f)` and point `t`, the
  pulled-back fibre is geometrically integral and integral, has
  `topologicalKrullDim = a i`, and has a unique generic point.  At each
  generic point its `Algebra.trdeg` over `T.residueField t` equals `a i`; at
  every point it is at most `a i`.  There is no relation asserted between
  different values `a i`.

The theorem docstring records the node's twelve proof steps: finite-presentation
induction and the finite-relations cokernel calculation; local constancy and
open-image shrinking; localization of all data and residue-field primeness;
geometric integrality; arbitrary-base-change fibre dimension; and the generic
point/transcendence-degree argument.  It names every proof dependency used by
those steps.

### Dependencies and declarations read

Statement dependencies were read at their recorded declarations:

- `def-weil-pbc-finitely-presented-algebra`: Mathlib
  `Algebra.FinitePresentation`.
- `def-sc-finitely-presented-module`: Mathlib `Module.FinitePresentation`.
- `def-trf-complete-algebra-devissage`: `Sheaf.TraceFormula.CompleteAlgebraDevissage`,
  `AlgebraicGeometry.CompleteAlgebraDevissage`.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Smooth` and
  `SmoothOfRelativeDimension`.
- `def-weil-flat-morphism`: Mathlib `AlgebraicGeometry.Flat`.
- `def-pc-integral-scheme`: Mathlib `AlgebraicGeometry.IsIntegral`.
- `def-kun-topological-krull-dimension`: Mathlib `topologicalKrullDim`.
- `def-weil-residue-field`: Mathlib `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the base-field algebra map is
  `Scheme.Hom.residueFieldAlgebraMap` from `WeilConjectures.PointCount`.
- `def-kun-transcendence-degree`: Mathlib `Algebra.trdeg`.
- `def-weil-affine-spectrum`: Mathlib `Spec` and `Spec.map`.
- `def-weil-pbc-module-localization`: Mathlib `LocalizedModule`.

The stated proof-dependency modules imported are
`Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
`WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`,
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`, and
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`.  Mathlib proof
leaves use their recorded declarations.  `lem-trf-smooth-connected-fibre-
normal-integrality` has no recorded Lean declaration in the DAG, so no private
copy or import was introduced; it remains named in the theorem docstring and
proof plan for stage 3.

### Edge cases checked

The empty dévissage (`D.n = 0`) is allowed: every indexed compatibility and
fibre conclusion is vacuous, and no positivity assumption was added.  Rank-zero
free sources (`Fin (D.rIndex i)` empty), zero modules, and `a i = 0` are all
allowed.  The identity localization gives the original data.  The prime
extension is required only after choosing `f ∉ p`; no inequality between
indices is imposed.  Arbitrary base change `T → Spec R_f` has no Noetherian,
finite-type, or flatness hypothesis, matching the node.

### Searches

- `msearch.py ... leanfinder "Finite presentation of complete algebra devissage modules and smooth geometrically integral fibres of constant dimension after localization"`: no complete theorem; only generic finite-presentation/smooth candidates.
- `msearch.py ... leansearch "finite presentation complete algebra devissage localized smooth geometrically integral fibres constant dimension"`: eight generic hits, including `Algebra.FinitePresentation.of_isLocalizationAway` and smooth finite-presentation lemmas; none states this dévissage result.
- `msearch.py ... loogle "Algebra.FinitePresentation, Module.FinitePresentation, SmoothOfRelativeDimension"`: no exact complete statement (the tool reports `SmoothOfRelativeDimension` as unknown in its Loogle environment).
- `msearch.py ... grep "CompleteAlgebraDevissage|completeDevissage|complete_devissage"`: no duplicate theorem in the searched source.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found only the recorded `CompleteAlgebraDevissage` definition and unrelated projective-localization results; no existing statement with this node's clauses.
- Declaration source/docstrings read directly: Mathlib `FinitePresentation`, `Module.FinitePresentation`, `Smooth`, `Flat`, `IsIntegral`, `Spec`, `LocalizedModule`, `topologicalKrullDim`, `Algebra.trdeg`; project modules listed above.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NL

Author self-check for direct delivery; the maintainer supplies the independent review.
I reread the node beside the module.  The ring, module, prime, and
complete-dévis­sage hypotheses are all explicit.  The first conclusion covers both
algebra and module finite presentation and every displayed ring map, including
first and successor maps.  The quotient is rendered by the range quotient.  The
localization existential keeps `f ∉ p`, the extended prime, the canonical tensor
algebra/module, rank and index preservation, every ring-map compatibility, alpha,
first-isomorphism, and cokernel compatibility.  The geometry conjunct contains
smoothness, flatness, finite presentation, quasi-compactness/separation,
geometric integrality, and a single nonnegative relative dimension for each
index.  The arbitrary `T,t` clause states geometric integrality, dimension,
unique generic point, generic transcendence degree equality, and the pointwise
upper bound.  No comparison of distinct dimensions, positive-length condition,
flatness of arbitrary base change, or extra Noetherian hypothesis appears.
The module compiles with `scompile.py` without errors or warnings.
The delivery dry run passed after recording the signature up to (excluding)
`:=`, as required by the preflight signature parser.
