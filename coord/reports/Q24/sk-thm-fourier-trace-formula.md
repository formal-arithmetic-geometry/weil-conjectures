## Worker report

Stated `WeilConjectures.fourierTraceFormula` in
`Sheaf.Paper.FourierTraceFormula`, with proof `sorry`. It states the negative
classical Fourier transform identity using the recorded adic common-stage Weil
fixed pairs and their existing trace function. No statement correction and no
new DAG node are needed. The auxiliary dependency repair is described below.

Hypothesis-by-hypothesis correspondence:

- The standing finite fields, q=p^a, positive a, fixed algebraic closure k,
  distinct primes p and l, finite coefficient extension E, fixed Qbar, and
  containment mu_p in E are exactly `F : FourierSetting.{u}`. No coefficient
  identification with discrete small-etale non-torsion sheaves is imposed.
- The fixed nondegenerate character in sk-def-char is supplied by
  `Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar` and `hΨ : Ψ ≠ 1`.
  `fourierTraceBaseCharacter F Ψ` is the already defined `AddChar.compTrace`
  specialization psi=Psi composed with Tr_(k0/Fp). The prime-field algebra
  comes from the actual characteristic of k0; it is not an extra hypothesis.
  Its extension psi_n in the classical transform is the further trace
  composition, exactly the clause of sk-def-char.
- The affine line is `fourierAffineModel F PUnit.{u + 1}`. The singleton index
  has one coordinate, and its cardinality supplies the signed shift [1].
  The standard pairing on its square is x*y.
- A Weil complex K is literally
  `sfCommonStageWeilComplex F.field F.coefficients.l
  F.coefficients.different (fourierAffineModel F PUnit.{u + 1})
  F.coefficients.Qbar`, the definition recorded by
  def-weil-weil-sheaf-complex. It is not replaced by a derived Weil-sheaf object,
  a heart object, or a pure or mixed complex. Bounded constructibility is built
  into this category. A finite-stage model of the Weil isomorphism is not an
  additional input: the existing trace function descends through all models.
- The extension and its positivity convention are `n : ℕ` and `hn : 1 ≤ n`.
  `y : F.field.extensionSubfield n hn` is every element of the actual root
  subfield F_(q^n) in the fixed closure, not only the base field or its units.
- `c : Compactification (fourierModelSnd F PUnit.{u + 1}).left` specifies
  the compact-support implementation, as in def-fd-transform. It is quantified
  over every compactification. Such a projection is separated of finite type
  and admits compactification; no restriction on K, n, y or character is added.

Clause-by-clause correspondence:

- The left hand side is `weilTraceFunction` of
  `affineCommonStageFourierTransform F PUnit.{u + 1} Ψ c K`, at n and at
  `fourierAffineExtensionPoint F n hn y`. This is exactly the alternating local
  geometric-Frobenius trace from sk-def-trace, with the point-return transports
  and iterated Weil map of def-weil-local-frobenius-trace.
- `fourierAffineExtensionPoint` is the actual morphism Spec(F_(q^n)) to A1,
  over the specified inclusion k0 to F_(q^n), sending the coordinate to y.
  It is constructed by `AffineSpace.homOfVector` and `Scheme.ΓSpecIso`, with
  `AffineSpace.homOfVector_over` providing the existing over-equation proof.
- The right hand side is the unary negative of
  `classicalFiniteFieldFourierTransform F (fourierTraceBaseCharacter F Ψ) n hn`
  applied to `fun x ↦ weilTraceFunction ... K n hn
  (fourierAffineExtensionPoint F n hn x)` and y. Unfolding this existing
  definition gives exactly `-sum_x t_K(x) * psi(Tr_(F_(q^n)/k0)(x*y))`.
  The minus sign is explicit, and the sum ranges over the entire extension.
- The final sentence of the node identifies this same sum as the classical
  transform, so the equation uses that recorded transform rather than adding
  a second finite-sum definition.

Recorded dependency declarations read and used:

- sk-def-fourier-set: `Sheaf.Paper.FourierSetting`,
  `WeilConjectures.FourierSetting`.
- def-fd-transform: the original `Sheaf.Paper.WeilFourierTransform` module,
  `AlgebraicGeometry.WeilComplex.fourierTransformOfPairing` and its full affine
  specialization were read. Their fixed-pair replacement needed here is
  `Sheaf.Paper.CommonStageFourierTransform`,
  `WeilConjectures.commonStageFourierTransformFunctor` (with object wrapper
  `WeilConjectures.commonStageFourierTransform`) and
  `WeilConjectures.affineCommonStageFourierTransform`.
- sk-def-trace: `Sheaf.Paper.FourierTraceFunctions`,
  `WeilConjectures.classicalFiniteFieldFourierTransform`; its public
  `Sheaf.Paper.WeilComplexTraceFunction` dependency defines
  `WeilConjectures.weilTraceFunction` by its finite-stage uniqueness property.
- sk-def-char: `WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter`,
  `AddChar.compTrace`, `compTrace_ne_one`, `isPrimitive_compTrace`, and
  `compTrace_compTrace`. Read the full live source with `scompile.py --source`
  because this module is absent from the older local source checkout.
- def-weil-weil-sheaf-complex: `Sheaf.Paper.SfWeilSheafComplex`,
  `WeilConjectures.sfCommonStageWeilComplex` and its underlying Frobenius
  pullback, forgetful functor and finite-stage inclusion.
- The item's stmt_deps additionally name four already landed definition nodes,
  not new nodes: def-fd-adic-fourier-realization (`fourierAdicKernel`),
  def-zl-common-stage-weil-shriek (`zlComplexShriek`),
  def-zl-weil-ind-sheaf-category (`zlPull`, `zlPullComp`, `zlFrobeniusSquare`),
  def-pur-completed-pullback-tensor-comparison
  (`canonicalCommonStagePullbackTensor`). Their statements and Lean records
  were read, and the exact constructions and normalizations used were read
  in their recorded source modules.
- Already stated proof dependencies are imported: the actual tensor/pullback
  comparison module, the published compact-support exchange module and the
  Fourier stalk-formula module. The general trace theorem, the full
  Artin--Schreier-properties sketch and lem-fix-weil-operations have no usable
  recorded statement modules; they are proof dependencies only and have not
  been substituted by hypotheses of this theorem.

Edge cases checked: y=0 is included, with trivial kernel scalar one; x=0 is
included; n=1 uses the canonical embedded base field; characteristic two keeps
both the kernel and the coefficient-valued minus sign (Qbar has characteristic
zero); zero complexes and complexes with negative cohomology degrees remain
allowed; arbitrary common-stage Frobenius isomorphisms need not be defined at
the displayed underlying coefficient stage. There is no purity, weight,
perversity or nonzero-point hypothesis. The generic transform helper also
allows rank zero, with shift zero, and arbitrary positive ranks. The model
prime-invertibility helper allows an empty model (its pointwise assertion is
then vacuous as required). Every universe and variable is explicitly bound.

Searches performed for an existing statement and reusable notions:

- msearch.py, LeanFinder: “The Frobenius trace of the Fourier Deligne transform
  is minus the finite field Fourier transform of the trace function”. Eight
  results included FiniteField.trace_to_zmod_nondegenerate,
  FiniteField.algebraMap_trace_eq_sum_pow, jacobiSum identities, gaussSum_frob,
  matrix trace over finite fields and FDRep.character. None concerns the
  constructible-sheaf transform.
- msearch.py, Loogle: `"fourier", "trace"`: zero hits.
- msearch.py, grep: `fourier.*[Tt]race|[Tt]race.*[Ff]ourier`: zero Mathlib hits.
- msearch.py, LeanSearch: “Fourier Deligne transform of a Weil complex has trace
  function the negative finite field Fourier transform”. Eight results concern
  analytic Fourier integrals or Fourier notation, not the required statement.
- rg in the upstream WeilConjectures tree, the side-project lean/Sheaf tree and
  dag/lean_names_upstream.json: found the existing classical transform,
  FourierTraceFunctions, WeilFourierTransform, SfWeilSheafComplex and the adic
  kernel/compact-support constructions. No existing fixed-pair trace formula.
  Exact new declaration-name searches in Mathlib, upstream and side Lean found
  no collision. The item-id grep in the older upstream checkout found no hit.
- The item's audit names
  `AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform`; retrieved and
  read the entire live `WeilConjectures.WeilSheaf.FourierTrace` through
  `scompile.py --source`, including its complete theorem signature and
  docstring. Also read live AffineSpace.FieldPoints. The existing trace theorem
  is genuinely present in the live source, but quantifies over the derived
  category of Weil sheaves and uses that category's trace and Fourier functors.
  It does not accept the fixed pairs expressly required by the current
  def-weil-weil-sheaf-complex node. No nonexistent category equivalence or
  unprovided lift is used to claim an existing match.

Validation: both delivered files were compiled separately in dependency order
with scompile.py Q24 sk-thm-fourier-trace-formula. Both compiled without errors
or unexpected warnings. The main theorem and all nine auxiliary proof
obligations are `sorry`, as required for stage 2; every definition has actual
data. All declarations have source/blueprint docstrings; every postponed
obligation has its natural-language proof. All lines are at most 100 characters.

## Dependency modules

`def-fd-transform`: its existing record gives a general ordinary-etale functor
and a lift to the upstream derived category of Weil sheaves. That lift cannot
consume the fixed-pair objects required by the other current statement
dependencies. Added `Sheaf.Paper.CommonStageFourierTransform`, publicly importing
and retaining those existing interfaces, and repairing only this dependency's
lean record. The original ordinary-etale functor, including its general ring,
pairing, rank, compactification and morphism formula, remains the exact imported
`AlgebraicGeometry.Etale.fourierTransform`; no discrete coefficients are used
for the new common-stage construction.

The needed fixed-pair functor is constructed on both objects and morphisms:
pull back K by `IsoAlgebra.mapOfNatIso (zlFrobeniusSquare ...)`, tensor using
the actual `commonStageDerivedTensor` and
`canonicalCommonStagePullbackTensor`, then apply `zlComplexShriek`. The model
kernel is the previously defined `fourierAdicKernel`, with the actual standard
evaluation pairing in the affine specialization. Its signed shift [r] is taken
in the recorded common-stage category over the model before geometric
pullback. The structure of this descended object is the inverse normalized
`zlPullComp` followed by the equality g composed with the model projection
is the model projection. This fixes the Frobenius maps, including their
normalization, without a mere Nonempty choice. Canonical shift compatibility
identifies the resulting expression with Rp2!(p1*K tensor kernel)[r].

The helper geometry and prime-invertibility theorems merely supply properties
of the specified affine spaces, model projections and residue fields; they
add no hypothesis to the formula. In particular coefficient-prime
invertibility follows from the fixed datum, and characteristic p is derived
from cardinality p^a. The tensor Frobenius comparison is a natural isomorphism with the explicitly
normalized monoidal components. Its naturality proof is a named postponed
obligation with a proof docstring. IsoAlgebra.mapOfNatIso then supplies the
whole tensor functor; composition with pullback and compact support supplies
the whole integral-transform functor. Its map on an equivariant underlying
arrow is pullback, tensor with the identity of the shifted kernel, then Rf!.
Identity and composition laws are inherited from those functors.

The primary declaration and all helper declarations are
listed in lean.declarations. The dependency's statement, source, stmt_deps,
proof, proof_deps and all other fields are unchanged.

Dry-run repair: the first preflight rejected six names of imported side-library
constants in lean.declarations, since this module does not declare them. They
remain public imports, but the record now lists only this module's own
constants and the exact existing upstream ordinary-etale transform. The
fixed-pair repair was also completed to a full functor on morphisms, with
normalized tensor/Frobenius components and a named naturality obligation.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
