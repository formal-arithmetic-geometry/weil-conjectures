## Worker report

Repair of returned stage-1 delivery dde02b944fe9. The dispatcher-retained sandbox contained
only `.brief*` markers, with no node or report to reuse. I read the current live Q70 node
(reviewed by NT-cc-Q70-dc240bbe1) and rebuilt this as a stage-2 delivery. The original five
proof steps, proof_deps, proof_origin, mathlib_searches, split_report, statement and other
metadata are preserved. The only changes to that node are its new lean record and the
addition of the already landed def-trf-hilbert-samuel-invariant to stmt_deps.

The module Sheaf.AlgebraicGeometry.HilbertSamuelEqualityComponentRigidity states
AlgebraicGeometry.HilbertSamuel.component_dimensions_eq_of_function_eq. Its sole proof is
`sorry`. It introduces no definitions, axioms or additional postponed theorems.

Clause-by-clause correspondence:

- Reduced X: `[IsReduced X]`.
- Finite type over Q: `[LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]`, with
  `p : Z ⟶ Spec (.of (ULift.{u} ℚ))`. ULift gives the rational field in the scheme's
  universe and excludes no scheme universe.
- Locally closed in a smooth scheme: `i : X ⟶ Z`, `[IsImmersion i]`, `[Smooth p]`.
  In particular the embedding is not strengthened to a globally closed immersion.
- Raw stalk lengths and inclusive summation: the existing
  `HilbertSamuel.localFunction` uses `Module.length` of the stalk modulo the (n+1)-st
  maximal-ideal power; `summation` sums indices in `Finset.range (n+1)`.
- H = Lambda^trdeg h: the existing `HilbertSamuel.function` iterates `summation` exactly
  `Cardinal.toNat (Algebra.trdeg k (X.residueField x))` times, using the canonical
  `p.residueFieldAlgebraMap`. For these finite-type schemes the lengths and transcendence
  degrees are finite. The transformed scheme is also finite type: its blowup is proper
  over X, and the identity strict transform is isomorphic to it by Tag 080E. Natural
  conversion therefore loses no values. No closed-point restriction is used.
- Smooth closed center: `I : X.IdealSheafData` is the canonical quasi-coherent ideal
  encoding of the closed subscheme, and `[Smooth (I.subschemeι ≫ i ≫ p)]` is smoothness
  over Q, rather than smoothness of the closed inclusion. On the Noetherian finite-type
  X the center is automatically of finite presentation.
- H_X locally constant on C: `hconstant : IsLocallyConstant (fun c : I.subscheme ↦
  function (i ≫ p) (I.subschemeι c))`. This restricts the function of X, not that of C.
- X' and its map: `I.strictTransform (𝟙 X)` is the existing scheme-theoretic closure in
  the fiber product for the blowup `I.blowupMap`; its projection to X is the canonical
  `strictTransformToSource (𝟙 X) I.blowupMap I.support.compl`. This is the intrinsic
  blowup, presented as a strict transform. Stacks 080E, already formalized by
  `exists_blowup_comap_iso_strictTransform`, identifies the strict transform in an ambient
  blowup with this intrinsic blowup. For a locally closed embedding one first restricts
  the ambient to the open in which the embedding is closed. Thus this formulation covers
  the given ambient strict transform up to its canonical isomorphism over X, without
  requiring a global ambient extension of C. Isomorphisms preserve stalk lengths,
  residue field transcendence degrees, components and their topological dimensions.
- y maps to x in C: the binders `x : X`, `hx : x ∈ I.support`,
  `y : I.strictTransform (𝟙 X)` and `hy : strictTransformToSource ... y = x`.
- Equality as sequences: `heq` is equality of the full functions `ℕ → ℕ`, over the
  structure map induced by that canonical projection. It is not equality of multiplicity,
  leading coefficient, dimension, or a finite truncation.
- P_X(x): the right-hand set comprehension uses `W : Set X`,
  `W ∈ irreducibleComponents X`, `x ∈ W`, and `topologicalKrullDim W = d`.
- P_X'(y): the left-hand comprehension uses exactly the same construction on the strict
  transform and y. The conclusion is equality of these sets, so repetitions of a
  component dimension are ignored, exactly as in the node.
- Components inside C are allowed: there is no density, nowhere-dense-center,
  noncontainment, equidimensionality or component-survival hypothesis.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  AlgebraicGeometry.LocallyOfFiniteType and AlgebraicGeometry.QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and Immersion:
  AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsImmersion (the latter gives
  the locally closed embedding; I.subschemeι already has the former instance).
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.RingTheory.Length: Module.length.
- Mathlib.RingTheory.AlgebraicIndependent.Basic: Algebra.trdeg.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and
  Scheme.Hom.residueFieldMap; the existing normalized function uses residueFieldAlgebraMap.
- WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup and blowupMap.
- WeilConjectures.Compactification.StrictTransform: AlgebraicGeometry.strictTransform,
  Scheme.IdealSheafData.strictTransform and AlgebraicGeometry.strictTransformToSource.
- Mathlib.Topology.Irreducible: irreducibleComponents.
- Mathlib.Topology.KrullDimension: topologicalKrullDim, applied to component subspaces.
- Sheaf.AlgebraicGeometry.HilbertSamuelInvariant (already landed
  def-trf-hilbert-samuel-invariant): summation, localFunction and function. This landed
  node is the sole stmt_deps addition; no dependency record is rewritten.

Proof-only imports follow all stated live proof dependencies: Noetherian; prime-spectrum
minimal-prime components; StrictTransformBlowup; Affine.Defs; ReesAlgebra; RelativeProj.BaseChange;
StrictTransform; Blowup.Proper (including Proper); and FiniteTypeDomainDimensionTrdeg.
The two proof inputs lem-trf-hilbert-samuel-near-normal-cone and
lem-trf-normal-cone-directrix-minimal-primes have no recorded Lean declarations on this
base, so there is no module to import for them; their complete roles remain in the five-step
docstring. They are proof dependencies, not missing statement notions.

Edge cases checked before writing: the empty X or empty center admits no x with hx; the
whole-scheme center has empty blowup/strict transform and admits no y. Centers containing
some components remain allowed. No requirement that every component have the same dimension
is imposed. Generic and nonclosed points are permitted and retain the trdeg shift. At n=0,
the raw function is the length of the residue field, and summation includes index zero.
Zero-dimensional components, repeated component dimensions and dimension bottom/top use
the unchanged Mathlib dimension codomain `WithBot ℕ∞`.

Searches made:

- msearch.py leanfinder: “Equality of extended Hilbert Samuel sequences at a near point
  of a blowup preserves the dimensions of irreducible components through the points”.
  Eight hits: prime-spectrum chains and regular-sequence Krull-dimension formulas;
  their displayed signatures do not state the near-point component equality.
- msearch.py loogle: `AlgebraicGeometry.HilbertSamuel.function, irreducibleComponents,
  topologicalKrullDim`. No hits; the project declaration is not in the Mathlib index.
- msearch.py grep: `hilbertSamuel|HilbertSamuel|hilbert_samuel` in AlgebraicGeometry:
  zero Mathlib hits.
- msearch.py leansearch: “Equality of Hilbert Samuel functions at a point of a blowup
  preserves dimensions of irreducible components”. Eight hits: homeomorphism dimension
  invariance, ring equivalence dimension/height invariance and a tautological function-field
  congruence; no near-point result.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, HilbertSamuel,
  component dimensions/profile and the proposed declaration: no existing theorem for this
  node; found and read HilbertSamuelInvariant, HilbertSamuelPresentation and
  HilbertSamuelLocalPresentations. Reused the existing invariant instead of defining it.
- Read the live item and all eleven original statement-dependency records, their source
  declaration docstrings/signatures, and the added invariant node/module. Read ILO VIII
  2.3.13 directly from the local PDF with pdftotext (printed p.94). BMT is marked WANTED
  in the live node; the proof and source fields are preserved, not silently replaced.

No statement correction, disputed statement, new node or dependency repair is needed.
The former absent lem-trf-blowup-generic-component-correspondence is not cited: the delivery
uses the unchanged current five-step Q70 proof, not the returned eight-step split.

## Second reading by Q23

A separate second pass in this session reread the live JSON statement and the whole final
Lean signature and docstring. No other agents were started, as the dispatcher forbids them;
this section records that second pass, not an invented independent worker.

I checked each binder against the statement: Q is universe-lifted but unchanged as a field;
reducedness, both finite-type conditions, immersion in a smooth scheme, and smoothness of the
actual center are present. The local-constancy binder evaluates H_X on the center inclusion,
and equality compares the induced H on the strict transform with H at x. Both x in C and
the canonical image equation for y are explicit. The conclusion uses all irreducible
components through the points and global topological subspace dimension, not local dimension
or only the largest dimension. It compares sets rather than multisets or cardinalities.
The H equality is essential and present; no component-avoidance assumption was introduced.

The one representation choice needing explicit explanation is X': the identity strict
transform in the intrinsic blowup replaces a chosen ambient model. I reread Tag 080E's
recorded comparison and its projection identity: this change of model is an isomorphism over
X, so it preserves every quantity in the statement. Using this model avoids accidentally
assuming that the locally closed embedding or the center is globally closed in the original
ambient. This explanation is now in both the module and the clause mapping above.

I verified the docstring retains all five Q70 proof steps and their dependency ids, including
the argument that components contained in C are excluded by equality only as a consequence.
No old stage-1 proof edits remain. The JSON lean.statement is extracted verbatim from the
final signature. All variables and the universe are bound with autoImplicit disabled.
