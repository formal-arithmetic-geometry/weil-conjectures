## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.TameRadicalNormalization` states
`AlgebraicGeometry.tame_radical_curve_normalization`, with `sorry` as its only proof.
It defines no new notion. The item JSON changes only in `lean`.

The live NM review dated 2026-10-22 is a stage-1 split review, not a stage-2
statement review: the live node has no `lean` record. This delivery preserves its
statement and all ten proof steps and does not re-split it.

I read the item, its statement-dependency records and their declarations/docstrings.
The cited CompactObject example has been withdrawn, so I also read its recorded
upstream replacement. I read the entire standing stage-2 brief and the stage-2
rules and delivery faults. Source checked: de Jong, *Families of curves and
alterations*, §3.5, printed p.607, at
https://www.numdam.org/item/10.5802/aif.1575.pdf (PDF page 9).
That passage constructs a radical extension and its normalization, extracts
algebraic constants, and treats tame ramification at separable branch points
and the étale marking. The DAG's ten-step Stacks expansion is in the theorem's
docstring. No mathematical statement correction is needed.

### Every hypothesis and object

- A field K: `(K : Type u) [Field K]`.
- The K-curve C and its structure map: `(C : Scheme.{u}) (q : C ⟶ Spec (.of K))`
  and `[IsSmoothProjectiveCurve q]`. The recorded upstream class extends the
  integral, separated finite-type, dimension-one curve class, smoothness and
  projectivity. `[GeometricallyIntegral q]` is the additional geometric-integrality
  hypothesis.
- F = K(C): the exact Mathlib generic stalk `C.functionField`, which is the
  integral-scheme clause of the recorded `def-sc-function-field`. No separate F
  or arbitrary function-field isomorphism is introduced.
- The K-inclusion in F: `[Algebra K C.functionField]` and `hK` identify its
  algebra map with the composite of the K-structure map on global sections
  and the germ at the generic point. This is a compatibility specification,
  not an additional mathematical restriction: that composite always supplies
  this algebra instance. It prevents an unrelated K-algebra structure.
- Positive invertible n: `(n : ℕ) (hn : 0 < n) (hnK : IsUnit (n : K))`.
- All nth roots of unity in K: `hroots : ∃ ζ : K, IsPrimitiveRoot ζ n`.
  For positive n invertible in a field, existence of a primitive nth root is
  equivalent to all nth roots of unity lying in K. This does not require that
  the functions be independent or that the radical extension have degree n^r.
- The finite list of nonzero rational functions: `(r : ℕ)` and
  `(a : Fin r → C.functionFieldˣ)`. Units of a field are exactly nonzero elements.
- Reduced finite étale closed subschemes D and M: the scheme binders, `iD`, `iM`,
  their `IsClosedImmersion` and `IsReduced` instances, and `IsFinite`/`Etale`
  instances on their composites with q. These are their K-structures.
- Disjointness: `hdisj : Disjoint (Set.range iD) (Set.range iM)`.
- The specified complement C minus D: `(U : C.Opens)` and `hU` identify its
  underlying set with the complement of the range of iD. Such an open always
  exists since iD is a closed immersion.
- Regularity of both a_j and its inverse off D: `hreg` has one conjunct for
  each, at every `x ∈ U`. Membership in the range of
  `algebraMap (C.presheaf.stalk x) C.functionField` means that the rational
  function is regular at x. These local conditions are equivalent to
  regularity on U by the sheaf axiom and injectivity into the function field.
- A fixed algebraic closure of F: `(Ω : Type u) [Field Ω]`
  `[Algebra C.functionField Ω] [IsAlgClosure C.functionField Ω]`.
  `[Algebra K Ω] [IsScalarTower K C.functionField Ω]` specify the composite
  K-inclusion; such an algebra always exists by restriction of scalars.
- The actual chosen roots: `(α : Fin r → Ω)` and `hα`, which is precisely
  `α j ^ n = algebraMap C.functionField Ω (a j)`.
- L inside Ω: `L : IntermediateField C.functionField Ω` and
  `hL : L = IntermediateField.adjoin C.functionField (Set.range α)`.
  Thus L is exactly F(α_1,...,α_r), not an arbitrary finite extension.
- The normalization: `C.normalizationIn L` and its canonical map
  `C.fromNormalizationIn L`, exactly the dependency's recorded declarations.
- E inside L: `algebraicClosure K L`, Mathlib's relative algebraic closure,
  whose elements are exactly those algebraic over K by `mem_algebraicClosure_iff`.
  This is not the absolute `AlgebraicClosure K`, and no chosen field is substituted.

All universes and variables are explicit; `set_option autoImplicit false` enforces
this. A common universe u hosts the fields and schemes, as required by the
recorded normalization and scheme definitions. It can be any universe and thus
can contain any given collection of these objects. No independent smaller
universe is used for field-extension tests.

### Every conclusion

- L/F finite Galois: `FiniteDimensional C.functionField L ∧ IsGalois C.functionField L`.
- E/K finite separable: `FiniteDimensional K (algebraicClosure K L)` and
  `Algebra.IsSeparable K (algebraicClosure K L)`.
- The normalization map finite and surjective: `IsFinite (C.fromNormalizationIn L)`
  and `Surjective (C.fromNormalizationIn L)` (the scheme morphism class).
- Étale above C minus D: `Etale (C.fromNormalizationIn L ∣_ U)`.
- Smooth over K: `Smooth (C.fromNormalizationIn L ≫ q)`.
- K algebraically closed in F: `algebraicClosure K C.functionField = ⊥`.
- E intersect F equals K inside L: for every `z : C.functionField`, membership
  of its canonical image in `algebraicClosure K L` is equivalent to membership
  of z in `Set.range (algebraMap K C.functionField)`. Since all field maps are
  injective, this is exactly the intersection equality, including both containments.
- The function field remains the specified L: the existential `e` is an
  isomorphism `Spec L ≅ Spec (C.normalizationIn L).functionField` and its equation
  identifies the canonical generic map to the normalization. The contravariant
  Spec equivalence makes this a field isomorphism, pinned to that generic map.
  This is the same interface already used by the recorded normalization module.
- Canonical structural factorization through Spec E: `qE` has source exactly
  the normalization and target exactly `Spec (algebraicClosure K L)`. Its first
  equation factors the K-structure map; its second equation says that on the
  canonical generic point it is the inclusion E into L. This specifies the
  canonical factorization, excluding a twist by an automorphism of E/K. The
  generic equation determines qE uniquely: the source is integral and the
  target affine, so its global-section map is determined in the generic stalk.
  This is not an arbitrary map assumed as an input.
- Over E the normalization is a smooth projective geometrically integral curve:
  `IsSmoothProjectiveCurve qE ∧ GeometricallyIntegral qE`.
- The reduced inverse image of M is finite étale over E: the actual scheme
  pullback `P = pullback (C.fromNormalizationIn L) iM` is asserted `IsReduced`;
  its composite `pullback.fst ... ≫ qE` is `IsFinite` and `Etale`.
  Therefore P itself is the reduced inverse image. This formulation needs no
  additional reduction construction. It has the same strength under the
  hypotheses and the étaleness-off-D conclusion: P → M is étale by base change
  and disjointness, so reducedness of M implies reducedness of P (the exact
  node proof step 9). No extra hypothesis or stronger geometric requirement
  is imposed on the input.

The normality and integrality of the normalization are supplied by the existing
normalization construction and its instances; no hollow definition is introduced.
The genus and group-action sentences in the node's general notion list introduce
no genus bound, group or action in this particular statement, so none is invented.

### Recorded dependency declarations used

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-smooth-projective-curve`: `AlgebraicGeometry.IsSmoothProjectiveCurve`,
  WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective (and its curve parents).
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIntegral`,
  Mathlib.AlgebraicGeometry.Geometrically.Integral. Its irreducible, reduced and
  connected companions were also read; integrality is the clause this item uses.
- `def-sc-function-field`: WeilConjectures.AlgebraicGeometry.FunctionField gives
  `Scheme.functionFieldOfComponents`; its documented integral specialization is
  Mathlib's `Scheme.functionField`, actually used here, not a private copy.
- `def-pc-field-extension`: `Algebra` with its `algebraMap`,
  Mathlib.Algebra.Algebra.Defs. Compatibility data are spelled out above.
- `def-fin-normalization-extension`: `Scheme.normalizationIn`,
  `Scheme.fromNormalizationIn` and `Scheme.fromSpecOfAlgebraFunctionField`,
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite; the integral-morphism definition
  was read, but is not an independent conclusion of this node.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth (publicly exported by Etale).
- `def-pc-genus`: `Scheme.arithmeticGenus`,
  WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar, read and imported
  transitively through SmoothProjective; there is no genus clause in this item.
- `def-weil-algebraic-closure`: `IsAlgClosure`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, exported by the public
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure import.
- The other notions use the existing Mathlib `IntermediateField.adjoin`,
  `algebraicClosure`, `IsGalois`, `IsPrimitiveRoot`, `FiniteDimensional`,
  `Algebra.IsSeparable`, and scheme pullbacks. No definition node is missing.

Every proof-dependency module with a currently recorded Lean module is imported
as a plain proof import, unless it is already a public statement import. The
existing theorem `exists_iso_toNormalization_normalizationIn` supplies the same
function-field comparison interface. The natural-language docstring names every
step and every dependency needed for stage 3, including the presently unstated
proof dependencies; this stage does not prove them.

### Edge cases checked

- `r = 0` is permitted: Fin 0 is empty, hα and hreg are vacuous and hL makes L
  the bottom intermediate field, canonically F. No nonempty index assumption occurs.
- `n = 1` is permitted. A primitive first root is 1, and the radical field is F.
- Empty D is allowed: U is the whole curve and the cover is everywhere étale.
- Empty M is allowed: the pullback is empty and finite étale over E. There is
  no Nonempty assumption on D, M or the pullback, nor any field structure on
  their rings of global sections.
- Positive characteristic dividing n is excluded exactly by hnK. Characteristic
  zero and imperfect fields otherwise remain included. Separability at the branch
  points comes from the finite étale D/K hypothesis, not perfection of K.
- Dependent radicals, repeated functions and functions which are nth powers are
  allowed: there is no full-degree or independence hypothesis.
- Nontrivial algebraic constants E/K are allowed: no E=K assumption is made.
- An empty C is correctly excluded by the node's integral dimension-one curve
  hypothesis. The zero ring is correctly excluded only for the fields, not for
  the finite étale empty schemes.

### Searches

Searches used the prescribed msearch.py wrapper and read-only rg searches.

- LeanSearch: "A Kummer cover of a smooth projective curve ramified tamely only
  over separable closed points has smooth normalization and finite separable
  algebraic constants". Eight hits concerned algebraicity of separable extensions,
  Kummer-Dedekind, radical-extension notation, cyclotomic separability and formally
  étale field maps. None was the normalization theorem.
- LeanFinder: "Normalization of a smooth projective curve in a tame Kummer
  radical extension is smooth over its algebraic constant field". Eight hits
  concerned Weierstrass curves, their reduction and standard smoothness; none
  stated this theorem.
- Loogle: "Scheme.normalizationIn, IntermediateField.adjoin, IsGalois".
  Zero hits; the service reported unknown identifier Scheme.normalizationIn
  (this is a project declaration, not a Mathlib one).
- msearch grep: "normalizationIn|tame.*normalization|radical.*curve", in
  AlgebraicGeometry. Zero Mathlib hits.
- Read-only rg in lean/WeilConjectures and lean/Sheaf for normalizationIn,
  radical curves and tame normalization found the existing normalization
  construction and the affine connected-curve normalization theorem. The
  latter is for affine curves over an algebraically closed field, so is not
  this smooth projective statement with constants E. A direct search for this
  node id in lean/WeilConjectures found no declaration. Field-theory hits for
  tame radical kernels concern Galois characters, not this scheme theorem.
- Read-only Mathlib searches found `IntermediateField.adjoin`, `algebraicClosure`
  and the absolute algebraic-closure interfaces; these are used directly.

No STATEMENT-DISPUTED flag or node fault remains.

### Validation

The delivered module was compiled in module mode by scompile.py against the
server's live published library, in both its sandbox and public module paths.
It compiled cleanly (3.5 seconds and 3.2 seconds respectively). The first probe
needed the explicit generic stalk germ in hK instead of germToFunctionField on
⊤, to avoid requesting an unnecessary Nonempty ⊤ typeclass. This was repaired
without a statement change. The final file has no diagnostic commands, no
local notation or local instances, no auxiliary proofs and no lines over 100
characters. All declarations are public and auto-bound implicits are disabled.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
