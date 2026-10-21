## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.TateResidueFieldExtension` states
`AlgebraicGeometry.Scheme.tate_residue_field_extension`, with `sorry` as its whole proof.
Its helper `tateRationalDifferentialMap` constructs the canonical map of rational
differentials. The helper contains real data: the existing generic stalk map,
Mathlib's map of Kähler differentials for a commutative square, and a proof that
this square commutes. No residue, field homomorphism, or differential map is chosen
from an existence assertion. Both declarations belong to this node's notion of
scalar extension of rational differentials and residues; no independent notion
needs a new node.

Hypothesis and clause correspondence:

- Any ground field and any field extension: `(k K : Type u) [Field k] [Field K]
  [Algebra k K]`. There is no algebraicity, finiteness, perfectness, characteristic,
  or separability restriction. A common universe can contain any given pair of fields.
- The scheme over k: `(C : Scheme.{u}) [C.Over (Spec (.of k))]`.
- Smooth projective curve: `[IsSmoothProjectiveCurve (C ↘ Spec (.of k))]`, exactly
  the recorded class. Its parent classes include integrality and dimension one.
- Geometrically connected: `[GeometricallyConnected (C ↘ Spec (.of k))]`.
  The two initial `letI` terms derive geometric irreducibility from smoothness and
  geometric connectedness, then geometric integrality using smooth geometric
  reducedness. These are supplied constructions, not additional assumptions.
  The existing base-change instance then supplies integrality of C_K.
- C_K and p: `C.baseChangeField k K` is the actual pullback of the structure
  morphism along `Spec.map (CommRingCat.ofHom (algebraMap k K))`. Its projection
  to C is `pullback.fst`, and its K-structure morphism is `pullback.snd`.
- Closed point: `∀ (x : C), IsClosed ({x} : Set C) → ...`.
- F and F_K: `C.functionField` and `(C.baseChangeField k K).functionField` are
  the generic stalks, with their existing field instances. `functionFieldAlgebra`
  and its compatibility proof install precisely the canonical structure-map
  algebras needed by `localSubalgebra` and Kähler differentials.
- Arbitrary rational differential: `∀ η : KaehlerDifferential k C.functionField`.
- Its induced image η_K: `tateRationalDifferentialMap k K C (C.baseChangeField k K)
  (pullback.fst ...) pullback.condition η`. The helper applies
  `Hom.functionFieldMap p p.apply_genericPoint_of_flat`, not an arbitrary map,
  and then `CommRingCat.KaehlerDifferential.map` to its structure-map square.
  On a generator f dg it is p*(f) d(p*(g)), by Mathlib's `map_d`/`map_D`.
  Flatness of this projection follows from base change of a field extension;
  it is resolved by instance search, not required as a new theorem hypothesis.
- Both local residues: `TateResidue.localRes (localSubalgebra ... ...)` uses
  exactly the existing finite-potent trace construction imported by the recorded
  Picard-duality module. No classical residue or residue-field trace substitutes it.
- The sum: `∑ᶠ y : {y : C.baseChangeField k K // pullback.fst ... y = x}, ...`.
  This is over the underlying points of p^{-1}(x), equivalently the points of
  Spec(κ(x) tensor_k K). The latter algebra is finite-dimensional over K because
  x is closed and C is of finite type. Thus the indexing type is finite and
  `finsum` is the ordinary finite sum. It does not introduce a finiteness assumption.
  The base-changed points are closed: p^{-1}(x) is closed and has finite Artinian
  coordinate algebra. Every term has coefficient one; nilpotents are retained in
  the local rings, with no separable reduction or added multiplicity.
- Right hand side: `algebraMap k K (TateResidue.localRes (localSubalgebra k C x) η)`
  is exactly the image under the specified inclusion ι:k→K.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsSmoothProjectiveCurve`, its parent classes and
  `IsSmoothProjectiveCurve.isIntegral_baseChangeField`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected` and `.Integral`:
  `GeometricallyConnected`, `GeometricallyIntegral`, `GeometricallyIrreducible`
  and `GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible`.
  `WeilConjectures.AlgebraicGeometry.Regular` provides
  `GeometricallyIrreducible.of_smooth_of_geometricallyConnected`; the imported
  `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced` supplies the
  smooth geometric-reducedness instance.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  its pullback conventions; `WeilConjectures.AlgebraicGeometry.BaseChangeField`:
  `Scheme.baseChangeField` and its second-projection structure morphism.
- `WeilConjectures.AlgebraicGeometry.FunctionField` and
  `Mathlib.AlgebraicGeometry.FunctionField`: the recorded component-product
  definition's integral clause uses `Scheme.functionField`, not a duplicate carrier.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal derivation
  and universal property; `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`:
  `CommRingCat.KaehlerDifferential.map` for the actual ring square.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the scheme-theoretic fibre indexing avoids choosing
  presentations or primes in a second model of the fibre algebra.
- `Sheaf.AlgebraicGeometry.Curve.PicardDuality`:
  `Scheme.picard_duality_one` and its normalized Tate trace; the local construction
  it imports is `WeilConjectures.RingTheory.TateResidue.LocalResidue`:
  `TateResidue.localRes`. Its local rings are the canonical
  `Scheme.localSubalgebra` in `Curve.AdelicStructureSheaf`.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`, `Scheme.Hom.apply_genericPoint_of_flat`.

Available proof-dependency modules are imported privately:
`Sheaf.RingTheory.TateAbstractResidueCalculus`,
`Sheaf.RingTheory.TateResidue.DVRResidueCalculus`, and
`Sheaf.RingTheory.TateResidueExactSequence`. The node
`lem-pc-curve-local-scalar-principal-parts` has no recorded Lean module in the read
checkout, so there is no such module to import; its objects are not needed to type
this statement. The complete six-step proof plan is in the theorem docstring.

Edge cases checked before writing: η=0 gives zero on both sides; the identity
extension reduces to the one-point fibre identity; a separably splitting extension
sums over all distinct points. In characteristic p, for k=F_p(a) and the point
T^p=a on P¹, extending to K=k(a^(1/p)) makes a single nonreduced fibre of length p.
The differential T^(p-1)dT/(T^p-a) has Tate residue 1 and remains residue 1 after
extension, demonstrating why multiplying the single term by p would be false.
The statement retains this case. The empty curve is excluded by the recorded
curve class; the proof imposes no nonempty fibre hypothesis. Inseparable and
transcendental extensions K/k are allowed. There is no statement correction and
no STATEMENT-DISPUTED fault.

Searches for existing declarations (all actual searches, 2026-10-21):

- `msearch.py ... leanfinder "Sum of Tate residues of rational differentials over
  a fibre commutes with arbitrary ground field extension"`: eight hits including
  `Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap`, number-field
  zeta residues and differential-field lemmas; none states Tate scalar compatibility.
- `msearch.py ... leansearch "Local residue of rational differentials commutes with
  extension of the base field"`: eight hits, residue-field maps and localization
  base change; no match for the residue functional on rational differentials.
- `msearch.py ... loogle "TateResidue.localRes, KaehlerDifferential.map"`:
  no hits; service reports unknown identifier TateResidue.localRes (project-local).
  Its actual definition was subsequently read in the project source.
- `msearch.py ... grep "residue.*baseChange|localRes.*[Bb]ase|residue.*fieldExtension"`:
  five Mathlib hits about cotangent-complex base change and unramified/quasifinite
  residue fields; none states the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, for Tate residues,
  field-extension residue statements, function-field maps, localSubalgebra and
  IsFunctionFieldAlgebra: found the canonical constructions listed above and no
  scalar-extension sum identity. Searching the item's blueprint id in
  `lean/WeilConjectures` gave no match. Searching the new declaration names gave
  no existing declaration. The finite-potent trace and local residue definitions
  were read rather than replaced.

Source checked: local PDF `literature/tate-residues-of-differentials-on-curves_ASENS-1968.pdf`,
pp. 149–155, especially the stable finite-dimensional trace characterization,
Theorem 1, formula (*), and local lattice residues. The helper's square uses germ
naturality and ΓSpecIso naturality; it has no postponed proof obligation.

Validation: scompile.py compiled this module as a standalone sandbox module and
under its final library module name against the live published library, both
successfully with no errors or non-sorry warnings. Delivery dry-run results follow
in the tool output.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
