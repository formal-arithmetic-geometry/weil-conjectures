## Worker report

The module `Sheaf.Paper.RealSheavesSetup` defines the complete chapter setup of
`d-real-setup`. Its primary declaration is `RealSheaves.Setup`. Its additional
recorded declarations spell out every geometric and Frobenius convention of the
same node. There are no theorems, postponed proofs, `sorry`s, new nodes, dependency
repairs, or changes to the natural-language statement.

I opened the current main-20261015 blueprint definition at
`sec-purity-real-sheaves/sk-d-real-setup/d-real-setup.md` and the DAG node.
The mapping of all hypotheses and clauses is as follows.

| Node clause | Lean rendering |
| --- | --- |
| A prime p | `Setup.p`, `Setup.p_prime : p.Prime` |
| Integer a >= 1 | `Setup.a : ℕ`, `Setup.a_pos : 1 ≤ a` |
| q = p^a | `Setup.q D := D.p ^ D.a` |
| A fixed field k_0 with q elements | `Setup.k₀`, its `Field` and `Fintype` structures, and `Setup.card_eq : Fintype.card k₀ = p ^ a` |
| A chosen algebraic closure k of k_0 | `Setup.k`, its field and algebra structures, and `Setup.closure : IsAlgClosure k₀ k` |
| A prime ell different from p | `Setup.l`, `Setup.l_prime : Fact l.Prime`, `Setup.l_ne_p : l ≠ p` |
| Q_ell | Existing `Padic l`, written `ℚ_[l]` |
| A chosen algebraic closure Qbar_ell | `Setup.Qbar`, its field and `Algebra ℚ_[l]` structures, and `IsAlgClosure ℚ_[l] Qbar` |
| An injective unital field homomorphism iota into C, without continuity | `Setup.iota : Qbar →+* ℂ`; homomorphisms from a field into the nontrivial field C are injective. No topology or inverse is supplied. |
| C_0 a scheme over k_0 | `C₀ : Scheme.{u}` and `[C₀.Over (Spec (.of D.k₀))]` |
| C_0 nonempty | First conjunct `Nonempty C₀` in `Setup.IsCurve` |
| Separated structure morphism | `IsSeparated (C₀ ↘ Spec (.of D.k₀))` |
| Smooth structure morphism | `Smooth (C₀ ↘ Spec (.of D.k₀))` |
| Finite type structure morphism | `LocallyOfFiniteType` and `QuasiCompact` of that structure morphism |
| Pure dimension one | The recorded `C₀.IsPureDimension 1` |
| C = C_0 times_{k_0} Spec k | `Setup.geometricCurve`, the existing `Limits.pullback` along `Spec.map (algebraMap D.k₀ D.k)` |
| C connected | `ConnectedSpace (D.geometricCurve C₀)` |
| x a closed point | The subtype binder `x : closedPoints C₀` |
| kappa(x) | Existing `C₀.residueField x.1` |
| e_x = [kappa(x):k_0] | `Setup.closedPointDegree`, the recorded structure morphism's `residueDegree x.1` |
| q_x = q^(e_x) | `Setup.closedPointCardinality` |
| F is inverse q-power field Frobenius on k | `Setup.frobenius` abbreviates `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`, whose data are the inverse of the recorded arithmetic Frobenius; `card_eq` identifies its exponent with q. |
| F_x on a chosen closure of kappa(x), inverse q_x-power Frobenius | `Setup.localFrobenius` takes any `Ω : Type w` with `IsAlgClosure (C₀.residueField x.1) Ω` and specializes the same existing construction to the finite residue field. Closed-point finiteness comes from the existing theorem `Scheme.Hom.finite_residueField_of_isClosed`, followed by `Module.finite_of_finite`; no finite-residue-field hypothesis is imposed on the caller. Since this is a finite extension of k_0, its cardinality is q^(e_x). |
| An open subscheme U_0 -> C_0 | `Setup.IsAffineOpen D j` requires `IsOpenImmersion j` and the equality between its composite and the structure morphism of U_0. |
| U_0 nonempty | First conjunct `Nonempty U₀` in `Setup.IsAffineOpen` |
| Isomorphic over k_0 to Spec A | The existential `e : U₀ ≅ Spec (.of A)` and its displayed equation on structure maps |
| A a finitely generated k_0-algebra | Existential ring and algebra structures and `Algebra.FiniteType D.k₀ A` |

The field choices are arbitrary fields of the specified cardinality, and arbitrary
algebraic closures, rather than fixed concrete carriers. This is exactly the
node's fixed-field convention: `GaloisField` realizes one such field, while the
node also explicitly permits any isomorphic field with q elements. All field,
algebra, closure and finite-set structures are real stored data. The structure's
instance fields are registered globally; none is a local instance. The universe
linter is disabled only on the bundled structure declaration because the two
independent universe parameters occur together in its resulting sort; this does
not equate the field/curve universe u with the coefficient universe v. The local
residue closure has a further independent universe w. Every universe and variable
is explicitly bound, and `autoImplicit` is false.

Dependency declarations read and used:

- `def-weil-finite-field-q-elements`: Mathlib `GaloisField` was read; the setup uses
  the node's field/Fintype/cardinality formulation, admitting every fixed field
  with q elements. Its existence/uniqueness description does not introduce an
  additional arbitrary structure on that field.
- `def-weil-algebraic-closure`: `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
  `AlgebraicClosure`, and `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosure`.
  Both field choices use the latter predicate exactly.
- `def-weil-l-adic-numbers`: `Mathlib.NumberTheory.Padics.PadicNumbers`, `Padic`.
- `def-pc-scheme` and `def-weil-affine-spectrum`:
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-weil-scheme-over-base`: `Mathlib.AlgebraicGeometry.Over`, `Scheme.Over` and
  its canonical structure morphism.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, through
  its `IsSeparated` predicate. Properness and universal closedness are not imposed.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`, whose complete componentwise
  Krull-dimension definition was read.
- `def-pc-base-change`: the current server source of
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` was read using
  `scompile.py --source`. Its node note explicitly records `Limits.pullback` for
  scheme base change and distinguishes it from `Scheme.Modules.moduleBaseChange`.
  The setup uses this recorded scheme construction.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`.
- `def-weil-closed-points`: `Mathlib.Topology.JacobsonSpace`, `closedPoints`.
- `def-weil-residue-field` and `def-weil-closed-point-degree`:
  `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`,
  `Scheme.Hom.residueDegree`. The latter computes finrank over the residue field
  of the unique point of Spec k_0, canonically identified with k_0 as its node says.
- `def-weil-frobenius-substitution`: `Mathlib.FieldTheory.Finite.Basic`,
  `FiniteField.frobeniusAlgEquivOfAlgebraic`; the already existing inverse wrapper
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` in
  `WeilConjectures.Mathlib.FieldTheory.Finite.Basic` is reused for both F and F_x.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.

For the local Frobenius specialization I also read and use the existing
`WeilConjectures.PointCount` declaration
`AlgebraicGeometry.Scheme.Hom.finite_residueField_of_isClosed` (its full signature
and proof were read). The `letI`s in this definition install concrete structures
and already established finiteness; none is a postponed proof or a let binder in
a theorem statement. Its domain requires only local finite type, already one of
the curve conjuncts, so it applies to every curve in the chapter.

Edge cases checked before writing and again after compilation:

- a=0 is excluded; a=1 and p=2 are allowed. The proof of p primality and ell
  primality is present, so the previously diagnosed composite-p ambiguity cannot
  recur. ell=p is excluded and all other prime choices are allowed.
- An embedding is not assumed to be continuous or surjective. The coefficient
  algebraic closure has no chosen topology in this record.
- The empty scheme fails the separate nonempty conjunct even though pure
  dimension is vacuous for the empty scheme. Spec k_0 fails pure dimension one.
  A smooth disjoint union of a curve and a point fails pure dimension one;
  a disjoint union of two curves fails connectedness after base change.
- A geometrically disconnected curve over k_0 fails the geometric connectedness
  conjunct even if it is connected over k_0. There is no rational-point assumption.
- Affine and proper smooth geometrically connected curves are both admitted.
  No affineness or properness is required of C_0. Empty affine opens fail, whereas
  the full open is admitted whenever the curve itself is affine.
- The affine-open isomorphism is over k_0 by an explicit equation. It is not merely
  an abstract isomorphism of schemes with an unrelated algebra structure.
- Higher-degree closed points are included; no assumption e_x=1 is made.
  Local Frobenius uses cardinality of the residue field, not q itself, and uses
  the inverse automorphism rather than arithmetic Frobenius.

Searches made through `msearch.py` (full audit also in sandbox searches.jsonl):

1. LeanSearch: "Smooth geometrically connected curve over finite field geometric
   Frobenius and algebraic closure of ell adic numbers embedding into complex
   numbers". Eight hits: arithmetic Frobenius, finite-field extension Frobenius,
   number-field embeddings and PadicComplex/PadicAlgCl. No combined setup.
2. LeanFinder: "Finite field algebraic closure geometric Frobenius smooth
   geometrically connected curve ell adic embedding complex chapter setup".
   Eight hits: Weierstrass reduction/good reduction, function fields, formal
   smoothness over perfect fields and isocrystals. No combined setup.
3. Loogle: "FiniteField.frobeniusAlgEquivOfAlgebraic,
   AlgebraicGeometry.Scheme.IsPureDimension" gave unknown identifier for the
   project-only pure-dimension predicate. Repeated with just
   "FiniteField.frobeniusAlgEquivOfAlgebraic": seven hits, all arithmetic Frobenius
   and its properties; their full signature was read. Only the Frobenius component
   matches, and it is reused through the existing geometric inverse.
4. msearch grep: "RealSheaves|RealCurve|IsPureDimension|geometricFrobenius" in
   Mathlib/AlgebraicGeometry: no hits. Direct Mathlib reads located all individual
   predicates used above.
5. Direct `rg` in WeilConjectures and lean/Sheaf for
   `RealCurve|IsPureDimension|geometricFrobenius|RealSheavesSetup` located the
   existing pure-dimension and geometric-Frobenius constructions, which are
   reused. `grep -rn d-real-setup WeilConjectures` found only a documentation
   mention of sk-d-real-setup in RealSheaves/Purity, not a setup declaration.
   The upstream `IsCurve` allows dimension at most one and omits smoothness,
   nonemptiness and geometric connectedness; `IsConnectedCurve` still omits
   smoothness and geometric connectedness. Neither is this chapter predicate.
   `WeilGroup` packages different representation and fundamental-group data.

No exact combined declaration was found. No private copies of the component
notions are introduced. `RealSheaves.Setup` and its explicitly listed clause
specializations are the declarations of this one definition node.

Validation: `scompile.py Q158 d-real-setup` compiled the module both as its sandbox
check and at its actual module path, with no errors or warnings. The initial
instance-registration problem was repaired; the final compile is clean.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
