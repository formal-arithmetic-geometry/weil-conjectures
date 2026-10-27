## Worker report

`Sheaf.RepresentationTheory.InvariantPowerBaseChangeDescent` states
`AlgebraicGeometry.InvariantPower.invariantPower_baseChange_descent`, with the
stage-2 proof `sorry`. It imports the landed definition owner
`Sheaf.AlgebraicGeometry.GroupScheme.InvariantSymmetricPowerLifting` and uses
`AlgebraicGeometry.InvariantSymmetricPower.HasInvariantPowerLifting` directly.
The only local helpers expose the supplied group-object instance, the actual
scheme pullback group, its inherited affineness, and its canonical coordinate
Hopf instance. No coaction, symmetric
coaction, or lifting predicate is defined again. No statement is corrected or
disputed; no new node or dependency replacement is delivered.

Source read: Alper, *Adequate moduli spaces and geometrically reductive group
schemes*, https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf,
Lemma 9.2.5(2),(5), printed pp.522–523, and Proposition 9.3.1(i),(ii), printed
p.524. The arbitrary-module condition is used, without the later Noetherian or
finite-module variants. The node's eight-step proof is retained in the theorem
docstring, including maximal-local and finite-etale-family descent.

Hypotheses and clauses:

- `A : CommRingCat.{u}` is an arbitrary commutative ring; `f : A ⟶ B` is its
  actual unital ring homomorphism.
- `H : Grp (Over (Spec A))` is the group scheme over the indicated affine base.
  `coordinateGroup A H := H.grp` exposes precisely those group diagrams on
  `H.X.left.asOver (Spec A)`. It supplies no new group law.
- Affine, flat, and finitely presented are `[IsAffine H.X.left]`,
  `[Flat H.X.hom]`, and `[LocallyOfFinitePresentation H.X.hom]`. Over the affine
  base, affineness of the total scheme is equivalent to an affine structure map.
  An affine morphism is quasi-compact and separated, hence quasi-separated;
  local finite presentation is therefore finite presentation here.
- The coordinate algebra is exactly `Γ(H.X.left, ⊤)`. Mathlib's
  `AlgebraicGeometry.Group.Affine` gives its canonical `Algebra A` and
  `HopfAlgebra A` structures from the supplied group scheme.
- Throughout, P(A,H) is the existing
  `InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} A Γ(H.X.left, ⊤)`.
  Its independently arbitrary universe v allows all module sizes through
  `N : Type (max u v)`. Neither finiteness nor flatness of N is assumed.
- In that imported definition, the rational module is the linear map
  `ρ : N →ₗ[A] N ⊗[A] C` with `IsCoaction A C N ρ`. The two clauses of
  `IsCoaction` are exactly counitality, using the right unitor, and
  coassociativity, using the tensor associator.
- The quotient is `lam : N →ₗ[A] A` with `Function.Surjective lam`.
  Equivariance to the trivial module is
  `∀ m, lam.rTensor C (ρ m) = lam m ⊗ₜ[A] (1 : C)`.
- The imported `symmetricCoaction A C N ρ` is the actual algebra map
  `SymmetricAlgebra.lift ((SymmetricAlgebra.ι A N).rTensor C ∘ₗ ρ)`.
  The existential `∃ (n : ℕ) (_ : 0 < n) (q : SymmetricAlgebra A N), ...`
  requires positive degree, equivalently n ≥ 1. Homogeneity is membership in
  `((TensorAlgebra.ι A).range ^ n).map (SymmetricAlgebra.algHom A N).toLinearMap`,
  the recorded degree-n tensor-image component. Invariance is
  `symmetricCoaction A C N ρ q = q ⊗ₜ[A] 1`. Evaluation is
  `SymmetricAlgebra.lift lam q = 1`; restricted to degree n it is Sym^n(lam)
  under Sym^n(A) = A, since both send products of n generators to their
  products of lam-images.
- `baseChange f H := (Over.pullback (Spec.map f)).mapGrp.obj H` is the actual
  fibre product group, including its multiplication, unit and inverse.
  `affineBaseChange` exposes the existing affine pullback instance.
  `baseChangeCoordinateHopf` exposes Mathlib's canonical Hopf instance with the
  bundled target ring retained for instance inference at concrete localizations.
- Clause (1) is the first conjunct, for every B and every f, from P(A,H) to
  P(B,H_B). The map f is unrestricted, including nonflat and noninjective maps.
- Clause (2) is the second conjunct. It assumes `f.hom.FaithfullyFlat` and
  reverses that implication, using the recorded ring-map notion.
- Clause (3) is the third conjunct, quantified over `m : MaximalSpectrum A`.
  It uses `Localization.AtPrime m.asIdeal` with the actual map
  `CommRingCat.ofHom (algebraMap A (Localization.AtPrime m.asIdeal))` and
  the coordinate algebra of its actual pullback group.
- Clause (4) is the fourth conjunct. `I : Type u` with `[Finite I]` allows
  every finite indexing set, including empty. The maps are `f i : A ⟶ B i`;
  `∀ i, Etale (Spec.map (f i))` gives etaleness, while
  `∀ x : Spec A, ∃ i y, (Spec.map (f i)).base y = x` is joint surjectivity
  on underlying points. P is assumed for each B_i and its actual pullback
  group, and concluded for A,H.
- There is no Noetherian, nonzero-ring, characteristic, or module finiteness
  hypothesis. Rings and schemes share the arbitrary universe u of the scheme
  category; v is independent. Every finite index set has a representative in u.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GroupScheme.InvariantSymmetricPowerLifting`:
  `AlgebraicGeometry.InvariantSymmetricPower.IsCoaction`, `symmetricCoaction`,
  and `HasInvariantPowerLifting`. The current node
  `def-sfb-invariant-symmetric-power-lifting` records exactly these declarations
  and is added to this item's `stmt_deps`. Its node and module are not modified.
- `Mathlib.AlgebraicGeometry.Group.Affine`: the canonical algebra and Hopf
  structures on global sections of an affine group over Spec A. The hypotheses
  are `[G.Over (Spec A)]`, `[GrpObj (G.asOver (Spec A))]`, `[IsAffine G]`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Functor.mapGrp`.
  These general group-object diagrams apply over Spec A as stipulated by this
  item's statement, including general rings rather than just fields.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`,
  `isAffine_of_isAffineHom`, `isAffineHom_of_isAffine`, and affine pullbacks;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `.Flat`: `Flat`; `.Etale`: `Etale`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Map`: `TensorProduct`,
  `LinearMap.rTensor`, `LinearMap.lTensor`;
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`: `SymmetricAlgebra`, `ι`, `lift`.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, whose component the shared
  lifting predicate uses.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`;
  `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.

Proof-only imports retain the recorded symmetric-algebra base-change theorem,
affine-chart comparison, module localization exactness and localization tensor
comparison, and proper-ideal maximal containment. They introduce no alternative
version of the predicate or coordinate Hopf algebra.

Edge cases checked:

- For A = 0, every A-module and symmetric algebra is zero; n = 1, q = 0 is
  invariant and evaluates to 1 = 0. No `Nontrivial A` is required.
- Clause (3) has a vacuous premise if there are no maximal ideals; this is the
  zero-ring case just checked.
- An empty family in clause (4) is jointly surjective only on the empty
  spectrum, hence only for the zero ring, again allowed.
- Degree zero is excluded by `0 < n`; the trivial rank-one module lifts in
  degree one. Arbitrary nonfinite and nonflat modules remain quantified over.
- Invariance is a tensor-coaction equation, not merely invariance on A-points.
  Base-change maps can be nonflat; only descent clause (2) assumes faithful
  flatness.

Searches actually made in the original work and repairs:

- msearch.py leanfinder, "Base change and faithfully flat local descent for
  invariant symmetric power lifting of rational modules of an affine flat
  group scheme": 8 hits, faithful-flat module/ring-map and scheme descent;
  no theorem stating these four clauses.
- msearch.py loogle, "SymmetricAlgebra.lift, GrpObj": 0 hits; the service did
  not recognize GrpObj, whose local source was nevertheless read.
- msearch.py grep, "geometricallyReductive|Comodule|invariantPower": 0 hits.
- msearch.py leansearch, "Rational comodule invariant symmetric power lifting
  geometric reductivity base change": 8 hits, symmetric-power and base-change
  maps; none states the item.
- Local rg of WeilConjectures and Sheaf for coactions, HopfAlgebra, geometric
  reductivity, invariant powers and the proposed names, plus the item id in
  WeilConjectures, initially found no item theorem. Field-only HopfAction and
  RationalRepresentation do not define the general-ring predicate.
- Current-main repair search `rg -n 'coordinateGroup|HasInvariantPower|InvariantPowerBaseChangeDescent'
  lean/Sheaf lean/WeilConjectures` finds the landed Q31 definition and its
  `ReductiveSymmetricPowerDvrReduction` consumer. Both complete signatures and
  docstrings were read. That consumer already applies
  `HasInvariantPowerLifting.{u, v, u}` to the canonical coordinate algebra;
  this theorem now uses precisely the same interface.

## Return repair

The first return against `6643b486659f` forbids duplicating the lifting predicate
and symmetric coaction. The second return against `4a69d74b2fc4` rejects the
reviewer's `--apply-fixes` path for the replacement definition-node JSON.
Current main now has the reviewed Q31 definition node and module. Relative to
both returned deliveries, this repair directly imports that landed module and
uses its `HasInvariantPowerLifting` in every theorem clause. The previous
sandbox replacement module
`Sheaf.RepresentationTheory.InvariantSymmetricPowerLifting` and its replacement
`def-sfb-invariant-symmetric-power-lifting.json` have been removed from the
packet. Thus there is no dependency-node fix requiring the rejected path, and
no competing definition owner. No declarations were renamed to hide a duplicate.

The real `coordinateGroup` helper has moved into the theorem module and is
listed in the item's Lean declaration list. It only exposes `H.grp` for the
canonical Mathlib coordinate-Hopf construction. A second real definition wrapper,
`baseChangeCoordinateHopf`, exposes that same construction for the pullback group
with the bundled target ring explicit. In clause (3), local `let B` and `let f`
name exactly the localization and its map, and `letI` supplies the canonical
`baseChangeCoordinateHopf f H` explicitly; these are definitions, not hypotheses.
The local `RationalCoaction`,
`symmetricCoaction`, and `HasInvariantPower` copies have all been removed.

The item node is refreshed from current main: only `lean` and the additional
statement dependency on the existing definition owner change. Its statement,
proof, proof dependencies, and all review metadata are preserved. The four
mathematical assertions and the eight-step proof docstring are unchanged.

Validation: the prescribed `scompile.py` compiled the final file in sandbox and
library modes successfully, with no errors and no warnings. The localization
instance is supplied explicitly, and the class-valued wrapper is marked
`@[instance_reducible]`. All variables and universes are explicit under
`set_option autoImplicit false`. Only the stage-2 theorem proof is postponed.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
