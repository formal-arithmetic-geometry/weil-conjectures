## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AlterationRelativeCurvePreparation.lean`
states `AlgebraicGeometry.alteration_relative_curve_preparation` with proof `sorry`.
It imports the recorded dependency modules/declarations and uses no private replacement
notion. The declaration has the exact source citation and the blueprint id in its
module and declaration docstrings.

The hypotheses and their Lean rendering are as follows.

- The base ring is `A : Type u` with `[CommRing A]`. The disjunction `hbase` says
  either `A` is a field (`IsField A`, for the given ring structure), or it carries a domain structure and a discrete
  valuation ring structure, with `IsExcellent A` in the latter branch. `S` is identified
  with `Spec (.of A)` by `eS`; `s : S` and `hs : IsGenericPoint s Set.univ` give its
  generic point.
- `X : Scheme.{u}`, `p : X ⟶ S`, `[IsIntegral X]`, `hp : IsProper p`,
  `hdom : DenseRange p.base`, and `hft : LocallyOfFiniteType p ∧ QuasiCompact p`
  render the proper dominant finite-type map and integral source.
- `d : ℕ`, `hd : topologicalKrullDim (p.fiber s) = (d : WithBot ℕ∞)`, and
  `hdpos : 1 ≤ d` render `d = dim X_s ≥ 1`.
- `Z : Scheme.{u}`, `i : Z ⟶ X`, `[IsClosedImmersion i]`, and
  `hZ : ∀ ξ, IsGenericPoint ξ Set.univ → ξ ∉ Set.range i.base` render a closed
  subscheme whose underlying closed set contains no generic point of `X`.

The conclusion quantifies `X₁`, `Y`, `h : X₁ ⟶ X`, `q : Y ⟶ S`, and
`f : X₁ ⟶ Y`. The conjunction renders each clause in order:

- `IsIntegral X₁` and the affine-open predicate
  `∀ U, IsAffineOpen U → IsExcellent Γ(X₁,U)` say that `X₁` is excellent integral;
  the analogous two conjuncts say the same for `Y`.
- `IsProper h`, `DenseRange h.base`, and
  `∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (h ∣_ U)` say that `h` is proper,
  dominant, and finite over a dense open (generically finite), with unrestricted degree.
- `IsHProjective q`, `IsProper q`, `DenseRange q.base`, and
  `LocallyOfFiniteType q ∧ QuasiCompact q` render projective, proper, dominant,
  finite type for `Y → S`; the next equality gives `dim Y_s = d - 1`.
- `IsProper f` and `DenseRange f.base` render the proper dominant map `f`.
- `h ≫ p = f ≫ q` says the structure map of `X₁` factors through `Y` over `S`.
- For every generic point `y` of `Y`, the fibre map
  `f.fiberToSpecResidueField y` is `SmoothOfRelativeDimension 1`, and
  `IsIntegral (f.fiber y)` makes that smooth one-dimensional fibre an irreducible
  curve. The pullback `Limits.pullback h i` is the scheme-theoretic inverse image of
  `Z`; `nilradical.subschemeι` is its reduction map, and its composite to `Y` is
  required to have finite and `Etale` generic fibre. Both predicates permit the fibre
  to be empty.

Recorded dependency declarations used:

- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` in Mathlib's finite-type/quasi-compact modules.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-exc-excellent-ring`: `IsExcellent` in `Sheaf.RingTheory.ExcellentRing`.
- `def-sc-discrete-valuation-ring`: Mathlib's `IsDiscreteValuationRing` class.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.SmoothOfRelativeDimension` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-pbc-scheme-reduction`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`, and `subschemeι` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber`, `fiberToSpecResidueField` in
  `Mathlib.AlgebraicGeometry.Fiber`.
- `def-kun-dimension`: `topologicalKrullDim` in
  `WeilConjectures.Mathlib.Topology.KrullDimension`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in Mathlib.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in Mathlib.
- `def-kun-projective`: upstream `AlgebraicGeometry.IsHProjective` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `def-sc-generic-point`: Mathlib's `IsGenericPoint` in `Mathlib.Topology.Sober`.

Searches for an existing declaration were made before writing the module:

- `msearch.py ... leanfinder "proper alteration relative curve smooth generic fibre finite etale boundary"`:
  returned smoothness and standard-smooth declarations, with no alteration theorem;
  verdict no exact match.
- `msearch.py ... loogle "Scheme.Hom.fiber, SmoothOfRelativeDimension, IsHProjective, IsFinite"`:
  returned zero hits (`Scheme.Hom.fiber` was not a Loogle identifier); verdict no match.
- `msearch.py ... grep "alteration|relative curve|generic smooth boundary" AlgebraicGeometry`:
  returned zero hits.
- `rg` over `WeilConjectures/`, `lean/Sheaf/`, and `dag/nodes/` found no declaration
  or duplicate node for this item; only the two lower-level proof nodes and parent
  references were present.

Edge cases checked: `d = 1` gives the required dimension `d - 1 = 0`; an empty `Z`
has an empty pullback fibre and satisfies the finite-étale conjunction; the field and
DVR branches of `hbase` are separate; no separability or degree-invertibility condition
was added, so inseparable alterations and unrestricted degree remain allowed.
There is no `STATEMENT-DISPUTED` flag and no node fault.

## Second reading by Q68

I reread the node, the source place, and the complete theorem signature after the clean
single-file compile. The base alternatives, generic-point hypotheses, integral and
excellence clauses, proper/dominant/finite-type predicates, projectivity, relative
fibre dimension, factorization equation, generic smooth integral curve, and reduced
inverse-boundary finite-étale fibre all have direct counterparts in the node. The
pullback/reduction composite is the canonical scheme-theoretic inverse image followed by
reduction, and the finite and étale predicates are imposed only on the generic fibre,
so the possibly-empty case is retained. No mismatch was found and no further change was
needed.

## Maintainer review fix (cc second reader, 2026-10-18)

The field branch of `hbase` was `Nonempty (Field A)`. That asserts only that the carrier
type admits *some* field structure, unrelated to the given `[CommRing A]`: for example
`Nonempty (Field ℤ)` holds (transport of `ℚ`'s field structure along a bijection `ℤ ≃ ℚ`;
checked by compiling `⟨((Denumerable.eqv ℤ).trans (Denumerable.eqv ℚ).symm).field⟩`),
while `¬ IsField ℤ`. The delivered hypothesis thus admitted `S = Spec ℤ` or `Spec` of any
ring whose carrier has the cardinality of a field, which the node excludes. The branch is
now `IsField A`, the field condition on the given ring structure (`S = Spec` of a field).
No other change: the DVR branch, every other hypothesis and every conclusion clause were
checked against the node and left as delivered.

