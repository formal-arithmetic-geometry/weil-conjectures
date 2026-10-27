## Worker report

One new statement module, `Sheaf.AlgebraicGeometry.DedekindSmoothFibreDenseAffine`, with
`AlgebraicGeometry.exists_isAffineOpen_geometric_fibre_dense_cartier_compl`. The entire proof
is `sorry`. There are no new definitions, auxiliary theorems, dependency repairs, or node
statement changes. The node copy changes only `lean`.

The statement was checked against BLR, Néron Models, 6.4 Lemma 4 and the construction in the
proof of Theorem 1, printed pp.155–156 (PDF pages 161–162, zero-based), using the primary scan
at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The source constructs the required open before invoking the torsor amplification argument.
The node's twelve-step proof is included in the theorem docstring. I also read the current
blueprint's `sec-six-functors-basics/sk-prop-open-coefficients/_section.md`; this item is a
refinement input, not the unit's own statement.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| D is a commutative domain | `(D : Type u) [CommRing D] [IsDomain D]` |
| D is Noetherian and integrally closed | `[IsNoetherianRing D] [IsIntegrallyClosed D]` |
| Krull dimension exactly one | `(hdim : ringKrullDim D = 1)` |
| S = Spec D, X a scheme, p : X → S | `{X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of D))` |
| p is smooth | `[Smooth p]` |
| p is separated, i.e. its diagonal is a closed immersion | `[IsSeparated p]`; its defining field is `isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal p)` |
| p is of finite type | `[LocallyOfFiniteType p] [QuasiCompact p]`, the dependency's stated convention |
| An affine open subscheme A of X | `∃ (A : X.Opens) ... , IsAffineOpen A ∧ ...`; its inclusion is the existing open immersion `A.ι` |
| An effective Cartier closed subscheme E | The existential `E : X.IdealSheafData` represents the subscheme `E.subscheme` with closed immersion `E.subschemeι`; `E.IsInvertible` is exactly local generation by a non-zero-divisor |
| Its support is exactly the complement of A | `(E.support : Set X) = (A : Set X)ᶜ` |
| Every geometric point of S | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of D)), ...` |
| The base-changed open is dense in the geometric fibre | `closure ((pullback.fst p s) ⁻¹' (A : Set X)) = Set.univ`; the ambient space is the scheme `pullback p s` |
| No group action, section, connectedness, properness, or Néron property | No such binder is present |
| Empty total scheme, empty fibres, empty divisor are allowed | No nonemptiness binder on X, A, E, or any fibre; E can be the unit ideal |

The ideal presentation is an equivalent encoding of a closed subscheme, not an omitted
existential: Mathlib's `E.subschemeι` is a closed immersion, its kernel ideal is E, and its
image is `E.support` (`ker_subschemeι`, `range_subschemeι`). I read these constructions and the
full definition `IsInvertible` and its affine predicate `Ideal.IsRegularPrincipal`, which is
`∃ s ∈ nonZeroDivisors R, J = Ideal.span {s}`. Thus invertibility here is the effective Cartier
condition itself, not a weaker abstract module-invertibility predicate. Conversely the
closed-immersion kernel is the ideal encoding of an effective Cartier divisor.

Dependency declarations read and reused:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, the same module.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, used by separatedness and the
  ideal-associated subscheme. `IsSeparated` is read from
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, as realized by `A.ι`.
- `def-nagata-effective-cartier-ideal`: `Scheme.IdealSheafData.IsInvertible`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
- `def-pc-divisor-line-bundle`: `WeilConjectures.AlgebraicGeometry.EffectiveCartier`, whose
  module documentation and `IdealSheafData.IsInvertible.isInvertible_dual_toModules` identify
  the divisor with the invertible ideal E. No associated-line-bundle conclusion is added.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose
  convention is `pullback p s`, with `pullback.fst p s` its projection to X. Pullback of the
  open immersion is the preimage open in this fibre. This uses the dependency's scheme
  base-change convention, not its unrelated module-base-change functor.

All nine recorded statement dependency modules are publicly imported. Available theorem
proof-dependency modules are plain imports. The two proof dependencies
`lem-trf-codimension-one-points-affine-neighbourhood` and
`lem-sfb-smooth-fibrewise-dense-open-base-change` have no usable Lean/module record in the
read repository and supply no object used in the signature, so no import is fabricated for
them. Their precise roles remain in the proof docstring for stage 3. Mathlib proof leaves
are covered by their topic imports or the statement dependency imports.

Edge cases checked before drafting: for X empty, A is the empty open and E the unit ideal;
its Cartier condition is vacuous and every fibre is empty. For X affine, A = X and the unit
ideal gives the permitted empty divisor. For an empty geometric fibre the closure equation
is equality of empty sets in an empty ambient space. No relative dimension is imposed,
so disconnected schemes and mixed relative dimensions remain included. Positive and zero
characteristic are both allowed. A field base is correctly excluded by `ringKrullDim D = 1`;
the node requires exactly dimension one. Geometric points range over arbitrary
algebraically closed fields in the same scheme universe, rather than just rational points
or the generic fibre; the universe variable u is explicit throughout.

Searches (2026-10-24, msearch.py Q83 and this item; raw wrapper results in searches.jsonl):

- LeanFinder: “A smooth separated finite type scheme over a Dedekind domain has an affine
  open dense in every geometric fibre with effective Cartier boundary”: 8 hits, including
  `IsSeparated.hasAffineProperty` and standard smooth charts; none is this existence theorem.
- LeanSearch: “A smooth separated scheme of finite type over a Dedekind domain admits an
  affine open dense in all geometric fibres with effective Cartier complement”: 8 hits,
  including `IsSeparated.of_isAffineHom`, `Scheme.affineBasicOpen`; no exact result.
- Loogle: `AlgebraicGeometry.IsAffineOpen, Dense`: 0 hits.
- Mathlib grep through msearch: `([Dd]edekind.*[Aa]ffine|[Aa]ffine.*[Dd]edekind|[Ff]ibrewise.*[Dd]ense|[Ff]iberwise.*[Dd]ense)`
  in AlgebraicGeometry: 0 hits.
- Project/source rg: `dedekind.*[Dd]ense|[Dd]ense.*[Aa]ffine|fibreDense|fiberDense|dedekind_smooth|lem-sfb-dedekind-smooth-fibre-dense-affine`
  in `lean/WeilConjectures` and `lean/Sheaf`: only general dense affine opens or affine
  curve results, not this theorem. `Scheme.exists_isAffineOpen_dense` in DenseAffineOpen
  does not assert density in every fibre or a Cartier boundary.
- Exact node-id grep in `lean/WeilConjectures`: no hits. Final proposed declaration-name rg
  in both project roots and `dag/lean_names_upstream.json`: no hits.

Validation: `scompile.py Q83 lem-sfb-dedekind-smooth-fibre-dense-affine <module>` succeeded in
both sandbox and library-module modes (1.6 s and 1.5 s), with no errors or unexpected warnings.
No statement fault or disputed claim was found. Every variable and universe is bound.

## Second reading by Q83

I reopened the node and the completed file for a separate second pass. This is the same
Q83 dispatcher worker, not an independent agent: the assignment explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review.

I rechecked all rows above against the actual theorem: hdim says equality with one, not an
at-most-one bound; the base is the affine spectrum of that same D; the morphism assumptions
are smooth, separated, locally finite type and quasi-compact; both A and its ideal E are
existential; affine is asserted of the open subscheme; E.IsInvertible is locally regular
principal; support equality has the intended complement direction. For density the
projection is `pullback.fst p s`, not `pullback.snd`, so its inverse image is A over the
geometric point inside X over that point. The closure is the whole geometric fibre, and
Ω, its field and algebraic-closedness instances, and the point s are all quantified after
the existential, so one single pair A,E works for every geometric point. No fibre or X
nonemptiness was accidentally assumed. The module and theorem docstrings carry the source,
node id, and all twelve proof steps. No mathematical mismatch or needed change was found.
