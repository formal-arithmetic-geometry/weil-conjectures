## Worker report

Item: `lem-per-char-zero-smooth-coefficient-system`, group Q118, stage 2.
Module: `Sheaf.FieldTheory.CharZeroSmoothCoefficientSystem`.
Main declaration: `FieldTheory.exists_charZero_smooth_coefficient_system`.

The module states the node verbatim in mathematical content, with one postponed
proof (`sorry`). It also supplies concrete canonical helpers
`FieldTheory.coefficientSubalgebraDiagram` and
`FieldTheory.coefficientSubalgebraCocone`, recorded in `lean.declarations`.
They introduce the specific diagram and cocone needed by this same node, not an
independent notion. Their maps are actual inclusions, not arbitrary maps or
objects chosen from an existence theorem. Their structural identity, composition
and naturality fields are checked by reflexivity after extensionality.

Sources read: the current DAG node with all nine proof steps and all five
statement dependencies; the source signatures/docstrings listed below;
[Bierstone--Milman--Temkin, Q-universal Desingularization](https://math.huji.ac.il/~temkin/papers/Q-universal_Desingularization.pdf),
Definition 7.2, Remark 7.3(1), Theorem 7.5 and its proof (printed pp.18--21),
read online on 2026-10-24; the latest blueprint ancestor
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md`
and its proof. The existing node records the archival paper as WANTED; this
worker did not alter the read-only literature. The module docstring retains the
complete nine-step DAG proof, including every cited dependency id. In particular
the regularity argument is the direct fibre argument of Step 9, not a citation
to the dropped smooth-colimit node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| characteristic zero | `[CharZero k]`; canonical rational algebra from `Mathlib.Algebra.Algebra.Rat` |
| there exists a small partially ordered set D | `∃ (D : Type u) (_ : PartialOrder D)` |
| D is nonempty | `Nonempty D` |
| D is directed | `IsDirected D (· ≤ ·)` |
| subrings of k containing Q | `R : D → Subalgebra ℚ k`; the rational algebra structure includes exactly the canonical prime-field image |
| each R_i is finite type over Q | `∀ i, RingHom.FiniteType (algebraMap ℚ (R i)) ∧ ...` |
| each R_i is smooth over Q | the second term `Algebra.Smooth ℚ (R i)` of that conjunction |
| ordered inclusions R_i ⊆ R_j | `hR : Monotone R` |
| each ordered transition is smooth | `∀ (i j : D) (h : i ≤ j), @Algebra.Smooth (R i) _ (R j) _ (Subalgebra.inclusion (hR h)).toRingHom.toAlgebra` |
| the union is k | `∀ x : k, ∃ i : D, x ∈ R i` |
| the inclusions exhibit k as the ring colimit | `Nonempty (IsColimit (coefficientSubalgebraCocone R hR))` |
| each R_i → k is regular | `∀ i : D, RingHom.IsRegular (R i).val.toRingHom` |
| no assertion about arbitrary smooth subalgebra inclusions | transition smoothness quantifies only over `h : i ≤ j`; the converse of monotonicity is neither assumed nor asserted |

The chosen `D` is in the same universe as `k`. This is sufficiently large:
the explicit proof indexes finite subsets of a transcendence basis and subrings
of `k`, both in that universe. No countability, finite generation of `k`,
algebraicity of `k/Q`, or independent smaller universe is imposed.
`Nonempty (IsColimit ...)` asserts the full universal property for the canonical
cocone in `CommRingCat.{u}`, using the dependency's actual `IsColimit`; it does
not substitute an abstract isomorphic field with unspecified structure maps.
Both helper definitions expose all their data. The theorem has no extra clause.

Dependency declarations used (recorded modules and full signatures/docstrings read):

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`;
  its inherited commutative ring and division ring structures give the node's field.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`; its defining body is `Algebra.FiniteType` for the map's
  induced algebra. Used directly for the canonical rational map.
- `def-weil-pbc-smooth-ring-map`: `Mathlib.RingTheory.Smooth.Basic`,
  `Algebra.Smooth` (formally smooth and finitely presented), exactly the recorded
  interface. In the transition clause the algebra is explicitly induced by the
  canonical inclusion map; no arbitrary algebra structure is used.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.Cocone` and `CategoryTheory.Limits.IsColimit`
  (definitions read in `Cones` and `IsLimit`); these specify a cocone with the
  given vertex and the full existence-and-uniqueness factorization property.
- `def-weil-pbc-g-ring`: `WeilConjectures.RingTheory.GRing`,
  `RingHom.IsRegular`; read its complete body and that of
  `Algebra.IsGeometricallyRegular`: flatness and Noetherian geometrically regular
  fibres, using the actual map's induced algebra.

All stated proof dependency modules are imported without `public`; statement
interfaces are imported publicly. The proof-only sources include the recorded
transcendence-basis, separating finite subextension, finite separable spreading,
etale permanence/fibre, smooth affine and polynomial, algebraic independence,
flatness, purely inseparable extension and regular-field modules. There is no
missing declaration and no repair or new node is needed.

Edge cases checked before and after writing:

- `k = ℚ`: a singleton poset and `R = k` has finite type, identity smoothness,
  coverage, the identity colimit and regularity. D is explicitly nonempty.
- Algebraic fields of characteristic zero, including infinite algebraic fields:
  finite separable subextensions provide smooth transitions; no finite-dimensional
  hypothesis is imposed on k.
- `k = ℚ(t)` and fields of arbitrary transcendence degree: finite basis subsets
  and etale localizations from the node's construction fit the index universe;
  no bounded dimension or finite basis is imposed.
- Equal indices and repeated subrings: the transition is the actual identity
  inclusion and is smooth; the family is not required to be injective.
- Empty finite generator sets are permitted in the proof, including the empty
  product denominator 1. The theorem does not admit an empty D.
- The zero ring is excluded as the ambient field by `Field`; zero fibres at
  nonzero primes remain allowed by the recorded regular-map definition.
- Arbitrary smooth subalgebra inclusions need not be smooth: inside ℚ(t),
  ℚ[t²] ⊆ ℚ[t] ramifies at t=0. The Lean clause never declares this inclusion
  smooth unless its indices are comparable in the selected order. This is why
  the upstream diagram of all smooth subalgebras is insufficient for this node.

Searches actually run (2026-10-24, msearch log `searches.jsonl`):

- LeanFinder through `msearch.py`: "A characteristic zero field is a directed
  union of smooth finite type rational subalgebras with smooth inclusion
  transitions". Eight hits, including `Field.Emb.Cardinal.directed_filtration`,
  smooth algebra descent, and formally smooth algebras over perfect fields;
  none states the full system with smooth transitions and regular projections.
- Loogle through `msearch.py`: `Algebra.Smooth, Subalgebra`. Two hits:
  `Algebra.Smooth.exists_subalgebra_fg` and
  `TensorProduct.toIntegralClosure_bijective_of_smooth`; neither matches.
- LeanSearch through `msearch.py`: "Every characteristic zero field is a filtered
  colimit of finite type smooth rational subalgebras with smooth transition
  inclusions". Eight hits, including ring filtered colimits, smooth algebra
  descent, prime-subfield and characteristic-zero instances; no exact match.
- Mathlib grep through `msearch.py`, FieldTheory:
  `smooth.*(subalgebra|[Tt]ransition)|([Ss]ubalgebra|transition).*smooth`.
  Zero hits in that directory. Supplementary direct rg in the Mathlib category
  and subalgebra modules located the standard canonical inclusion and colimit
  interfaces used here.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`, same smooth/subalgebra
  pattern: found `WeilConjectures.FieldTheory.SeparableSmoothColimit` and related
  separable extension modules. Read `smoothSubalgebraDiagram`,
  `smoothSubalgebraCocone` and the full signature/docstring of
  `separable_extension_is_filtered_colimit_smooth`: this uses all smooth
  subalgebras with all inclusion arrows and asserts affine (not smooth)
  transitions of their spectra. It does not state this node.
- Direct rg of the item id in `lean/WeilConjectures`: no match. Direct rg of all
  three proposed declaration names in Mathlib, `WeilConjectures`, `Sheaf` and
  `dag/lean_names_upstream.json`: no collision.

No statement correction, disputed statement, missing notion or dependency
interface fault was found. The inherited node is changed only in `lean`.

Validation: prescribed `scompile.py` compiled the sandbox and module paths
cleanly (2.3 s and 2.1 s, no warnings or errors). The first probe found the
canonical rational algebra instance was not publicly imported; adding the exact
Mathlib rational algebra module resolved it without adding any hypothesis.
The delivery dry run and push are performed using `deliver2.py`.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
