## Worker report

The module `Sheaf.AlgebraicGeometry.TranslatedCartierParameterFamily` states
`AlgebraicGeometry.exists_translated_cartier_parameter_family`, with `sorry` as its only
postponed proof. It introduces no new definitions. The accepted natural-language statement
and split are unchanged; only the node's `lean` field is set.

The former stage-1 BLOCKED ending does not apply: brief-stage2 §0 explicitly authorizes this
stage-2 handoff, the current queue lists the item at stage 2, and the live node had no Lean
record. There is no released repair note for this item.

The source read is Stacks Project `groupoids.tex`, Tag 0BF7,
`lemma-algebraic-quasi-projective`, lines 1402–1467: the smooth irreducible construction,
the finite-etale chart, its norm footnote, affine complements on fibres, point avoidance,
and the construction of `M = O(E)` immediately before rational equivalence for Picard.
This statement deliberately ends at that point of the source, as the node does.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The k-group scheme is `(H : Over (Spec (.of k))) [GrpObj H]`. Thus the actual
  multiplication, identity, inverse and their laws are present, with no commutativity
  restriction. `H.left` is the underlying scheme and `H.hom` its structure map.
- Smoothness is `[Smooth H.hom]`, integrality `[IsIntegral H.left]`, and finite type
  `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`.
- Separatedness in precisely the node's formulation is
  `[IsClosedImmersion (pullback.diagonal H.hom)]`.
- The integer `d ≥ 0` is `d : ℕ`, including zero. The affine space in this node is literally
  `Spec (.of (MvPolynomial (Fin d) k))`, with its structure map induced by `algebraMap`.
- The parameter scheme is `V : Over (Spec (.of k))`. Its map `j` into that polynomial
  spectrum is an open immersion, and the following equality makes it a k-map.
  `IsAffine V.left` and `Nonempty V.left` impose exactly affine and nonempty.
- The single module is `M : (pullback H.hom V.hom).Modules`, with `M.IsInvertible`.
  This is a module on the actual product over k.
- A rational parameter is `v : Over.mk (𝟙 (Spec (.of k))) ⟶ V`. Its fibre inclusion
  is the canonical `pullback.lift (𝟙 H.left) (H.hom ≫ v.left)`; the compatibility proof
  uses only identity, associativity and the over-category triangle. The first projection
  is the identity and the second is the constant map through v, hence this is `(h,v)`.
- `s` is one dependent family of global sections of `(tensorPullback i_v).obj M`.
  This is the dependency's actual tensor inverse image, not Mathlib's other pullback.
- `U` is a family of opens of `H.left`; for every rational v, `IsAffineOpen (U v)` and
  `(U v : Set H.left) = Scheme.Modules.nonvanishingLocus (...) (s v)` state precisely
  that the section's nonvanishing locus is affine. The equality supplies openness
  without choosing another nonvanishing predicate. The recorded predicate is the germ
  outside maximal-ideal times stalk, equivalently nonzero residue-field value.
- For every rational h (an over-category map from `Spec k` to H), the last existential
  requires some rational v with `h.left (IsLocalRing.closedPoint k) ∈ U v`. Spec k has
  one point, so this is exactly the requested rational-point coverage.
- There is no assertion identifying any two fibre modules or their isomorphism classes.
  There is no assertion that the sections arise from one global section (the proof
  constructs one, but the statement only asks for the displayed family).

Dependency declarations used, after reading their source signatures and docstrings:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`
  (the node's match explicitly names this component).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to schemes over Spec k as documented
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (the former imports the latter).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.lift`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `def-pc-module-pullback`: `AlgebraicGeometry.Scheme.Modules.tensorPullback`, public
  through its recorded `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  defined explicitly in `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `def-weil-pbc-ample-invertible-module`: the recorded component
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`,
  `WeilConjectures.AlgebraicGeometry.Ample`.

Public imports provide statement notions, including the separated diagonal. Plain imports
supply all currently stated proof dependencies: finite locally free degree, canonical
section, invertible pullback, norm sections, finite coproduct base change, Jacobson finite
type, affine diagonal intersections, closed immersion implies finite, and closed-point
residue fields. Five proof dependencies have no recorded declaration or Mathlib match:
`lem-sfb-smooth-affine-cartier-boundary`, `lem-sfb-smooth-integral-finite-etale-chart`,
`lem-sfb-finite-image-nowhere-dense`, `lem-sfb-finite-locally-free-function-norm`, and
`lem-sfb-finite-locally-free-fppf-descent`. They are named in the proof docstring, and no
import is invented for them. None is needed to type the present statement. No import cycle
requires omitting a stated dependency.

Edge cases checked before writing: d = 0 is allowed (zero-variable polynomial spectrum);
V = empty is expressly excluded; H = empty is excluded by IsIntegral (also by its group
unit). Finite type and separatedness are both genuine hypotheses. The trivial group
Spec k is allowed, with d = 0, unit module and section 1. Zero sections can have empty
affine nonvanishing opens, but cannot provide the coverage required by the last clause.
There is no positive-characteristic restriction. One common universe u suffices for k,
H, polynomial spectra and V; every scheme over the field is represented after enlarging
this common universe, and there is no quantification over a smaller test-algebra universe.
The parameter-dependent section type retains the precise tensor pullback for each v.

Searches made (msearch.py, Q85, this item; raw output preserved by that tool):

- leanfinder: “A smooth integral separated algebraic group over an algebraically closed
  field has an affine-space parameter family of line bundles with affine section loci
  covering rational points”. Eight hits: AffineSpace and its affineness/surjectivity,
  integral-morphism and affine-transition-limit facts; none gives this family.
- leansearch: “A smooth integral separated group scheme over an algebraically closed field
  has a line bundle on its product with an affine open of affine space whose fibre sections
  have affine nonvanishing opens covering rational points”. Eight hits: affine covers,
  affine opens, integrality and separatedness; no matching theorem.
- loogle: `"IsInvertible", "IsAffineOpen"`: zero hits.
- grep of Mathlib/AlgebraicGeometry:
  `translatedCartier|translated_cartier|parameterFamily|parameter_family|HasAmpleFamily`:
  zero hits.
- rg of upstream WeilConjectures and project Sheaf for
  `translated.cartier|TranslatedCartier|parameterFamily|parameter.family|FiniteEtaleChart`:
  only unrelated representation-theory parameter families; no matching scheme theorem.
- grep of upstream WeilConjectures for this blueprint id: no hits.
- Upstream names index contains Cartier-related declarations but no translated-Cartier
  parameter-family declaration. The final full theorem name is new.

Validation: scompile.py compiled both the sandbox probe and the actual library module
successfully, without errors or warnings. The only declaration proof is `sorry` as
required for stage 2. The first compile's over-category identity simplification was
repaired by adding `Over.mk_hom`; the resulting statement is unchanged mathematically.
No node fault, statement correction or disputed assertion was found.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
