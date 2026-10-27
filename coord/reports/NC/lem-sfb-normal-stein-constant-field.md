## Worker report

The new module `Sheaf.AlgebraicGeometry.NormalSteinConstantField` states
`AlgebraicGeometry.exists_normal_stein_constant_field`. Its sole theorem has proof `sorry`;
there are no new Lean definitions, auxiliary postponed theorems, axioms, or statement corrections.
A new definition node records the existing canonical function-field algebra (see below).
All variables and the single universe `u` are explicitly bound, and `autoImplicit` is false.

The previous worker's stale-assignment diagnosis confused stages: the NL delivery merged at
03:34 on 2026-10-22 (`coord/ledger.md:24470`) supplied the seven-step stage-1 split. The live
node has `reviewed` but neither `lean` nor `reviewed_lean`. This delivery supplies its missing
stage-2 statement without changing any reviewed mathematical text or proof steps.

Clause-by-clause reading of the node and signature:

- A field k is `(k : Type u) [Field k]`. T and B are `Scheme.{u}` with `[IsIntegral T]`
  and `[IsIntegral B]`. The maps `t` and `b` give their structures over `Spec k`.
- Finite type over k is `[LocallyOfFiniteType t] [QuasiCompact t]` and the corresponding
  pair for b, exactly the recorded definition (Mathlib has no separate bundled finite-type
  class). No properness over k is imposed on t or b.
- The proper dominant map is `(f : T ⟶ B) [IsProper f] [IsDominant f]`.
  `hf : f ≫ b = t` makes it the morphism over k of the node. This is the compatibility
  inherent in a morphism of k-schemes, not an additional restriction on the base field.
- T normal means `hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧
  IsIntegrallyClosed (T.presheaf.stalk x)`, literally the node's local-ring convention.
- The factorization is the existentially quantified `B₀`, `q : B₀ ⟶ B`, `g : T ⟶ B₀`
  and `g ≫ q = f`. The existential class proofs supply `IsIntegral B₀`, `IsDominant q`,
  and `IsDominant g`. The last is implicit in the node's inclusion k(B₀) into E: g is
  surjective because all its geometrically connected fibres are nonempty, hence dominant.
  It serves to type the canonical function-field map, and adds no mathematical restriction.
- q finite and dominant are `IsFinite q` and the quantified `IsDominant q` proof.
- B₀ normal is the displayed all-stalk domain/integral-closedness condition. It is integral
  by its existential class proof, and finite type over k by
  `LocallyOfFiniteType (q ≫ b) ∧ QuasiCompact (q ≫ b)`.
- g proper with geometrically connected fibres is `IsProper g ∧ GeometricallyConnected g`.
  The latter is Mathlib's field-valued geometric-fibre condition, including nonemptiness.
- The prescribed construction is encoded by
  `∀ V : B.Opens, IsAffineOpen V → IsIso (g.app (q ⁻¹ᵁ V))` together with finiteness of q.
  This does not merely posit an arbitrary finite model. Since finite q is affine,
  W = q⁻¹V is affine, canonically W ≅ Spec Γ(W,O). The pullback on sections of g is
  exactly the asserted isomorphism Γ(W,O) → Γ(g⁻¹W,O). The factorization identifies
  g⁻¹W = f⁻¹V. Composing the affine identification with Spec of this section isomorphism
  gives the required chart W ≅ Spec Γ(f⁻¹V,O). By the Spec/global-sections adjunction,
  g restricted to f⁻¹V becomes the canonical evaluation map to this spectrum. These maps
  agree on overlaps since they come from the single g. Thus this states precisely the
  relative spectrum of f_*O_T, with the specified evaluation maps, up to canonical
  isomorphism of schemes; it uses the same interface as the landed
  `exists_stein_smooth_generic_curve` in `Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve`.
- E and F are `T.functionField` and `B.functionField`. Every field inclusion comes from
  `Scheme.Hom.dominantFunctionFieldAlgebra`, which is the actual generic-stalk map of
  f, g, or q, not a freely chosen ring homomorphism or a chosen abstract extension.
- The equality inside E is the equality between `Set.range` of g's canonical algebraMap
  and the underlying set of `algebraicClosure B.functionField T.functionField` with f's
  canonical algebra structure. Membership in this Mathlib intermediate field is precisely
  algebraicity over F (`mem_algebraicClosure_iff`). It therefore identifies the image of
  k(B₀) inside E, rather than just giving an abstract field isomorphism.
- Finiteness over F is `(algebraMap B.functionField B₀.functionField).Finite`, using q's
  canonical generic-stalk algebra structure. For fields, RingHom.Finite means finite
  dimensionality with this scalar action. The induced maps commute because g ≫ q = f.
- Algebraic closedness in E is
  `algebraicClosure B₀.functionField T.functionField = ⊥`, using g's scalar action.
  Bottom is the image of the base field in E. Thus every element algebraic over k(B₀)
  already belongs to that image, without asserting that k(B₀) is an algebraically closed
  field in the absolute sense.

Dependencies read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme` and `def-weil-affine-spectrum`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, and `Spec.map`, in `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, in
  `Mathlib.AlgebraicGeometry.Properties` (nonempty and domain section rings).
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Universally closed supplies quasi-compactness.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `def-weil-finite-integral-morphism`: `IsFinite` and `IsIntegralHom`, in the Mathlib
  morphism modules `.Finite` and `.Integral`; the statement uses `IsFinite q`.
- `def-sc-function-field`: recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField` is publicly imported. Its docstring
  explicitly delegates the arbitrary integral-scheme clause to Mathlib's `Scheme.functionField`,
  the generic stalk; the component-product declaration is not used for these integral schemes.
- `def-pc-geometrically-irreducible`: recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` is imported, as is `.Connected`,
  whose `GeometricallyConnected` is the node's geometrically connected notion.
- `def-weil-relative-algebraic-closure`: `algebraicClosure` from
  `Mathlib.FieldTheory.AlgebraicClosure`, and `mem_algebraicClosure_iff`.
- Added `def-sfb-dominant-function-field-map` to `stmt_deps`, recording the existing
  `AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra` in
  `Sheaf.TraceFormula.LocalDimensionFormula`. Read the complete definition and docstring:
  it constructs the algebra from `f.functionFieldMap h`, where dominance gives that f
  maps the generic point to the generic point. No copy of this helper is made. The
  local-dimension theorem is not cited in `stmt_deps` or used in the statement.

The module also imports the recorded modules of the proof dependencies:
`Mathlib.AlgebraicGeometry.Normalization`, `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.Algebra.Module.LocalizedModule.Exact`,
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`,
`WeilConjectures.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks`,
`WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`,
`WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine`, and
`Sheaf.AlgebraicGeometry.CoherentFiniteType`. The properness/permanence/target-local
proof dependencies are in the publicly imported Proper module, and affine-fraction
identification is in FunctionField. The theorem docstring carries all seven node steps,
including the denominator calculation and the proof of algebraic transitivity.

Edge cases checked before drafting:

- Empty T or B is excluded by the node's integrality convention, as in `IsIntegral`.
  The empty affine open V is included in the chart clause; its section map is the
  isomorphism of zero rings, so no nonemptiness premise has been silently added.
- Identity on a normal integral finite-type scheme: B₀ = T = B, relative algebraic
  closure is the whole field, and the field extension is finite of degree one.
- Finite dominant maps from normal T, including purely inseparable field extensions:
  B₀ = T and g is the identity. The full finite extension E/F is algebraic; no
  separability, perfection, or geometric integrality condition is imposed.
- A nonnormal B is allowed: a finite normalization with normal T is an instance,
  so normality is intentionally imposed only on T and B₀.
- Projective space over a normal integral base illustrates positive relative dimension:
  the constant subfield is F inside the purely transcendental E, not all of E.
- No characteristic restriction, dimension restriction, chosen affine base, regularity,
  algebraic closedness of k, or geometric reducedness of the generic fibre is assumed.
  All objects use the arbitrary common scheme universe u; there is no auxiliary small
  test universe that would make a quantified condition vacuous.

Searches for an existing statement:

- `msearch.py ... leanfinder` query: “Stein factorization of a proper dominant morphism
  from a normal integral scheme has normal finite base with function field the relative
  algebraic closure”. Eight hits: relative normalization construction and its integral,
  dominant and integral-source instances, plus proper global-section finiteness. None
  states this combined normal Stein/relative algebraic-closure theorem.
- `msearch.py ... loogle '"AlgebraicGeometry", "normalization"'`: twelve hits for
  normalization, its maps, chart cover, integral/dominant instances, and descent. No match
  for the complete statement, notably no constant-field equality or connected fibres.
- `msearch.py ... grep '[Ss]tein|normal.*[Pp]ushforward|[Pp]ushforward.*normal'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch` query: “Proper dominant morphism of normal integral schemes
  Stein factorization relative algebraic closure function fields”. Eight hits for
  IsDominant, IsProper, generic-stalk fraction fields, and dominance-to-surjectivity;
  none is this theorem. The wrapper recorded these searches in `searches.jsonl`.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Stein, normal Stein, constant fields,
  function-field maps and dominant-function-field algebras found affine Stein and the
  smooth-generic-curve specialization, plus the reusable canonical field algebra. Read
  `SteinSmoothGenericCurve.lean`, `FunctionField.lean`, the canonical algebra helper,
  `Curve/DivisorPullback.lean`, and the corresponding Mathlib signatures/docstrings.
  No full duplicate exists. The smooth-generic-curve result assumes a smooth generic
  curve and excellence and has a different conclusion; it cannot replace this node.
- The exact-id search in `lean/WeilConjectures` found no declaration for this item.

Source checks use the local Stacks source: `more-morphisms.tex`,
`theorem-stein-factorization-Noetherian` (03H0), properties (1)--(5), and
`properties.tex`, `lemma-normal-integral-sections` (0358). These agree with the node's
canonical normalization/relative spectrum description. The NL report's missing local
publisher PDF is not used as an independent source here. There is no statement dispute.

Validation: the single delivered module compiled cleanly with the prescribed
`scompile.py NC lem-sfb-normal-stein-constant-field` (sandbox and library module checks).
`deliver2.py NC lem-sfb-normal-stein-constant-field --no-push` passed preflight and
compilation, printing `OK (dry run)` for commit `6ef6126a31b` before this validation note
was appended. The delivery wrapper repeats those gates for the final packet.

## Second reading by NC

This is a second pass by the same worker, not an independent-agent review: the dispatcher
explicitly forbids starting other agents and assigns the independent review to the maintainer.
With the node and final signature open, I rechecked each clause above. In particular the
construction is fixed by the actual g section map, the equality is inside E via the actual
map of function fields, the finite field extension uses q rather than an unrelated scalar
structure, and the final bottom is the image of k(B₀), not an absolute algebraic closure.
I also checked that the existential class-proof binders scope over all later field expressions
and that the module compiles with `autoImplicit false`. No mathematical mismatch or statement
change was found. The new definition node is checked separately below; no dependency record is repaired.

## New nodes

`def-sfb-dominant-function-field-map` records the exact existing definition
`AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra` with `existing: true` and
module `Sheaf.TraceFormula.LocalDimensionFormula`. No new Lean module is needed.
It supplies precisely the canonical algebra of a dominant morphism of integral schemes:
`{X S : Scheme.{u}}`, `[IsIntegral X] [IsIntegral S]`, `(f : X ⟶ S) [IsDominant f]`,
and result `Algebra S.functionField X.functionField`. Its data is the actual generic
stalk pullback `f.functionFieldMap h`, converted by `.hom.toAlgebra`. The proof of h
uses the image of the generic point and density, not any local-dimension inequality.
The upstream `functionFieldMap` is explicitly the structure-sheaf stalk map, preceded
by `stalkSpecializes` along the generic-point equality.

Source: `literature/stacks-project/morphisms.tex`, 01RM (dominant image of the generic
point), definition-function-field, and 0A1Z with its following composition paragraph.
I read those passages and both existing Lean bodies. The mathematical statement
introduces its schemes, morphism, density condition, generic points and fields, and
cites their definition nodes. No finite-type, Noetherian, smoothness, or flatness
hypothesis is added. Empty schemes are excluded by integrality; the identity yields
the identity field map; finite inseparable extensions remain permitted.

Searches performed during repair: `msearch.py leansearch` with “A dominant morphism
of integral schemes induces a canonical inclusion of function fields at the generic
points” returned eight constituent results (IsDominant, denseRange, functionField,
germToFunctionField), not the algebra definition. `msearch.py loogle '"functionField"'`
returned twelve object/fraction-ring/germ interfaces, not this construction.
`msearch.py grep 'functionFieldMap|dominantFunctionFieldAlgebra' AlgebraicGeometry`
returned no Mathlib matches. Actual search records are copied into mathlib_searches.
`rg` of `lean/WeilConjectures` found functionFieldMap in Curve/DivisorPullback;
`rg` of `lean/Sheaf` found the exact dominantFunctionFieldAlgebra. Searches of
`dag/nodes` and a definition-node scan found no definition node carrying either map;
the only lean.declarations entry for this algebra belonged to the local-dimension
theorem. `blueprint_refs.py search 'function field'` returned 23 statements, none
defining this map; `search 'dominant function'` returned zero. `ancestor` returned
None. The new node preserves that null ancestor and prepends the item to its via.

## Returned-delivery repair

H2 in the independent review at immutable head e7a621d2fbd3 is repaired: the item
now cites the new definition node instead of lem-trf-local-dimension-formula. The
Lean import remains necessary to access the existing definition owned by the new
node; no conclusion of the dimension theorem is used. The signature, seven proof
steps, and all previously accepted mathematical clauses are unchanged. Comparison
with the current shared base finds only lean and stmt_deps changed on the item,
and the new H12 definition-node record. The delivery wrapper rebases this packet
on the current live branch. The initial saved-packet dry run passed as 688b997731f;
that mechanical pass did not check or resolve the independent ownership objection.

Second reading by NC after repair (same worker, as no other agents are authorized):
I read the new definition node against the full existing definition and its underlying
functionFieldMap. Every scheme, integrality and dominance binder matches, the output
is exactly the canonical field algebra, and no data is postponed. I reread the item
signature against its node: only the dependency ownership changes; the finite normal
Stein construction, geometric connectedness, equality inside E, finite extension and
relative algebraic closedness retain their accepted meanings.

Repair validation: scompile.py compiled the sandbox form in 4.6 s and the library
module in 4.8 s, both clean. Local packet self-check confirms verbatim signatures,
only the allowed item fields changed, and the three actual search kinds recorded.
