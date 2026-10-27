## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantFamilyJetEquality` states
`AlgebraicGeometry.Scheme.eq_of_constantFamily_jets`, with its proof `sorry`.
Its two helper definitions construct the canonical quotient-stalk spectrum map and
its product with the parameter scheme. Their data are explicit; neither definition
chooses a witness of an existence theorem. No independent notion, new node,
dependency repair, or statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The three k-schemes are `{X T Z : Scheme.{u}}` and their structure morphisms
  `s`, `t`, `z` to `Spec (.of k)`. Explicit structure maps are used because the
  statement uses several base changes and k-morphisms.
- Integrality is `[IsIntegral X]`; separatedness of X/k is `[IsSeparated s]`.
  Finite type is `[LocallyOfFiniteType s] [QuasiCompact s]`, exactly the
  conjunction specified by the recorded finite-type dependency.
- The rational point is `P : Spec (.of k) ⟶ X`, with `hP : P ≫ s = 𝟙 _`.
  Its underlying point is `P (IsLocalRing.closedPoint k)`; Spec k is a singleton.
- The local ring R is literally `X.presheaf.stalk (P (IsLocalRing.closedPoint k))`.
  The canonical map R → k is `(Scheme.stalkClosedPointTo P).hom`, whose definition
  is P's stalk map composed with the canonical stalk-of-Spec-k isomorphism.
  Thus m is literally `RingHom.ker (stalkClosedPointTo P).hom`, rather than a
  new arbitrary ideal. For a rational point this is also R's maximal ideal.
- `rationalPointJetInclusion k P n` has domain `Spec (.of (R ⧸ m ^ (n + 1)))`.
  Its data are `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ...))` followed
  by `X.fromSpecStalk` at that point. Hence it is exactly the canonical X_n → X.
- T has `[LocallyOfFiniteType t] [QuasiCompact t]`, with no reducedness,
  connectedness, smoothness, nonemptiness, or irreducibility requirement.
- Z/k has `[IsSeparated z]`, using Mathlib's definition as closed diagonal.
  There is no finite-type assumption on Z.
- The ambient product T ×_k X is `pullback t s`; the open subscheme is
  `(E : (pullback t s).Opens)`, with scheme `E.toScheme` and canonical immersion `E.ι`.
- `hE` asserts that every point of the product whose second projection is the
  underlying point of P belongs to E. This is precisely containment of the
  support of T ×_k {P}. The fibre over P is T itself, since P has residue field k.
- `constantFamilyJetMap k t s P n` is the actual map T ×_k X_n → T ×_k X:
  `pullback.lift` preserves the first projection and composes the second
  projection with `rationalPointJetInclusion`. X_n's structure map is its
  composite through X, so this is the stated base change, not a freely chosen map.
- Every jet family has the support of the constant section: the radical of
  m^(n+1) is m. Thus hE puts its whole image in E and the universal property of
  open immersions supplies its unique factorization through E. This explanatory
  fact in the node is used to express restrictions canonically without a new
  factorization hypothesis: `pullback.snd (constantFamilyJetMap ... n) E.ι`
  is the inverse image restriction, whose first projection to T ×_k X_n is
  an isomorphism. Agreement on this inverse image is therefore exactly agreement
  on the whole T ×_k X_n. No conditional agreement on unspecified maps is used.
- `f g : E.toScheme ⟶ Z` and the equations `hf`, `hg` say exactly that both
  are k-morphisms for the structure map `E.ι ≫ pullback.fst t s ≫ t`.
- `hjet : ∀ n : ℕ, 1 ≤ n → ...` says that their composites with the preceding
  canonical restriction are equal for every n ≥ 1. No compatibility among
  consecutive jets is added, and no finite bound replaces all positive n.
- The conclusion is literally `f = g`. No smoothness assumption on X occurs.

Dependency declarations used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (reexported).
- `def-weil-algebraic-closure`: the algebraically-closed clause `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; no algebraic closure is chosen.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and its public dependency `Morphisms.QuasiCompact`.
- `def-weil-pbc-algebra-hom-quotient`: Mathlib's ideal powers, quotient ring,
  `Ideal.Quotient.mk`, imported by `Mathlib.RingTheory.Ideal.Quotient.Operations`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, reexported by the public geometric imports.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, same module.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, public through Separated.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`; the concrete open immersion is E.ι.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; scheme pullbacks
  and their existence come from `Mathlib.AlgebraicGeometry.Pullbacks`.
- Canonical stalk interfaces: `Scheme.fromSpecStalk`, `Scheme.stalkClosedPointTo`,
  `Mathlib.AlgebraicGeometry.Stalk`. They are composites of the recorded scheme
  and spectrum notions, not replacement definitions of a DAG dependency.

The source was read at `literature/stacks-project/algebra.tex`,
`lemma-intersection-powers-ideal-module` (Tag 00IQ), particularly part (2),
and its local-Krull proof. The module docstring records all eight proof steps,
including the coefficientwise tensor argument that retains nonreduced T.
All proof dependencies already have Mathlib matches. Their geometric interfaces
are in the public geometric imports; the additional proof-only imports are
`Mathlib.RingTheory.FiniteType`, `Mathlib.RingTheory.Localization.Submodule`,
`Mathlib.RingTheory.Filtration`, and `Mathlib.LinearAlgebra.TensorProduct.Map`.
No proof dependency import creates a cycle.

Edge cases checked mathematically before writing and again on the signature:

- Empty T: allowed (no `Nonempty T`), and equality of maps from its open product
  is immediate. Empty X is excluded by the original integrality assumption.
- X = Spec k: m = 0, so all jets are X and hjet is ordinary equality.
- T = Spec(k[ε]/ε²): allowed. No reducedness assumption entered the pullbacks
  or hjet; the proof uses a vector-space basis of its possibly nonreduced ring.
- Disconnected T and empty open components: allowed. The proof works chartwise.
- Singular integral X, such as a cusp: allowed; only a Noetherian local domain
  and Krull intersection are used, with no regularity/smoothness assumption.
- The first required index is n = 1, with exponent 2. The helper also has n = 0,
  but the theorem imposes no order-zero test. All positive characteristic cases
  are retained, and no independent test-object universe can make hjet vacuous.

Searches (prescribed msearch wrapper, Q147 / this item, 2026-10-24):

- LeanFinder: "Morphisms from a constant family agreeing on every infinitesimal
  neighborhood of a rational point in an integral scheme are equal". Eight hits:
  local spread-out uniqueness, `hom_ext_of_forall`, stalk and field-point
  equivalences; no theorem detecting all jets over nonreduced parameters.
- Loogle: `"IsIntegral", "stalk"`. One hit: the stalk-domain instance;
  not this morphism-equality statement.
- Mathlib grep: `jet.*equal|infinitesimal.*dens|fromSpecStalk`, AlgebraicGeometry.
  Twenty-five hits, primarily canonical stalk morphisms, rational maps, and
  spread-out lemmas; no constant-family jet detection result.
- LeanSearch: "Two morphisms from a family of integral schemes agreeing on all
  infinitesimal neighborhoods of a constant rational section to a separated
  scheme are equal". Eight hits: dominant-map extensionality, ordinary Hom
  extensionality, closed equalizers, and separated uniqueness. The dominant-map
  versions require reduced source and do not cover the nonreduced T allowed here.
- `rg` on the project `lean/WeilConjectures` and `lean/Sheaf` for
  `jet.*equal|constantFamily|constant_family|fromSpecStalk|jetMap|jetScheme`,
  and separately for this blueprint id: no exact statement. Existing adic
  neighbourhoods in Artin modules are over their Artin base, and torus jets
  use affine localizations; neither supplies this rational-point stalk map.
  This module simply composes `Ideal.Quotient.mk`, `Spec.map`, and
  `Scheme.fromSpecStalk` rather than redefining their underlying notions.
- Exact-name search for all three delivered declarations in Mathlib, both
  project trees, and `dag/lean_names_upstream.json`: no collisions.

Verification: `scompile.py Q147 lem-sfb-constant-family-jet-equality <module>`
compiled both sandbox and library module successfully (5.6 s / 5.9 s), no
warnings or errors. `set_option autoImplicit false` enforces explicit binding.
No statement fault or `STATEMENT-DISPUTED` finding.

## Second reading by Q147

The dispatcher requires this worker to deliver directly and forbids starting
another agent; the independent mathematical review is assigned to the maintainer.
This is a separate self-check of the final node and file, not a claim that a
second worker reviewed it.

I reread the signature against every clause. The field, X's integrality,
separatedness and finite type, T's finite type, and Z's separatedness all appear
with exactly their stated scope. The structure equations hP/hf/hg preserve
k-linearity. In particular, no absolute separatedness of Z, finite type of Z,
or smoothness of X was substituted. The jet ideal is the evaluation kernel
itself and the exponent is n+1; the quantifier is precisely n ≥ 1. The open
containment condition includes every point above P rather than just closed
points of T. Inverse-image restriction tests the entire jet, because hE
contains its support; it does not impose a stronger test family or assume a
choice of lift. Both concrete definitions have real data and the only theorem
has exactly `sorry`. I found no mathematical mismatch. Compiler repairs used
named implicit arguments for `pullback.condition` and explicit coercion of the
pullback scheme to its point type; neither changed the mathematical statement.
