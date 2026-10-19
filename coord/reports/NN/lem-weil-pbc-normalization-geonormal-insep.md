## Worker report

Module `Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep` states
`AlgebraicGeometry.exists_finite_purelyInseparable_geometricallyNormal_normalization`.
Its only proof is `sorry`. No definitions or proofs were added, and the node's natural
statement, dependencies, proof plan, and sources are unchanged.

Hypothesis and clause correspondence:

- The field k is `(k : Type u) [Field k]`.
- The k-scheme is `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]`.
  Its finite-type hypothesis is exactly `LocallyOfFiniteType` together with
  `QuasiCompact` on its structure map. Neither separatedness nor reducedness nor
  integrality is assumed.
- The extension is the existential field `k'` with `Field k'` and `Algebra k k'`.
  A field algebra map is injective, so this is a field extension. The conjunction
  `Module.Finite k k' ∧ IsPurelyInseparable k k'` is precisely finite purely
  inseparable, including characteristic zero.
- The base-changed scheme is `pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k k')))`, with its k'-structure map
  `pullback.snd`.
- The node's reduced irreducible components are represented by the existential
  finite family `C : Fin n → Scheme.{u}`, integral structures `hC`, and closed
  immersions `ι i` into that base change. The image condition is the equivalence
  `Z ∈ irreducibleComponents ... ↔ ∃ i, Set.range (ι i) = Z`.
  Injectivity of `i ↦ Set.range (ι i)` excludes repeated components. These conditions
  characterize exactly the reduced induced components: an integral closed subscheme
  with a specified irreducible closed support is its unique reduced induced structure.
  In affine terms the closed immersion is a quotient A/I, reducedness says I is
  radical, and its support determines that radical ideal. Thus there is no arbitrary
  thickening or replacement scheme in the representation.
- N is the actual coproduct of the existing `Scheme.normalization` objects of these
  components. It occurs as the domain of `Sigma.desc (fun i =>
  @Scheme.fromNormalization (C i) (hC i) ≫ ι i)`. This is a direct term using the
  recorded integral normalization and coproduct, rather than a newly defined notion
  or a postulated arbitrary normal modification. Choosing a finite enumeration
  expresses the disjoint union in the node; finite type over a field makes the
  set of components finite. Every such enumeration gives the same normalization
  over the base, up to the unique componentwise isomorphism.
- N's structure map is that `Sigma.desc` composed with `pullback.snd`.
- Every extension L/k' is `∀ (L : Type u) [Field L] [Algebra k' L]`.
  Its base change N_L is the pullback of that structure map along the spectrum
  map of `algebraMap k' L`. All schemes and fields use the same explicit universe,
  as in the recorded base-change conventions; there is no independent smaller test
  universe which could make this quantification vacuous.
- Every point is the subsequent `∀ z : ↥(pullback ...)`. Its local ring is that
  scheme's `presheaf.stalk z`. The two conclusions are `IsDomain` and
  `IsIntegrallyClosed` of precisely that stalk, not merely of global sections.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms
  (def-pc-scheme).
- The convention node def-weil-pbc-scheme-conventions has no declaration of its own;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` supplies `LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` supplies `QuasiCompact`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`
  (def-weil-pbc-finite-purely-inseparable-extension).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd` (def-pc-fibre-product); the scheme pullback instance is used.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` (the normal-domain clause of def-weil-pbc-normal-ring).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization`, `Scheme.fromNormalization`
  (def-sc-normalization), read in the upstream source, including the `IsIntegral`
  binder and both docstrings. The integral structure is explicitly passed as `hC i`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`
  (def-weil-irreducible-components).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: the recorded reduction is
  `X.nilradical.subscheme`, with inclusion `X.nilradical.subschemeι`
  (def-weil-pbc-scheme-reduction). The signature characterizes the reduced component
  by integrality and closed immersion, as explained above, so does not need to
  construct an extra reduction or an unrecorded normalization functor.
- `Mathlib.AlgebraicGeometry.Limits`: the scheme coproduct instance, `Sigma.desc`,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι` (the Mathlib match of
  lem-weil-pbc-scheme-coproduct-family). Coproduct existence is used in the signature;
  the open/disjoint cover facts explain the normal-stalk argument in proof step 3.

All recorded Lean modules of the proof dependencies are imported. Dependencies without
a Lean record remain as the node's future proof plan; no substitute theorem was invented.
The docstring carries all nine natural-language proof steps, including their cited node IDs.

Edge cases checked: X empty permits n = 0; the normalization and all its base changes
are empty, so the stalk condition is vacuous as it should be. A reducible X has one
summand per distinct component, including intersecting components. Nonreduced X is
handled by the reduced component condition, not by retaining nilpotents. In
characteristic zero the purely inseparable extension can be the identity. The test
extension L = k' is included, as are transcendental extensions. Zero local rings are
excluded at actual points by `IsDomain`, as required. No dimension restriction is imposed.

Searches for an existing statement:

- msearch.py leanfinder: "Normalization of a finite type scheme becomes geometrically
  normal after a finite purely inseparable field extension" returned 8 hits on relative
  normalization (integrality, reducedness, normalizationDesc), none on geometric normality
  after a purely inseparable extension.
- msearch.py loogle: `"normalization", "IsPurelyInseparable"` returned 0 hits.
- msearch.py grep: `normalization.*[Gg]eometr|[Gg]eometr.*normalization` in
  AlgebraicGeometry returned 3 module-comment/import hits, no matching theorem.
- rg of the upstream WeilConjectures tree and lean/Sheaf using the same geometric
  normalization pattern found only normalization documentation and unrelated unit/Čech
  normalizations. The item ID has no upstream declaration.
- rg of dag/lean_names_upstream.json found no matching geometric-normalization statement
  or collision with the new declaration name.

Source checked directly: literature/stacks-project/varieties.tex,
lemma-finite-extension-geometrically-normal (Tag 0BXT). It states exactly the same
finite purely inseparable extension and geometric normality of the normalization.
Its open-ambient typo is already corrected in the node's proof plan; the statement
itself requires no correction. No STATEMENT-DISPUTED flag or node fault remains.

Validation: server-only scompile.py passed cleanly, 1.6 seconds, nice 19, two threads,
60-second per-file limit. The initial elaboration issue was fixed by writing the
explicit scheme-to-point-type coercion `↥(pullback ...)` in set and point binders.
No local compiler or library build was run.

## Second reading by NN

Independent reading of the sandbox node and module against
`literature/stacks-project/varieties.tex`, label
`lemma-finite-extension-geometrically-normal` (Tag 0BXT), including its proof.
The definition `definition-algebraic-scheme` in the same file means finite type
structure morphism, without separatedness. The normalization section and
`lemma-normalization-and-change-of-fields` use the reduced componentwise
normalization. No statement correction is needed; there is no `statement_change`.

Object/hypothesis/conclusion checklist, in the order of the node:

1. A field k: `(k : Type u) [Field k]`. Exact.
2. A k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]`.
   Its structure morphism is exactly `X ↘ Spec (CommRingCat.of k)`. Exact.
3. Finite type: the two instances `LocallyOfFiniteType` and `QuasiCompact`
   on that structure morphism. This is the convention node's finite type
   condition. No extra normality, reducedness, integrality, separatedness,
   dimension, or Noetherianity hypothesis is imposed. Exact.
4. There exists a finite purely inseparable extension k'/k:
   `∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
   Module.Finite k k' ∧ IsPurelyInseparable k k' ∧ ...`.
   A unital map between fields is injective, and `Module.Finite` is finite
   dimensionality here. The extension is selected before all component and
   geometric-normality data. Exact.
5. X_{k'}: `pullback (X ↘ Spec (CommRingCat.of k))
   (Spec.map (CommRingCat.ofHom (algebraMap k k')))`. Its map to Spec k'
   is `pullback.snd`, so the orientation of both base changes is correct.
6. Reduced irreducible components: `∃ (n : ℕ) (C : Fin n → Scheme.{u})
   (hC : ∀ i, IsIntegral (C i)) (ι : ∀ i, C i ⟶ ...)`, together with
   `∀ i, IsClosedImmersion (ι i)`, injectivity of the support map, and
   the biconditional characterizing all members of `irreducibleComponents`.
   Exact: each C i is reduced, irreducible, and nonempty; a closed subscheme
   of a given closed support is uniquely determined once reduced. On an affine
   open its ideal is radical, and V(I) determines that ideal. Thus these are
   precisely the reduced induced components, up to isomorphism over X_{k'};
   arbitrary thickenings or finite covers are not admitted. Conversely the
   reduced induced components have all these properties. Finite type over
   a field gives finitely many components, so `Fin n` adds no restriction.
7. N, the disjoint union of their normalizations: the domain of
   `Sigma.desc (fun i => @Scheme.fromNormalization (C i) (hC i) ≫ ι i)`
   is the categorical coproduct of the actual `Scheme.normalization (C i)`.
   The integral instances are passed explicitly to the recorded upstream
   normalization, which is in the component's own function field. No
   arbitrary normal scheme or normalization in a larger field replaces it.
   Composing with `pullback.snd` gives the intended k'-structure map. Exact.
8. Every extension L/k': `∀ (L : Type u) [Field L] [Algebra k' L]`,
   after the single existential choice of k' and the components. The second
   pullback is along `Spec.map (algebraMap k' L)`. Exact, with no algebraicity,
   finiteness, separability, or perfectness hypothesis on L.
9. Every local ring of N_L is an integrally closed domain:
   `∀ z : ↥(pullback ...), IsDomain ((pullback ...).presheaf.stalk z) ∧
   IsIntegrallyClosed ((pullback ...).presheaf.stalk z)`. Both conjuncts
   concern that same scheme and point. This is stalk normality, not merely
   normality of global sections. Exact.

Dependency audit: read every statement-dependency node and its recorded Lean
signature. Opened the upstream integral `Scheme.normalization` and
`Scheme.fromNormalization` declarations and their function-field docstrings,
Mathlib `IsIntegral` in AlgebraicGeometry/Properties, the finite-type and
quasi-compact classes, `IsClosedImmersion`, `irreducibleComponents`, pullback
and its projections, `IsPurelyInseparable`, `IsIntegrallyClosed`, and the
subscheme construction and inclusion. Read the coproduct node's complete
Mathlib match and Limits.lean's small-index coproduct instance, open cover,
and disjoint-image theorem. The convention dependency has no separate
notion to import. The reduction dependency is rendered by the equivalent
reduced-closed-support characterization explained in item 6, rather than
by inventing another reduction. No dependency record is unusable, and
there are no new nodes or delivered dependency modules to audit under
H12/H13. The modules of recorded proof dependencies are imported; the nine
numbered docstring steps follow the node's nine proof steps, including the
source's open-ambient typo correction already present in the node.

Edge cases: X empty is represented by n = 0; the empty coproduct and its
base changes have no points, so the local condition is correctly vacuous.
If X is nonempty, n = 0 cannot satisfy the component biconditional. Components
may intersect in X, but the normalization coproduct separates them.
Nilpotents in X are permitted and removed componentwise. Characteristic
zero allows the identity extension; positive characteristic is unrestricted,
and n = 0 imposes no field-characteristic condition. Test extensions include
L = k' and transcendental extensions. The nontriviality of local rings at
points is demanded by `IsDomain`, as in the node. Universe u is explicit
and shared by k, X, k', C, and test fields, following the project's scheme
base-change convention; no independently smaller test universe creates a
vacuous quantifier. Larger cardinalities of test extensions do not change
geometric normality: for finite-type charts failure is detected after a
finitely generated subextension, which fits the common universe. No
variables or universes are auto-implicit or left unbound by inspection.

Independent searches used different wording from the author:

- msearch leanfinder: `finite inseparable base field extension makes component
  normalization geometrically normal` returned eight hits (field-normality,
  geometric reducedness, and relative-normalization integrality), none the
  statement. These are different conclusions or different objects.
- msearch loogle: `"IsPurelyInseparable", "IsIntegrallyClosed"` returned zero.
- msearch grep: `geometricallyNormal|geometrically_normal|normal.*purelyInseparable`
  returned only `IsPurelyInseparable.normal`, which is normality of a field
  extension, not geometric normality of scheme stalks.
- Direct rg in upstream WeilConjectures, Mathlib AlgebraicGeometry, and
  project lean/Sheaf with case variants of geometric normality and purely
  inseparable normality found no duplicate statement. Opened Mathlib's
  relative normalization interface: it is not this existence theorem.
  Project `GeometricallyNormalTensorNormal` concerns a tensor-product
  consequence, not existence of the required finite field extension.
  Upstream names and source contain neither this item ID nor the proposed
  declaration name. No existing declaration can replace this module.

Verdict and changes: no mismatch found. Kept the Lean module, natural
statement, dependencies, proof plan, and Lean record unchanged; added this
independent review only. The node's `lean.statement` was checked verbatim
against the file's signature and matches. No line exceeds 100 characters.
There is exactly one theorem with proof `sorry`, no data definition, no
local notation or private copy, and both required source docstrings are
present. No theorem was proved.
