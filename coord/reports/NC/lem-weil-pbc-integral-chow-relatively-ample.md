## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple` states
`AlgebraicGeometry.exists_integral_chow_relatively_ample`, with `sorry` as its only proof.
No definition, additional node, dependency replacement, or statement correction is needed.
The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`.
- The integral scheme is `(X : Scheme.{u}) [IsIntegral X]`.
- Its structure map is `f : X ⟶ Spec (.of k)`. Separatedness is `[IsSeparated f]`;
  finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`. There is no properness
  hypothesis on `f`.
- The nonnegative integer is `N : ℕ`. The coordinate type `ULift.{u} (Fin (N + 1))`
  has N+1 homogeneous coordinates, including one coordinate when N=0.
- The source and map are `Y : Scheme.{u}` and `π : Y ⟶ X`. Its structure map is
  `π ≫ f`, so π is automatically a morphism over k. The conjunction
  `IsIntegral Y ∧ IsSeparated (π ≫ f) ∧ LocallyOfFiniteType (π ≫ f) ∧
  QuasiCompact (π ≫ f)` gives precisely the four asserted properties of Y.
- `IsProper π ∧ Surjective π` gives properness and surjectivity.
- `j : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k))`
  and `IsImmersion j` give the immersion, without requiring it to be closed.
  The equation `j ≫ (ProjectiveSpace ... ↘ Spec (.of k)) = π ≫ f`
  specifies that j is also over k.
- `U : X.Opens` with `(U : Set X).Nonempty` is the required nonempty open.
  `IsIso (π ∣_ U)` asserts that the restriction from the inverse image to U is
  an isomorphism. No unnecessary affineness or separate density hypothesis is imposed.
- The displayed module is exactly `(Scheme.Modules.tensorPullback j).obj
  (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)) 1)`.
  The existential invertibility proof asserts its invertibility rather than assuming it.
- `∀ W : X.Opens, IsAffineOpen W → ...` quantifies over every affine open W.
  Tensor pullback along `(π ⁻¹ᵁ W).ι` is restriction of that same module to the
  inverse image. The existential `hW` establishes invertibility on that restriction;
  `@Scheme.Modules.IsAmple (π ⁻¹ᵁ W).toScheme ... hW` asserts its absolute ampleness.
  The invertibility witness supplies the class argument required by the shared definition;
  it is not an additional input hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and the separatedness interface.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact` (their conjunction is finite type).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `.Immersion`:
  `IsClosedImmersion` and `IsImmersion`. The dependency's mathlib_match explicitly
  supplies IsImmersion as the notion for the immersion clause.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, as implemented by
  canonical inclusions of scheme opens and the morphism restriction interface.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and its
  structural morphism (base change of the integral Proj model).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`.
  Reading its actual docstring and definition confirms that it already defines O(1)
  on the base-change projective space and describes exactly the transition units of
  the node. It uses the integral Proj model internally; no separate comparison object
  or duplicate twist is needed in this statement.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.

All recorded modules of stated proof dependencies are imported, with proof-only modules
as non-public imports. In particular these include the general Chow lemma, projective
ampleness, standard charts, scheme-theoretic-image modules and the tuple-immersion tool.
The complete six-step natural-language proof from the node is carried in the theorem's
docstring, including the named dependency references.

Source checked: `coherent.tex`, lemma-chow-Noetherian and
remark-chow-Noetherian, especially (1) projectivity over X, (2) schematic closure,
(3) reducedness; `morphisms.tex`, lemma-characterize-ample-on-finite-type.
The resulting statement retains the nonproper-X case used in Tag 0A3M.

Edge cases checked: X cannot be empty because IsIntegral includes Nonempty. A nonempty
open in an integral X is dense, but density is not an extra conclusion demanded by the
node. N=0 is permitted. The quantification includes the empty affine open W; its inverse
image is empty, where invertibility and the ample affine-nonvanishing condition are
vacuous and quasi-compactness holds. Every field characteristic is permitted. Schemes,
the field, and lifted coordinates use the common arbitrary universe u; no test category
or index universe restricts the theorem. No hypothesis is universally true for arbitrary
instances of its type.

Searches actually run:

- `msearch.py ... leanfinder`, query “Integral separated finite type schemes over a field
  admit integral Chow modifications with relatively ample projective twist”: eight hits,
  for normalization and integral morphisms, no exact Chow-modification statement.
- `msearch.py ... loogle`, query `"IsProper", "IsIntegral", "IsImmersion"`: zero hits.
- `msearch.py ... grep`, query `Chow|relativelyAmple|RelativelyAmple`: 25 hits consisting
  of author-name Salchow matches, no relevant statement.
- `msearch.py ... leansearch`, query “integral Chow modification with relatively ample
  twisting sheaf”: UNAVAILABLE (Internal Server Error), not a negative result.
- `rg` in upstream WeilConjectures for integral/Chow and relatively ample terminology:
  only generic projective-space/Segre material, no exact theorem. Search by the exact
  blueprint id and by `integral_chow|chow_integral` gave no hit.
- `rg` in this project's `lean/Sheaf` for Chow and IsAmple: read ChowRelativeAmple,
  ChowFiniteType, ChowModificationData and ProjectiveAmpleInvertible. The first assumes
  a proper structure map and a supplied modification, the second does not assert integral
  Y or birationality or ampleness, and ChowModificationData lacks integral Y and
  ampleness. None states this node. Their existing notions are used rather than copied.

Validation: `scompile.py NC lem-weil-pbc-integral-chow-relatively-ample` compiled the
single module on the server in 1.4 seconds, nice 19, two threads, 60-second limit,
with no errors or warnings. No local compiler was invoked.

## Second reading by NC

Independent second reading of the sandbox module and node, with the source open.
The node has no `statement_change`; there are no new nodes or dependency modules.
I found no mismatch and left the Lean module and node record unchanged.

Object, hypothesis, and conclusion inventory, matched in order:

1. A field k: `(k : Type u) [Field k]`. Exact; no assumption on characteristic,
   algebraic closure, or perfection.
2. An integral scheme X: `(X : Scheme.{u}) [IsIntegral X]`. Exact. I read the
   dependency node and Mathlib's class: it includes nonemptiness and domain rings
   on nonempty opens, equivalently reduced and irreducible.
3. The k-structure and separated finite-type hypotheses: `(f : X ⟶ Spec (.of k))`
   with `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. Exact. I read
   the proper/separated and finite-type dependency nodes and the actual Mathlib
   classes. The last two classes together express finite type; no properness or
   Noetherian instance is required as an input.
4. An integer N >= 0: `∃ (N : ℕ)`. Exact. The homogeneous coordinate type is
   `ULift.{u} (Fin (N + 1))`, so the projective space has dimension N, not N-1.
5. An integral separated finite-type k-scheme Y: `Y : Scheme.{u}` followed by
   `IsIntegral Y`, `IsSeparated (π ≫ f)`, `LocallyOfFiniteType (π ≫ f)`, and
   `QuasiCompact (π ≫ f)`. Exact, with its k-structure given by the composite.
6. A proper surjective k-morphism π: `(π : Y ⟶ X)` and
   `IsProper π ∧ Surjective π`. Exact. Compatibility over k follows from the
   chosen composite structure map. I read the dependency records and the actual
   `IsProper` and `Surjective` classes; universally closed supplies the
   quasi-compactness needed for properness to mean finite type.
7. An immersion j into P^N_k: the typed existential `j` and `IsImmersion j`.
   Exact. The equation `j ≫ (ProjectiveSpace ... ↘ Spec (.of k)) = π ≫ f`
   makes the immersion a k-morphism. I checked the closed-immersion dependency's
   immersion clause against Mathlib `IsImmersion.isImmersion_iff_exists`:
   closed immersion followed by open immersion. No closedness of j is asserted.
8. A nonempty open U and an isomorphism over it: `∃ U : X.Opens,
   (U : Set X).Nonempty ∧ IsIso (π ∣_ U)`. Exact; the restriction has source
   the inverse image of U. Density is automatic for this integral X and is
   neither an extra input nor an omitted required clause.
9. The particular invertible module L = j^*O(1): the existential invertibility
   witness concerns exactly `(Scheme.Modules.tensorPullback j).obj
   (ProjectiveSpace.twist ... 1)`. Exact, with no arbitrary substitute module.
   I read the module-pullback node and its tensor construction, the twist node
   and upstream `ProjectiveSpace.twist`, and the invertibility node and upstream
   `Scheme.Modules.IsInvertible`. ProjectiveSpace is the integral-model base
   change, with first projection as structure map; its shared twist is the
   integral Proj twist pulled back to that same space. Its docstring gives the
   standard chart gluing description. The upstream TODO about comparison with
   affine Proj is a comparison theorem, not a missing object for this signature.
10. Relative ampleness on every affine inverse image: `∀ W : X.Opens,
    IsAffineOpen W → ∃ hW : ...IsInvertible, @Scheme.Modules.IsAmple ... hW`.
    Exact. The restricted object is tensor pullback along `(π ⁻¹ᵁ W).ι` of
    the very same module L. I opened the ample dependency and its implementation:
    quasi-compactness plus affine nonvanishing loci of positive tensor-power
    sections is precisely the node's absolute ampleness. The witness hW supplies
    an argument of that predicate and is an asserted property, not a hypothesis.
    Nesting this conclusion under the existential U does not change its meaning:
    the module and the universal W-clause do not depend on U.

Source reading: `coherent.tex`, `lemma-chow-Noetherian` assumes a Noetherian
base and a separated finite-type morphism; Spec k is Noetherian for every field.
`remark-chow-Noetherian` (1) gives the closed immersion into P^N_X, (2) allows
schematic closure of the isomorphism open, and (3) gives reducedness. With the
integral open this yields integral Y. In `morphisms.tex`,
`lemma-characterize-ample-on-finite-type` has the finite-type hypothesis, which
proper π supplies here. The Chow paragraph in `etale-cohomology.tex` Tag 0A3M
uses exactly j^*O(1) and its identification with the pullback from P^N_X.
No standing source assumption needs adding to the node or Lean statement.

Edge cases: empty X and zero coordinate ring are excluded by integral X and the
field axiom respectively, as the source requires. Surjectivity forces Y nonempty.
N=0 is allowed and gives one homogeneous coordinate; N is existential, so this
asserts no dimension-zero choice for all X. There is no arbitrary empty index
set. Empty affine W is included; its inverse image is empty, the invertibility
condition is vacuous, and IsAmple has compactness and no point to check. A zero
module on nonempty Y cannot satisfy invertibility, while on the empty inverse
image it causes no defect. All characteristics are allowed. The common arbitrary
universe u and the lifted finite coordinate type accommodate every size of field
and scheme after universe enlargement, without vacuous test-object quantifiers.
Every variable/universe is explicitly bound (`autoImplicit false`).

Independent searches, using terms different from the worker's first queries:

- `msearch.py ... leanfinder "proper birational quasi-projective model of an
  integral variety with ample line bundle"`: eight hits about normalization,
  Proj, and integral morphisms; none states this result.
- `msearch.py ... loogle '"IsIntegral", "IsAmple"'`: zero hits.
- `msearch.py ... grep 'birational|quasi.projective'`: sixteen hits, chiefly
  Mathlib birational scheme definitions, no integral Chow-ampleness statement.
- `rg` for Chow, birational/ample combinations in Mathlib, upstream
  WeilConjectures, and this project's Lean: inspected upstream ChowLemma and
  the local ChowRelativeAmple, ChowFiniteType, and ChowModificationData
  signatures. ChowLemma lacks integral source and the ample conclusion;
  ChowRelativeAmple requires proper g and a supplied modification;
  ChowFiniteType lacks integrality, the isomorphism open, and ampleness;
  ChowModificationData lacks integrality and ampleness. None is this theorem.
- Exact-name searches for `exists_integral_chow_relatively_ample`,
  `integral_chow`, and `chow_integral` in the upstream name index,
  WeilConjectures, and project Lean found no existing declaration.

H4/H5/H6/H8/H9 checks: the delivery adds only this named theorem, with `sorry`
as its sole proof, no definitions or private notions. Its source/blueprint
references and all six proof steps match the node, including schematic closure,
reducedness, the proper graph immersion, and the chart/twist comparison.
The recorded modules of every stated proof dependency are imported. No line
exceeds 100 columns. The node's `lean.statement` was checked byte-for-byte
against the theorem signature and agrees. No correction or unresolved dispute
is needed.

Validation: independently reran `scompile.py NC
lem-weil-pbc-integral-chow-relatively-ample
lean/Sheaf/AlgebraicGeometry/IntegralChowRelativelyAmple.lean`: clean server
compile in 1.4 seconds, nice 19, two threads, 60-second per-file limit, no
warnings or errors. No local compiler or library build was invoked.
