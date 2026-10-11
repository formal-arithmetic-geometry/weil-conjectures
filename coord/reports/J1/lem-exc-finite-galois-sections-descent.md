## Worker report

The module states finite Galois descent for sections of a set-valued sheaf. Its only
proof is `sorry`. Stacks Project Tag 04JM, Lemma 59.56.5, was read online because
`literature/stacks-project/` is absent on this machine. The cited passage uses the
decomposition of `Spec E ×_{Spec L} Spec E` into one copy of `Spec E` per Galois
automorphism, followed by the sheaf condition for the finite etale cover.

Clause and hypothesis mapping:

- `L E : Type u`, `[Field L]`, `[Field E]`, `[Algebra L E]` encode the field extension.
- `[FiniteDimensional L E]` is finiteness of the extension.
- `[IsGalois L E]` gives separability and normality; its Galois group is
  `E ≃ₐ[L] E`. The local instance declaration registers the existing theorem
  `Algebra.Etale.of_finite_of_isSeparable` to form the etale-site object.
- `F : Sheaf (Spec (.of L)).smallEtaleTopology (Type v)` is a sheaf of sets on
  the small etale site of `Spec L`, with no algebraic structure on sections.
- `etaleSpec L L` and `etaleSpec L E` represent `Spec L` and `Spec E` in that
  site. `F.obj.map (etaleSpecMap (Algebra.ofId L E)).op` is pullback along
  `Spec E -> Spec L`.
- `{s | ∀ q : E ≃ₐ[L] E, F.obj.map (etaleSpecMap q).op s = s}` is exactly the
  subset of sections invariant under all field automorphisms. Each
  `etaleSpecMap q` is the corresponding automorphism of `Spec E` over `Spec L`.
- `Set.BijOn ... Set.univ ...` says this pullback maps every section downstairs
  into that subset, is injective, and is surjective onto it.

Dependency declarations read and used: `CategoryTheory.Sheaf` in
`Mathlib.CategoryTheory.Sites.Sheaf`; `Algebra.IsSeparable` in
`Mathlib.FieldTheory.Separable` through `IsGalois`; and `Algebra` in
`Mathlib.Algebra.Algebra.Defs`. The site uses `Scheme.smallEtaleTopology` in
`Mathlib.AlgebraicGeometry.Sites.Etale`. The source library's
`AlgebraicGeometry.Scheme.etaleSpec` and `etaleSpecMap` in
`WeilConjectures.AlgebraicGeometry.Sites.Hilbert90` supply the site objects and
maps; `Algebra.Etale.of_finite_of_isSeparable` is in
`WeilConjectures.Mathlib.RingTheory.Etale.Field`.

Edge cases checked: when `E = L`, the automorphism group is trivial and the map
is the identity up to the canonical site presentation. For `E = C` over `L = R`,
the predicate requires invariance under identity and conjugation. No choice of
characteristic or cardinality of the section set is imposed. Field spectra are
nonempty; the empty-scheme case is outside the node's quantified objects.

Searches for an existing theorem: `msearch leanfinder` with "Finite Galois
descent for sections of an etale sheaf over a field, invariant sections"
returned eight related etale algebra and Galois results, none about sections.
`msearch loogle` with "Sheaf, IsGalois, smallEtaleTopology" returned zero hits.
`msearch grep` with "Galois.*(sheaf|section)|invariant.*section" in
`AlgebraicGeometry` returned one unrelated ideal-sheaf Galois connection.
`rg` over the source `WeilConjectures` and project `lean/Sheaf` found no exact
finite-Galois section descent theorem. `grep -rn` for this node ID in the source
found nothing. Mathlib source searches of `AlgebraicGeometry/Sites` and
`FieldTheory` found only foundational definitions and unrelated results.

## Second reading by J1

Independent reading against the node and Stacks Project Tag 04JM, Lemma
59.56.5, direct proof. The source starts with a sheaf of sets on the small
etale site of the spectrum of a field. Its finite Galois extension occurs in
the direct descent argument; the node states that intermediate assertion.

- Base field `L`: `(L E : Type u) [Field L]`. Verdict: exact.
- Extension field and its map from `L`: `[Field E] [Algebra L E]`.
  This is the Mathlib declaration recorded by `def-pc-field-extension`.
  Verdict: exact; the algebra map is injective because `L` is a field.
- Finite separable algebraic extension and normality:
  `[FiniteDimensional L E] [IsGalois L E]`. The first gives finiteness;
  `IsGalois` supplies `Algebra.IsSeparable L E` (including algebraicity) and
  `Normal L E`, as required by the node and
  `def-weil-pbc-separable-algebraic-extension`. Verdict: exact.
- Automorphism group `Q = Aut_L(E)`: `q : E ≃ₐ[L] E` in the target set.
  The implicit group is Mathlib's `AlgEquiv` group; the displayed pullback
  gives its action on sections. Verdict: exact.
- Sheaf of sets on `(Spec L)_et`:
  `(F : Sheaf (Spec (.of L)).smallEtaleTopology (Type v))` uses the
  `CategoryTheory.Sheaf` and small-etale-topology declarations recorded by
  `def-weil-pbc-etale-sheaf-of-sets`. Verdict: exact.
- The site objects for `Spec L` and `Spec E` are `etaleSpec L L` and
  `etaleSpec L E`. Their imported definition in `Hilbert90.lean` is the
  spectrum over `Spec L`; the local `Algebra.Etale` instance follows from
  the finite separable hypotheses. Verdict: exact.
- Pullback `F(Spec L) -> F(Spec E)`:
  `F.obj.map (etaleSpecMap (Algebra.ofId L E)).op`. The imported
  `etaleSpecMap` is induced by the algebra map, so its scheme direction is
  `Spec E -> Spec L`. Verdict: exact.
- Invariant sections:
  `{s | forall q : E ≃ₐ[L] E, F.obj.map (etaleSpecMap q).op s = s}`.
  This tests pullback by every automorphism, including the identity;
  there is no extra equivariance datum. Verdict: exact.
- Bijection onto precisely that subset: `Set.BijOn` of the pullback map
  from `Set.univ` to the invariant set. It asserts image containment,
  injectivity, and surjectivity onto invariants. Verdict: exact.

Edge cases: `E = L` is allowed and has the trivial Galois group. Every
characteristic is allowed. There is no nonempty assumption on a section set:
the empty-set-valued sheaf case remains within the quantified `F`. The
empty scheme and an index `n = 0` are not among this node's objects; field
spectra are nonempty. The field and site objects share universe `u` as
required by the imported `etaleSpec` API, while section values use an
independent universe `v`; neither universe is fixed to a concrete level.

Independent searches used different wording from the worker: `msearch
leanfinder` for "global sections etale sheaf finite Galois field extension
fixed points" returned eight field or etale-algebra declarations, no
section-descent statement. `msearch loogle` for
`CategoryTheory.Sheaf, IsGalois` returned no hits. `msearch grep` for
`finiteGaloisSectionsDescent|fixed.*section|section.*invariant` returned
unrelated invariant/section names. `rg` for the theorem name and Galois
section phrases in the source `WeilConjectures` and the project's
`lean/Sheaf` found no existing declaration. I opened `Hilbert90.lean`,
`Etale/Field.lean`, Mathlib's `Galois/Basic.lean`, and the three recorded
dependency nodes to check their signatures, not only their names.

No statement mismatch was found and the Lean module and node record did not
need repair. The sole change is this replacement of the placeholder second
reading. `scompile.py` compiled the module cleanly with only its intended
`sorry` proof.
