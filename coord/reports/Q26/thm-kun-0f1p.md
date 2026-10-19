## Worker report

Recorded the existing declaration
`AlgebraicGeometry.Etale.isIso_kunnethMap_of_isSepClosed` in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` (slopmaster2).
No new module is needed: the live upstream source explicitly names blueprint
`thm-kun-0f1p` in its docstring and asserts `IsIso` of the very
`AlgebraicGeometry.Etale.kunnethMap` recorded by `def-kun-kunneth-map`.
The recorded signature is copied verbatim, without the proof, from the live
source obtained with `scompile.py --source`; its section parameters were also
read. The older local upstream checkout does not contain this module.

Read the node's complete statement and proof, both statement-dependency nodes,
Mathlib's `IsSepClosed` and `IsSepClosure` signatures/docstrings, and the live
`kunnethMap` construction and the complete theorem docstring/signature.
The source is [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P),
Lemma 59.97.9, whose hypotheses and two-step proof agree with the imported node.
The blueprint source path named by the node is absent in this read-only clone;
the node's text and the Stacks source were read instead.

Hypothesis and clause matching:

- A separably closed field is rendered by `{k : Type u} [Field k] [IsSepClosed k]`.
  `IsSepClosed` is the recorded declaration of `def-kun-separably-closed`, in
  `Mathlib.FieldTheory.IsSepClosed`. Its polynomial-splitting definition is
  equivalent to having no nontrivial finite separable extension; the same file
  gives `IsSepClosed.algebraMap_bijective` for a separable field extension.
- The schemes and their structure maps are `{X Y : Scheme.{u}}`,
  `(aX : X ⟶ Spec (.of k))`, `(aY : Y ⟶ Spec (.of k))`.
  `[LocallyOfFiniteType aX] [QuasiCompact aX]` and the corresponding two
  instances for `aY` mean exactly finite type. This is the convention explicitly
  documented in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, rather than
  an extra separatedness or properness hypothesis.
- For the node's positive integer `n`, specialize the upstream coefficient ring
  `Λ : Type (u+1)` to `ULift.{u+1} (ZMod n)`. This is the ring `ℤ/nℤ` carried in
  the coefficient universe, via the canonical ULift ring equivalence. Its
  module carriers are in `Type (u+1)` as required for the small étale site.
  Positivity makes `ZMod n`, hence its lift, finite, supplying `[Finite Λ]`.
  `ZMod.natCast_self n` gives `(n : Λ) = 0` after lifting. The hypothesis that
  `n` is invertible in `k` gives the same unit in `Γ(Spec k, ⊤)` under
  `Scheme.ΓSpecIso`, so `n` witnesses
  `[HasInvertibleExponent Λ (Spec (.of k))]`. The class was read in
  `WeilConjectures.AlgebraicGeometry.InvertibleExponent`: its witness is precisely
  a positive annihilating integer which is a unit in these global sections.
  Thus the broader finite-ring parameterization has no additional assumption
  in the node's coefficient specialization; no change to the node is made.
- The fibre product is represented by `{W : Scheme.{u}}`, its two projection
  maps `(p₁ : W ⟶ X)`, `(p₂ : W ⟶ Y)`, and
  `(sq : IsPullback p₁ p₂ aX aY)`. Taking the categorical pullback and its
  canonical square gives `W = X ×_k Y`. Allowing any representative of this
  fibre product does not change the statement or replace it by another square.
- The arbitrary unbounded complexes are exactly
  `(E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)))`
  and the corresponding `K` on `Y`. There are no boundedness, constructibility,
  finite Tor dimension, perfectness, or cohomology restrictions.
- The conclusion is
  `IsIso (kunnethMap (ModuleCat.{u+1} Λ) p₁ p₂ aX aY (p₁ ≫ aX)
    rfl sq.w.symm E K)`.
  The definition's source is `RaX_* E ⊗ᴸ RaY_* K` and target is
  `R(p₁ ≫ aX)_*(Lp₁^* E ⊗ᴸ Lp₂^* K)`. Its commutativity inputs `rfl` and
  `sq.w.symm` are the actual structure-map equalities. The termwise exact
  inverse images are the node's `p₁⁻¹` and `p₂⁻¹`; the tensor is the existing
  ordinary uncompleted derived tensor bifunctor.
- This map lies in `D((Spec k)_ét, Λ)`, exactly the form used by the recorded
  Künneth-map definition. Read through the separably closed point equivalence,
  it is the node's displayed map in `D(Λ)`. The same upstream module provides
  `constantSheafEquivalenceOfIsSepClosed`,
  `rightDerivedGlobalSectionsIsoOfIsSepClosed`, and
  `nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed`.
  The adjacent `nonempty_iso_kunneth_of_isSepClosed` explicitly applies
  `rightDerivedGlobalSections` to `asIso` of this very `kunnethMap`, and conjugates
  by the canonical tensor and Leray identifications
  `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`. Consequently this
  attachment asserts invertibility of the specified canonical map, including
  the displayed source and target, rather than the existence of an unrelated
  isomorphism between its endpoints.

The live docstring also carries the node's proof route: the product-square
specialization of `lem-kun-0f1n`, identified with the canonical map by
`kunnethMap_eq`; the projection map from `lem-kun-0f12` using the finite
cohomological dimension of `lem-kun-0f10`; and the Leray composition
identification. This matches both paragraphs of the node's proof.

Dependency declarations used: `AlgebraicGeometry.Etale.kunnethMap` from
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`, as recorded for
`def-kun-kunneth-map`, and `IsSepClosed` from `Mathlib.FieldTheory.IsSepClosed`,
as recorded for `def-kun-separably-closed`. Both interfaces are usable; no
private copy, new node, or dependency repair is needed.

Edge cases checked: `n = 1` is retained (zero coefficient ring, hence zero
module category); `n = 0` is outside the source's positive-integer hypothesis;
empty `X` or `Y` and zero complexes are retained because no nonemptiness or
nonzero assumption is present; unbounded complexes are retained; positive
characteristic is restricted only by invertibility of `n`; nonseparated finite
 type schemes are retained. Arbitrary universe `u` is retained, with the
coefficient ring lifted as above and the prescribed `u+1` module carrier size.

Searches actually run:

- `msearch.py leanfinder`: “Kunneth formula etale cohomology separably closed
  field finite type schemes” returned eight algebraic étaleness results, none
  stating this cohomological formula.
- `msearch.py loogle`: “kunnethMap, IsSepClosed, Etale” returned no hits, reporting
  unknown identifier `kunnethMap` in Mathlib.
- `msearch.py grep`: `kunnethMap|0F1P` in Mathlib returned no hits.
- `msearch.py leansearch`: “Kunneth formula etale cohomology canonical external
  product isomorphism” was unavailable with HTTP Internal Server Error. This is
  recorded as unavailable, not as evidence that the declaration does not exist.
- `rg` in the local upstream `WeilConjectures` tree for `0F1P`, `kunneth`,
  `Kunneth`, `kun.*0f1p`, and `IsSepClosed` found the older
  `Etale.nonempty_iso_kunneth` in `Derived.Finiteness.Kunneth`. Its full signature
  and docstring were read: it gives only an unspecified isomorphism and is not
  the declaration attached here.
- `rg` for the same key words and for `kunnethMap`/`nonempty_iso_kunneth` in
  `lean/Sheaf` found no duplicate of this canonical-map assertion; matches were
  unrelated algebraic tensor Künneth or supporting étale lemmas.
- `grep -rn thm-kun-0f1p` in the older local upstream `WeilConjectures` tree
  returned no matches, confirming that the live source needs to be consulted.
- `rg` of `dag/lean_names_upstream.json` for `thm-kun-0f1p` and
  `isIso_kunnethMap_of_isSepClosed` found no match in that older index.
- `scompile.py --source WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`
  found the live canonical-map definition and `isIso_kunnethMap_of_isSepClosed`
  (lines 90–120 and 780–860 of the retrieved source). The full signatures,
  section parameters, docstrings, and adjacent global-sections identification
  were read. This live source is authoritative over the older local checkout.

There is no statement dispute or correction. Only the item's `lean` field is
changed. The required dry run performs a compiled `#check` of the existing
upstream declaration and the server preflight; nothing is pushed by this worker.

## Second reading by Q26

I read the item node and its two statement-dependency nodes, the current source of
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` (including the
section parameters, the definition of `kunnethMap`, the theorem, and the
separably closed point/global-sections identifications), Mathlib's
`IsSepClosed` and finite-type definitions, and `HasInvertibleExponent`.
I independently fetched the current source through `scompile.py --source`;
it agrees byte for byte with the worker's saved source. The shared clone now
also contains that module. I checked the recorded signature against the
source programmatically: it is verbatim equal. Only `lean` differs between the
sandbox node and the base node.

Source reading: the local Stacks source directory is absent. I read the
[official Tag 0F1P page](https://stacks.math.columbia.edu/tag/0F1P), then fetched
Stacks' `etale-cohomology.tex` and `tags/tags` into the sandbox scratchpad.
The tag maps to `etale-cohomology-lemma-kunneth`. I read that lemma and its
proof, together with the opening of `section-kunneth` and
`remark-define-kunneth-map`. The section imposes no extra standing
separatedness, properness, or boundedness hypothesis. The remark defines the
canonical map by exactly the adjunction/counit construction used by the
recorded dependency. The proof first uses the unbounded punctual base-change
lemma, then the constant-complex tensor lemma with finite cohomological
dimension. This is the node's two-step proof, including its expanded Leray
and qcqs checks.

My object/hypothesis/conclusion inventory and the corresponding Lean:

1. A field `k`, separably closed: `{k : Type u} [Field k] [IsSepClosed k]`.
   Verdict: exact. I opened `Mathlib.FieldTheory.IsSepClosed`: the class says
   every separable polynomial splits. `IsSepClosed.algebraMap_bijective`
   confirms the no-nontrivial-separable-extension interpretation used by
   `def-kun-separably-closed`. There is no perfectness assumption, so separably
   closed imperfect fields remain covered.
2. Two schemes over `k`, each finite type: `{X Y : Scheme.{u}}`, explicit
   structure maps `aX`, `aY` to `Spec (.of k)`, with
   `[LocallyOfFiniteType aX] [QuasiCompact aX]` and the corresponding pair for
   `aY`. Verdict: exact. Mathlib's `Morphisms.FiniteType` explicitly defines
   finite type as these two properties. In particular there is no implicit
   separatedness, properness, smoothness, or nonemptiness hypothesis.
3. An integer `n >= 1`, invertible in `k`, and coefficients `Z/nZ`: specialize
   the existing theorem's `(Λ : Type (u+1)) [CommRing Λ] [Finite Λ]` to
   `ULift.{u+1} (ZMod n)`. Verdict: exact specialization, with no new
   hypothesis. `ULift.ringEquiv` identifies this coefficient ring with `ZMod n`.
   Positivity supplies `NeZero n` and finiteness. Its annihilating positive
   integer is `n`, by `ZMod.natCast_self`, and invertibility in `k` maps through
   `(Scheme.ΓSpecIso (.of k)).inv.hom` to the unit required by
   `[HasInvertibleExponent Λ (Spec (.of k))]`. I wrote a scratch specialization
   check using only `hn : 0 < n` and `hu : IsUnit (n : k)` to construct these
   instances required by the recorded theorem. This check is not a delivered
   module or new declaration.
4. The product `X ×_k Y` and its projections: `{W : Scheme.{u}}`, `p₁ : W ⟶ X`,
   `p₂ : W ⟶ Y`, and `sq : IsPullback p₁ p₂ aX aY`. Verdict: exact, allowing
   any representative of the specified categorical fibre product. There is
   no arbitrary square substituted for the product. The common structure
   map is `p₁ ≫ aX`; the two equalities fed to `kunnethMap` are `rfl` and
   `sq.w.symm`, with the correct orientation.
5. Arbitrary unbounded complexes `E` and `K` of the respective small étale
   module sheaf categories: the two binders are
   `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ))` and the
   analogous category for `Y`. Verdict: exact. There are no degree bounds,
   constructibility, compactness, or finite Tor amplitude restrictions.
6. The specified canonical external-product map: the conclusion is `IsIso`
   of `AlgebraicGeometry.Etale.kunnethMap`, the very declaration recorded by
   `def-kun-kunneth-map`. I read its actual construction: it is the mate
   under the derived inverse/direct image adjunction of the composition and
   tensor comparisons followed by the two counits. Verdict: same map, not
   a second definition or a freely chosen morphism. Exact inverse image on
   constant-coefficient module sheaves agrees with its left-derived version.
7. The displayed source is the ordinary derived tensor of the two derived
   global sections, and the target is derived global sections of the
   tensor of the two inverse images. Verdict: exact under the separably
   closed point identification. In the recorded theorem the map is written
   in `D((Spec k)_et, Λ)`. I opened
   `constantSheafEquivalenceOfIsSepClosed`,
   `rightDerivedGlobalSectionsIsoOfIsSepClosed`, and the tensor comparison;
   they identify its endpoints with the displayed ones in `D(Λ)`.
   The adjacent `nonempty_iso_kunneth_of_isSepClosed` explicitly applies
   global sections to `asIso` of this same `kunnethMap`, and conjugates by
   the Leray and tensor identifications. Thus the attachment asserts
   invertibility of the canonical map, rather than only abstractly
   isomorphic endpoints. The stronger general finite-ring formulation is
   usable at precisely the node's coefficients; no statement correction
   or change to dependencies is needed.
8. The only conclusion is that this map is an isomorphism, for every such
   pair `E,K`. Verdict: exact `IsIso`, with the schemes, coefficient data,
   product and then complexes in the required order; no additional clause.

Edge cases: `n=1` gives the zero coefficient ring and is included; `n=0` is
excluded by the source's positivity assumption. Empty schemes and zero
complexes are included. No index-set restriction occurs. Arbitrary
characteristic is included exactly when `n` is invertible; purely inseparable
extensions/perfectness are not assumed. The universe `u` is arbitrary, the
small étale site uses the established object/morphism sizes, and module
carriers and the coefficient lift are in `u+1`. No extra universe equality or
restriction on complexes has been introduced.

Independent searches (using words different from the worker's first query):

- `msearch.py leanfinder` for “Derived global sections external tensor product
  isomorphism for two schemes over a separably closed point” returned eight
  scheme pullback/carrier results, none a cohomological Künneth assertion.
- `msearch.py loogle '"kunneth"'` returned zero results.
- `msearch.py grep 'externalProduct|kunneth'` returned abstract external
  products of functors/Day convolution, not this statement.
- I searched Mathlib's `AlgebraicGeometry`, local upstream
  `WeilConjectures/SixFunctors/Etale`, and project `lean/Sheaf` with
  `kunneth|external.?product`. The older upstream
  `Derived.Finiteness.Kunneth.nonempty_iso_kunneth` was opened: its conclusion
  is a bare `Nonempty` isomorphism, so it does not replace the canonical-map
  assertion. Project algebraic tensor Künneth statements concern different
  objects. The current shared upstream `Derived.Kunneth.Ordinary` has the
  exact canonical-map assertion and is the declaration recorded here.

No mathematical mismatch was found. I retained the correct existing
attachment and node signature; no module, dependency repair, new definition,
proof, or statement change is delivered. H5/H6 introduce no issue because
this delivery adds no Lean declarations. The existing theorem's docstring
states the blueprint and its two proof steps; its actual source body is
upstream reference material, not a proof added by this stage-2 delivery.
The only addition by this second reading is this independent review and its
scratch coefficient-specialization checks. Compilation and delivery
checks are recorded below when complete.

Validation: the focused coefficient scratch checks pass `scompile.py` with
no errors or warnings, both in sandbox and library positions. The earlier
scratch experiment with the entire derived-category specialization timed out
at the unchanged 60-second limit locally and on server confirmation; I reduced
that optional experiment to the two coefficient obligations rather than raise
the limit. The delivered existing declaration is checked separately by the
mandatory delivery probe. No scratch source is included in the delivery.

The mandatory `deliver2.py Q26 thm-kun-0f1p --no-push` completed successfully:
`OK (dry run): commit ce5a7f0ca1 passes the preflight and compiles; nothing pushed`.
Its existing-declaration probe passed, and server preflight accepted the
node/report delivery. Only this report and the item's `lean` record are staged.
