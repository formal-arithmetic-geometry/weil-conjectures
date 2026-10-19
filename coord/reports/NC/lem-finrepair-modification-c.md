## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer` states
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_modification`, with
`sorry` as its entire proof. No definitions, helper theorems, node corrections or
new nodes are needed. The item node changes only in `lean`.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`.
- `X`, `Y` and `S` are `Scheme.{u}` with their `Over (Spec (.of k))`
  structures. For each, `LocallyOfFiniteType` and `QuasiCompact` of the structure
  map express finite type over `k`.
- The morphisms are `(f : X ⟶ S)` and `(π : Y ⟶ X)`. The two `IsProper`
  instances express properness; `f.IsOver` and `π.IsOver` express that they are
  morphisms over the same field. Composition `π ≫ f` means the node's `fπ`.
- `(U : X.Opens)` gives the open subset, with canonical open immersion `U.ι`.
  `IsIso (pullback.snd π U.ι)` says exactly that the base change of `π` over
  `U` is an isomorphism. No density or surjectivity assumption is imposed.
- The reduced closed complement is presented invariantly as `(i : Z ⟶ X)`
  with `[IsClosedImmersion i]`, `[IsReduced Z]`, and
  `_hi : Set.range i.base = (U : Set X)ᶜ`. A reduced closed subscheme with
  this image is precisely the reduced induced closed structure, unique up to
  isomorphism over `X`. Thus this quantifies over presentations of the specified
  complement, rather than restricting to a privately chosen construction.
  `Z.Over` and `i.IsOver` equip it with its inherited field structure. The
  finite-type binders for `Z` are automatic mathematical consequences of the
  closed immersion into finite-type `X`; their explicit presence supplies the
  interface required by the recorded property `C`. They impose no further
  geometric restriction on the reduced complement.
- `(N : ℕ)`, `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` and `hX`, `hY`,
  `hS`, `hZ : IsSmoothBaseChangeCoefficients N Λ ...` give exactly the inherited
  fixed coefficient convention: positive `N`, finite commutative `Λ`,
  `(N : Λ) = 0`, and invertible constant section `N` on the schemes.
  The condition on `Z` is inherited by pulling back the invertible section
  along `i`; spelling it out is necessary to apply the recorded `C` interface
  and adds no restriction. No nonzero-ring assumption is made.
- `hπ : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f)` renders
  `C(fπ)`. `hi : HasConstructibleHigherDirectImages k N Λ hZ hS (i ≫ f)`
  renders `C(fi)`.
- The conclusion is the same recorded predicate
  `HasConstructibleHigherDirectImages k N Λ hX hS f`, exactly `C(f)`.
  Its definition quantifies over every `q : ℕ` and every constructible small
  etale module sheaf, and asks for constructibility of `higherDirectImage`.
  It includes degree zero and imposes no vanishing or uniform amplitude bound.

Statement dependencies read and used:

- `def-finrepair-property-c`: the full signature, docstring and body of
  `AlgebraicGeometry.Etale.HasConstructibleHigherDirectImages` in
  `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`. Its imported
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients` supplies
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`; that definition's
  full signature, docstring and body were also read.
- `def-weil-pbc-scheme-conventions`: its record is intentionally a convention
  with no declaration or module. Its prescribed Mathlib meanings are used:
  `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`,
  `IsClosedImmersion`, and the pullback. The relevant Mathlib declaration
  signatures and docstrings were inspected, as was `IsReduced` in
  `Mathlib.AlgebraicGeometry.Properties`.

All recorded proof-dependency modules are imported without `public`: constructible
pullback, the open-closed exact sequence, constructible extension by zero and
closed direct image, modification acyclicity, the composition spectral sequence,
the full long exact sequence, enough injectives, left exact direct image, and
constructible kernels/cokernels. The statement docstring records all seven
DAG proof steps, including the degree-zero case and the finite filtration
argument for the spectral-sequence collapse. No global proper-constructibility
theorem is imported (that theorem uses this item).

Edge cases checked before writing:

- `U = ⊥`: the pullback over the empty open is an isomorphism, and the complement
  is the reduction of `X`. No nonempty or dense-open binder excludes this case.
- `U = ⊤`: `π` is an isomorphism and `Z` is empty. The statement includes this
  case without a nonempty or proper-subset binder.
- Empty `X`, `Y`, `S` and `Z` are permitted whenever the stated maps exist.
- The zero coefficient ring is permitted; positivity concerns `N`, not the ring.
- Degree zero is included by the actual property `C`; the proof plan uses its
  initial exact segment and never asks for a negative derived functor.
- Nonreduced `X` and disconnected schemes are allowed. Only `Z` is reduced,
  exactly as in the statement. No dimension, smoothness, integrality, density,
  surjectivity or amplitude restriction was added.
- The site/coefficient size is the recorded `u + 1` convention, not a smaller
  independent coefficient universe.

Searches made on 2026-10-15:

- `msearch.py ... leanfinder "Proper modification isomorphism over open constructible
  higher direct images closed complement"`: eight hits, including scheme
  constructible images, topological constructibility, and module restriction
  functors; none state the etale higher-direct-image transfer.
- `msearch.py ... loogle 'AlgebraicGeometry.IsProper, "constructible"'`: zero hits.
- `msearch.py ... leansearch "Proper modification constructible higher direct image
  etale sheaves"`: service unavailable (Internal Server Error); no conclusion
  about presence or absence was drawn from that unavailable search.
- `msearch.py ... grep 'modification.*constructible|constructible.*modification'`:
  zero Mathlib hits.
- `rg` for `lem-finrepair-modification-c` in upstream `WeilConjectures`: no hits.
- `rg` for `HasConstructibleHigherDirectImages`, `constructible.*modification`, and
  `modification.*constructible` in upstream and `lean/Sheaf`: found the recorded
  predicate and sibling composition, projective, proper and finite-surjection
  statements, plus a proof-plan mention of this item in the proper theorem;
  no existing modification transfer declaration.
- `rg` for the proposed full declaration's short name in Mathlib, upstream,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing declaration.
- Mathlib's `Scheme.vanishingIdeal` docstring was also inspected: it confirms the
  reduced induced closed structure; the statement instead uses its equivalent
  reduced-closed-immersion presentation, so no additional notion is introduced.

Validation: `scompile.py NC lem-finrepair-modification-c` compiled the delivered
module cleanly, including its side-only modification-extension-zero import.
The only theorem is deliberately postponed by `sorry`. No statement dispute or
source correction is needed. `deliver2.py NC lem-finrepair-modification-c --no-push` printed OK: the
module compiles and passes preflight except for the independent second-reading
section, which the second reader must write. Nothing was pushed.

## Second reading by NC

Independent second reader, 2026-10-15. I opened the item node and its blueprint
source, both statement-dependency nodes, the complete recorded property-C and
coefficient declarations, and the delivered Lean module. The node is already
explicitly in the finite-type-over-a-field setting; the older blueprint paragraph
alone does not supply this setting. This delivery does not correct the node and
has no new nodes or dependency modules to audit.

Object, hypothesis and conclusion inventory, checked item by item:

1. A field k: `(k : Type u) [Field k]`. Exact; no characteristic, perfection or
   algebraic-closure assumption.
2. Schemes X, Y, S of finite type over this field: `{X Y S : Scheme.{u}}`, their
   `Over (Spec (.of k))` instances, and each pair `LocallyOfFiniteType` /
   `QuasiCompact` on its structure morphism. Exact under the scheme convention.
   I read the Mathlib class signatures in Morphisms/FiniteType, QuasiCompact and
   Proper; properness includes universal closedness and hence quasi-compactness.
3. Proper k-morphisms f and pi: `(f : X ⟶ S) (π : Y ⟶ X)`, `[IsProper f]`,
   `[IsProper π]`, and their `IsOver (Spec (.of k))` instances. Exact. The order
   `π ≫ f` is the source's f-pi composite.
4. An arbitrary open U in X: `(U : X.Opens)`. The projection
   `pullback.snd π U.ι` is Y-times-X-U to U, so its `IsIso` instance is exactly
   the requirement that pi is an isomorphism over U. Exact; no density or
   surjectivity has been inserted.
5. The reduced closed complement i:Z to X: `{Z : Scheme.{u}}`, `(i : Z ⟶ X)`,
   `[IsClosedImmersion i]`, `[IsReduced Z]`, and
   `_hi : Set.range i.base = (U : Set X)ᶜ`. Exact up to the unique isomorphism
   over X inherent in speaking of a closed subscheme. I independently checked
   Stacks `schemes.tex`, lemma-reduced-closed-subscheme and
   definition-reduced-induced-scheme: a closed subscheme with prescribed closed
   support is uniquely determined by reducedness. Mathlib Properties defines
   `IsReduced` by reduced rings of sections, matching lemma-reduced there;
   ClosedImmersion defines a closed embedding with surjective stalk maps.
   Thus this is not an arbitrary closed scheme structure or an unconstrained map.
6. The inherited field structure on Z is `Z.Over` with `i.IsOver`. Its two
   finite-type binders impose no additional geometric hypothesis: closed
   immersions are finite type, and composition with the finite-type structure
   map of X is finite type. The compatible structure map of Z is forced by i.
7. Fixed coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`
   with `hX`, `hY`, `hS`, `hZ : IsSmoothBaseChangeCoefficients N Λ ...`.
   I read the predicate body: `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧
   IsUnit (N : Γ(T, ⊤))`. This is precisely the inherited convention, using
   the same N and ring everywhere. The Z condition follows by pulling the unit
   section on X back along i; its explicit binder is needed by property C.
8. C(f-pi): `hπ : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f)`.
   Exact. C(f-i): `hi : HasConstructibleHigherDirectImages k N Λ hZ hS (i ≫ f)`.
   Exact; this uses the same closed immersion and coefficient ring.
9. Conclusion C(f): `HasConstructibleHigherDirectImages k N Λ hX hS f`.
   Exact. Opening the recorded definition confirmed the quantifiers
   `∀ (q : ℕ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
   Scheme.IsConstructibleEtaleModuleSheaf F → ...` on the actual
   `higherDirectImage Λ f (q : ℤ) F`. There is no degree bound, uniform
   vanishing, chosen sheaf, or interchange of quantifiers.

Edge cases: U empty gives the reduction of X and requires no dense open;
U all of X makes Z empty and pi an isomorphism. Empty schemes, including
empty Y when allowed by the isomorphism condition, are covered. X need not be
reduced, separated over k, connected or nonempty. Degree q=0 is included;
the seven-step proof docstring explicitly treats its initial exact segment.
N=0 is excluded by the source's positivity convention, not by an added
assumption. The zero coefficient ring is admitted and every characteristic
compatible with the invertibility convention is covered. There is no indexing
set or finite-family hypothesis. Universe u is arbitrary; the shared field and
scheme universe and coefficient/module universe u+1 follow the recorded
small-etale convention rather than imposing a new universe equality.

Independent searches used different words from the worker's searches:

- LeanFinder through msearch.py: "Localization by an open subscheme and its
  closed complement preserves constructibility of derived pushforwards under a
  proper map" returned eight results about constructible subsets and scheme
  images/preimages. None is an etale higher-direct-image transfer statement.
- Loogle through msearch.py: `"higherDirectImage"` returned zero hits.
- LeanSearch through msearch.py: "Constructibility of sheaf cohomology transferred
  by proper modification and localization" was unavailable (Internal Server
  Error); I draw no absence conclusion from that service.
- Direct rg on Mathlib/AlgebraicGeometry/Morphisms, upstream
  WeilConjectures/ConstructibleSheaf and project lean/Sheaf/AlgebraicGeometry,
  using `modification`, `HasConstructibleHigherDirectImages`, and both orders
  of `constructible` / `direct.image`, found neighboring finite-surjection and
  projective results, the recorded property C, and ModificationExtensionZero.
  None states this item. I also opened ConstructibleHigherDirectImage.lean:
  its `IsConstructibleHigherDirectImage` is another predicate on a general base,
  not the requested modification theorem or the item's recorded C declaration.
  The delivered theorem correctly uses the recorded HasConstructibleHigherDirectImages.

H5-H9: the delivery has no definitions, hence no hollow data. The sole theorem's
whole proof is sorry. The source/blueprint docstrings contain all seven node
proof steps, including spectral-sequence filtrations and degree zero. Public
imports supply statement notions; ordinary imports supply the recorded proof
plan. No private notion, local instance or notation is introduced. The explicit
universe and autoImplicit false leave no unbound parameter. The node's
lean.statement is the signature of the delivered theorem.

Mismatches found: none. Changes: appended this independent review only;
retained the correct Lean and node record unchanged. Validation: the prescribed
scompile.py compiled the delivered file cleanly (sandbox 3.2 seconds, library
3.4 seconds), with no errors or warnings. Delivery dry-run follows this review.
