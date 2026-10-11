## Worker report

The module `Sheaf.AlgebraicGeometry.GrothendieckExistenceProper` states
`AlgebraicGeometry.grothendieck_existence_proper`, with `sorry` as its only proof.
It says exactly that the already defined completion functor is an equivalence.
No new notions, dependency modules, statement corrections, or disputed statements are needed.

Source read: Stacks Proposition 088C, https://stacks.math.columbia.edu/tag/088C
(the local Stacks checkout is absent). It agrees with the DAG statement. Its proof is
rendered step by step in the declaration docstring, following the node's eight steps.

Hypothesis and clause correspondence:

- The commutative Noetherian ring is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- Its ideal is `(I : Ideal A)`; completeness, including separatedness, is
  `[IsAdicComplete I A]`, the recorded dependency declaration. This is equivalent to
  bijectivity of `AdicCompletion.of I A` by `AdicCompletion.of_bijective_iff`.
- The scheme and the named structure morphism are `(X : Scheme.{u})` and
  `(f : X ⟶ Spec (CommRingCat.of A))`; properness is `[IsProper f]`.
- The ideal I O_X is
  `((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)`.
  The kernel ideal sheaf of the closed immersion Spec(A/I) → Spec(A) is precisely
  the quasi-coherent ideal associated to I. Its `comap f` is the extended ideal,
  i.e. the image of the pulled-back ideal in O_X. No arbitrary ideal is substituted.
- The source category is the recorded `CoherentModules X`: the full subcategory
  of `X.Modules` with predicate `RingedSpace.IsCoherent X.toRingedSpace`.
- The target category is the recorded `CoherentFormalModule X` at this ideal:
  coherent inverse systems with the required annihilation and quotient isomorphisms.
  Positive level n+1 is indexed by `op n`, exactly as in the dependency module.
- The object assignment F ↦ F^ and its map assignment are the existing `completion`:
  actual cokernel quotients F/I^(n+1)F and canonical reductions of module maps.
- The conclusion `.IsEquivalence` has fields `faithful`, `full`, `essSurj` in
  Mathlib's `Functor.IsEquivalence`. Thus it includes full faithfulness and that
  every formal object is isomorphic to the completion of some coherent module,
  exactly the two clauses explaining equivalence in the node. Those clauses are
  not duplicated as additional conjuncts.
- `@completion X (isNoetherian_of_locallyOfFiniteType f)` explicitly supplies the
  derived Noetherian structure on X using the existing source theorem. Properness
  supplies finite type/quasi-compactness and Spec(A) is Noetherian. There is no
  added `[IsNoetherian X]` hypothesis, `let`, hidden `show`, or local instance.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (ring as its own module).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  used through the source full subcategory in the next module.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentModules`,
  `CoherentFormalModule`, `completion`; full signatures and defining quotients,
  system conditions, and map assignments were read.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`, supplying a proof needed
  by the completion definition, not a new definition or additional hypothesis.

Edge cases checked mathematically before writing:

- I=0: completeness holds for every ring; completion is the constant coherent
  system, and the formal conditions require all transitions to be isomorphisms.
- I=A: completeness forces A to be the zero ring (Hausdorffness); Spec(A), and
  therefore any scheme mapping to it, is empty. Both categories are trivial.
- Empty X and zero modules are included with no nonemptiness assumptions.
- General complete Noetherian rings are covered: neither localness nor a
  characteristic restriction appears. The ideal need not be maximal or nonzero.
- There is no positive-index boundary error: the dependency uses n+1, n : ℕ.
- A and X share the ambient universe of schemes, which can be enlarged to include
  any ring and scheme in question. No independently smaller testing universe or
  unbound implicit variables occurs; `universe u` is explicit.

Searches made for an existing statement:

- `msearch.py ... leansearch "Grothendieck existence equivalence coherent sheaves
  formal completion proper scheme"`: service unavailable (Internal Server Error).
- `msearch.py ... leanfinder "Grothendieck existence theorem proper scheme complete
  Noetherian ring completion coherent modules equivalence"`: 8 hits, comprising
  limit-section lemmas, condensed module constructions, and
  `AdicCompletion.of_bijective_iff`; none states scheme-level existence.
- `msearch.py ... loogle "Functor.IsEquivalence, IsAdicComplete"`: 0 hits,
  unknown identifier `Functor.IsEquivalence`; its actual declaration was then
  read directly from Mathlib/CategoryTheory/Equivalence.lean.
- `msearch.py ... grep "Grothendieck|completion.*IsEquivalence" AlgebraicGeometry`:
  25 displayed hits about Grothendieck topologies/abelian categories; no match.
- `rg` for Grothendieck/existence_proper/completion equivalence in Mathlib,
  WeilConjectures, and lean/Sheaf: no matching existence theorem; numerous
  unrelated Grothendieck-abelian/site hits. The coherent formal module gives
  the definitions but does not state this theorem.
- Exact item-id grep in WeilConjectures: no hits. Name grep for
  `grothendieck_existence_proper` and `completion_isEquivalence` in
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no hits.
- `tools/lean_names_upstream.py show` was consulted for the item: no attachment.
- Ideal sheaf constructors and Noetherian structure theorems were searched and
  read directly; existing `Hom.ker`, `IdealSheafData.comap`, and the finite-type
  theorem suffice, so no duplicate notion is introduced.

Validation: `scompile.py C1 prop-weil-pbc-grothendieck-existence-proper` compiled
this module on the server in 2.6 seconds, exit 0, with no warnings or errors.
The node copy changes only `lean`, records the signature verbatim, and retains
one-space JSON indentation, Unicode, and a final newline.

## Second reading by C1

I independently opened the node copy and `GrothendieckExistenceProper.lean` and matched the statement in order:

- The Noetherian base ring is `(A : Type u) [CommRing A] [IsNoetherianRing A]`, rendering the node's Noetherian ring.
- The ideal is `(I : Ideal A)` and `[IsAdicComplete I A]`, rendering completeness for the same ideal with no locality, nonzero, or characteristic assumption.
- The scheme is `X : Scheme.{u}` and the named structure morphism is `f : X ⟶ Spec (CommRingCat.of A)`, with `[IsProper f]`; this is the node's proper A-scheme.
- The ideal on X is `((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)`. This is the kernel ideal sheaf of `Spec(A/I) -> Spec A`, pulled back along f, hence the extended ideal `I O_X` required by the node (the recorded `IdealSheafData.comap` declaration was read).
- `@completion X (isNoetherian_of_locallyOfFiniteType f) (...)` is the recorded completion functor. Its source is `CoherentModules X`, the full subcategory of coherent X-modules; its target is `CoherentFormalModule X (...)`, whose levels are indexed by `op n` and use the required annihilation and quotient-isomorphism conditions. The dependency definition was read, including its quotient `F/I^(n+1)F` and map assignment.
- The conclusion `.IsEquivalence` is exactly categorical equivalence, including full faithfulness and essential surjectivity, with no duplicated or weakened clause.

No mismatch was found and no source or node change was needed. The explicit Noetherian instance argument is an implementation term for the completion definition, not an extra hypothesis. Universes are shared (`A`, `X`, and the morphism use `u`), so no test universe is inadvertently excluded.

Edge cases checked: `I = 0`, `I = ⊤`/the zero-ring situation, empty X, zero coherent modules, arbitrary (including nonmaximal and nonzero) ideals, and all positive levels `n+1`; no nonemptiness, characteristic, localness, or positive-index hypothesis is added. The statement also permits the empty scheme and zero objects covered by the source.

Searches were rechecked with `rg` over `lean/Sheaf`, Mathlib, and `WeilConjectures`, plus the worker's LeanSearch, LeanFinder, and Loogle queries recorded above. They found only the existing completion and coherent-formal-module definitions and unrelated equivalences; no existing Grothendieck-existence theorem. The source citation is Stacks Proposition 088C (coherent.tex, section 0886), which agrees with the node and signature.

Validation: `scompile.py C1 prop-weil-pbc-grothendieck-existence-proper lean/Sheaf/AlgebraicGeometry/GrothendieckExistenceProper.lean` exits 0 with no warnings other than the permitted `sorry` proof status.
