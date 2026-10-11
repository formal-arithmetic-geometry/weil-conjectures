## Worker report

The module `Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification` states the Stacks Tag 07RZ
stratification theorem. It quantifies over schemes `X,S`, a morphism `f`, and the hypotheses
`[Flat f]`, `[LocallyOfFinitePresentation f]`, `[IsSeparated f]`, and
`hf : f.IsQuasiFinite`. It produces `Z : ℕ → Set S`; `Z 0 = ∅` represents `Z₋₁`, all `Z n`
are closed, and `Monotone Z` represents the increasing closed filtration. The local strata are
`strata r = Z (r+1) \\ Z r`, so they are pairwise disjoint and cover `Set.univ`.
For every scheme `T`, map `g : T ⟶ S`, and `r`, the projection `pullback.snd f g` is
`IsFiniteLocallyFreeOfDegree r` exactly when `Set.range g ⊆ strata r`. Finally each stratum
intersected with a compact (quasi-compact) open `W` is compact, rendering the quasi-compactness
of `S_r → S`.

The Lean hypotheses render flatness, local finite presentation, separatedness, and quasi-finiteness
with the dependency declarations listed below. `pullback.snd f g` is the chosen fibre product
projection. `Z 0 = ∅`, closedness, monotonicity, pairwise disjointness, covering, the universal
property, and compactness are the successive conjuncts of the conclusion. The index shift is
necessary because Lean's `ℕ` has no `-1`; it is definitionally the same filtration after naming
`Z 0` as the source's `Z₋₁`.

Dependencies used: `AlgebraicGeometry.Scheme` (Mathlib match for `def-pc-scheme`),
`AlgebraicGeometry.Flat` (Mathlib match for `def-weil-flat-morphism`),
`AlgebraicGeometry.LocallyOfFinitePresentation` (Mathlib match for
`def-sbc-locally-finite-presentation`), `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`
(`AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`),
`CategoryTheory.Limits.pullback` (Mathlib match for `def-pc-fibre-product`), and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
(`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`).

Edge cases checked: degree `r = 0`; empty strata; an empty scheme `T`; empty `S`; and arbitrary
(including empty) index sets are all admitted by the `ℕ`, `Set`, and scheme quantifiers. The
universal property uses the set-theoretic image `Set.range g`, as in the source.

Searches made: `msearch.py leanfinder` for “flat locally finitely presented separated quasi-finite
morphism stratification finite locally free constant degree” (hits only generic finite-presentation,
flatness, and local-constant-rank declarations; no stratification); `msearch.py loogle` for
`AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation` (no stratification; generic
flatness hits); `msearch.py leansearch` for “flat quasi-finite morphism admits closed stratification
finite locally free of each degree” (service unavailable); and `msearch.py grep` for
`stratif|finiteLocallyFree|IsFiniteLocallyFreeOfDegree` in `Mathlib/AlgebraicGeometry` (no hits).
`rg` over `WeilConjectures` and `lean/Sheaf` found no existing declaration of this theorem.

## Second reading by J1

I independently read the item node, its seven statement-dependency nodes, the delivered
module, and the actual declarations those dependencies record. The repository's literature
checkout is absent on this machine; I read the available Stacks source at
`/home/ubuntu/c1-stacks-review/more-morphisms.tex`, lines 12844–12899, and confirmed in
`/home/ubuntu/c1-stacks-review/tags/tags` that 07RZ is
`more-morphisms-lemma-stratify-flat-fp-qf`. The chapter introduction and the surrounding
section impose no standing field, Noetherian, or other assumptions. The source's four
hypotheses and both parts of its conclusion agree with the node. There is no statement
correction or new/dependency node in this delivery.

The object/hypothesis/conclusion inventory and its Lean rendering follow. Every entry passes.

| Node item | Lean rendering and reading |
| --- | --- |
| Arbitrary schemes X and S and a scheme morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)`. Mathlib's `Scheme` is a locally ringed space locally isomorphic to spectra; its `Hom` is a morphism of locally ringed spaces. No extra object structure. |
| Flat f | `[Flat f]`. I read the class and `Flat.iff_flat_stalkMap` in Mathlib's `Morphisms/Flat.lean`: this is flatness of every local-ring map, as def-weil-flat-morphism requires. |
| Locally of finite presentation f | `[LocallyOfFinitePresentation f]`. The class in `Morphisms/FinitePresentation.lean` requires finite-presentation maps on affine opens, the existing Mathlib match recorded by def-sbc-locally-finite-presentation. No global finite-presentation hypothesis is added. |
| Separated f | `[IsSeparated f]`. The class in `Morphisms/Separated.lean` requires the diagonal to be a closed immersion, exactly the convention node's separatedness clause. |
| Quasi-finite f | `(hf : f.IsQuasiFinite)`. I read `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: this is locally finite type AND quasi-compact AND every singleton `{f.asFiber x}` open in the scheme fibre. This is finite type with isolated fibre points, exactly pqf-def-quasifinite, rather than Mathlib's weaker local predicate. |
| Increasing closed subsets indexed from -1 with empty first term | `∃ Z : ℕ → Set S`, `Z 0 = ∅`, `∀ n, IsClosed (Z n)`, `Monotone Z`. Lean's Z n is the paper's Z_(n-1), so no initial term is omitted. Subset monotonicity permits equality, as the source does. |
| Degree-r stratum is Z_r minus Z_(r-1) | `let strata := fun r => Z (r + 1) \ Z r`. This is exactly the same difference under the index shift. Locally closedness follows from the closed terms, without extra subscheme data. |
| All strata disjoint and covering S | `Pairwise (fun r t => Disjoint (strata r) (strata t))` and `(⋃ r, strata r) = Set.univ`. Neither a finite partition nor eventual stabilization is required. |
| Every test scheme T and morphism g:T→S, for each r≥0 | `∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ)`. These quantifiers are inside the one existential filtration. The harmless order of the universal r binder does not change the property. |
| Base-change projection X×_S T→T | `pullback.snd f g`. I read `pullback`, `pullback.snd`, and the scheme pullback match; the second projection targets T, not X. |
| Projection finite locally free of degree r iff g(T) lies in S_r | `(pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔ Set.range g ⊆ strata r`. I read `FiberDegree.lean`: the class extends `IsFiniteLocallyFree`, which extends finiteness, flatness, and local finite presentation; `fiberDegree_eq` requires `Module.finrank` of the global sections of each scheme-theoretic fibre over its residue field to equal r. The class has no hidden affine/field/reduced-base hypothesis. This is length/dimension, not the number of fibre points. `Set.range g` uses the underlying point map; the containment is set-theoretic, not scheme-theoretic factorization. |
| Each S_r→S quasi-compact | `∀ r (W : S.Opens), IsCompact (W : Set S) → IsCompact (strata r ∩ (W : Set S))`. This is exactly the node's stated equivalent formulation. Mathlib's `IsCompact` is open-cover compactness and assumes no Hausdorff condition, so it means quasi-compactness here. |

Edge cases: r=0 gives `strata 0 = Z 1 \ Z 0`, hence the paper's Z_0; no
positive-rank condition appears. Empty strata are allowed. For empty T, the image
containment is true for every r and the fibre-degree condition is vacuous; the empty
base change is finite locally free, so the biconditional has the correct meaning.
For empty S all Z and strata can be empty, the covering equality remains valid,
and all test schemes mapping to it are empty. For empty X over nonempty S, degree
zero is the whole base and higher strata are empty. The indexing set is necessarily
ℕ, as the node specifies, but any or all indexed strata may be empty. The empty
open W is allowed. No characteristic, field, nonempty, integral, reduced, Noetherian,
quasi-separated-base, or global bounded-degree condition is assumed. The universe u
is declared and arbitrary; X, S, and every test T inhabit the same ambient category
of schemes, as the recorded pullback and degree notions require. Residue-field test
schemes fit that universe; the universal property is not vacuous for size reasons.

Independent searches (different wording from the worker):

- LeanFinder via msearch: "Increasing closed subsets classify the rank of base changes
  of a separated flat quasifinite map" returned module rank/base-change lemmas,
  including `Module.rankAtStalk_baseChange`, not a scheme stratification theorem.
- Loogle via msearch: `"stratification"` returned no hits.
- Mathlib grep via msearch, AlgebraicGeometry:
  `stratification|closed.*filtration|degree.*strat|strat.*degree` returned no hits.
- LeanSearch via msearch: "A flat separated quasi-finite morphism has rank strata
  characterized by finite locally free base change" was unavailable (HTTP internal
  server error); no negative mathematical verdict is inferred from that failure.
- The same independent rg search over WeilConjectures and the project's lean/Sheaf
  found finite constructible-sheaf stratifications, generic-flatness remarks, and
  unrelated Weil-sheaf stratifications, but no theorem with this universal property.
  I opened `WeilConjectures/Topology/Stratification.lean`: its bundled stratification
  has finitely many `Fin n` strata and therefore cannot render this potentially
  infinite degree-indexed filtration. Existing notions used by this statement are
  imported rather than redefined; the local `let strata` just names set differences.

H5/H6/H8/H9: no definition with sorry, no auxiliary proof, and precisely one named
theorem with proof `by sorry`. Both module and declaration docstrings identify Tag
07RZ and the exact blueprint id. I matched the ten numbered docstring proof steps
against the ten node steps, including affine-local gluing, locality of fixed degree,
descent to finitely generated ideals, induction on the complements, and the final
closed-subset argument. Both imports are used. No line exceeds 100 characters;
all variables and the sole universe are explicitly bound. The node's lean.statement
is verbatim the source signature through the conclusion, excluding `:= by`.

Mismatches and changes: none in the Lean or node. The worker report is preserved;
this independent reading and its searches are the only additions.
