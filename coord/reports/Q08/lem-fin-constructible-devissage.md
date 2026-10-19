## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleSheafDevissage` states
`AlgebraicGeometry.Etale.exists_constructible_sheaf_devissage`, with its entire proof `sorry`.
It introduces no definitions, helper theorems, new nodes, or dependency repairs. The node is
unchanged except for its `lean` record. All variables and universes are explicit.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`.
- X a scheme of finite type over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and `[QuasiCompact (X ↘ Spec (.of k))]`.
  Finite type is exactly the conjunction recorded by def-weil-finite-type-morphism.
- The finite commutative coefficient ring and its coefficient convention:
  `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` and
  `hΛ : IsSmoothBaseChangeCoefficients N Λ X`. Unfolding that recorded predicate says
  `0 < N`, `Finite Λ`, `(N : Λ) = 0`, and `IsUnit (N : Γ(X, ⊤))`.
  The explicit Finite instance supplies the instance parameter of the constructibility
  predicate; it repeats precisely the same finiteness fact, with no extra restriction.
- F is a constructible Λ-module sheaf on the small étale site:
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. This is the recorded finite-constant-value
  notion, not the distinct upstream `IsConstructibleSheaf` predicate.
- A finite filtration by subsheaves: `∃ (m : ℕ) (S : Fin (m + 1) → Subobject F)`.
  `IsZero (S 0 : Sheaf ... (ModuleCat Λ))` states F₀ = 0; a subobject with zero underlying
  object is exactly the zero subsheaf. `S (Fin.last m) = ⊤` states Fₘ = F as a subsheaf.
  `hS : ∀ r : Fin m, S r.castSucc ≤ S r.succ` states each successive inclusion.
  Adjacent inclusions are equivalent to an increasing chain on this finite linear order.
- For every r = 1,...,m: `∀ r : Fin m`, with `r.castSucc` and `r.succ` denoting r−1 and r
  in the displayed one-based mathematical indexing.
- Locally closed constructible subschemes: `∃ (T : Scheme.{u}) (j : T ⟶ X)`,
  `IsImmersion j` and `Topology.IsConstructible (Set.range j)`. The former is Mathlib's
  locally closed immersion (locally closed image, embedding, surjective stalk maps).
- The specified scheme-theoretic closure and factorization are the canonical Mathlib
  `j.image = j.ker.subscheme`, `j.toImage : T ⟶ j.image` and
  `j.imageι : j.image ⟶ X`. The latter is a closed immersion, and their composite is j
  (`Scheme.Hom.toImage_imageι`). `∃ (_ : IsOpenImmersion j.toImage)` asserts the open
  immersion into this closure. Since X is finite type over a field, it is Noetherian;
  its immersed subschemes and these maps are quasi-compact, so the kernel construction
  is the kernel of the structure-sheaf restriction, precisely the stated closure.
  The closedness and composite equality are supplied by the construction, not extra
  arbitrary factorization data or an assumed comparison map.
- Lisse Λ-sheaves on each T: `L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`
  with `Scheme.IsFiniteLocallyConstantSheaf L`. This is locally constant with finitely
  generated stalks, hence finite stalks over the finite ring Λ, as the node requires.
- The quotient is `cokernel (Subobject.ofLE (S r.castSucc) (S r.succ) (hS r))`.
  Its required isomorphism is expressed by `Nonempty ( ... ≅ ... )`.
  The right side is exactly `(lowerStar (ModuleCat Λ) j.imageι).obj
  ((openImmersionLowerShriek (ModuleCat Λ) j.toImage).obj L)`, that is i_* u_! L
  for the specified scheme-theoretic closure factorization. No splitting is asserted.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, extension by zero on module-valued
  small étale sheaves (public import).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, with the section formula on the base-changed
  étale object (publicly imported through the preceding module).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`. The first two notions
  and the immersion characterization come from the dependency's recorded Mathlib API.
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients` (public import).
- `Field` from Mathlib; `LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` is publicly imported through
  SmoothBaseChangeCoefficients, as required by def-weil-pbc-constructible-complexes.
  Its public dependency `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
  defines `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
  `WeilConjectures.ConstructibleSheaf.Defs` supplies
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`, recorded by the definition
  node that def-weil-pbc-constructible-complexes cites for lisse sheaves.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible` (publicly available
  through the constructibility dependency).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`, `imageι`,
  `toImage`; `Mathlib.CategoryTheory.Subobject.Limits`: `Subobject`, `Subobject.ofLE`,
  and the cokernel API. These are existing canonical constructions, not new notions.

Recorded proof dependencies that have modules are imported non-publicly:
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`WeilConjectures.SixFunctors.OpenClosed.Exact`,
`WeilConjectures.ConstructibleSheaf.Pullback`,
`Sheaf.AlgebraicGeometry.OpenClosedRecollement`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.
`fin2-lem-lisse-dense-open` has no recorded Lean declaration/module yet, so no import
can be added for it. It is only a proof dependency, not needed to type this statement.
The docstring gives every proof step, including the closure comparison and indexing.

Edge cases checked:

- m = 0 is allowed: Fin 0 has no factors, and the endpoints say that F is zero.
- The empty scheme and the zero sheaf therefore admit the length-zero filtration.
- The zero coefficient ring is allowed (no Nontrivial Λ hypothesis); N = 1 is allowed
  when the coefficient convention holds. No characteristic restriction beyond that
  convention is introduced.
- The filtration inclusions are not strict, as in the node's proof when a zero term
  occurs. The factors need not be nonzero, and the filtration need not split.
- No disjointness, reducedness, density in all components, or smoothness is added to
  the strata. Nonreduced structure is retained by `j.ker.subscheme`, not replaced by
  the reduced topological closure.
- Sites use Scheme.{u} with coefficient modules and the ring Λ in universe u+1,
  matching the recorded constructibility and six-functor declarations.

Searches for an existing declaration (2026-10-16):

- msearch.py leanfinder: "finite filtration of a constructible etale module sheaf by
  extensions by zero of finite locally constant sheaves on locally closed subschemes".
  Eight hits, all generic SheafOfModules finite-type/generator predicates and lemmas;
  none states this devissage.
- msearch.py loogle: "Subobject, cokernel, IsFiniteLocallyConstantSheaf".
  Zero hits; service reports unknown identifier Subobject.
- msearch.py grep, Mathlib/AlgebraicGeometry:
  "constructible.*(filtration|devissage)|devissage.*constructible|scheme.theoretic.*image".
  Seven hits identify the canonical scheme-theoretic image API; no sheaf devissage.
- msearch.py leansearch: "constructible sheaf admits finite filtration by extensions
  by zero of lisse sheaves". Service unavailable (Internal Server Error).
- rg over upstream WeilConjectures and side lean/Sheaf for
  "lem-fin-constructible-devissage|constructible.*[Ff]iltration|constructible.*[Dd]evissage"
  found a distinct prime-field filtration used for curve arguments, not geometric
  locally closed lisse factors. Additional devissage/filtration searches in
  WeilConjectures/ConstructibleSheaf also found only the lisse p-group filtration.
- rg for the new full declaration name over Mathlib, WeilConjectures and lean/Sheaf
  found no collision.

Validation: compiled using the prescribed scompile.py wrapper. The first draft used
`S 0 = ⊥`; finding the bottom-subobject instance exceeded the default typeclass search
budget. The final statement uses the equivalent direct zero-object characterization
above, with no timeout setting changed. Final dry-run result is recorded below.

No statement fault or mathematical dispute was found.

## Second reading by Q08

I independently read the DAG node, its five proof steps, the sandbox module, and the
recorded statement-dependency declarations. I also read the blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-constructible-devissage.md`, the unit section,
and `sbc-def-coefficient-conventions.md` from the project literature on the server
(the literature documents are absent from this machine's shared checkout). For the
underlying sheaf notions I read Stacks `etale-cohomology.tex`,
`definition-constructible` (095E) and
`lemma-constructible-quasi-compact-quasi-separated` (095F); for the induction I read
`lemma-ses-associated-to-open` (095L). Stacks assumes a Noetherian coefficient ring
for its module constructibility clause; the stipulated finite commutative ring
supplies this. The finite-type scheme is Noetherian, so the global finite partition
in the recorded definition agrees with the source's affine-local condition. The
source adds no separatedness, smoothness, reducedness, or algebraic-closedness
hypothesis to this lemma.

Here is my object, hypothesis, and conclusion checklist, in the node's order.
Every row passes.

| Node clause | Lean rendering and verdict |
| --- | --- |
| A field k | `(k : Type u) [Field k]`: exactly a field, with no closure or characteristic hypothesis. Pass. |
| X a finite-type k-scheme | `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and the two instances `LocallyOfFiniteType (X ↘ Spec (.of k))`, `QuasiCompact (X ↘ Spec (.of k))`. This is precisely the finite-type conjunction recorded in `def-weil-finite-type-morphism`. Pass. |
| Positive N and finite commutative coefficients annihilated by N, with N invertible on X | `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` and `hΛ : IsSmoothBaseChangeCoefficients N Λ X`. I opened its real definition: `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(X, ⊤))`. The Finite instance repeats the finiteness fact needed by the sheaf API; it adds no restriction. Pass. |
| F a constructible Λ-module sheaf on the small etale site | `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. I read this predicate, its finite locally closed stratification, etale trivializations and finite constant module values, and the public imports through `BoundedConstructibleComplexes`. This is the dependency's recorded constructibility notion. Pass. |
| A finite filtration by subsheaves | `∃ (m : ℕ) (S : Fin (m + 1) → Subobject F)`. All terms are subobjects of this same F, so their arrows are subsheaf inclusions. Pass. |
| Initial term zero and final term F | `IsZero (S 0 : Sheaf ...)` and `S (Fin.last m) = ⊤`. The first says the initial subobject has zero underlying object, hence is the zero subsheaf; the second is equality as subobjects of F. Pass. |
| Increasing successive terms | `∃ hS : ∀ r : Fin m, S r.castSucc ≤ S r.succ`. Adjacent inequalities give the entire finite increasing chain. Strictness is not imposed. Pass. |
| Each quotient has its own locally closed constructible subscheme | After choosing the chain, `∀ r : Fin m, ∃ (T : Scheme.{u}) (j : T ⟶ X), IsImmersion j ∧ Topology.IsConstructible (Set.range j) ∧ ...`. I read `IsImmersion` and its closed-then-open factorization theorem, and `Topology.IsConstructible` as the Boolean algebra generated by open retrocompact sets. The order of choices is correct. Pass. |
| Factor through the scheme-theoretic closure, first openly and then closedly | `j.image`, `j.toImage`, `j.imageι`, and `∃ (_ : IsOpenImmersion j.toImage)`. I read `Hom.image := j.ker.subscheme`, `Hom.ker`, `Hom.ker_apply`, the construction of `Hom.toImage`, and `Hom.toImage_imageι`. The image inclusion is the canonical closed subscheme inclusion. Since an immersion into Noetherian X is quasi-compact, `Hom.ker_apply` gives exactly the structure-sheaf kernel of the node; Mathlib's `IsImmersion` instance proves `IsOpenImmersion j.toImage` for a quasi-compact immersion. Thus the explicit open-immersion witness imposes no extra mathematical restriction. Pass. |
| A lisse sheaf on each stratum | `L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` with `Scheme.IsFiniteLocallyConstantSheaf L`. I opened the recorded class: it extends locally constant and finite sheaves, where module stalks are finitely generated. Over finite Λ those stalks are finite, exactly the lisse condition in `def-weil-pbc-constructible-complexes`. Pass. |
| Quotient is the specified locally closed extension | `Nonempty (cokernel (Subobject.ofLE (S r.castSucc) (S r.succ) (hS r)) ≅ (lowerStar (ModuleCat.{u + 1} Λ) j.imageι).obj ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j.toImage).obj L))`. I read `Subobject.ofLE`, the actual upstream `lowerStar` section formula and `openImmersionLowerShriek` construction. The cokernel is the adjacent subobject quotient; for zero-based `r = q`, it is the mathematical factor numbered q+1. The right side is exactly i_* u_! L, using the canonical closure, and existence of an isomorphism is all the node asserts. Pass. |
| Filtration need not split | There is no splitting, semisimplicity, nonzero-factor, disjoint-support, or frontier condition in the conclusion. Pass. |

Edge cases and size checks:

- `m = 0` is permitted. `Fin 0` makes the factor requirements empty, while the
  coinciding endpoints require F itself to be zero. Zero F and the empty scheme
  are therefore covered by the length-zero case.
- Zero factors and repeated subobjects are permitted; no nonemptiness is required
  for a stratum. No choice of geometric point is required by the statement.
- There is no `Nontrivial Λ` assumption, so the zero coefficient ring is covered.
  N = 0 is excluded precisely by the source convention, not by an accidental
  binder. N = 1 is allowed when that convention holds. The only characteristic
  restriction is invertibility of N on X; k need not be perfect or algebraically
  closed.
- Nonreduced strata and nonreduced closures are covered: `j.ker.subscheme` retains
  the scheme-theoretic kernel rather than taking a reduced topological closure.
  A disconnected or nonseparated finite-type X is also covered.
- The explicit universe u is arbitrary. X, k and the immersed schemes are in u;
  coefficient modules and Λ are in u+1, as in all the recorded small-etale sheaf
  APIs used here. There is no independent lower test-object universe and no
  equality between unrelated universes. The finite index types are `Fin` types,
  so no family-size restriction is being introduced. All variables are bound.

Independent searches, using different queries from the first reader:

- `msearch.py ... leanfinder`: "A sheaf on the small etale site is an iterated
  extension of local systems supported on constructible locally closed subschemes".
  Eight hits: small/big etale topology definitions and unrelated condensed or
  quasicoherent sheaf constructions. No matching devissage theorem.
- `msearch.py ... loogle`: `CategoryTheory.Subobject.ofLE`. Twelve hits, including
  its actual signature and mono/composition lemmas. These confirm the quotient
  interface, but none is the constructible-sheaf theorem.
- `msearch.py ... grep`: `lisse|locally.*closed|filtration`, restricted to
  `Constructible`. Zero Mathlib hits.
- `msearch.py ... leansearch`: "Every constructible etale sheaf of modules has a
  finite chain of subobjects whose factors are local systems extended from locally
  closed supports". The service returned Internal Server Error; this is an
  unavailable search, not evidence of absence.
- I independently used `rg` for `filtration`, `iterated.extension`, and both
  spellings of devissage in upstream `WeilConjectures/ConstructibleSheaf` and
  project `lean/Sheaf/AlgebraicGeometry`, and searched Mathlib, upstream and the
  side library for the full proposed name and finite-sheaf-filtration phrases.
  I opened the plausible alternatives: upstream
  `ConstructibleSheaf/OpenClosed.lean` states constructibility iff the open and
  closed restrictions are constructible, not a finite filtration; project
  `LocallyConstantCoverFiltration.lean` gives constant prime-field quotients after
  a finite etale cover; `Curve/PrimeFieldFiltration.lean` concerns coefficient
  prime-field extensions. None states this geometric devissage on X. The full
  proposed declaration name has no existing collision.

No new nodes or dependency modules were supplied by the first worker, and none
is needed. There is no `statement_change`: the node and the Lean both agree with
the source. The source's locally closed extension shorthand is made explicit by
the already recorded node's closure convention, which the Lean follows exactly.
I found no mathematical or interface mismatch and retained the Lean and node
records without alteration. I added only this independent reading to the report.

H5/H6/H8/H9 checks: the module introduces exactly one theorem and no definition,
helper, private copy or axiom; its entire proof is `sorry`. Both docstrings name
the source and blueprint id. The theorem docstring follows the node's five proof
steps: dimension induction, open-closed exact sequence, closed pushforward,
closure comparison, and inverse-image filtration with cokernel quotients. Its
statement and proof imports account for the recorded declarations; the sole
unstated proof dependency is `fin2-lem-lisse-dense-open`, which is not needed to
type the statement. There is no file-local notation or instance. The maximum
Lean line length is 91, and the node's `lean.statement` is verbatim equal to the
file's signature.

Validation: the prescribed `scompile.py Q08 lem-fin-constructible-devissage`
compiled the sole delivered module successfully, both in its sandbox context and
as the library module. There were no errors or warnings. The prescribed
`deliver2.py Q08 lem-fin-constructible-devissage --no-push` then printed OK:
the delivery passed preflight and compiled successfully.
