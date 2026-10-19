## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProperDirectImageComparisonFinitude.lean`
states `AlgebraicGeometry.Etale.properDirectImage_comparison_finitude`, with its proof
left as `sorry`. It introduces no definition and makes no node correction. The source
blueprint file `sec-smooth-purity/sk-prop-sf-cbc/obl-fin-comparison.md` was read from the
project server because the untracked literature is absent from the shared source mirror.
Its two clauses agree verbatim with the DAG statement. The declaration docstring carries
all four DAG proof steps, including the explanation of module-linear sheaf vanishing.

Hypotheses, clause by clause:

- The field is `(k : Type u) [Field k]`.
- The positive integer N, the finite commutative coefficient ring killed by N, and the
  prime-to-characteristic condition are `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]` and `hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`.
  Unfolding the recorded definition gives `0 < N`, `Finite Λ`, `(N : Λ) = 0` and
  `IsUnit (N : Γ(Spec (.of k), ⊤))`. The last condition, under the canonical
  global-sections isomorphism for an affine spectrum, says that N is invertible in k;
  for a field this is precisely the intended prime-to-characteristic condition,
  including characteristic zero. Killing 1 in the coefficient ring kills every
  module section. The separate `Finite Λ` instance supplies the typeclass required
  by the recorded constructibility predicate and adds no mathematical assumption.
  Applying the coefficient predicate to Spec k preserves this condition even when
  S is empty; invertibility on every k-scheme follows by pullback.
- `S` of finite type over k is `[S.Over (Spec (.of k))]` with
  `[LocallyOfFiniteType (S ↘ Spec (.of k))]` and
  `[QuasiCompact (S ↘ Spec (.of k))]`. There is no assumption that S is separated.
- The proper morphism is `(f : X ⟶ S) [IsProper f]`. X need not carry a separately
  supplied k-structure: the composite through S gives it canonically.
- The nonnegative fibre bound is `(d : ℕ)`. The hypothesis `hfib` quantifies over
  every `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)` and requires
  `topologicalKrullDim ↥(pullback f s) ≤ (d : WithBot ℕ∞)`. These are exactly the
  geometric fibres. The WithBot codomain retains the empty fibre of dimension bottom.
- The sheaf is `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. This is the finite-value
  constructibility notion of the recorded dependency, rather than the distinct
  upstream predicate defined using finite generation of geometric stalks.

Conclusions, clause by clause:

- Clause (i) quantifies over every `q : ℕ` and every geometric point `s` as above.
  The first conjunct is exactly the presentation of the comparison supplied by
  `geometricFiber_finite_stalk_formula`: `sourceIso` identifies the global sections
  of `baseChangeSourceFunctor Λ s f q` with the geometric stalk of
  `higherDirectImage Λ f q F`; `targetIso` identifies the global sections of
  `baseChangeTargetFunctor Λ (pullback.fst f s) (pullback.snd f s) q` with the
  ordinary module-valued cohomology of the fibre with F pulled back by `upperStar`.
  `IsIso (sourceIso.inv ≫ Γ.map (baseChangeHomologyMap Λ
  (IsPullback.of_hasPullback f s) q F) ≫ targetIso.hom)` is the comparison assertion.
  Thus the middle arrow is the specified degree-q exchange map of the dependency,
  with the dependency's two endpoint identifications; no unrelated morphism or new
  choice of a comparison map is introduced.
- The next conjunct, `Finite ((cohomology (ModuleCat.{u + 1} Λ)
  (pullback f s) q).obj (...))`, says that each fibre-cohomology group is a finite
  Λ-module. The group already is an object of ModuleCat Λ, and `Finite` asserts
  finiteness of its underlying set, hence also finite generation over Λ.
- The last conjunct of (i) is `2 * d < q → IsZero` of that same cohomology object.
  It expresses precisely vanishing for q > 2d.
- Clause (ii) is the second outer conjunct: for every `q : ℕ`,
  `Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f q F)` and
  `2 * d < q → IsZero (higherDirectImage Λ f q F)`. This is constructibility for
  every nonnegative degree and vanishing as a module sheaf above 2d. IsZero gives
  equality to the zero object in the intrinsic categorical sense, without requiring
  an arbitrary equality of bundled sheaves.

Recorded statement dependencies used:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`,
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`,
  `AlgebraicGeometry.Etale.isIso_geometricFiber_finite` and
  `AlgebraicGeometry.Etale.geometricFiber_finite_stalk_formula`. Both complete
  signatures and proof docstrings were read through `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, which uses the
  publicly imported `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` of
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`. Both definitions were
  read; only the underlying sheaf predicate is needed for this node.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, through the existing `higherDirectImage`
  construction in `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`.
  The latter is homology of bounded-below derived direct image on F in degree zero;
  its definition and the base-change source, target, and arrow definitions were read.
- `Mathlib.CategoryTheory.Sites.Point.Basic`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, specialized with
  `AlgebraicGeometry.Scheme.pointSmallEtale` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. The full constructions were inspected:
  the fibre category consists of pointed etale neighbourhoods and sheafFiber is
  the associated presheaf colimit restricted to sheaves.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration or
  module. Its meanings are rendered by Scheme, IsProper, LocallyOfFiniteType,
  QuasiCompact, pullback and the field-valued geometric point, using Mathlib.

All stated proof dependencies have their modules imported. The property C and proper
constructibility modules, constructible-module finite-stalk lemma, fibrewise dimension
bound, upstream constructible pullback, finite-sheaf predicate, and geometric-stalk
conservativity supply the proof route. `lem-weil-pbc-proper-fp-permanence` has no recorded
Lean module; its proper-base-change content is already available in the imported
Mathlib Proper module and is needed only for the future proof, not for the statement.
No missing statement notion or unusable statement-dependency interface was found.

Edge cases checked against the node and source:

- q = 0 is included; coercions from Nat to Int keep degree zero unchanged.
- d = 0 gives vanishing in every strictly positive degree. At q = 2d no vanishing
  is asserted, so the upper-degree boundary is retained.
- Empty X, empty S, and empty geometric fibres remain permitted. The empty fibre
  satisfies the WithBot dimension inequality. There are no geometric-point choices
  or nonemptiness hypotheses. On empty S the field coefficient hypothesis remains.
- The zero sheaf and the zero coefficient ring are allowed, as is N = 1. N = 0 is
  excluded precisely by the positive-integer coefficient convention.
- Characteristic zero and positive characteristics not dividing N are both covered.
- The identity morphism is allowed; its geometric fibres have dimension zero.
- No smoothness, flatness, separatedness over k, or equidimensionality was added.
- Scheme and geometric fields have the common universe u, and coefficient modules
  have the recorded u+1 size, matching the existing comparison and stalk interfaces.

Searches for an existing statement (all msearch calls use Q32, obl-fin-comparison):

- `msearch.py ... leanfinder`, query: "proper direct image of a constructible finite
  coefficient etale sheaf has constructible higher direct images, finite geometric
  fibre cohomology and vanishing above twice fibre dimension". Eight hits, including
  Scheme.Hom.isConstructible_image and isLocallyConstructible_image, concerned
  constructible subsets or unrelated limit facts; none states this theorem.
- `msearch.py ... loogle`, query: "AlgebraicGeometry.Etale.higherDirectImage, IsProper,
  Finite". No hits; the service reported the project identifier unknown.
- `msearch.py ... grep`, query:
  `constructible.*higher.*direct|higher.*direct.*constructible|geometricFiber.*finite`,
  subdirectory AlgebraicGeometry. No Mathlib hits.
- `msearch.py ... leansearch`, query: "proper higher direct image constructible sheaf
  etale geometric stalk finite cohomology vanishes above twice the dimension".
  Service unavailable, Internal Server Error; no mathematical verdict from this search.
- `rg` over WeilConjectures and lean/Sheaf for proper/constructible/direct-image and
  geometric-fibre terms found the recorded GeometricFiberFinite theorem and the
  separate ProperCaseConstructibility and ProperConstructibleHigherDirectImages
  modules. The first contains comparison without the finitude/vanishing clauses;
  the latter two contain constructibility (and, for ProperCaseConstructibility,
  sheaf vanishing) without the full stalk comparison and finite fibre cohomology.
  None is the combined statement of this node.
- Search for `obl-fin-comparison` in WeilConjectures found no declaration.
- Search for `ProperDirectImageComparison`, `properDirectImage_comparison`, and
  `proper_comparison_and_finitude` in WeilConjectures, lean/Sheaf and the upstream
  declaration-name index found no collision for the new module/declaration.

Validation: the prescribed `scompile.py Q32 obl-fin-comparison` wrapper compiled the
module cleanly, including the sandbox and library-file checks (9.8 s and 23.3 s).
There is exactly one theorem and its proof is `sorry`; no definitions or proofs were
added. All binders/universes are explicit, autoImplicit is disabled, and every Lean
line is at most 93 characters. No disputed statement or node fault was identified.


## Second reading by Q32

I independently opened the DAG node, its sandbox module, and every statement
dependency's node record and declaration. I read the blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/obl-fin-comparison.md` and its parent
`_section.md` on the server, rather than inferring the source from the worker
report. The blueprint statement agrees with the node. I also read Stacks
`etale-cohomology.tex`, `lemma-proper-base-change-stalk` (Tag 0DDF, including
its proof), the adjacent proper relative cohomological-dimension lemma, and
`section-cd` (Tag 0F0P). The source imposes no further separatedness or
smoothness assumption here. The coefficient convention supplies positive N
and invertibility; it does not impose a nonzero coefficient ring.

The independent object/hypothesis/conclusion checklist is as follows. Each
entry passes; none requires a change to the statement.

1. A field k: `(k : Type u) [Field k]`. This is an arbitrary field, not an
   algebraically closed or finite field.
2. The positive integer N and finite commutative ring Lambda killed by N:
   `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, with `hcoeff`.
   I opened `IsSmoothBaseChangeCoefficients`: its data are exactly
   `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
   The explicit finite instance duplicates an existing mathematical hypothesis
   only to type the constructibility predicate. A ring killed by N makes its
   modules killed by N as required.
3. Characteristic prime to N: `hcoeff` is imposed on `Spec (.of k)`, so its
   unit condition is precisely invertibility of N in k through the affine
   global-sections isomorphism. It remains present when S is empty. In
   characteristic zero any positive N is invertible; in characteristic p this
   excludes exactly the multiples of p.
4. A finite-type k-scheme S: `{X S : Scheme.{u}}`,
   `[S.Over (Spec (.of k))]`, `[LocallyOfFiniteType (S ↘ Spec (.of k))]`,
   and `[QuasiCompact (S ↘ Spec (.of k))]`. These are the node's finite-type
   condition, without separatedness over k. The source X obtains its
   k-structure by composition and needs no extra choice or hypothesis.
5. The proper map f: `(f : X ⟶ S) [IsProper f]`. The small etale sites and
   constant-coefficient module sheaves are the recorded objects. In
   particular, I checked `Etale.lowerStar` and the actual
   `Etale.higherDirectImage` in `SixFunctors.Etale.SmoothBaseChange.Defs`:
   the latter is homology of the bounded-below derived direct image of F[0].
   It is not the unrelated coherent-module higher direct image on X.Modules.
6. A nonnegative bound d and every geometric fibre of dimension at most d:
   `(d : ℕ)` and `hfib`, quantified over `(Ω : Type u) [Field Ω]
   [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`, with
   `topologicalKrullDim ↥(pullback f s) ≤ (d : WithBot ℕ∞)`.
   These are field-valued geometric points, and the fibre is the categorical
   scheme pullback, with no rational-point or closed-point restriction.
7. A constructible Lambda-sheaf F: `(F : Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ))` and `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
   I opened `BoundedConstructibleComplexes` and its publicly imported
   predicate. The latter chooses the finite locally closed constructible
   stratification and finite constant module trivializations specified by
   the node; no replacement by a distinct upstream stalk predicate occurs.
8. Clause (i), every nonnegative q and every geometric point s: the first
   outer conjunct starts `∀ (q : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
   (s : Spec (.of Ω) ⟶ S)`. Its first inner conjunct has exactly the two
   endpoint isomorphisms of the recorded
   `geometricFiber_finite_stalk_formula`, which I read via
   `scompile.py --source Sheaf.AlgebraicGeometry.GeometricFiberFinite`.
   The map inside `IsIso` is
   `sourceIso.inv ≫ Γ.map (baseChangeHomologyMap Λ
   (IsPullback.of_hasPullback f s) q F) ≫ targetIso.hom`.
   I opened the source/target functors and `baseChangeHomologyMap`: they
   are the degree-q homology of the fixed derived exchange map. This is
   therefore the specified comparison, not existence of an unrelated
   isomorphism between the stalk and cohomology. The endpoint choices do
   not weaken its being an isomorphism: composing with isomorphisms
   preserves and reflects `IsIso`.
9. Clause (i), finite fibre cohomology: `Finite` of the module object
   `(cohomology (ModuleCat.{u + 1} Λ) (pullback f s) q).obj
   (DerivedCategory.singleFunctor ... 0 ... upperStar ... F)`.
   I opened `Etale.cohomology` in `Derived.LowerShriek`: despite that
   module's name, this functor is ordinary derived global sections, not
   compactly supported cohomology. `upperStar ... (pullback.fst f s)`
   is restriction of F to the fibre. Since Lambda is finite, finite
   underlying set and finite generation of this module are equivalent.
10. Clause (i), these same groups vanish for q > 2d: `2 * d < q → IsZero`
    of exactly the same module object. The strict inequality is correct.
11. Clause (ii), all higher direct images constructible: the second outer
    conjunct is `∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf
    (higherDirectImage Λ f q F) ∧ ...`, using the same recorded predicate
    as for F, and the same higher direct image as the stalk comparison.
12. Clause (ii), higher direct images zero for q > 2d:
    `2 * d < q → IsZero (higherDirectImage Λ f q F)`.
    This is zero as a module sheaf, not merely vanishing of selected stalks.
    No uniform vanishing in lower degrees is asserted.

I checked the dependency records down to the pertinent Mathlib constructions:
`Point.sheafFiber` is the colimit of the pointed-neighbourhood presheaf;
`Scheme.pointSmallEtale s` has the lifts of s as its fibre. These supply
exactly the geometric stalk in entry 8. The convention-only dependency
`def-weil-pbc-scheme-conventions` introduces no additional structure or
missing declaration. There are no new definition nodes, dependency modules,
private notions, or `statement_change` in this delivery, so no new-node or
corrected-citer audit is required.

Edge cases: q = 0 is included by Nat-to-Int coercion in the imported functors;
d = 0 gives vanishing only in positive degrees, and q = 2d is retained.
Empty X and S are admitted and every geometric-point quantifier remains
universal rather than chosen; empty fibres have bottom dimension in
`WithBot ℕ∞`. The zero sheaf, zero coefficient ring and N = 1 are admitted;
N = 0 is excluded exactly by the positive-N source convention. Both
characteristic zero and all allowable positive characteristics are included.
The identity map is permitted. There is no index family whose nonemptiness
was imposed. Universes are explicitly bound: schemes and geometric fields
use arbitrary u (including u = 0), and the module/coefficient size is the
recorded u+1 convention, which admits finite rings and finite module values
by lifting; no extra universe equality or small-field assumption is added.

Independent searches, using queries different from the first worker:

- `msearch.py Q32 obl-fin-comparison leanfinder` with “Etale cohomology of
  geometric fibers for a proper morphism has finite cohomology and
  constructible direct images with dimension bound”: eight hits, including
  finite underlying fibres of finite morphisms and constructible images of
  subsets; none is this cohomological statement.
- `msearch.py ... leansearch` with “For proper morphisms, etale constructible
  finite module sheaves have finite fiber cohomology and constructible higher
  direct images vanishing above twice the fiber dimension”: service
  unavailable, Internal Server Error; no mathematical verdict inferred.
- `msearch.py ... grep` with
  `proper.*(finitude|finite.*cohomology)|comparison.*constructible|finite.*geometric.*stalk`:
  zero Mathlib hits.
- Direct `rg` on upstream WeilConjectures, project lean/Sheaf, and
  `dag/lean_names_upstream.json`, for proper-direct-image comparison names,
  finite fibre cohomology, the blueprint id and the full declaration name:
  no exact existing declaration or name collision. I additionally opened
  `ProperCaseConstructibility` and `ProperConstructibleHigherDirectImages`:
  their signatures give only proper constructibility/vanishing or C(f),
  without the full comparison and finite fibre-cohomology conclusion.
  The existing geometric-fibre formula gives comparison without the full
  finitude conclusions. They are dependencies, not duplicates of this node.

No mathematical or signature mismatch was found. I preserved the correct
Lean and node record and appended this independent reading only. The module
has one theorem with proof `sorry`, no new definition, explicit binders and
`autoImplicit false`. Its declaration docstring reproduces all four current
DAG proof steps, including the module-linear sheaf-vanishing argument, and
both docstrings name the source and blueprint id. Every Lean line has at
most 100 characters. The node's `lean.statement` is byte-for-byte the
signature in the module. Compilation and delivery preflight are recorded
below after execution.

Validation by the second reader: `scompile.py Q32 obl-fin-comparison
lean/Sheaf/AlgebraicGeometry/ProperDirectImageComparisonFinitude.lean` exited
zero with no warnings or errors (sandbox 14.7 s; library file 38.3 s).
`deliver2.py Q32 obl-fin-comparison --no-push` exited zero and printed
`OK (dry run): commit 6c1cb66462 passes the preflight and compiles; nothing pushed`.
