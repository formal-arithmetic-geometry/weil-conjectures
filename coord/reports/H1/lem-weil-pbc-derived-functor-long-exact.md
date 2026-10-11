## Worker report

The module `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` states
`CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_full_long_exact` with a single
`sorry` proof. It states the entire long exact sequence, including its initial zero.
The original node is unchanged except for its Lean record. No new definitions, dependency
modules or statement correction are needed. Nothing is proved.

Hypothesis and clause correspondence:

- The abelian source and target are `{A : Type u₁} {B : Type u₂}` with independent
  `[Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]`.
- Enough injectives is `[EnoughInjectives A]`; Mathlib supplies `HasInjectiveResolutions A`
  from this and `Abelian A`. This is the node's actual hypothesis, not an assumption of
  chosen compatible resolutions or injectivity of the objects in the short exact sequence.
- The additive functor is `(F : A ⥤ B) [F.Additive]`.
- Left exactness is `[PreservesFiniteLimits F]`. As the dependency's Mathlib match explains,
  for additive functors between abelian categories this is equivalent to preserving kernels.
  The hypothesis remains present although the horseshoe proof only needs additivity.
- The short exact sequence is `{S : ShortComplex A} (hS : S.ShortExact)`; `S.X₁`, `S.X₂`,
  `S.X₃`, `S.f`, and `S.g` are respectively the three objects and the two given maps.
  `ShortExact` includes exactness, monicity of `S.f`, and epicity of `S.g`.
- The functors `R^n v` are exactly `F.rightDerived n`, computed using Mathlib's injective
  resolutions. The maps are `(F.rightDerived n).map S.f` and `.map S.g`.
- The connecting morphisms are the existential family
  `δ : ∀ n : ℕ, (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁`.
- Exactness at the initial `R^0v(A)` (the preceding zero) is
  `Mono ((F.rightDerived 0).map S.f)`.
- Exactness at each `R^nv(B)` is `(S.map (F.rightDerived n)).Exact`.
- Exactness at each `R^nv(C)` is `(ShortComplex.mk _ _ w₁).Exact`, for the pair
  `(F.rightDerived n).map S.g`, `δ n`. Its existential witness `w₁` says their composite is zero.
- Exactness at each `R^{n+1}v(A)` is `(ShortComplex.mk _ _ w₂).Exact`, for the pair
  `δ n`, `(F.rightDerived (n + 1)).map S.f`. The witness `w₂` says their composite is zero.
  Together these cover every term of the displayed infinite sequence; no naturality of
  the boundaries is imposed since the node does not ask for it.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (class fields and preceding docstring).
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.rightDerived`,
  `Mathlib.CategoryTheory.Abelian.RightDerived`; `Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`; `Limits.PreservesFiniteLimits` in
  `Mathlib.CategoryTheory.Limits.Preserves.Finite` (the dependency record gives all clauses).
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution` and
  `HasInjectiveResolutions`, `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`;
  `CategoryTheory.Injective` in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
  Their use is through `rightDerived`, not a private resolution construction.
- `Mathlib.CategoryTheory.Abelian.Injective.Resolution` supplies the instance from enough
  injectives. `ShortComplex.ShortExact`, `ShortComplex.map`, and `ShortComplex.Exact` are
  Mathlib notions. The module imports the existing source extension
  `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`, whose anonymous instance
  proves `(F.rightDerived n).Additive`, giving preservation of zero morphisms needed for
  `S.map`. This avoids adding that property as a new hypothesis.

Edge cases checked before writing: degree zero retains the initial monomorphism; degree
one and every higher degree are covered by the previous connecting map. The zero sequence
and sequences with any endpoint zero are included. The zero functor is allowed; all the
maps then have zero source and target and are exact. No characteristic, size, nonzero-object
or finite-dimensional restriction is added. Four independent explicit universes allow
unrelated object and morphism sizes for source and target. All variables are explicitly bound.

Searches for an existing statement (2026-10-11):

- `msearch.py leansearch`: query "long exact sequence of right derived functors of an
  additive left exact functor" returned UNAVAILABLE, Internal Server Error. No verdict
  is claimed for that unavailable service.
- `msearch.py leanfinder`: "long exact sequence of right derived functors of a left exact
  additive functor" returned eight hits, including Ext exact sequences and homological
  functor exactness; none is this statement for arbitrary `F.rightDerived`.
- `msearch.py loogle`: `CategoryTheory.Functor.rightDerived,
  CategoryTheory.ShortComplex.ShortExact` returned zero hits.
- `msearch.py grep`: `rightDerived.*exact|exact.*rightDerived`, subdirectory
  `CategoryTheory`, returned four hits (generic localization derived functors and the
  degree-zero comparison); no full long exact sequence.
- `rg` of the source's `CategoryTheory/Abelian/RightDerived`, and `lean/Sheaf/CategoryTheory`
  for `rightDerived|long.exact`, found the source's
  `CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_δ_exact`. Its entire module
  was read: it gives exactness only at `R^qv(C)` and `R^{q+1}v(A)` for a single degree.
  It omits the initial mono and exactness at `R^qv(B)`, so it is a partial cover, exactly
  as the stage-1 report says. Other project hits concern composites, acyclic resolutions,
  or particular functors, not this statement.
- `rg` for the item id in `WeilConjectures` returned no matches. The new declaration name
  was searched in Mathlib, the source, `lean/Sheaf`, and `dag/lean_names_upstream.json`;
  there was no collision.

Source checked: https://stacks.math.columbia.edu/tag/015B, Lemma 13.20.4, (1) for complexes
concentrated in degree zero and (2) for vanishing below zero. The local literature copy is
absent on this machine; the official Stacks page was opened. The docstring gives the node's
five-step horseshoe proof and names each proof dependency. No statement fault or dispute
was found.

## Second reading by H1

I independently opened the node copy, the complete delivered module, all three statement
dependency nodes and the Mathlib declarations they record. I also read the entire source
`WeilConjectures/CategoryTheory/Abelian/RightDerived/LongExactSequence.lean` and the imported
source extension `WeilConjectures/Mathlib/CategoryTheory/Abelian/RightDerived.lean`.
No mathematical mismatch was found; the Lean file and node record are kept as written.
The second reading adds this report only.

Source: the local Stacks checkout is absent, so I read the official
[Tag 015B](https://stacks.math.columbia.edu/tag/015B) and the actual
[derived.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex),
section `section-right-derived-functor` and lemma `lemma-higher-derived-functors`.
The section introduces additive functors between a source abelian category with enough
injectives and a general target abelian category. The lemma assumes left exactness;
part (1), on objects concentrated in degree zero, gives the desired long exact sequence,
and part (2) supplies vanishing in negative degrees and hence its initial zero. No
Grothendieck, smallness, field, Noetherian or target enough-injectives hypothesis is implicit.
The node asks only for these clauses, not the source's further universal delta-functor
assertion. There is no `statement_change`, new definition node or dependency module.

My object/hypothesis/conclusion inventory and item-by-item H3 verdict:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Source category, abelian | `{A : Type u₁} [Category.{v₁} A] [Abelian A]` | Exact match to `def-sp-abelian`. |
| Source has enough injectives | `[EnoughInjectives A]` | Exact hypothesis; the abelian resolution instance supplies `HasInjectiveResolutions A`, without an extra assumption. |
| Target category, abelian | `{B : Type u₂} [Category.{v₂} B] [Abelian B]` | Exact match, with independent source/target sizes. |
| Additive functor v | `(F : A ⥤ B) [F.Additive]` | Exact match to the dependency's additive notion. |
| Left exactness of v | `[PreservesFiniteLimits F]` | Equivalent to preserving kernels for additive functors between abelian categories. |
| Right derived functors for all nonnegative degrees, using injective resolutions | `F.rightDerived n`, `n : ℕ` | Uses the recorded Mathlib definition, not a private copy. |
| Arbitrary short exact sequence and its three objects/two maps | `{S : ShortComplex A} (hS : S.ShortExact)`, `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g` | `ShortExact` requires exactly middle exactness, mono first map and epi second map; `S.zero` is a consequence of any short exact sequence. |
| Connecting maps for the whole sequence | `∃ δ : ∀ n : ℕ, (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁` | One family for each given sequence, with exactly the stated sources and targets. |
| Maps induced by f and g | `(F.rightDerived n).map S.f`, `(F.rightDerived n).map S.g` | The same morphisms as in the node, at every degree. |
| Initial zero and exactness at R⁰v(A) | `Mono ((F.rightDerived 0).map S.f)` | Precisely exactness of `0 → R⁰v(A) → R⁰v(B)` in an abelian category. |
| Exactness at every Rⁿv(B) | `∀ n : ℕ, (S.map (F.rightDerived n)).Exact` | Includes degree zero and every higher degree. |
| Consecutive composites involving the connecting map vanish | `w₁ : (F.rightDerived n).map S.g ≫ δ n = 0`, `w₂ : δ n ≫ (F.rightDerived (n + 1)).map S.f = 0` | Required for the two short complexes; not extra hypotheses on the original sequence. |
| Exactness at every Rⁿv(C) | `(ShortComplex.mk _ _ w₁).Exact` | Exactly image of Rⁿv(g) equals kernel of δⁿ. |
| Exactness at every Rⁿ⁺¹v(A) | `(ShortComplex.mk _ _ w₂).Exact` | Exactly image of δⁿ equals kernel of Rⁿ⁺¹v(f). Together with the initial mono this covers all A terms. |

Dependency check: `Abelian` (Basic.lean:112) is the normal mono/epi formulation, with
kernels, cokernels and finite products; the zero object and finite biproducts follow.
`Functor.Additive` (AdditiveFunctor.lean:42) preserves sums of morphisms, equivalently
finite biproducts here. `preservesFiniteLimits_of_preservesKernels` (LeftExact.lean:117)
shows that the left exactness binder imposes no stronger requirement. Conversely finite
limits include kernels. `PreservesFiniteLimits` also preserves finite shapes in larger
universes (Preserves/Finite.lean:53), so its definition using `J : Type` does not restrict
sizes. `Injective` (Injective/Basic.lean:32) is extension along every mono;
`EnoughInjectives` (:64) provides an injective presentation of every object.
`InjectiveResolution` (Injective/Resolution.lean:43) is a complex of injectives with a
quasi-isomorphism from the object in degree zero. Mathlib's `Functor.rightDerived`
(Abelian/RightDerived.lean:110) is the homology functor after applying F to the chosen
resolution; `isoRightDerivedObj` (:114) compares any other resolution. The imported source
extension supplies additivity of every `F.rightDerived n`, needed by `S.map`, rather than
postulating it. `ShortComplex.map` uses the given maps; `ShortComplex.Exact` means zero
homology, equivalent here to image equals kernel. No dependency record needs repair.

Edge cases: `n = 0` has both the initial mono and exactness at B and C, while δ⁰ supplies
exactness at degree-one A. Every positive A degree has its preceding δ. The zero category,
zero sequence, zero objects at either endpoint and zero functor are allowed. Abelian
categories have a zero object, so an empty category is already outside the node's
hypotheses. There is no variable index set, scheme or characteristic; in particular no
empty-scheme or characteristic case is excluded by a new condition. The four universes
`u₁`, `u₂`, `v₁`, `v₂` are independent. All binders, including `n`, `δ`, `w₁` and `w₂`, are
bound explicitly; no common source/target universe or finite dimension is required.

Independent H4 searches on 2026-10-11, with queries different from the first reader's:

- `msearch.py leanfinder`, "derived delta functor exact at middle object and degree zero
  monomorphism": eight hits, including `ShortComplex.ShortExact.mono_δ`, derived-category
  homology mono criteria and `Functor.homologySequence_exact₁/₂/₃`. These are statements
  about complexes or homological functors, not this full statement about `F.rightDerived`.
- `msearch.py loogle`, `"rightDerived", "Exact"`: zero hits.
- `msearch.py leansearch`, "right derived functors send short exact sequences to exact
  sequences beginning with zero": UNAVAILABLE, Internal Server Error; no no-match verdict
  is inferred from the failed service.
- Direct `rg` on Mathlib's abelian-category files, the source `WeilConjectures/CategoryTheory`
  and the project's `lean/Sheaf/CategoryTheory` for
  `rightDerived.*[Ee]xact|[Ee]xact.*rightDerived|rightDerived.*[Mm]ono|δ.functor|delta.functor`
  found comparison results, acyclicity results, the project's abstract delta-functor
  definition and the source's `exists_rightDerived_δ_exact`. I read that theorem's
  signature: for each single q it gives only exactness at R^qv(C) and R^{q+1}v(A).
  It omits exactness at R^qv(B) and the initial mono; it is not an existing realization.
- Direct `rg` for the full proposed declaration name across Mathlib, WeilConjectures,
  `lean/Sheaf` and `dag/lean_names_upstream.json` found no collision. The item id in the
  source found no declaration, while project mentions occur only in proof docstrings.

H5-H9: no definition is introduced, so no hollow definition or duplicate notion occurs.
The only theorem has exactly `by sorry`. Its module and declaration docstrings identify
Tag 015B and the blueprint id. The proof docstring follows all five node steps: compatible
resolutions, split exactness after applying F, long exact cohomology, the initial mono,
and transport via the resolution comparison isomorphisms. All lines are at most 100
characters; both imports serve notions used by the statement; the topic directory and
namespace are appropriate. The node's `lean.statement` is verbatim the file's signature.

Validation: the complete delivered module was compiled with `scompile.py` against the
server's prescribed library. Delivery dry run and final delivery follow this reading.
