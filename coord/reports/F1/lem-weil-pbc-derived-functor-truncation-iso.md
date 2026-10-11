## Worker report

The module `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso` states the general morphism theorem and the stated degree-n truncation corollary. Both are theorem statements with `sorry`; no definition, instance, or proof is added. The node changes only in `lean`. No statement correction, new node, or dependency module is needed.

Clause-by-clause correspondence:

- The two Grothendieck abelian categories are `{A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]` and the corresponding binders for `B`. The generator, small colimits and exact filtered colimits are the existing Grothendieck class's axioms and inferred consequences, with its smallness universe equal to the hom universe as specified by the dependency's Mathlib match.
- The left exact additive functor is `(v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]`. For abelian categories, this is precisely additivity and kernel preservation, as recorded by `def-sp-left-exact-additive`.
- The right derived functor `Rv : D⁺(A) ⥤ D⁺(B)` is Mathlib's `v.rightDerivedFunctorPlus`. Enough injectives follows from Grothendieck abelianness, so there is no extra enough-injectives hypothesis. This is the existing functor computed by bounded-below injective resolutions. Such resolutions are K-injective, as the source's `DerivedCategory.Plus` injective-object instance states. This realizes the K-injective convention of `def-sp-kinjective-bridge`, up to the usual canonical resolution comparison; no alternate resolution definition is made.
- The arbitrary integer is `(n : ℤ)`; the two bounded-below derived objects and their morphism are `{L M : DerivedCategory.Plus A} (c : L ⟶ M)`.
- The low-degree cohomology-isomorphism hypothesis is `hiso : ∀ i : ℤ, i ≤ n → IsIso ((DerivedCategory.Plus.homologyFunctor A i).map c)`. This uses the actual cohomology maps of `c` and includes every integer below the bound, not only nonnegative degrees.
- The degree-`n + 1` monomorphism hypothesis is `hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map c)`.
- The general conclusion is `∀ j : ℤ, j ≤ n → IsIso ((DerivedCategory.Plus.homologyFunctor B j).map (v.rightDerivedFunctorPlus.map c))`. Thus the map asserted invertible is exactly `H^j(Rv(c))`, not an unspecified isomorphism between the objects.
- The corollary binds `(K : DerivedCategory.Plus A)` and uses `(DerivedCategory.TStructure.t.onPlus.truncLEι n).app K` as the canonical `τ≤n K → K`. The standard t-structure induces one on its bounded-below full subcategory by Mathlib's `TStructure.onPlus`; its truncation is canonical and agrees with the lower truncation of a representing bounded-below complex in the derived category. Thus neither a representative nor an additional boundedness hypothesis is imposed.
- The corollary conclusion applies `v.rightDerivedFunctorPlus.map` to that canonical map and then `(DerivedCategory.Plus.homologyFunctor B n).map`, with `IsIso` on precisely this induced degree-n map.
- The explicit `[HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]` binders are the chosen localization/size data already part of `def-weil-abstract-derived-category`, not a mathematical restriction. All category object, hom, and derived hom universes are explicit and independent.

Dependencies read and used:

- `def-sp-left-exact-additive` (Mathlib leaf): `CategoryTheory.Functor.Additive`, `CategoryTheory.Limits.PreservesFiniteLimits`, and the kernel-preservation equivalence in `Mathlib.CategoryTheory.Preadditive.LeftExact`. Its ordinary object-level `Functor.rightDerived` is not substituted for the complex-level functor.
- `def-sp-grothendieck-abelian` (Mathlib leaf): `CategoryTheory.IsGrothendieckAbelian`, in `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`; the imported `EnoughInjectives` module supplies `IsGrothendieckAbelian.enoughInjectives`.
- `def-sp-kinjective-bridge`: read `Sheaf.CategoryTheory.KInjectiveBridge` in full, including `CochainComplex.KInjectiveResolutionChoice`, `grothendieckKInjectiveResolutionChoice`, `CategoryTheory.Functor.rightDerivedComplexWithResolution` and `rightDerivedCohomologyWithResolution`. These define the resolution-dependent complex/object convention, not a functor on derived morphisms. The required morphism-level functor already exists as `CategoryTheory.Functor.rightDerivedFunctorPlus` in `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, so there is no missing notion and no reason to replace the bridge's record. Read its full definition/unit and the source's `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, including its bounded-below K-injective instance and injective-model identification. This explains the use of the existing derived functor in the statement rather than an ill-typed application of the resolution-dependent object definition to `c`.
- `def-weil-pbc-bounded-derived-subcategories` (Mathlib leaf): `DerivedCategory.Plus` in `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, the standard t-structure's full subcategory of objects bounded below.
- `def-weil-abstract-derived-category` (Mathlib leaf): `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.homologyFunctor`; `DerivedCategory.Plus.homologyFunctor` in `Mathlib.Algebra.Homology.DerivedCategory.Plus` is its restriction along the full inclusion.
- `def-sbc-standard-tstructure-derived-category` (Mathlib leaf): `DerivedCategory.TStructure.t`; `TStructure.onPlus` in `Mathlib.CategoryTheory.Triangulated.TStructure.Induced` restricts it to the same bounded-below subcategory. `TStructure.truncLEι` in `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` is the canonical truncation morphism.

Source and edge cases:

Read Stacks `derived.tex`, Lemma 05TC (`lemma-negative-vanishing`), both parts and the entire proof, from the available local copy `/home/ubuntu/c1-stacks-review/derived.tex:5497`. The repository's literature checkout is absent on this machine. Part (2) uses the truncation triangle, part (1) to kill the third vertex below `n + 1`, and the long exact sequence. The node generalizes that argument to the cone of `c`; its proof is reproduced step by step in the main theorem's docstring, including the boundary monomorphism and the truncation specialization.

Checked arbitrary negative `n` and `n = 0`: all indices are integers and there is no nonnegative lower bound. Checked the boundary `j = n`: injectivity on `H^(n+1)(c)` is retained and is exactly what forces the cone to vanish in that degree. Checked zero objects and zero functors: all hypotheses/conclusions have their expected zero-object interpretation. If the truncation is below a lower bound for K, it is zero, and negative vanishing gives the required zero cohomology on the target. Neither K nor the categories are required nonzero. The corollary retains all bounded-below objects, including those without a chosen representative. No false statement or disputed edge case was found.

Searches (2026-10-11):

1. `msearch.py ... leanfinder "right derived functor induces cohomology isomorphisms in degrees at most n on a morphism which is an isomorphism in these degrees and monic in degree n+1"`: eight hits, including `InjectiveResolution.isoRightDerivedObj`, quasi-isomorphism localization results and homology-factorization results. None states the morphism/truncation conclusion.
2. `msearch.py ... loogle "CategoryTheory.Functor.rightDerivedFunctorPlus, DerivedCategory.Plus.homologyFunctor"`: zero hits.
3. `msearch.py ... grep "rightDerivedFunctorPlus.*trunc|isIso.*rightDerivedFunctorPlus|rightDerivedFunctorPlus.*isIso" Algebra/Homology`: two hits, the examples showing the derived-functor unit is invertible on injective complexes. No theorem matching this item.
4. `msearch.py ... leansearch "right derived functor truncation low degree cohomology isomorphism"`: service unavailable (Internal Server Error); no result claimed.
5. `rg -n` over `WeilConjectures` and `lean/Sheaf` with `rightDerivedFunctorPlus.*trunc|isIso.*rightDerivedFunctorPlus|rightDerivedFunctorPlus.*isIso|homologyMap.*rightDerived`: project hits concern units on acyclic complexes, exact functors, and natural transformations. None is the node's statement; no matching landed Sheaf theorem.
6. `rg -n "lem-weil-pbc-derived-functor-truncation-iso"` over the source repository: no tagged declaration. Direct inspection of the source `RightDerivedFunctorPlus.lean` finds negative vanishing and triangulatedness, not this theorem.
7. Checked the chosen declaration names with `rg -n` in `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and `lean/Sheaf`: no collision.
8. Direct source searches located the standard t-structure restriction `TStructure.onPlus` and the canonical map `truncLEι`, so no new truncation definition is introduced.

Validation: `scompile.py F1 lem-weil-pbc-derived-functor-truncation-iso <module>` completed with exit code 0 in 1.5 seconds, without errors or warnings. The delivery dry run is the final validation; the independent second reader supplies its own section and performs delivery.

## Second reading by F1

Independent reading on 2026-10-11. I opened the sandbox node and both theorem signatures,
all six statement-dependency nodes, the landed KInjectiveBridge module, and the relevant
Mathlib/source definitions rather than relying on the worker's descriptions. The source
is the local Stacks copy `/home/ubuntu/c1-stacks-review/derived.tex:5497-5541`, Lemma 05TC,
both parts and their proofs. It assumes an additive functor between abelian categories
and existence of the indicated derived values; it imposes no ambient field, finiteness,
Noetherianity, or characteristic condition. The node explicitly specializes to left exact
functors between Grothendieck categories, where these derived values exist, and generalizes
the source's truncation argument to the cone of an arbitrary morphism. This is precisely
the node's existing statement, not a new correction.

Objects, hypotheses, and conclusions, listed independently from the node:

1. Two Grothendieck abelian categories A and B. Lean: `{A : Type u₁}` and
   `{B : Type u₂}`, each with its independent `Category`, `Abelian`, and
   `IsGrothendieckAbelian` binders. Verdict: exact. Read Basic.lean:70 and its
   `hasColimits` instance: the class gives a generator, small colimits and exact filtered
   colimits in the hom universe, exactly the dependency's verified size convention.
2. A left exact additive functor v from A to B. Lean: `(v : A ⥤ B) [v.Additive]
   [PreservesFiniteLimits v]`. Verdict: exact. The left-exact dependency's clauses are
   Mathlib's Additive and kernel preservation; read LeftExact.lean:117, which recovers
   finite-limit preservation from kernels with the additive finite-product instances.
   There is no exactness, right exactness, or preservation of injectives assumption.
3. Its right derived functor on D⁺, computed using K-injectives. Lean:
   `v.rightDerivedFunctorPlus`. Verdict: exact existing derived functor, not the
   object-level `v.rightDerived`. Read its Mathlib definition as a total right derived
   functor of termwise v on the bounded-below homotopy category. Read the source's
   `DerivedCategory.Plus.injectiveObjectEquivalence`, bounded-below injective complexes'
   K-injective instance, and `rightDerivedFunctorPlusIsoInjectiveObject`: it is computed
   termwise on those K-injective models. KInjectiveBridge's recorded definitions retain
   a chosen complex resolution and do not define a functor on derived morphisms; hence
   using the already existing morphism-level functor introduces no duplicate notion.
   EnoughInjectives.lean:380 supplies enough injectives from the existing Grothendieck
   hypothesis, with no additional binder. `[HasDerivedCategory.{w₁} A]` and the B binder
   are the chosen localization data of the abstract-derived-category dependency; its
   `HasDerivedCategory.standard` always supplies them in `max u v`.
4. Any integer n, two objects L and M of D⁺(A), and a morphism c. Lean: `(n : ℤ)
   {L M : DerivedCategory.Plus A} (c : L ⟶ M)`. Verdict: exact. Read TStructure.lean:204:
   Plus is the full subcategory of objects bounded below in cohomology, not complexes
   concentrated in nonnegative degrees or only bounded objects.
5. H^i(c) is an isomorphism for every i ≤ n. Lean: `hiso : ∀ i : ℤ, i ≤ n →
   IsIso ((DerivedCategory.Plus.homologyFunctor A i).map c)`. Verdict: exact, including
   all negative i. Plus.lean:151 defines this functor as the full inclusion followed by
   the recorded `DerivedCategory.homologyFunctor`, so these are the node's actual maps.
6. H^(n+1)(c) is a monomorphism. Lean: `hmono : Mono
   ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map c)`. Verdict: exact; the boundary
   condition is retained and not strengthened to an isomorphism.
7. For every j ≤ n, H^j(Rv(c)) is an isomorphism. Lean: `∀ j : ℤ, j ≤ n → IsIso
   ((DerivedCategory.Plus.homologyFunctor B j).map (v.rightDerivedFunctorPlus.map c))`.
   Verdict: exact induced map, with the correct bound and quantifier order; not merely
   existence of an isomorphism of its source and target.
8. For any K in D⁺(A), take the canonical map τ≤n K → K. Lean: `(K :
   DerivedCategory.Plus A)` and `(DerivedCategory.TStructure.t.onPlus.truncLEι n).app K`.
   Verdict: exact. Read the standard t-structure definition, Induced.lean's
   `tStructure` and `onPlus`, and TruncLEGT.lean:81. `onPlus` is defined on
   `t.plus.FullSubcategory` with the same inequalities as the ambient standard
   t-structure, despite its upstream docstring incorrectly saying bounded above.
   Its canonical truncation triangle agrees, by the uniqueness of t-structure
   truncations, with the image of the canonical complex truncation in the node.
   No chosen representative or extra bound on K is required.
9. The degree-n cohomology map after Rv of that canonical map is an isomorphism.
   Lean: the complete conclusion of
   `isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`, applying first
   `v.rightDerivedFunctorPlus.map` and then degree-n `homologyFunctor.map` to the map
   in item 8. Verdict: exact, with the same categories and functor hypotheses as items 1-3.

Edge cases: n = 0 and negative n are included because every bound is integral; j = n
uses the monomorphism at n+1 to kill the cone's boundary cohomology. For zero objects and
the zero functor the induced zero-to-zero maps have the required interpretation. If n
is below K's lower bound, τ≤n K is zero and negative vanishing makes the target degree-n
cohomology zero as well. Trivial abelian categories are allowed. There is no index family,
scheme, coefficient ring, or characteristic in this abstract statement, so empty index
sets, empty schemes and characteristic cases introduce no additional hypotheses.
The two object universes, hom universes, and localization hom universes are separately
bound and unrestricted within the dependency's size convention. No free variable or
universe was found.

Independent searches, using different conceptual wording from the worker:

- LeanFinder: `An additive left exact derived functor preserves a morphism whose cone has
  cohomology zero below an integer bound`. Eight hits: exact-functor Ext maps, homological
  functor exactness/localization, and vanishing on injective objects. None states either
  theorem of this delivery.
- Loogle: `CategoryTheory.Functor.rightDerivedFunctorPlus`. Twelve hits, giving the
  existing functor, units, shift/triangulated instances and natural transformations;
  none gives the low-degree morphism or truncation theorem. The service indexes newer
  Mathlib; I checked the actual pinned source independently.
- LeanSearch: `canonical truncation induces isomorphism on cohomology after right derived
  functor`. Unavailable (Internal Server Error), recorded without claiming a result.
- `rg -n -i 'derived.*trunc|trunc.*derived|rightDerivedFunctorPlus'` over the source's
  WeilConjectures and the repository's lean/Sheaf located standard truncation/cohomology
  facts, derived functor models and comparisons, and specialized geometric applications.
  A narrower follow-up across Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for `rightDerivedFunctorPlus.*trunc`,
  `trunc.*rightDerivedFunctorPlus` and the two delivered declaration names returned no
  hits. Read the whole pinned Mathlib RightDerivedFunctorPlus module and the source's
  injective model comparison: neither states this item. No existing statement or name
  collision was found.

No new nodes or dependency modules are delivered, and there is no `statement_change`.
All five proof steps are carried by the main docstring: cone cohomology vanishing,
triangulatedness, negative vanishing at n+1, the second long exact sequence, and the
canonical truncation specialization. Both declarations have source/blueprint docstrings;
the two proofs are solely `sorry`, and there are no definitions or new instances.
Every import serves a statement hypothesis or the existing derived functor. All lines
are at most 100 characters. The primary `lean.statement` equals the file signature
verbatim, checked independently.

Mismatches and changes: none found in the Lean or node; preserved both. Added only this
independent second-reading report. The single-file server compile completed cleanly in
1.5 seconds, exit code 0, with no errors or warnings. Delivery preflight follows below.

Delivery validation: `deliver2.py F1 lem-weil-pbc-derived-functor-truncation-iso --no-push`
printed OK: the delivery passes the stage-2 preflight and compiles on the server.
