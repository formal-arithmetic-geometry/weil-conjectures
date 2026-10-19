## Worker report

The module `Sheaf.CategoryTheory.Galois.ExactFiniteGsetsForgetful` states
`ContAction.nonempty_forget_iso_of_exact_finite`, with its sole proof `sorry`.
It uses existing Mathlib constructions throughout. No definitions, helper theorems,
new nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/pione.tex`, the whole lemma and proof
`pione-lemma-second-fundamental-functor`, lines 280–351, Tag 0BMV (confirmed in
`literature/stacks-project/tags/tags`). The source has an arbitrary topological
group, not necessarily profinite or Hausdorff, and an exact set-valued functor
with finite values, exactly as the DAG statement. The declaration docstring
records all nine expanded DAG proof steps, including the finite regular cover
and kernel-pair argument that fills the source's final omitted passage.

Hypothesis and conclusion correspondence:

- Topological group G: `{G : Type g} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]`. No compactness, separation or finiteness assumption
  is imposed on G.
- Category of finite sets with continuous left G-action and equivariant maps:
  `ContAction FintypeCat.{u} G`. Read `Action.IsContinuous` and `ContAction`
  in `Mathlib.CategoryTheory.Action.Continuous`: this is the full subcategory
  of `Action` satisfying joint continuity of the induced left action.
  `FintypeCat` bundles finite underlying types (via the `Finite` property;
  it does not require chosen enumerations). Its maps are all functions.
  Action morphisms satisfy the equivariance equation.
- Every finite set has the discrete topology: `open scoped FintypeCatDiscrete`
  activates the existing scoped `HasForget₂ FintypeCat TopCat` instance in
  `Mathlib.Topology.Category.FinTopCat`; its topology is bottom, and its maps
  are the given functions equipped with continuity from a discrete space.
  No new notation or instance is defined in this file.
- H is set-valued: `(H : ContAction FintypeCat.{u} G ⥤ Type u)`.
- H preserves finite limits: `[PreservesFiniteLimits H]`.
- H preserves finite colimits: `[PreservesFiniteColimits H]`.
  These are the actual declarations recorded by `def-galois-exact-functor`'s
  `mathlib_match`, read with their full signatures and docstrings in
  `Mathlib.CategoryTheory.Limits.Preserves.Finite` (lines 44 and 196).
  `CategoryTheory.exactFunctor` and its `exactFunctor_iff` in
  `Mathlib.CategoryTheory.Limits.ExactFunctor` were also read; they define
  exactly the conjunction of these two properties. No additive exactness
  or Galois fiber-functor class is substituted for them.
- Finite H(S) for every S: `[∀ X : ContAction FintypeCat.{u} G,
  Finite (H.obj X)]`. This is a hypothesis on every action, including empty ones.
- U sends an action to its underlying set: the explicit composite
  `forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl`.
  Read the continuous-action forgetful instance, `Action.forget` (objects V,
  maps f.hom), and `FintypeCat.incl` (the full-subcategory inclusion into types).
  Thus this is the specified U, not an arbitrary functor equipped with an
  assumed comparison.
- Existence of a natural isomorphism U to H: `Nonempty (U ≅ H)` with the
  explicit U above. This asserts existence of an invertible natural
  transformation in the functor category, with the requested orientation.

Dependency declarations used:

- Statement dependency `def-galois-exact-functor` is a Mathlib leaf:
  `CategoryTheory.Limits.PreservesFiniteLimits` and
  `CategoryTheory.Limits.PreservesFiniteColimits`, imported publicly from
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`.
- Proof dependency `lem-trf-cofiltered-finite-sets-section` is a Mathlib leaf:
  `nonempty_sections_of_finite_cofiltered_system`, imported non-publicly from
  `Mathlib.CategoryTheory.CofilteredSystem`. Its full declaration and docstring
  were read: arbitrary small category universes, cofiltered-or-empty,
  finite nonempty values, conclusion `F.sections.Nonempty`, no transition
  surjectivity required. The docstring explains its intended use on the set
  of open normal finite-index subgroups; no category of all actions indexes
  the inverse limit.

Edge cases checked before writing:

- Empty action and empty coproduct are included in FintypeCat and ContAction;
  preservation of the initial object forces H(empty) empty. No nonemptiness
  hypothesis is imposed on all source actions or all H-values.
- The singleton with trivial action is included; finite-limit preservation
  gives a singleton image. For the trivial group this reduces to uniqueness
  of the exact finite-valued functor on finite sets.
- Nonempty actions have nonempty images by the pushout argument, not by an
  additional assumption. Surjectivity arguments also include the empty map
  from empty to empty.
- Groups with no proper open finite-index subgroup still have the subgroup
  G itself and all trivial finite actions; no residual finiteness is assumed.
- No Hausdorff hypothesis occurs: open stabilizers suffice for continuity
  on discrete carriers, precisely as in the node proof.
- All universes are explicitly declared (`g u`); group size is independent
  of the finite-set universe. Finite quotient sets of a larger group can
  be represented by equivalent finite types in any universe. The same u
  is used for finite input carriers and Sets in the comparison; this is
  the usual set-universe convention for U and H, not an equality imposed
  between the group universe and the set universe. The theorem is generic
  in u, and no bounded-cardinality or skeletal restriction is introduced.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "An exact finite valued functor on finite
  continuous group sets is naturally isomorphic to the forgetful functor"`:
  eight hits, including `functorToContAction_obj_obj`,
  `functorToAction_comp_forget₂_eq`, and
  `FintypeCat.instFiberFunctorActionFintypeCatForget`; none states uniqueness
  of an arbitrary exact finite-valued H.
- `msearch.py ... loogle "ContAction, FintypeCat"`: eight hits, all concerning
  the Galois-category equivalence induced by a fiber functor; none is this
  statement for an arbitrary topological group.
- `msearch.py ... leansearch "Every exact finite valued functor on finite
  continuous group actions is isomorphic to the forgetful functor"`: eight
  hits about exact-functor bundling, forgetful functors and their preservation
  properties, not the required uniqueness theorem.
- `msearch.py ... grep "nonempty.*[Ii]so|second.*fundamental|exact.*[Ff]unctor"
  CategoryTheory/Galois`: four hits in Equivalence, EssSurj,
  Prorepresentability and Full, none with the required conclusion.
- `rg` on `WeilConjectures` and `lean/Sheaf` for ContAction, finite continuous
  actions and exact forgetful functors: existing constructions and Galois
  equivalences, but no uniqueness result for arbitrary H. Read
  `Sheaf.CategoryTheory.FiniteContinuousModule` and
  `Sheaf.CategoryTheory.Galois.AbstractEquivalence` to distinguish these
  from the desired statement; neither is imported or duplicated.
- Search for this node id in `WeilConjectures`: no hits.
- Search for `nonempty_forget_iso_of_exact_finite` in Mathlib,
  `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no hits.

No statement dispute or node fault was found.

## Second reading by Q37

Independent maintainer second reading, 2026-10-18, of immutable delivery
517a4d74c5c0c020100ef7cf9f6e369299752e42. This section was supplied by the
independent stage-2 reviewer, who neither wrote nor previously second-read
this delivery. The delivered version explicitly described its section as the
worker's own rereading. The maintainer replaces that section here; the worker
report above is retained verbatim. No mathematical or Lean change was needed.

Read the item node and all nine proof steps in the immutable snapshot, the
whole delivered Lean module, the worker report, the statement dependency
`def-galois-exact-functor`, and the proof dependency
`lem-trf-cofiltered-finite-sets-section`. Also read the finite-limit/colimit
definition underlying the exact-functor dependency.

Sources checked in the read-only Q37 clone:

- `literature/stacks-project/pione.tex:280-351`, Tag 0BMV,
  `lemma-second-fundamental-functor`, including both omitted passages;
  `pione.tex:43-59`, `definition-G-set-continuous`, and `pione.tex:192-204`,
  `example-galois-category-G-sets` and `equation-forgetful`.
- `literature/stacks-project/categories.tex:3278-3291`, Tag 0034,
  `definition-exact`; `categories.tex:2863-2867`, Tag 086J,
  `lemma-nonempty-limit`.

Hypothesis-by-hypothesis and conclusion checks:

1. `{G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
   is precisely an arbitrary topological group. There is no profiniteness,
   Hausdorffness, compactness, finite generation or residual finiteness premise.
2. `ContAction FintypeCat.{u} G` is the full category of finite continuous
   left actions. Read `Action` and `Action.Hom.comm` in
   `Mathlib/CategoryTheory/Action/Basic.lean:44-48,90-93`, and
   `Action.IsContinuous`, `ContAction`, and its forgetful instances in
   `Mathlib/CategoryTheory/Action/Continuous.lean:59-86`. Morphisms are all
   equivariant functions. `FintypeCat` is the existing full subcategory of
   finite types, not a newly defined or skeletal replacement.
3. `open scoped FintypeCatDiscrete` selects the existing bottom topology and
   forgetful functor to `TopCat` from `Mathlib/Topology/Category/FinTopCat.lean`.
   Thus continuity is joint continuity on the discrete carrier as required.
4. `H : ContAction FintypeCat.{u} G ⥤ Type u` is set-valued.
   `[PreservesFiniteLimits H]` and `[PreservesFiniteColimits H]` are exactly
   the two clauses of `def-galois-exact-functor`. Read their full declarations
   at `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean:44,196`, including
   transport to finite shapes in arbitrary universes. Also read
   `exactFunctor` and `exactFunctor_iff` at `Limits/ExactFunctor.lean:93-99`.
   Finite limits and colimits of these actions exist by the explicit finite
   set constructions in step 1; no missing existence premise is being hidden.
5. `[∀ X : ContAction FintypeCat.{u} G, Finite (H.obj X)]` covers every
   action, including the empty one, without requiring nonempty values.
6. `forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl`
   is the specified underlying-set functor: the action forgetful functor maps
   an object to its carrier and a map to its underlying function, and
   `FintypeCat.incl` is the full-subcategory inclusion into types.
7. `Nonempty (U ≅ H)` asserts existence of a natural isomorphism in the
   correct direction. It is neither a chosen arbitrary comparison nor merely
   pointwise equicardinality. Verdict: every clause matches the node and source.

Proof-outline and citation audit:

1. Finite invariant subsets, products, coproducts and quotients retain open
   stabilizers. The stated universal properties follow directly from the
   equivariant set constructions. The exactness dependency gives their
   preservation, including the empty and singleton diagrams.
2. The two-singleton pushout distinguishes empty from nonempty input, so
   nonemptiness of H(X) is deduced, not assumed.
3. A surjection is the coequalizer of its kernel pair; descending a function
   along a surjection preserves equivariance. The exactness dependency gives
   surjectivity of H(q) and the specified pullback identification.
4. Normality makes `(gN, gaN)` well-defined and gives the coproduct/product
   bijection. Finite positivity justifies cancellation of |H(Q_N)|.
5. The subgroup index is a set, contains G, and is closed under intersections.
   The cited `nonempty_sections_of_finite_cofiltered_system` at
   `Mathlib/CategoryTheory/CofilteredSystem.lean:79-81` has independent object,
   morphism and value universes and requires finite nonempty values, without
   transition surjectivity. Its conclusion is exactly the compatible family
   needed here. This is the only non-elementary step in the outline.
6. Finite continuity makes K_X open; normality and finite index come from
   the permutation representation. Intersecting kernels proves independence
   and naturality of H(f_{N,x})(gamma_N) by the displayed equations.
7. Distinct right translations have empty equalizer. Preservation plus step 4
   proves bijectivity on regular finite quotients.
8. Coproduct preservation gives bijectivity on the cover Y; surjectivity of
   q and H(q) gives surjectivity on each X.
9. Pullback preservation and surjectivity on the finite kernel pair R give
   injectivity on X; naturality of inverse functions follows by composing the
   naturality equation. Steps 6 and 9 supply the source's omitted details.

Size and edge cases: empty X, the empty coproduct, the empty-to-empty
surjection and the empty kernel pair are included. The singleton/trivial
action and the trivial group are included. The subgroup G is always present,
including when there are no proper open finite-index subgroups. No separation
hypothesis is used. Universes `g u` and all variables are bound; `g` is
independent of `u`. A finite quotient of a larger group can be represented
by a finite type in universe u; no restriction of the group size is imposed.
The common universe for input finite sets, underlying sets and H is the
ordinary Sets convention for the displayed natural isomorphism.

Independent searches: searched the pinned Mathlib Galois directory for
`nonempty.*[Ii]so`, `[Ii]so.*[Ff]iber`, `[Ii]so.*[Ff]ibre`, and uniqueness;
read the nearby `autIsoFibers`/prorepresentability interfaces. They concern
automorphisms of a fixed fibre functor, not the stated arbitrary H. Searched
upstream `WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json`
for the item id, proposed name and exact finite-action forgetful theorem.
Read the side finite-continuous-action and abstract Galois-equivalence
interfaces to distinguish their conclusions. No duplicate exact declaration
was found. The worker report records LeanFinder, Loogle, LeanSearch and grep
queries with their results.

Maintainer gates: only one theorem, with sole proof `by sorry`; no new
construction or hollow definition. Module and declaration docstrings contain
the source and blueprint id, and the latter follows all nine node steps.
All lines are at most 100 characters. All four imports are justified by the
statement or its recorded proof dependencies. A literal comparison confirmed
`lean.statement` equals the source signature from `theorem` up to `:=`.
No statement correction, new node or dependency repair is needed.
The dependencies are absent from `origin/newtargets-dag`'s route-pivot dropped
list, and no repair note exists there for this item. No dropped machinery or
pro-etale substitute appears.

Compiler reproduction on 2026-10-18: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q37
lem-wf-exact-finite-gsets-forgetful <immutable snapshot module path>`.
Exit code 0; no errors or warnings. The installed wrapper currently performs
the server overlay check, reporting sandbox compilation in 3.6 s and the
library-path module in 11.5 s, with the 60 s per-file limit. Thus this is
fresh compiler evidence rather than relying on the delivered report's
prospective validation sentence. No global build, direct ssh command, Git
mutation, or live Lean write was performed by the reviewer.

Finding and correction: the original second-reading section was explicitly
a self-rereading, not an independent review (H11, with the independent-reader
requirement in brief-stage2 section 6). This replacement supplies the actual
independent reading and observed compiler result. The Lean and node record
are accepted unchanged.
