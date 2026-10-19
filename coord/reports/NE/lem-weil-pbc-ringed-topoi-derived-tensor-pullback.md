## Worker report

The module `Sheaf.Paper.RingedTopoiDerivedTensorPullback` states
`SheafOfModules.ringedTopoiDerivedTensorPullback`, with one `sorry` and no new definitions.
The source is Stacks, Cohomology on Sites, Tags 07A4 and 0G7E, read in the local
`sites-cohomology.tex` at the labels `lemma-pullback-tensor-product` and
`lemma-pullback-K-flat`. No node statement correction or dependency replacement is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The two small sites are `C D : Type u` with `Category.{u}` and topologies `JC JD`.
  The coefficient and module universe is the same arbitrary `u`; no finite bound on
  objects or morphisms is imposed. Smaller site universes can be lifted into `u`.
- The commutative ring sheaves are `R`, `S`; `RI` is the algebraic inverse image of `R`.
- The geometric morphism is `uInv`, `uPush`, `adj : uInv ⊣ uPush` and
  `[PreservesFiniteLimits uInv]`. `I : AlgebraicInverseImage uInv R RI` identifies
  the inverse-image ring and module operations and underlying set sheaves. This is
  exactly the algebraic inverse-image interface used by the recorded derived-pullback
  dependency, not an arbitrary unrelated module functor.
- The ring morphism is `c : RI ⟶ S`. There is no flatness assumption on `c`.
- The module pullback formula is `hobj`: `uStar.obj M = changeOfRings c (I.modules.obj M)`.
  `hmap` fixes the functor's action on morphisms to `changeOfRingsHom`, with the necessary
  equality transports. `[uStar.Additive]` is the additive structure of this specified
  tensor pullback, as in the recorded derived-pullback dependency; it does not ask for
  exactness, flatness, or an extra geometric property.
- `D(R)` and `D(S)` are precisely `DerivedCategory (SheafOfModules ...)`, with explicit
  `[HasDerivedCategory.{w} ...]` binders choosing the morphism universe, not a substitute
  derived category. The module category is definitionally the `ringedSiteModules`
  abbreviation of the dependency node, which transparently abbreviates Mathlib's
  `SheafOfModules`; the inherited Mathlib abelian instance is used.
- `LF`, `epsilon`, `hLF` specify the total left derived functor of the given termwise
  pullback on homotopy categories, using `Functor.IsLeftDerivedFunctor`. Its existence
  and computation on K-flat flat-term resolutions are the recorded
  `ringedTopoiDerivedPullback` theorem. Thus these binders name the `Lu*` appearing in
  the node, and do not assume the desired tensor compatibility.
- `PR`, `PS`, `hPR`, `hPS` specify exactly the full subcategories of K-flat complexes
  with flat terms. The biconditionals fix the predicates on every complex; they are
  not arbitrary classes of preferred representatives.
- `TR`, `TS`, `rR`, `rS` name the derived tensor bifunctors and their natural
  representative comparisons. Explicit `curriedTensor` with `monoidalCategory R/S`,
  followed by `map₂HomologicalComplex` and `Functor.uncurry`, is the recorded total
  tensor, with the differential signs of `def-pc-tensor-complex-sheaves`.
  The comparisons are natural isomorphisms on the full product of K-flat flat-term
  complexes, not just objectwise isomorphisms. They are restrictions to complexes of
  the homotopy-level comparisons supplied by `site_derived_tensor_descent`; the latter's
  localization equivalence and unique extension clause identify this bifunctor on all
  derived morphisms. These are representation specifications for the tensors named
  in the node, rather than new tensor definitions or assumptions of the conclusion.
- The first conjunct quantifies over every complex `P` and assumes precisely
  `P.IsKFlat` and `∀ n, (P.X n).IsFlat`. It concludes both K-flatness and flatness of
  every term of its actual termwise image under `uStar.mapHomologicalComplex`.
- The final `Nonempty (TR ⋙ LF ≅ (LF.prod LF) ⋙ TS)` is a natural isomorphism of
  functors on the product derived category. At `(F,G)` its direction is exactly
  `Lu*(F tensor_R^L G) ≅ Lu*F tensor_S^L Lu*G`. Naturality in the product includes
  arbitrary simultaneous maps of both derived inputs. The docstring records the
  canonical construction from ordinary tensor comparison and derived representative
  comparisons, and its independence of resolutions by two-variable localization.

The apparently auxiliary binders specify the named functors using the existing
existential dependency interfaces: they do not postulate K-flat preservation or
monoidality. No selected tensor or pullback is constructed anew. In particular,
there is no localization of ordinary termwise pullback on all complexes.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and `DerivedCategory.Qh`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat` and its explicit total-tensor
  predicate; `CochainComplex.IsKFlatResolution`; the zero-preservation instances.
- `Sheaf.Algebra.Homology.KFlatResolution`: `CochainComplex.exists_isKFlatResolution`
  (proof import).
- `Mathlib.Algebra.Homology.BifunctorShift` and `Bifunctor`:
  `CochainComplex.mapBifunctor` and `Functor.map₂HomologicalComplex`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  definitionally Mathlib's `SheafOfModules`, with the existing abelian structure.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: `SheafOfModules.changeOfRings`,
  `SheafOfModules.changeOfRingsHom`; `SheafOfModules.monoidalCategory` from the upstream
  monoidal module is the dependency's recorded sheaf tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: `SheafOfModules.IsFlat` is exactness
  of the right tensor functor, matching the node's flatness convention.
- `Sheaf.Paper.RingedTopoiDerivedPullback`: `SheafOfModules.ringedTopoiDerivedPullback`;
  its public `Sheaf.CategoryTheory.AlgebraicInverseImage` gives `AlgebraicInverseImage`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`:
  `SheafOfModules.site_derived_tensor_descent`, including naturality and unique descent
  for arbitrary transformations in two variables.
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`: `CochainComplex.kFlat_closure`
  (proof import, countable sums of flat sheaves).
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction` (proof import).

The proof-only nodes `lem-weil-pbc-ringed-pullback-preserves-kflat` and
`lem-weil-pbc-ringed-topoi-module-pullback-tensor` have no Lean records in this snapshot,
so no nonexistent module is imported. Their roles are preserved in the six-step
proof docstring. No other stated proof dependency has been omitted.

Edge cases checked: zero complexes and zero ring sheaves are allowed; no nonempty
site or nonzero ring hypothesis appears. There is no degree bound on the complexes,
and negative as well as positive degrees occur in `ℤ`. Nonflat scalar extension
(e.g. `ℤ → ℤ/2`) is included; ordinary pullback need not preserve all quasi-isomorphisms,
which is why `LF` is derived from homotopy categories rather than induced from
termwise pullback on arbitrary complexes. Both tensor inputs remain arbitrary derived
objects; only their resolving subcategories are restricted to K-flat flat-term complexes.
The tensor comparison is in the stated direction.

Searches made (2026-10-15, actual launcher search calls recorded in `searches.jsonl`):

- LeanFinder: `Derived pullback for ringed topoi commutes with derived tensor product of
  unbounded complexes`: eight hits, led by `SheafOfModules.pullbackComp`,
  `pullback_assoc`, `pullbackIso`; these concern ordinary pullback for continuous site
  functors, not the theorem on arbitrary geometric morphisms and unbounded derived tensor.
- Loogle: `SheafOfModules.pullback, CategoryTheory.MonoidalCategory.curriedTensor`:
  zero hits.
- Mathlib grep: `derived.*[Tt]ensor|[Tt]ensor.*[Pp]ullback` in
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- Upstream/project `rg` with that expression finds scheme and pro-etale specialized
  tensor/pullback material, plus the two general-site dependency modules. No existing
  arbitrary-ringed-topos derived tensor/pullback comparison was found. A separate
  exact node-id search in upstream `WeilConjectures` returned no hits, and an exact
  declaration-name search in upstream, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no collision. Mathlib `SheafOfModules.pullback` was read: it is an ordinary
  left adjoint for a continuous functor of sites, so it does not state this result.

Server compilation via `scompile.py`: clean after fully qualifying the K-flat
predicate on a `mapHomologicalComplex` object. The delivered file took 4.2 seconds;
all side imports were compiled in the server's private overlay, with nice 19,
two threads and the 60-second per-file limit. No local compiler was run.

No new nodes, dependency modules, statement changes, or disputed statements.

## Second reading by NE

I independently read the node copy, its nine statement dependencies and their recorded
signatures, the delivered module, and Stacks `sites-cohomology.tex` at
`lemma-pullback-K-flat` (0G7E) and `lemma-pullback-tensor-product` (07A4), including
the surrounding derived-pullback section. The source assumes a morphism of ringed
topoi and commutative structure rings; it imposes no flatness, finiteness, boundedness,
or geometric hypotheses. The node agrees with this source. No statement correction,
new definition node, or dependency replacement is required.

Object/hypothesis/conclusion checklist (in node order):

1. Two sites small relative to module sizes: `{C D : Type u}`, `[Category.{u} C]`,
   `JC`, `JD`. Verdict: correct small-site presentation in an arbitrary universe,
   matching the recorded pullback and descent interfaces. Smaller presentations may
   be lifted to this common universe; no cardinality or finiteness bound is imposed.
2. Commutative ring sheaves R and S: `R : Sheaf JC CommRingCat.{u}` and
   `S : Sheaf JD CommRingCat.{u}`. Verdict: correct; no field or nonzero assumption.
3. Geometric morphism from Sh(D) to Sh(C): `uInv`, `uPush`, `adj : uInv ⊣ uPush`,
   `[PreservesFiniteLimits uInv]`. Verdict: inverse-image direction and finite-limit
   condition agree exactly with the node. `AlgebraicInverseImage uInv R RI` uses
   the dependency's existing algebraic lift, including its underlying-sheaf natural
   isomorphism and generalized-section operation equations, rather than an unrelated
   additive functor.
4. Structure map: `c : RI ⟶ S`. Verdict: the required map from inverse-image R;
   no flatness is assumed.
5. Module categories and tensor pullback: the explicit Mathlib `SheafOfModules`
   categories are definitionally `CategoryTheory.ringedSiteModules`; their abelian
   structure is Mathlib's. `hobj` specifies extension of scalars after `I.modules`;
   `hmap` specifies the corresponding maps, with transports in the correct direction.
   The read `changeOfRings` sheafifies sectionwise extension of scalars, and
   `changeOfRingsHom` sheafifies `id tensor a`. Verdict: exactly the node's module
   pullback. `[uStar.Additive]` is its additive structure, already used by the recorded
   dependency, and does not assert exactness.
6. Unbounded D(R), D(S), and Lu*: `DerivedCategory`, `[HasDerivedCategory.{w} ...]`,
   `LF`, `epsilon`, `hLF`. Verdict: Mathlib's actual localization of integer cochain
   complexes, with the morphism universe explicitly chosen. `hLF` specifies the total
   left derived functor on the homotopy category; the recorded
   `ringedTopoiDerivedPullback` gives existence and computation on resolving complexes.
   This is not an assumption that ordinary pullback preserves all quasi-isomorphisms.
7. K-flatness and flatness: `P.IsKFlat` is the dependency's acyclic-test total-tensor
   predicate, read in `KFlat.lean`; `(P.X n).IsFlat` is exactness of right tensor,
   read in `Flat.lean`. `hPR`, `hPS` specify precisely their conjunction on all
   complexes. Verdict: the node's notions, without extra constraints on representatives.
8. Preservation clause: the first conjunct quantifies over every integer complex P,
   takes K-flatness and flat terms, and concludes both properties for its actual
   image under `uStar.mapHomologicalComplex`. Verdict: every clause present, no
   boundedness hypothesis and no ring-map flatness requirement.
9. Derived tensor computed by total tensor: `TR`, `TS`, `rR`, `rS`. Verdict:
   the comparisons are natural isomorphisms on the full product of K-flat flat-term
   complexes. The explicit existing `monoidalCategory` and `map₂HomologicalComplex`
   compute the same total tensor as the recorded `CochainComplex.mapBifunctor`:
   direct sums along p+q=n, with the second differential signed by (-1)^p.
   Reading `site_derived_tensor_descent` confirms these comparisons are supplied by
   its homotopy-level construction and uniquely specify the derived bifunctor up
   to natural isomorphism. The binders specify derived tensor, rather than assume
   its compatibility with pullback.
10. Comparison for every F,G, simultaneously natural: the second conjunct
    `Nonempty (TR ⋙ LF ≅ (LF.prod LF) ⋙ TS)` is a natural isomorphism of functors
    on the full product derived category. Verdict: its component has exactly the
    stated direction and both inputs are arbitrary derived objects. The canonical
    construction is described in the six-step proof docstring: representative
    comparison followed by the inverse total pullback/tensor comparison, then unique
    two-variable descent. `Nonempty` expresses existence of this natural isomorphism;
    it does not choose an additional tensor structure.

Edge cases: empty sites and zero ring sheaves are admitted; there are no nonemptiness
or nontriviality binders. Zero complexes and complexes supported in degree zero are
included, and degrees range over all integers. There is no external index-set binder
to impose a nonempty restriction; total tensor includes all its integer summands.
Nonflat maps such as Z to Z/2 and every characteristic are admitted. Scheme hypotheses
and hence nonempty-scheme assumptions are absent. `u` is arbitrary and `w` explicitly
controls localization morphisms. Every variable and universe is bound by eye.

Independent searches, 2026-10-15: LeanFinder via `msearch.py`, query
`Strong monoidal left derived inverse image between ringed topoi`, returned eight hits
on ordinary sheafification monoidality, ordinary pushforward adjunctions, and condensed
free functors; none states this result. Loogle, query
`CategoryTheory.Functor.IsLeftDerivedFunctor`, returned the existing derived-functor
interface and uniqueness/comparison API, not tensor compatibility. The `msearch.py`
grep query `pullback.*tensor|tensor.*pullback` found scheme pullbacks and categorical
cartesian tensors. Direct case-insensitive `rg` searches of Mathlib's module-sheaf
folder, upstream `WeilConjectures`, and project `lean/Sheaf` found ordinary site
pullback, scheme-specific derived tensor, pro-etale interfaces, and the general-site
input modules; no existing arbitrary-ringed-topos theorem with both conclusions.
An exact search for `ringedTopoiDerivedTensorPullback` in upstream, project Lean and
the upstream name index found no collision. I read the relevant input declarations
rather than treating any similarly named scheme or ordinary-pullback theorem as a match.

H5/H6/H8/H9: no definitions are added, and the sole theorem has only `sorry` as its
proof. The source and blueprint identifiers are in both docstrings. The theorem's
six proof steps track all six node proof steps, including flat total terms,
coproduct preservation, differential signs and descent for arbitrary derived maps.
No file-local notation/instance, private copy, hidden let/show binder, or additional
unbound parameter occurs. The node's `lean.statement` matches the file signature
verbatim. No mathematical or Lean mismatch was found; the module and node record
are retained unchanged. This second-reading report is the only change.

Independent server compilation succeeded through `scompile.py`: the delivered file
compiled in 4.3 seconds with no errors or warnings; side-only dependencies were
compiled separately in the private overlay, nice 19, two threads, 60 seconds per file.


## Maintainer search supplement, 2026-10-15

The independent stage-2 maintainer reviewer supplied the missing LeanSearch record;
this is a reviewer search, not a claim that the worker ran it.

- Tool: LeanSearch (`lean_leansearch`). Query: `Derived pullback between ringed topoi
  preserves unbounded derived tensor products`. Result: `HTTP Error 500: Internal
  Server Error`. Verdict: unavailable, not no match.
- Independent LeanFinder query: `For a morphism of ringed topoi the total left derived
  module pullback commutes with the derived tensor bifunctor`. Six results: ordinary
  `SheafOfModules.pullbackComp`, `pullback_assoc`,
  `pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc`,
  `conjugateEquiv_pullbackComp_inv`, `PresheafOfModules.pullbackComp`, and
  `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`. Their ordinary
  continuous-site pullback interfaces do not state the unbounded derived theorem.
- Independent direct `rg` searches in pinned Mathlib's module-sheaf directory,
  upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  used `derived.*tensor.*pullback|pullback.*derived.*tensor` (case-insensitive),
  and the exact declaration name and node id. The related hits are scheme,
  etale/pro-etale, and the existing general-site input modules; there is no exact
  existing arbitrary-ringed-topos statement with both conclusions. Exact-name/id
  searches returned no collision. The ordinary Mathlib pullback declaration was
  read in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:52`.

The delivered module was independently recompiled unchanged with server-only
`scompile.py`, against the private side overlay: 4.3 seconds, exit status 0, no
errors or warnings. All reported invocations used nice 19, two threads and a
60-second per-file limit. The report is the sole maintainer correction (H4 search
record omission); the Lean signature, node record and mathematics need no change.
