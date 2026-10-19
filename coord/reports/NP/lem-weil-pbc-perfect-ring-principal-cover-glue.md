## Worker report

The module `Sheaf.RingTheory.PerfectPrincipalCoverGlue` states
`DerivedCategory.isPerfect_of_principal_cover`, with its proof exactly `by sorry`.
It formalizes Stacks Project, More on Algebra, Tag 066Y, `lemma-glue-perfect`.
The source was read in `literature/stacks-project/more-algebra.tex`, at that label.
No statement correction, new definition, or dependency replacement is needed.

Hypotheses and conclusion, clause by clause:

- A commutative ring R is `{R : Type u} [CommRing R]`.
- The object C in D(R) is `C : DerivedCategory (ModuleCat.{u} R)`;
  `HasDerivedCategory.{u}` supplies the node's chosen morphism universe.
- A finite family of r elements, with r allowed to be zero, is `(r : ℕ)
  (f : Fin r → R)`.
- Generation of the unit ideal is exactly `hf : ∃ v : Fin r → R,
  ∑ i : Fin r, v i * f i = 1`, including the coefficients explicitly stated in the node.
- The ring R[1/f_i] is the existing `Localization.Away (f i)`; its structural
  ring map is `algebraMap R (Localization.Away (f i))`. The dependent
  `HasDerivedCategory` instance supplies D(R[1/f_i]) for each i.
- Derived scalar extension is named `L i`, with counit `ε i` and the class
  `(L i).IsLeftDerivedFunctor (ε i) (HomotopyCategory.quasiIso ... (.up ℤ))`.
  The functor being derived is precisely termwise `ModuleCat.extendScalars`
  along the structural ring map, followed by the target localization `Qh`.
  Its additive structure is supplied explicitly by the extension/restriction
  adjunction, with no local instance or extra additivity hypothesis.
  These binders specify the derived operation already used in the node;
  they do not allow an arbitrary functor or require a new ring hypothesis.
  Existence is the ring-module specialization of derived change of rings,
  and uniqueness of left derived functors makes the statement independent of
  this presentation. This uses the same universal-property encoding as the
  landed `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance` statement.
- Local perfection for every i is `hlocal : ∀ i : Fin r,
  IsPerfect ((L i).obj C)`.
- The conclusion that C is perfect is exactly `IsPerfect C`.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the localization functors; these are the recorded
  declarations of `def-weil-abstract-derived-category`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, imported
  via `Mathlib.RingTheory.Localization.Away.Basic` to obtain its ring and algebra
  structures, as required by `def-weil-ring-localization-away`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect`: `DerivedCategory.IsPerfect`.
  Its complete definition is an isomorphism to `Q.obj P`, where P has a lower and
  upper strict bound and every term is projective and finitely generated.
  This is exactly `def-pc-perfect-ring-complex`, with no Noetherian assumption.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: `SheafOfModules.derivedChangeOfRings`.
  The recorded theorem supplies the universal left derived functor of termwise
  scalar extension; its one-object-site specialization is the ordinary module
  scalar extension used here. Its module is retained as a proof import.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `ModuleCat.extendScalars`,
  `ModuleCat.extendRestrictScalarsAdj`; `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`:
  `CategoryTheory.Functor.IsLeftDerivedFunctor`. These existing APIs specify the
  ring-module derived scalar extension without defining a second operation.

All stated proof dependencies are imported, including the localization and tensor
flatness leaves, K-flat resolutions, finite-free replacement, pseudo-coherence and
its localization descent, the flat model criterion for Tor amplitude, and the
pseudo-coherence plus finite Tor criterion for perfectness. The proof dependency
`lem-weil-pbc-tor-amplitude-principal-cover-glue` has no recorded Lean module on this
base, so there is no import to add yet; step 4 of the theorem's docstring records it.
This does not prevent elaborating the statement. The docstring carries all five
steps of the node's proof.

Edge cases checked: r=0 makes the cover equation 0=1, so R is the zero ring;
all unital modules are then zero and C is perfect. No Nonempty or Nontrivial
hypothesis excludes that case. A zero member of a nonempty cover gives the zero
localization, which is allowed. A unit member localizes to R. Repeated members,
zero objects, arbitrary characteristic, and non-Noetherian rings are allowed.
The existing perfectness definition uses ring and module universe u; any ring
and any chosen small complex fit after increasing the common universe. No
quantification over modules in a smaller, unrelated universe is introduced.

Searches performed (2026-10-15):

- msearch leanfinder, query: `A derived ring complex perfect after localizing at finitely many elements generating the unit ideal is perfect`.
  Eight hits about smoothness and localization (including
  `Algebra.IsSmoothAt.exists_notMem_smooth` and
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`); none is perfection descent.
- msearch loogle, query: `DerivedCategory.IsPerfect, Localization.Away`.
  Zero hits; Mathlib service does not know the project's `DerivedCategory.IsPerfect`.
- msearch grep, query: `perfect.*localiz|localiz.*perfect|isPerfect.*[Gg]lue`.
  Zero Mathlib hits.
- msearch leansearch, query: `Perfect complexes descend along a finite principal localization cover of a commutative ring`.
  Service unavailable (Internal Server Error); no verdict inferred from that search.
- rg of the upstream WeilConjectures tree and the project's `lean/Sheaf`, query:
  `perfect.*localiz|localiz.*perfect|lem-weil-pbc-perfect-ring-principal-cover-glue`.
  Upstream only has a smooth-localization discussion. Project hits concern
  geometric localization, derived tensor identities, or other perfectness criteria;
  none states finite principal-cover descent for arbitrary derived ring objects.
- rg for `isPerfect_of_principal_cover` in upstream declaration inventory,
  upstream WeilConjectures, Mathlib, and project Sheaf: no collision.

Validation: scompile.py compiled the delivered module on the server in 1.6 seconds,
nice 19, two threads, 60 seconds per file, without errors or warnings. Nothing was
proved, no local compilation was run, and no source checkout was edited directly.

## Second reading by NP

I independently read the node, Tag 066Y (`lemma-glue-perfect`) in
`literature/stacks-project/more-algebra.tex`, its chapter introduction, the delivered
Lean, and the recorded statement-dependency declarations. The source works in
commutative algebra and permits unbounded complexes; it imposes no Noetherian,
nonzero-ring, or finite-generation hypothesis on the original complex. Flatness
of localization identifies its ordinary localized complexes with the node's
derived scalar extensions.

My object/hypothesis/conclusion checklist, matched against the actual signature:

1. An arbitrary commutative ring R: `{R : Type u} [CommRing R]`. Exact; no field,
   Noetherian, domain, or Nontrivial instance is present.
2. An object C in D(R): `[HasDerivedCategory.{u} (ModuleCat.{u} R)]` and
   `(C : DerivedCategory (ModuleCat.{u} R))`. I opened Mathlib's
   `DerivedCategory.Basic`: `HasDerivedCategory` chooses a localization, and
   `DerivedCategory` is the localization of integer cochain complexes at
   quasi-isomorphisms. This is the recorded abstract derived category, not a
   bounded subcategory. Verdict: exact.
3. A finite list of elements, with length allowed to be zero: `(r : ℕ)` and
   `(f : Fin r → R)`. No nonempty premise. Verdict: exact.
4. Generation of the unit ideal with the node's explicit coefficients:
   `(hf : ∃ v : Fin r → R, ∑ i : Fin r, v i * f i = 1)`.
   No coefficient is fixed or assumed invertible. Verdict: exact.
5. Each localization R[1/f_i]: `Localization.Away (f i)`, with
   `algebraMap R (Localization.Away (f i))`. I opened the recorded monoid
   localization abbreviation (localization at `Submonoid.powers`) and the ring
   API used by the import. The dependent `HasDerivedCategory` instance simply
   chooses the target derived category. Verdict: exact.
6. Derived extension of scalars to that localization: `L i`, `ε i`, and
   `[(L i).IsLeftDerivedFunctor (ε i) ...]`. I opened Mathlib's
   `ModuleCat.extendScalars` (objects are S tensor_R M), its extension/restriction
   adjunction, and `Functor.IsLeftDerivedFunctor` in `Derived.LeftDerived`.
   The latter requires the right Kan extension along the quasi-isomorphism
   localization; `leftDerivedUnique` supplies uniqueness up to natural
   isomorphism. Thus these are choices of the specified derived operation,
   rather than an unconstrained functor or a stronger ring hypothesis.
   The explicit `left_adjoint_additive` argument supplies the additive proof
   needed to map homotopy categories; it adds no hypothesis.
   I also read `SheafOfModules.derivedChangeOfRings`: its termwise scalar
   extension, universal counit, and K-flat computation give the cited operation
   on the one-object site. No substitute definition is introduced. Verdict: exact.
7. All localized objects perfect: `(hlocal : ∀ i : Fin r,
   IsPerfect ((L i).obj C))`. The quantifier is over every member of precisely
   the given cover, after choosing its scalar extension. Verdict: exact.
8. C perfect: conclusion `IsPerfect C`. I opened upstream
   `WeilConjectures.CategoryTheory.DerivedCategory.Perfect`, where `IsPerfect`
   is an isomorphism to `Q.obj P` with integer strict lower and upper bounds,
   and `Module.Projective` and `Module.Finite` for every term. This is exactly
   the dependency node's notion, with no Noetherian premise. Verdict: exact.

Edge cases: `r = 0` forces `0 = 1` via `hf`; the zero ring and its zero derived
objects are allowed. A zero member gives the allowed zero localization. A unit
member, repeated elements, zero C, every characteristic, and non-Noetherian R
are admitted. There is no scheme, empty-scheme, or degree-n parameter here.
The common universe u is the universe of the recorded upstream `IsPerfect`;
any ring and complex can be placed in a common enlarged universe. There is no
independent smaller test-module universe, no boundedness premise on C, and all
variables/universes in the signature are explicitly bound.

Independent H4 searches, with queries different from the first reader's:

- msearch leanfinder: `Descent of a bounded finite projective complex from finitely many basic open localizations`.
  Eight hits, mostly Proj covers and `Module.basicOpen_subset_freeLocus_iff`;
  none concerns descent of a perfect derived object.
- msearch loogle: `"ModuleCat.extendScalars", "IsPerfect"`: zero hits.
- msearch grep: `principal.*perfect|perfect.*principal|IsPerfect.*localization`:
  one irrelevant perfectoid period-ring comment.
- msearch leansearch: `A complex is perfect if it becomes perfect on each member of a finite cover by basic open sets`:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- Direct rg in Mathlib, upstream WeilConjectures, and project Sheaf for
  `perfect.*[Ll]ocaliz|[Ll]ocaliz.*[Pp]erfect|principal.*[Pp]erfect|isPerfect_of_principal_cover`.
  Hits concern geometric pullbacks, Koszul complexes, or perfectoid rings, not
  finite principal-cover descent for arbitrary derived ring objects. The new
  declaration name has no collision. No existing exact statement was found.

There are no new definition nodes, dependency replacement modules, or statement
corrections in this delivery. I also checked the pseudo-coherence localization
and finite-Tor perfectness proof interfaces: their actual signatures supply the
steps the docstring describes. The still-unstated Tor-amplitude cover lemma is
correctly named in proof step 4, without an invented import. All five DAG proof
steps are present in the theorem docstring, including the common interval and
empty-family choice. The only delivered proof is `by sorry`; there is no hollow
definition, private helper, local notation, or proved auxiliary statement.

Mismatches found: none. Changes: appended this independent second-reading
record; retained the Lean and node signature unchanged. A textual check confirms
`lean.statement` is verbatim the theorem signature, with no line above 100
characters. Validation uses only the required server scompile.py command;
the first invocation used a relative path from the read-only clone and failed
before compilation, so I reran it with the absolute sandbox module path.
The corrected absolute-path invocation compiled the sole delivered module cleanly
in 1.6 seconds, nice 19, two threads, with the 60-second limit and no warnings.
