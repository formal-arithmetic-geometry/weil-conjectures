## Worker report

The module `Sheaf.RingTheory.ModuleLocalizationTowerVanishing` states
`DerivedCategory.module_localization_tower_vanishing_iff`, with its sole proof `sorry`.
The node statement and dependency lists are unchanged. No new nodes or dependency modules.

Clause-by-clause correspondence:

- A commutative ring: `{A : Type u} [CommRing A]`; an arbitrary element: `(f : A)`.
- The unbounded derived-category object: `(K : DerivedCategory (ModuleCat.{max u v} A))`.
  `HasDerivedCategory.{w}` chooses the morphism universe as required by the recorded
  abstract-derived-category declaration, without bounding cohomological degrees.
- The ring `A_f` is exactly Mathlib's `Localization.Away f`, namely localization at
  `Submonoid.powers f`. Its localization equivalence relation is the stated eventual
  equality after multiplication by a power of f, including rings with zero divisors.
  `ULift.{v}` merely transports this module into universe `max u v`; the existing linear
  equivalence `ULift.moduleEquiv` identifies it with the original module.
- Its degree-zero complex is `(singleFunctor (ModuleCat.{max u v} A) 0).obj
  (ModuleCat.of A (ULift.{v} (Localization.Away f)))`.
- Every term of the inverse tower is K: `K := fun _ : ℕ ↦ K`; every transition is
  `fun _ ↦ f • 𝟙 K`, using the canonical A-linear structure on the derived category.
- A product structure is expressed by `[HasProduct (fun _ : ℕ ↦ K)]`, required to
  formulate the dependency's Roos triangle. The theorem quantifies over that structure
  and any object T satisfying `hT : IsDerivedLimit ... T`; there is no chosen limit.
  Indexing from zero instead of one is the order-preserving renumbering of this tower.
- T is zero: `IsZero T`. The iff has exactly the node's orientation.
- For every integer shift q: `∀ (q : ℤ)` and source shift `⟦q⟧`.
- A Hom group is zero: `∀ (g : ... ⟶ K), g = 0`, literally every morphism is zero.
- No boundedness, injectivity, regularity, or nonzerodivisor hypothesis is present.

Statement dependencies used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.singleFunctor`; their full declarations
  and source docstrings were read. Basic is publicly imported through DerivedCategory.Linear.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimit`,
  whose source definition existentially quantifies p and delta and uses
  `IsDerivedLimitTriangle`. Both full definitions and docstrings were read.

Other public imports provide ModuleCat's abelian structure, derived A-linearity,
ULift's existing module structure, and principal localization. Non-public imports of
already stated proof dependencies are `Sheaf.Algebra.Homology.DerivedInternalHom`,
`Sheaf.Algebra.Homology.HomComplex`, `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`, and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` (the Mathlib match for
lem-weil-pbc-kinjective-hom-derived). The remaining proof dependency
lem-weil-pbc-local-hom-tower-criterion has no recorded module, so no import is available.
The declaration docstring records all four proof steps, including that future criterion.

Source checked directly: `literature/stacks-project/more-algebra.tex`,
lemma-hom-from-Af, including its unbounded-complex argument and multiplication-tower
notation immediately before it. The formulation is equivalence (1) and (3), with
shifted-source degree q corresponding to Ext degree -q.

Edge cases checked mathematically before writing:

- f = 0 or nilpotent: localization is the zero module, all displayed Hom groups vanish,
  and the multiplication tower has zero derived limit (1 minus the shift is invertible).
- f a unit: localization is A; multiplication is invertible, so a derived limit is
  isomorphic to K, and all shifted Hom groups vanish exactly when K is zero.
- K = 0 and the zero ring are permitted; both sides vanish.
- Arbitrary zero divisors and unbounded K are allowed by the source; the theorem has
  no hypotheses excluding either. Every integer shift, positive and negative, occurs.
- Independent u, v, w allow arbitrarily large module and Hom universes. The localization
  is lifted rather than forcing all modules into the ring's universe.

Searches made (msearch.py, group NO, this item):

- LeanFinder: "Vanishing of all shifted Hom groups from a principal localization equals
  vanishing of the derived multiplication tower". Eight hits, including
  HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE, hasExt_iff,
  subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE and isLE_Q_obj_iff; none compares
  principal localization with the multiplication tower.
- Loogle: `IsLocalization.Away, DerivedCategory`: zero hits.
- Mathlib grep through msearch: `Away.*(KInjective|homotopy|DerivedCategory)|
  (KInjective|homotopy|DerivedCategory).*Away`: zero hits.
- LeanSearch: "Hom from a principal localization vanishes in all shifts if and only if
  the derived multiplication tower limit is zero": unavailable, Internal Server Error.
- rg in the source WeilConjectures tree and lean/Sheaf:
  `Away.*(Derived|[Tt]ower)|[Tt]ower.*Away|lem-weil-pbc-module-localization-tower-vanishing`:
  unrelated scalar-tower localization occurrences; no equivalent theorem.
- grep -rn of the item id in upstream WeilConjectures: no match.
- rg for `module_localization_tower_vanishing_iff` in dag/lean_names_upstream.json,
  upstream WeilConjectures and lean/Sheaf: no match (name is new).
- rg for multiplication towers and IsDerivedLimit in lean/Sheaf located the existing
  DerivedCompleteModuleComplex module; its definition quantifies tower vanishing and
  does not state this localized-Hom characterization. Its recorded definitions were reused
  conceptually, without copying them or adding an unnecessary statement dependency.

Validation: scompile.py compiled the delivered module cleanly on the server under nice 19,
two threads, 60 seconds per file. No errors or warnings were emitted.
No statement dispute or node fault was found.

## Second reading by NO

I independently read the sandbox node and module against Stacks `more-algebra.tex`,
`lemma-hom-from-Af` (Tag 091P), including the preceding definition of T(K,f), all
conditions (1), (3), (6), (7), and the unbounded-complex paragraph in its proof.
The section introduces no Noetherian, regularity, boundedness, or nonzerodivisor
assumption. This node selects exactly equivalence (3) with (1), writing Ext in
shifted-source notation. No statement correction is needed.

The object/hypothesis/conclusion inventory, with its Lean rendering and verdict:

1. A commutative ring A: `{A : Type u} [CommRing A]`. Exact. No nontriviality,
   characteristic, finiteness, domain, or field restriction is imposed.
2. An arbitrary element f of A: `(f : A)`. Exact, including zero and zero divisors.
3. An object K of the unbounded D(A):
   `(K : DerivedCategory (ModuleCat.{max u v} A))` with
   `[HasDerivedCategory.{w} (ModuleCat.{max u v} A)]`. Exact. I opened the recorded
   abstract-derived-category node and Mathlib Basic: `HasDerivedCategory` is the
   chosen localization at quasi-isomorphisms with morphisms in Type w, and
   `DerivedCategory` is `HomologicalComplexUpToQuasiIso` for `ComplexShape.up ℤ`.
   This is not a bounded derived subcategory. `HasDerivedCategory.standard`
   supplies a choice at a sufficiently large universe; the binder expresses
   size/localization data, not an additional mathematical restriction.
4. A_f, localization at all powers of f, with the stated fraction relation:
   `Localization.Away f`. Exact existing Mathlib localization. I read Away.Basic
   and the monoid-localization construction: localization is the quotient with
   `mk_eq_mk_iff` and `r_iff_exists`, so equality allows multiplication by a further
   denominator. For powers of f this gives the node's eventual equality even
   with zero divisors. No cancellation is assumed.
5. A_f as an A-module concentrated in degree zero:
   `(singleFunctor (ModuleCat.{max u v} A) 0).obj
     (ModuleCat.of A (ULift.{v} (Localization.Away f)))`.
   Exact. Basic's `singleFunctor` is the complex concentrated at its index,
   followed by localization. Module.ULift supplies the transported scalar action
   and `ULift.moduleEquiv`; the lift changes size only, not the module.
6. The inverse tower with every term K and every transition multiplication by f:
   `(K := fun _ : ℕ ↦ K)` and `(fun _ ↦ f • 𝟙 K)` inside `IsDerivedLimit`.
   Exact. I read DerivedCategory.Linear: localization transports the canonical
   A-linear structure, so this scalar multiple is multiplication by f on K.
   I also read `towerProductShift` and `towerTransitionEndomorphism`: projection n
   of the endomorphism is projection n minus projection n+1 followed by f.
7. Any derived limit T of that tower:
   `[HasProduct (fun _ : ℕ ↦ K)]`, `(T : DerivedCategory ...)`, and
   `(hT : IsDerivedLimit ... T)`. Exact. I read the dependency node and both
   `IsDerivedLimit` and `IsDerivedLimitTriangle`: the predicate existentially
   quantifies p and delta making the Roos triangle distinguished; it chooses
   neither an object nor a canonical triangle. The product binder is precisely
   the prerequisite of that recorded notion. All choices of product structure
   and all such T are quantified, without assuming a categorical inverse limit.
8. First equivalent condition, T is zero: `IsZero T`. Exact categorical vanishing.
9. Second equivalent condition, every shifted-source Hom group is zero:
   `∀ (q : ℤ), ∀ (g : ...⟦q⟧ ⟶ K), g = 0`. Exact, including all integers and
   every morphism, rather than existence of a zero morphism. The displayed `↔`
   has the node's orientation. The source's Ext index is -q; quantifying all
   integers preserves precisely condition (1).
10. No boundedness or nonzerodivisor hypothesis: neither occurs in the signature.
    Exact. All implicit variables and universes are explicitly declared.

Edge cases independently checked: the zero ring and K = 0 are admitted. For f = 0
or nilpotent, A_f is zero and 1 minus the tower shift is invertible by a finite
geometric sum, so both conditions hold. For a unit f, A_f is A and the tower is
isomorphic to the identity tower; its derived limit is K, while Hom from all
shifts of A detects every cohomology module. Zero divisors need no cancellation.
The index is the fixed nonempty countable tower; an empty indexing family is not
part of this node, and starting at 0 rather than 1 simply renumbers it. q = 0 is
included together with all negative and positive degrees. There are no scheme
objects, so the empty scheme is not an additional case. Arbitrary characteristic
is allowed. Module objects have universe max u v, large enough for A_f and any
chosen larger module size; `ULift.{v}` puts A_f in that same universe. w is
independent localization morphism-size data, not a bound on degrees or test objects.

Independent H4 searches (different wording from the first reader):

- LeanFinder, via msearch: "Derived Hom from A localized at an element computes
  the inverse telescope of scalar multiplication on an unbounded complex".
  Eight results about derived fractions, categorical localization, A-linearity,
  and degree-bounded fractions. Their displayed signatures do not mention
  principal ring localization or a multiplication tower; no match.
- Loogle: `Localization.Away, IsZero` was rejected because the unqualified IsZero
  was unknown. Repeated as `Localization.Away, CategoryTheory.Limits.IsZero`:
  valid search, zero hits. The rejected search is not negative evidence.
- LeanSearch: "Derived Hom out of principal ring localization is the homotopy
  inverse limit of repeated scalar multiplication" returned Internal Server
  Error. Recorded as unavailable, not a negative mathematical result.
- rg in Mathlib's RingTheory and Algebra/Homology, the entire upstream
  WeilConjectures tree, and project lean/Sheaf, using telescope, homotopy limit,
  IsDerivedLimit, derived complete, orthogonal, Away, and localization. The broad
  search found scalar-tower/localization algebra and general homotopy limits.
  I opened the project DerivedCompleteModuleComplex: it defines vanishing of
  multiplication towers but does not state the localization-Hom equivalence.
  I also opened upstream Complete/Principal and Complete/Defs: their completion
  is via quotient-power tensor reductions; the orthogonality characterization
  assumes a principal nonzerodivisor and quantifies all invertible-action objects
  in a sheaf derived category. It is not this arbitrary-element module statement.
  Project HomotopyLimitVanishing is about transfinite unions of subcomplexes and
  null-homotopy into termwise injectives, also not a match.
- Exact item-id and declaration-name searches in upstream WeilConjectures,
  project lean/Sheaf, and dag/lean_names_upstream.json found no duplicate.

There are no new definition nodes or dependency modules in this delivery.
The two statement dependencies are usable as recorded and are actually imported;
no private copy or replacement notion occurs. The module defines no new data,
contains one named theorem with sole proof `sorry`, and its source-tagged docstring
carries all four node proof steps in order: trivial-site specialization, K-injective
Hom complex, shifted Hom/cohomology identification, and the local-Hom tower
criterion followed by acyclicity detection. Stated proof dependencies are imported;
the local-Hom tower criterion has no recorded module yet, as the worker noted.
Header, namespace, public imports, source references, and line widths conform.

Mismatches found: none. Changes: appended this independent second-reading record;
left the correct Lean file, node statement, dependency lists and lean signature intact.

Second-reader validation: scompile.py compiled the delivered file successfully on
server (1.2 seconds; nice 19; two threads; 60-second per-file limit), with no errors
or warnings. Its side dependency overlay also compiled cleanly. A textual check
confirmed that lean.statement equals the complete file signature verbatim and that
all Lean lines are at most 100 characters.
