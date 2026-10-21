## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.BoundedBelowHomTest` states
`DerivedCategory.isIso_of_boundedBelow_hom_bijective`; its only proof is `sorry`.
No definitions, hypotheses, clauses, or DAG dependencies were changed.

Clause-by-clause correspondence with lem-sf-bounded-below-hom-test:

- A small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
- The sheaf of commutative rings is `(R : Sheaf J CommRingCat.{u})`.
- Mod(O) is the dependency's `CategoryTheory.ringedSiteModules.{u}` applied to
  `((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)`. Forgetting to RingCat
  retains the commutative ring sheaf's underlying ring and its given action.
- The ordinary unbounded derived category is Mathlib's `DerivedCategory`, with
  `[HasDerivedCategory.{w} ...]` recording the localization and its Hom universe,
  exactly as def-weil-abstract-derived-category specifies. This is not D-plus.
- `{B G : DerivedCategory ...}` and `(α : B ⟶ G)` introduce both endpoints and
  the specified morphism. Neither endpoint has any boundedness predicate.
- The quantifier `∀ H : DerivedCategory ...` ranges over all objects.
  `(∃ a : ℤ, ∀ q : ℤ, q < a → IsZero ((homologyFunctor _ q).obj H))`
  is precisely eventual cohomological vanishing in negative degrees. It does
  not demand that H's chosen complex have zero terms there.
- `∀ n : ℤ` retains all integer shifts. `Function.Bijective
  (fun f : H⟦n⟧ ⟶ B ↦ f ≫ α)` is the stated postcomposition map, with
  injectivity and surjectivity, and with the source shifted in the stated direction.
- `IsIso α` is exactly the conclusion.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the recorded transparent abbreviation of `SheafOfModules`, with Mathlib's
  category structure and abelian instance (not a newly chosen instance).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`: ordinary localization at quasi-isomorphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`: cohomology on that localization.

The module includes non-public proof-plan imports for all recorded proof dependencies:
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` (def-kun-truncations),
`Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`
(lem-kun-complex-colimit-hocolim, including its module-sheaf specialization),
`Mathlib.CategoryTheory.Limits.HasLimits` (colimit), and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated` (triangulated structure
and `Triangle.yoneda_exact₂`/`Triangle.yoneda_exact₃`). The public derived-category
imports already provide def-weil-abstract-derived-category.
The theorem's docstring includes all seven proof steps and the explicit two
Hom-exactness chases. No theorem is proved in this delivery.

Sources read: the item's full statement and proof; both statement-dependency
nodes and their declarations/docstrings; the main-20261015 blueprint proof of
sk-prop-sf-rf-shriek-preservation, especially its final composition/open-locality
paragraph; the module-sheaf telescope specialization and the Hom-exactness signatures.

Edge cases checked: the empty site; the zero coefficient ring and zero objects;
H with merely cohomological lower boundedness; all negative, zero and positive
integer shifts; arbitrary unbounded B and G. No nonempty-site, nonzero-ring,
compactness, generator, or boundedness hypothesis is imposed. The site, coefficient
and module sizes use the common small-site universe u; w independently records
only the chosen derived Hom size, as in the recorded localization interface.

Actual searches:

- msearch.py leanfinder: "A morphism in the unbounded derived category of sheaves
  of modules is an isomorphism if Hom from every bounded below object and shift
  gives a bijection". Eight hits on localization, cohomology and individual
  truncation models, including `DerivedCategory.isIso_Q_map_iff_quasiIso` and
  `DerivedCategory.exists_iso_Q_obj_of_isGE`; no exact Hom-detection theorem.
- msearch.py loogle: `"DerivedCategory", "IsIso"`. Five hits, namely the Q-map
  quasi-isomorphism criteria, `DerivedCategory.isIso_iff`, the Qh criterion and
  the D-plus cohomology criterion; none is this bounded-below Hom test.
- msearch.py grep: `isIso.*[Hh]om|[Hh]om.*isIso|boundedBelow|IsBoundedBelow`
  in Mathlib/Algebra/Homology/DerivedCategory. Twenty-three hits, concerning
  cohomology, Q, Qh and localization; no exact theorem.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and
  `isIso_of_boundedBelow_hom_bijective`: no matching declaration.
- rg for `bounded.below.*[Hh]om.*(detect|isomorph)|[Hh]om.*bounded.below.*(detect|isomorph)`
  in both library roots and Mathlib's DerivedCategory directory found only
  `ExactFunctor.lean` (identity comparison on bounded-below homotopy objects) and
  `ExceptionalAdjointUniqueness.lean` (a specialized right-adjoint uniqueness statement
  with bounded-below endpoints). Their matching contexts were read; neither states
  the node's arbitrary unbounded-endpoint test.

No statement correction, new node, dependency repair or mathematical dispute is needed.

Validation: the prescribed scompile.py was invoked twice. It fails before compiling
this module, while loading the existing dependency RingedSiteModules: unknown module
prefix Mathlib, with only the live project's build path and Lean's core library in
its search path. Its fallback reports `Live published library is unavailable`.
This is a compiler-service/build-publication failure, not an elaboration diagnostic
in the delivered statement. The required deliver2.py --no-push dry run failed identically: `COMPILE FAILED on the server, nothing pushed`, followed by the same missing Mathlib path and `Live published library is unavailable`. No delivery was pushed.

## Second reading by Q22

Author's separate second pass (independent maintainer review remains required):
the node and theorem were read together. The site and commutative coefficient
sheaf match; ringedSiteModules uses the recorded declaration; localization has
an explicit Hom universe; lower boundedness is cohomological with its own
existential integer bound for each H; every n is retained; the function is
postcomposition from Hom(H[n],B) to Hom(H[n],G); and the conclusion is IsIso α.
B and G are unrestricted. All binders and universes are explicit. The docstring
preserves the seven-step telescope proof rather than replacing the test by a
cohomology criterion. No mismatch was found on this reading. Compilation has not
been certified because the supplied build service cannot load its Mathlib dependency.

## Retry validation, 2026-10-21

Retained the saved packet and ran the required `deliver2.py Q22
lem-sf-bounded-below-hom-test --no-push` first. It again exited 1 before checking
the theorem: the overlay dependency `Sheaf.CategoryTheory.RingedSiteModules`
could not load the `Mathlib` prefix, and server confirmation returned
`Live published library is unavailable`. A subsequent prescribed `scompile.py`
retry exited 1 on the same dependency, now identifying the absent published object
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean`; server confirmation again
returned `Live published library is unavailable`. Neither result is a diagnostic
against this packet's theorem. No launcher tool, published source, or library
artifact was modified; the packet is retained and nothing was pushed.

## Saved-packet retry, 2026-10-21 04:11 UTC

Retained the previous module and node. The required first dry run
`deliver2.py Q22 lem-sf-bounded-below-hom-test --no-push` exited 1 before
checking the theorem. Two prescribed `scompile.py` invocations were also
started; the final retry confirmed the same exit-1 failure: the published
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean` is absent while
loading `Sheaf.CategoryTheory.RingedSiteModules`. Server confirmation again
reported `Live published library is unavailable`. This is not a busy-server
exit 124 or a packet elaboration error. No authorized source repair can
provide that published Mathlib artifact, and no tool or library was modified.

Compared the saved node with the current repository node: only `lean` differs.
Read the current statement dependencies and the full ringedSiteModules
declaration; the packet still uses those interfaces. The statement and its
clause-by-clause self-check remain unchanged. Compilation is unverified and
nothing was pushed.

## Saved-packet retry, 2026-10-21 04:12 UTC

The required first `deliver2.py Q22 lem-sf-bounded-below-hom-test --no-push`
and a direct prescribed `scompile.py` retry both exited 1 before checking the
statement. Both identify the missing published object
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean` while loading
`Sheaf.CategoryTheory.RingedSiteModules`; server confirmation says
`Live published library is unavailable`. This is not exit 124 or an elaboration
failure in the packet. No published artifact or launcher tool was modified.

Retained the Lean statement and verified its recorded signature verbatim and
its 100-character line limit. Refreshed the copied node's newly changed upstream
`lean_audit` field so that only `lean` differs from the current repository node.
Compilation remains unverified and nothing was pushed.

## Saved-packet retry, 2026-10-21 04:18 UTC

Retained the saved packet and ran the required first `deliver2.py Q22
lem-sf-bounded-below-hom-test --no-push`. It exited 1 before checking the
item: the wrapper waited for a concurrent compile and then reported
`LOCAL COMPILE (exit 124)` for the existing upstream overlay dependency
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, with
`timeout after 60 s`. Server confirmation returned
`Live published library is unavailable`. A prescribed `scompile.py` retry
of the saved module exited 1 with exactly the same upstream timeout and
server confirmation. These are dependency-compilation diagnostics, not
the busy-service message `no answer from the compile server`. Neither
attempt reached this packet's theorem. The failing upstream module and
the published artifacts are read-only; no tool or artifact was modified.

Self-check against current sources: only `lean` differs between the saved
node and the repository node; both recorded statement dependencies and
their full declarations/docstrings were read, together with the source
blueprint proof. The saved signature matches `lean.statement` verbatim,
all Lean lines meet the 100-character limit, and the theorem has exactly
one `sorry`. The module and node are retained unchanged. Compilation
remains unverified and nothing was pushed.

## Current repair and validation, 2026-10-21

Retained the packet and began with the prescribed dry run. That first run
confirmed the previously reported 60-second timeout in upstream
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
Sandbox diagnostic copies tested `@[no_expose]` on its definitions and
transparency options through scompile.py; these did not establish a clean
repair. No upstream source, launcher script, or published artifact was edited.

An isolated diagnostic compile of the exact theorem, omitting only the two
project proof-plan imports, revealed a genuine missing import:
`J.HasSheafCompose (forget₂ CommRingCat RingCat)` could not be synthesized.
Added `public import Mathlib.Algebra.Category.Ring.Limits` to the delivered
module. Its `CommRingCat.forget₂Ring_preservesLimits` instance supplies the
forgetful sheaf composition. Recompiled the isolated statement with scompile.py:
both sandbox and library passes succeeded, in 6.0 and 5.7 seconds, without
warnings. The delivered file retains both original project proof-plan imports;
its theorem signature and all hypotheses are unchanged.

Subsequently the full prescribed scompile.py invocation progressed past the
earlier dependency and failed instead on
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`: its imported published
object `WeilConjectures/Topology/Stratification.olean` does not exist.
The required deliver2.py --no-push retry independently confirmed exactly
this missing artifact in both its overlay and server-confirmation paths,
in approximately 0.5 seconds. It did not reach the delivered theorem and
printed `COMPILE FAILED on the server, nothing pushed`. This is a missing
published artifact in the compiler service, not a 60-second elaboration timeout
or an absent mathematical declaration. The Stratification source is present
in the read clone, and scompile.py --source successfully returned its current server source.
The final full-file compile remains uncertified and no delivery has been pushed.

Current self-check: refreshed all non-owned node fields from the read clone;
only `lean` differs. The Lean signature still matches lean.statement verbatim;
all lines meet the 100-character limit; the sole proof is sorry; variables and
universes are explicitly bound. The import repair does not change any clause
of the correspondence in the Worker report or its second reading.


## Successful retained-packet validation, 2026-10-21

Retained the saved theorem, imports and node record. The prescribed dry run
`deliver2.py Q22 lem-sf-bounded-below-hom-test --no-push` now exits 0 and
prints `OK (dry run): commit c2ee8eb22b8 passes the preflight and compiles;
nothing pushed`. The earlier build-service failures documented above are
resolved for this packet; its full delivered module is now compilation-certified.

Repeated the self-check against the current repository node and both recorded
statement-dependency interfaces. Only `lean` differs from the current node;
`lean.statement` matches the theorem signature verbatim. All variables and
universes are explicitly bound, all Lean lines have at most 100 characters,
and the only theorem proof is one `sorry`. The small site, commutative ring
sheaf, ordinary unbounded derived category, cohomological lower bound for each
test object, every integer shift, postcomposition bijection and isomorphism
conclusion agree clause by clause. Neither endpoint has a boundedness
hypothesis. The empty site, zero ring and zero test objects remain allowed.
No statement correction, new node or dependency repair was needed.
