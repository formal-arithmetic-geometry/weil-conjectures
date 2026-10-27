## Worker report

Item: def-sfb-dc-hom. The module
`Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves` restores the missing
conditional restriction, with full data and no sorry. This repaired delivery contains
only the item module, its lean record, and this report. The finiteness dependency
record remains as on the base branch; no dependency module is delivered.

Clause-by-clause correspondence:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The base is `{k : Type u} [Field k]`.
  `[Fact (ringChar k).Prime]` makes its characteristic p a positive prime, and
  `[Fact (ringChar k ≠ ℓ)]` states the required inequality of primes.
- The separated scheme of finite type over k is `X : Over (Spec (.of k))` with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`.
  These are the setting dependency's existing bundled scheme-over-field conventions.
- The arbitrary commutative condensed ring is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is the object/structure form of the recorded
  `Profinite.CondensedRing = Mon (Sheaf ... Ab)`; no topological presentation is assumed.
- The pulled-back ring object is exactly `condensedRingObj Λ X.left`.
  `BoundedConstructible` is the recorded full subcategory of its ordinary unbounded
  derived internal-module category, with bounded constructible cohomology and without
  derived completeness. The ambient H is the recorded `derivedHom Λ X.left`.
- The preservation hypothesis is `h : ∀ K L : BoundedConstructible ...,
  boundedConstructible ... (((derivedHom ...).obj (op K.obj)).obj L.obj)`.
  It is precisely preservation on pairs of objects of C, without tensor closure,
  a monoidal structure on C, or an ell-adic finiteness-coefficient hypothesis.
- The output is a curried bifunctor `Cᵒᵖ ⥤ C ⥤ C`, equivalently the displayed
  product-category bifunctor. Precomposition is by `ι.op.prod ι`.
  `ObjectProperty.lift` takes the same ambient H object and attaches `h`;
  its morphism is `homMk` of the ambient map. Consequently u and v act by the
  contravariant/covariant ambient maps. Currying preserves this assignment using
  the ambient identity laws. Identity and composition are inherited from the
  existing functor constructions; there are no new postponed well-definedness claims.
- `boundedConstructibleHomOfPreservesCompatibility` compares
  `H_C(K,-) ⋙ ι` with `ι ⋙ H(ι K,-)` by `Functor.curryObjProdComp` followed by the
  inverse currying unit. Both have identity components and identity inverse components;
  `ObjectProperty.lift` forgets its certificate definitionally.
- The cited coefficient examples remain supplied by lem-sfb-dc-hom-preserves:
  its recorded finite-extension theorem states the rational and integral cases for
  `continuousCoefficientRingObj E` and the closed-unit-ball subring O, respectively.
  The existing `isMonoidalClosed_boundedConstructible`, owned by
  lem-sfb-dc-hom-small-coefficients, supplies the Qlbar case
  using `Profinite.padicAlgClRingObj ℓ`. The ring is the finite-subextension-valued
  condensed ring, not the full continuous-function sheaf on the algebraic closure.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  its setting binders, `compactificationOverField`, and the existing full-category notation.
  Compactification is contextual only: this restriction takes no morphism of schemes.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`; its underlying unbundled ring object as above.
- `sk-def-sfb-bounded-constructible`:
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly exports
  `AlgebraicGeometry.ProEtale.boundedConstructible`, `BoundedConstructible`, and
  `mem_boundedConstructible_iff`, originally in
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
  The discrete-coefficient auxiliary predicate is not substituted for the general one.
- `sk-def-sfb-derived-tensor-hom`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` (the existing closed derived
  relative-module tensor internal Hom, not an arbitrary bifunctor).
- `lem-sfb-dc-hom-preserves`: its base-branch record remains unchanged. Its
  `boundedConstructibleHom_finiteExtension` is background for the coefficient examples;
  the restriction itself takes preservation as the explicit parameter h and uses no
  declaration from that deleted module. The existing
  `isMonoidalClosed_boundedConstructible` belongs to lem-sfb-dc-hom-small-coefficients;
  it is not added to the finiteness dependency record.
- `sk-def-sfb-qlbar-condensed`:
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `padicAlgClRingObj`, via public imports.
- General machinery is Mathlib `ObjectProperty.lift`, `Functor.curry`,
  `Functor.uncurry`, `Functor.curryObjProdComp`, and `Functor.currying`.

Edge cases checked before finalizing:

- Empty schemes and zero complexes require no nonemptiness, positive rank, or nonzero
  object hypothesis. The lift is defined at every supplied pair, including zero pairs.
- General coefficients such as Z/4 need not preserve bounded Hom: `h` is essential,
  and is not inferred from a blanket coefficient instance.
- No tensor-preservation hypothesis, unit membership, dualizability, perfectness,
  completeness, or triangulated-subcategory hypothesis is introduced.
- p and ell are distinct positive primes; their ordering is irrelevant. Finite field
  extensions are allowed to have degree one. O is exactly the valuation unit ball by hO.
- Universe u stays explicit, sheaves are Ab.{u+1} on Profinite.{u}, and X is Scheme.{u}.
  The finite-extension interface retains E : Type u and uses the recorded Type 0
  transport route rather than requiring E itself to be Type 0.
- Both variables' variances were checked from `Functor.uncurry` and `ι.op.prod ι`.
  At identities, the currying comparison reduces by the ambient map-identity laws.

Searches actually run:

1. `msearch.py ... leansearch` with query
   `Restrict derived internal Hom of condensed module objects to bounded constructible complexes assuming preservation`:
   eight hits, including `LightCondensed.ihomPoints`, general derived Ext size facts,
   and condensed closed structures; no exact restricted constructible-module bifunctor.
2. `msearch.py ... loogle` with query
   `CategoryTheory.ObjectProperty.lift, CategoryTheory.curry`:
   zero hits, unknown identifier `CategoryTheory.curry` (the actual namespace is Functor).
3. `msearch.py ... leanfinder` with query
   `A bifunctor restricts to a full subcategory when it preserves the object property in both variables`:
   eight hits; `ObjectProperty.lift`, inclusion/fullness declarations, and localization
   machinery. Used the generic lift, which does not itself state this scheme/coefficient notion.
4. `msearch.py ... grep` with query
   `boundedConstructibleHom|restrictedDerivedHom|def curry|def uncurry`, directory CategoryTheory:
   sixteen hits, principally `Functor/Currying.lean` and unrelated curry/uncurry functions.
5. `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
   `boundedConstructibleHom|restrictedDerivedHom|def-sfb-dc-hom`:
   upstream `boundedConstructibleHom` and its compatibility found in the existing
   BoundedConstructible module, plus WeilObject users. Reading full signatures shows
   its extra `[IsEllAdicFinitenessCoefficient ℓ Λ]`; it cannot replace this node's
   arbitrary-coefficient conditional definition.
6. `msearch.py ... grep` for
   `boundedConstructibleHom_finiteExtension|boundedConstructible.*Hom`: zero Mathlib hits.
   `rg` of both project trees and `dag/lean_names_upstream.json` for
   `boundedConstructibleHom_finiteExtension|boundedConstructibleHomOfPreserves`:
   no existing declaration. The node records describe their prior deletion.
7. `scompile.py --source Sheaf.Paper.BoundedConstructibleHomFiniteness`:
   `Module source unavailable`. The local module is likewise absent. The return
   establishes that H5 had already proved it before its maintainer deletion; this
   absence does not authorize replacing that proof with a sorry. The dependency is
   unnecessary for the conditional restriction and is omitted from this delivery.

Read the current blueprint under `literature/blueprint/latest/` for the item,
its unit, and the finiteness dependency. It agrees with the node's conditional
restriction. No statement dispute or correction is needed.

Validation: the repaired item module is compiled alone through
`scompile.py N6 def-sfb-dc-hom`, followed by the required `deliver2.py --no-push`
and delivery checks. The final module has no sorry. The repair changes the returned
item module only by deleting the unused public import; both declaration signatures
and construction bodies remain exactly those approved in the returned head.

## Repair of returned delivery 4179cba36065

- R1 (H13): removed the sandbox dependency module
  `Sheaf.Paper.BoundedConstructibleHomFiniteness`. The base node records H5's proof
  landing `20261019T005303-L-2748498` and reviewed_proof pass on 2026-10-19. The earlier
  delivery incorrectly restored its deleted source with a sorry; the repair does
  not replace or reopen that proof.
- R2 (H13/H4): removed the sandbox dependency node copy. Thus
  `lem-sfb-dc-hom-preserves` remains exactly as on the base branch, including Q35's
  single-declaration record. `isMonoidalClosed_boundedConstructible` remains owned
  by `lem-sfb-dc-hom-small-coefficients`.
- R3 (H9): deleted exactly the item's unused
  `public import Sheaf.Paper.BoundedConstructibleHomFiniteness` line. The item uses
  the ambient derived Hom and explicit hypothesis h, so no finiteness theorem is
  needed to construct its conditional restriction.

Compared the retained sandbox with the returned module text and the current base
node records. The item's lean record still names the two unchanged declarations;
no mathematical statement or dependency list is changed. The final delivery has
one module, one item node copy with only its lean field changed, and this report.

## Second reading by N6

Re-read the current node JSON and final item module after applying R1--R3. No
separate agent was started, as the dispatch brief prohibits it. The maintainer's
independent return already accepted both item declarations clause by clause.

Rechecked prime ell, field k, positive prime characteristic unequal to ell,
separated finite-type X, arbitrary commutative condensed Lambda, and exactly
objectwise preservation h. The curried lift retains the ambient objects and both
morphism actions. The fixed-K inclusion comparison has identity components. All
variables and universes remain explicit, and neither signature nor construction
body changed in this repair. The item contains no sorry, no added finiteness
assumption, and no imported or delivered replacement of the deleted dependency.
The dependency record is absent from the repair's changed files, so its proof
status and declaration ownership are preserved.
