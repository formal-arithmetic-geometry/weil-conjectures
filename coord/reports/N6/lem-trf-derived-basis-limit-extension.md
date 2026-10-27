## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedBasisLimitExtension` states
`AlgebraicGeometry.derived_basis_limit_extension`, with its proof `sorry`.
The real-data helper `derivedOpenMapRestrictHom` is the canonical inverse
`derivedModuleOpenMapCompIso` followed by the derived restriction of a morphism.
It introduces no chosen map, extra datum, theorem or independent notion.
Both declarations have source and blueprint docstrings. The node's mathematical
statement and proof are unchanged. Its statement dependencies now include the
canonical-comparison definition node requested in return H2/H4.

Hypothesis-by-hypothesis correspondence:

- The scheme is `X : Scheme.{u}`. The global and all-open
  `HasDerivedCategory.{w}` binders select the shared derived categories.
  As in the recorded increasing-union and local-Hom-gluing dependencies,
  `D(O_U)` is encoded as
  `DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))`.
  The canonical `Scheme.Modules.overEquiv U` identifies this with modules on
  the open subscheme. These are the same module-sheaf categories and restriction
  functors as the proof dependencies, with no extra mathematical hypothesis.
- The set of opens is `B : Set X.Opens`; `hcover : sSup B = ⊤` is its covering
  condition. `hrefine` is exactly the union-of-basis-subopens description of
  every intersection. No topological basis assumption is added.
- `K U` is the given object for each member of B. `rho U V h` is the given
  restriction isomorphism for V contained in U. `rho_id` equates its diagonal
  component with the canonical identity restriction comparison, constructed
  sectionwise by `Iso.refl`, then passed to the derived category.
  This identity comparison is written as a term: the named helper in
  `DerivedBasisBbdDescent` belongs to the downstream parent, whose proof uses
  this item; importing that parent would close the intended import cycle.
  No duplicate identity declaration is made. `rho_comp` states the cocycle,
  with the canonical comparison accounting for iterated restriction.
- `hnegative` is negative self-Hom vanishing of every K_U, expressed by
  `Subsingleton (K U ⟶ (K U)⟦i⟧)` for every integer i < 0.
- `lambda : Ordinal.{v}` allows an arbitrary set-sized ordinal, independently
  of the scheme universe. `hlimit : Order.IsSuccLimit lambda` says it is nonzero
  and a limit. The stages are indexed by `lambda.ToType`.
- `W` gives the opens, `hincreasing` their monotonicity, and `hunion` says
  each stage is a union of members of B. `hcontinuous` uses
  `Order.IsSuccPrelimit delta`; this means precisely continuity at nonzero
  limits together with the initial empty-open condition. At the least stage
  the predecessor subtype is empty and its supremum is bottom. Thus the
  separate written condition W_0 = empty is included, not omitted.
  The final open is the actual union `iSup W`, not an arbitrary supplied open.
- `F beta` and `s beta U h` give the supplied solution on each stage.
  `hs` is its compatibility with every basis inclusion. `hFnegative` is
  exactly the separate negative self-Hom condition on the stage objects.
- `r gamma beta h` gives every strict-stage comparison. `hr` is its cocycle,
  for every eta < gamma < beta. `hrs` is precisely the equation saying it
  preserves all supplied structure maps on basis opens in W_gamma.

Conclusion clause-by-clause correspondence:

- `L` belongs to the derived category on `iSup W`.
- `sL U h` supplies an isomorphism for EVERY basis member contained in the
  final union. The first conjunction states every solution inclusion equation.
- `rL beta` is the comparison to each supplied F_beta. The second conjunction
  is `r_gamma^beta (r_beta restricted) = r_gamma`.
- The third conjunction is exactly
  `s_lambda,U = s_beta,U (r_beta restricted to U)` for each U in W_beta.
- The last conjunction quantifies over EVERY U in the final basis collection.
  Its first part is the defining equation on every V contained in both U and
  W_beta. Its second part quantifies over ALL morphisms `a`, with the same
  equation, and concludes `a = (sL U hU).hom`. Together these state that sL is
  the unique morphism with those restrictions. It is an isomorphism because
  sL itself is iso-valued. Uniqueness is not restricted to invertible maps.
- No U is required to lie in one stage. There is no quasi-compactness,
  finite-cover, boundedness or quasi-coherent-cohomology assumption.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphism
  structure and `Scheme.Opens` (def-pc-scheme).
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (def-pc-derived-category), read
  together with its underlying sheaf-of-modules category and universes.
- `Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion`:
  `derivedModuleOpenMapCompIso` in the public statement interface;
  `derived_basis_increasing_union` for proof step 1.
- `Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue`:
  `derived_basis_local_hom_glue` for proof steps 3--5, a plain proof import.
  The full recorded signatures and docstrings of both proof dependencies were read.

Sources: read Stacks cohomology.tex, Situation 0D67, uniqueness 0D68,
increasing-union 0D6B, and the entire BBD gluing theorem 0D6C and its final
limit paragraph. Also read the current `literature/blueprint/latest` unit
sk-i-curve-zero and the ancestor lem-trf-local-term-locality statement/proof.
The item is an auxiliary source-based gluing lemma, not the unit statement.

Edge cases checked before and after writing: X empty and B empty; the empty
open included in B; all W_beta empty; repeated stages; zero K and F;
U contained in the final union but in no individual stage; equality in basis
inclusions; strict ordinal comparisons; arbitrary negative shift; no upper or
lower cohomological bound. In the empty cases the conclusion and uniqueness
use the singleton Hom sets on the empty open, as the dependency explicitly
allows. The canonical comparison in every nested restriction keeps the
source and target of the equations correct even for equality inclusions.

Searches for an existing exact statement:

- msearch LeanFinder: "Extend compatible derived object identifications to every
  basis open at a continuous ordinal union with negative self Ext vanishing".
  Eight hits, led by `DerivedCategory.IsLE` and bounded-representative lemmas;
  none states the extension or its uniqueness.
- msearch LeanSearch: "Gluing derived complexes along a continuous ordinal union
  and extending isomorphisms to every basis open". Eight hits, ordinary
  presheaf/sheaf or topological gluing; no derived extension theorem.
- msearch Loogle: `DerivedCategory, "glue"`: zero hits.
- msearch grep: `derived.*(increasing|ordinal|gluing)|(increasing|ordinal).*derived`
  in Mathlib/AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for derived/basis/ordinal gluing,
  the item id and `limit_extension`; rg in dag/lean_names_upstream.json.
  Found the two proof dependencies and the parent `derived_basis_bbd_descent`,
  not this more explicit continuous-limit extension statement. The parent is
  downstream and does not supply the prescribed-stage and all-morphism
  uniqueness clauses of this item as a declaration.
- Read Mathlib's overMap and its existing canonical comparisons; reuse the
  shared module and derived categories, derived overMap, and
  `derivedModuleOpenMapCompIso` instead of new copies.

Validation: the prescribed scompile.py server check compiled the delivered
file in both sandbox mode (21.6 seconds) and library mode (22.3 seconds),
with no errors or warnings. No mathematical statement correction is needed. The H2/H4 repair below
adds the missing definition node and statement dependency. The only postponed theorem is the item's own theorem.

## Repair of returned delivery 2b18da31a6be

H2/H4: `derivedOpenMapRestrictHom` uses
`AlgebraicGeometry.derivedModuleOpenMapCompIso`, which in turn uses
`AlgebraicGeometry.moduleOpenMapCompIso`. The previous packet reached these
plain definitions only through the proof-dependency theorem module. Added
`def-trf-module-open-map-comp-iso` to the item's `stmt_deps` and recorded both
existing declarations under that definition node. The existing public import
now corresponds to a definition statement dependency. No Lean source or
mathematical statement changes are required. The maintainer's independent
reading of the returned head accepted all hypotheses, clauses and edge cases.

## New nodes

`def-trf-module-open-map-comp-iso` records the canonical comparison between
successive and direct restrictions on localized open sites, and its derived
comparison. The source is the restriction convention in Stacks 0D6B/0D6C.
It depends on `def-pc-scheme` and `def-pc-derived-category`, and reuses the exact
real-data definitions `moduleOpenMapCompIso` and `derivedModuleOpenMapCompIso`
in `Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion` with `existing: true`.
LeanSearch, Loogle, Mathlib grep, project/DAG rg and blueprint_refs.py searches
found related restriction APIs and these exact project definitions, but no
definition node recording them. Their signatures and complete bodies were
checked: the ordinary comparison is sectionwise `Iso.refl`, and the derived
comparison is `(Functor.mapDerivedCategoryCompIso _ _).symm` followed by
`Functor.mapDerivedCategoryNatIso (moduleOpenMapCompIso X i j)`. Identity
inclusions, coinciding opens and empty opens are all allowed.

## Repair self-check by N6

Compared the retained packet with current main: the main node has no Lean
record yet, and there is no landed comparison-definition node. Relative to
the returned packet the only item changes are the added definition dependency
and the Lean record date. The theorem signature and real-data helper are
unchanged. The new node describes both existing definitions and introduces no
extra hypotheses or chosen maps. The statement-level import of their module
is now justified by the explicit definition dependency.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
