## Worker report

This stage-2 delivery states the item with one `sorry`, named
`AlgebraicGeometry.ProEtale.supported_finiteStage_topology_defect`, in
`Sheaf.Paper.SupportedFiniteStageTopologyDefect`. The helper
`supportedFiniteStageTopologyObject` constructs exactly G or H from the displayed
formula with real data. Only the node's lean field changes; no statement correction
or additional node is needed. The prior stale-assignment diagnosis confused reviewed
stage 1 with stage 2: the live node has NJ's reviewed split but no Lean record.

Clause-by-clause rendering:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field of characteristic p>0 different from ell is `(p : ℕ) (k : Type u)
  [Field k] [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)`.
- X is `Over (Spec (.of k))` with `LocallyOfFiniteType X.hom`,
  `QuasiCompact X.hom`, `IsSeparated X.hom`, exactly separated finite type over k.
- Omega is the existing standard algebraic closure `PadicAlgCl ℓ` with its
  extended ell-adic norm, as in the recorded coefficient definitions. The fixed
  model loses no isomorphism-invariant case. It is not completed.
- C is `Profinite.padicAlgClRingObj ℓ`, finite-subextension-valued continuous
  functions, and B is `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`, all norm-
  continuous functions. The latter is definitionally the recorded universe-general
  continuous-map construction at coefficient universe zero.
- Pulled-back rings are `condensedRingObj`; c_X is
  `coefficientMap (algClTopologyInclusion ℓ) X.left`, the existing actual inclusion.
- Categories are ordinary unbounded `DerivedCategory (Mod ... ...)` on the small
  site `Scheme.ProEt.topology`, with coefficient category `Ab.{u+1}`.
- J_X is the existing `algClTopologyScalarExtension ℓ X.left`, namely the total
  K-flat left-derived extension of scalars. U_X is `(Mod.comap c_X).mapDerivedCategory`.
- The unit in the triangle is precisely
  `(Mod.derivedExtendMapDerivedCategoryAdjunction c_X).unit.app H`; it is not an
  arbitrary map or an extra hypothesis. This existing derived adjunction is derived
  from the scalar-insertion unit v |-> 1 tensor v, with exact termwise restriction.
- Two independent immersions are `S T`, `a`, `b`, `ha : IsImmersion a`,
  `hb : IsImmersion b`. Their constructible images are `haCons` and `hbCons`.
  The source requires two constructible locally closed immersions, not a whole
  stratification; the recorded finite stratification module is imported, and its
  immersion predicate is Mathlib's same `IsImmersion`.
- `E F : PadicAlgCl.FiniteIntermediateField ℓ` quantify independently over all
  finite intermediate fields, with the inherited restricted norm topologies.
- L and M are module objects over `condensedRingObj (continuousMapRingObj E) S`
  and its independent F,T counterpart. `hL`, `hM` use the recorded
  `IsLisseCoefficientModule`, whose covering ranks vary and may be zero.
- G is `supportedFiniteStageTopologyObject ℓ X a ha E L`; H uses b,hb,F,M.
  The helper first forms `DerivedCategory.singleFunctor _ 0`, then total left
  derived `Mod.extendScalars` along the recorded
  `coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) S`, then applies
  exact termwise `coefficientHeartLocallyClosedExtension ... a ha`.
- That existing extension is open extension into the scheme-theoretic closure
  (`a.toImage`), followed by closed direct image (`a.imageι`), exactly i_* j_!.
  Its data is not selected from mere existence. The helper derives Noetherianity
  from `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`. It extracts only the existential
  Prop witness for exactness of the closed direct image from the recorded
  `condensed_open_closed_recollement`; it chooses no functor, map, or object.
  This lets it use `mapDerivedCategory` for the actual exact composite, rather
  than assuming exactness or replacing it by an arbitrary functor.
- Every triangle is encoded by arbitrary Q, v, w with
  `Triangle.mk (specified unit at H) v w ∈ distTriang _`. Thus every possible cone
  of the actual unit is covered. All shifts are `n : ℤ`.
- `Subsingleton (G ⟶ Q⟦n⟧)` says Hom=0, since the ambient category already has
  a zero morphism. No extra flatness hypothesis appears.

Every variable and universe is explicit, with `set_option autoImplicit false`.
There is no let/show binder in the theorem statement. The only local instances
are inside the real helper's construction, not file-local statement dependencies.
Every theorem proof is sorry; all eight DAG proof steps are in its docstring.

Dependency declarations used (their full recorded signatures and docstrings read):

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` / `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
- `sk-def-sfb-qlbar-condensed`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` / `Profinite.padicAlgClCondensedRing`.
- `def-sfb-continuous-map-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing` / `Profinite.continuousMapRingSheafOfUniverse`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` / `AlgebraicGeometry.ProEtale.coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod` / `CategoryTheory.Mod`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` / `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `sk-def-sfb-derived-extension-of-scalars`: `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` / `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction`.
- `def-constructible-stratification`: `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` / `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion` / `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` / `AlgebraicGeometry.IsClosedImmersion`.
- `lem-weil-pbc-condensed-open-closed-recollement`: `Sheaf.Paper.CondensedOpenClosedRecollement` / `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement`.
- `def-sfb-lisse-coefficient-module`: `Sheaf.Paper.CoefficientHeartStratificationDefs` / `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `def-weil-triangulated-category`: `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean` / `CategoryTheory.Pretriangulated`.

Additional reused declarations: `coefficientMap` in upstream
`ModuleObject.ChangeOfCoefficients`; `Profinite.padicSubfieldRingObjToPadicAlgCl`
in upstream `RingObjects.Condensed.FiniteSubextension`; topology inclusion and
J_X in `Sheaf.Paper.ConstructibleAlgClTopologyComparison`; support extension in
`Sheaf.Paper.CoefficientHeartFiltration`. The parent independent review explicitly
requests reuse of its inclusion in this future item. Only its helper definitions
are used, never its comparison theorem. Do not add a backwards DAG edge to that
parent, which already uses this item. Its future proof import of this module must
be omitted to avoid an import cycle (stages/2-statements.md rule 7). No coefficient,
module category, scalar functor or support functor is copied. The new helper merely
names the composite G/H explicitly introduced by this item's statement.

All available recorded proof modules are imported privately. The proof-only
`Sheaf.Paper.BoundedConstructibleHomFiniteness` is omitted: there is no local
source, `scompile.py --source` reports source unavailable, and the compile server
reports its olean missing. This does not affect the statement. The three unpublished
comparison inputs (qlbar internal Hom, norm internal Hom, norm cohomology) likewise
have no module to import. They remain explicit in the preserved proof docstring.

Edge cases checked: empty X, S or T, zero L or M, rank zero on a cover, distinct
and disjoint supports, unrelated E and F (including the base field), zero/positive/
negative shifts, and every cone. There is no nonemptiness, connectedness, common
support, common coefficient field, bounded scalar-extension, flatness or completeness
assumption. No counterexample or node typing defect was found. The exact-literature-
proof-WANTED notice is preserved; this stage does not assert that proof was found.

Searches:

- msearch leanfinder, "Supported finite stage lisse modules have zero morphisms to
  the cone of the derived extension restriction scalar adjunction unit from finite
  subextension valued condensed coefficients to norm continuous algebraic closure
  coefficients": eight results on solid condensed modules and their free functors,
  no matching theorem.
- msearch loogle, `"distTriang", "Subsingleton"`: zero hits.
- msearch grep, `(Condensed|PadicAlgCl).*(orthogonal|[Cc]one)|([Cc]one|orthogonal).*(Condensed|PadicAlgCl)`:
  two irrelevant hits (discrete characterization and free condensed module sequence).
- msearch leansearch, "Morphisms from finite coefficient locally constant sheaves
  to the cone of change of algebraic closure topology scalar adjunction unit vanish":
  eight results on sheafification, constant sheaves and global sections; no match.
- rg on both project Lean roots for supported finite-stage, topology defect, and
  the exact item id: no matching theorem. The parent references this missing
  obligation and already defines the inclusion reused here.
- rg on DAG for `algClTopologyInclusion` and `algClTopologyScalarExtension` found
  the parent record. `tools/blueprint_refs.py search 'coefficient topology inclusion'`
  found zero blueprint matches; `ancestor` confirms the inherited null ancestor.
- Read the blueprint source paragraph (3), all statement dependencies and their
  declarations and docstrings, support implementation and scalar adjunction source.

Validation: scompile.py clean in sandbox mode (16.0 seconds) and actual library
module mode (20.5 seconds), with no errors or non-sorry warnings. All compiles use
the required wrapper and all changes are confined to this sandbox. No direct git
command, live-source edit or global build was performed. The delivery wrapper runs
its own independent server preflight before delivery.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
