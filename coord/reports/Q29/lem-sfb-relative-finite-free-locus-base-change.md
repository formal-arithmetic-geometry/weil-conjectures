## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFiniteFreeLocusBaseChange` states
`AlgebraicGeometry.Scheme.Modules.relative_finiteFreeLocus_baseChange` and defines its
`AlgebraicGeometry.Scheme.Modules.finiteFreeLocus` by actual finite free trivializations.
This locus is a helper belonging to this theorem's own notion, recorded in
`lean.declarations`, rather than an independent replacement for finite local freeness.
The only postponed proof is the named theorem; the locus has real set-builder data.

Read the full node and every statement dependency's statement, Lean record, source signature
and docstring. Read Stacks `more-morphisms.tex`, label `lemma-finite-free-open`, Tag 0CZR,
lines 4823–4853: its hypotheses and arbitrary-base-change conclusion agree with the item.
No statement correction or dependency repair is needed. The example Sheaf CompactObject
module is withdrawn; its recorded upstream replacement was read for the module conventions.

The hypothesis and clause correspondence is:

- Schemes Y and T are `{Y T : Scheme.{u}}`; the given morphism is `(p : Y ⟶ T)`.
- Local finite presentation is `[LocallyOfFinitePresentation p]`.
- The O_Y-module is `(F : Y.Modules)`.
- Finite presentation is `[SheafOfModules.IsFinitePresentation.{u} F]`. This is exactly
  local cokernels of maps between finite free sheaves, by the Mathlib class docstring.
  Its existing instance supplies `SheafOfModules.IsQuasicoherent F`; the node's
  quasi-coherence hypothesis is therefore included without an additional independent binder.
- Flatness over T is `(hflat : F.IsFlatOver p)`, the recorded affine-local predicate.
- W(F) is `finiteFreeLocus F`: a point y belongs when there are an open `U : Y.Opens`
  containing y, `r : ℕ`, and an isomorphism `F.over U ≅ SheafOfModules.free ...` on
  `ULift.{u} (Fin r)`. The ring is `Y.ringCatSheaf.over U`. The over-site is the category
  of opens contained in U, so this is precisely restriction to the open neighbourhood.
  `SheafOfModules.free` is the coproduct of copies of the unit sheaf, giving O_U^r.
- Openness is the first conjunct `IsOpen (finiteFreeLocus F)`.
- Every new base and base morphism are quantified by `∀ (T₁ : Scheme.{u}) (v : T₁ ⟶ T)`.
- Y_1 and q are the canonical `pullback p v` and `pullback.fst p v`.
- Tensor pullback is `(tensorPullback (pullback.fst p v)).obj F`, using the recorded
  dependency's public upstream functor with its actual tensor construction.
- The second conjunct is the exact equality of sets
  `finiteFreeLocus ((tensorPullback (pullback.fst p v)).obj F) =
  (pullback.fst p v) ⁻¹' finiteFreeLocus F`.
- There are no assumptions on v, no flatness assumption on p, and no Noetherian assumptions.
  Every universe and every variable is explicit, and `autoImplicit` is disabled.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public Mathlib
  `SheafOfModules.IsQuasicoherent`, alongside the recorded
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` (the conjunction is not
  assumed here because finite presentation already includes both of its conditions).
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` is the variable-rank local-trivialization notion.
  The locus uses the underlying actual finite free isomorphisms, on the open over-site,
  rather than incorrectly assuming this global property of all of F.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the theorem uses the first projection.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, defined in the imported
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; the recorded
  `tensorPullbackSectionAdjunction` and comparisons remain available.

Proof-plan imports are the recorded existing modules for
`lem-a1-map-over-base-finite-presentation`,
`lem-weil-pbc-finite-presentation-source-stalk`,
`lem-sc-affine-standard-cover-finite-free-local-fp-flat`, and
`lem-weil-pbc-finite-flat-local-free`. Their full signatures were read.
The proof-only nodes `lem-sfb-relative-module-flat-locus-base-change` and
`lem-trf-finite-presentation-stalk-basis-spread` currently have neither a Lean record nor
Mathlib match and hence have no module to import. They are not needed to type this
statement, and remain named explicitly in its step-by-step proof docstring.

Edge cases checked before writing:

- Rank zero is allowed by `r : ℕ`; the empty coproduct gives the zero sheaf.
- The zero sheaf therefore has the whole scheme as its locus, and the theorem's equality
  gives the whole base-changed scheme. Empty schemes and empty base changes are covered.
- Rank can vary between disjoint open neighbourhoods; no global rank is imposed.
- For v the identity, the assertion uses the actual tensor pullback and canonical pullback
  projection. For nonflat v it retains exactly the same conclusion and hypotheses.
- A nonflat p is permitted: over a field an arbitrary finitely presented scheme can
  carry a base-flat sheaf, and the binder introduces no `Flat p` instance.
- All schemes use the same arbitrary universe u, as in Mathlib's category of schemes;
  the finite free basis uses ULift to place its index in the module universe. In particular
  `IsFinitePresentation.{u}` is essential: the initial omitted universe argument elaborated
  the module universe as zero, and the compiler diagnostic was repaired by this annotation.

Searches actually run with `msearch.py Q29 lem-sfb-relative-finite-free-locus-base-change`:

- leanfinder, query “The finite locally free locus of a finitely presented quasi-coherent
  sheaf flat over a scheme base is open and commutes with arbitrary base change”: 8 hits,
  including `Module.isOpen_freeLocus`, `LocallyOfFinitePresentation`, and
  `SheafOfModules.isFinitePresentation`; none is this relative sheaf theorem.
- loogle, query `Module.freeLocus, Module.Flat`: `Module.freeLocus_eq_univ` only.
- grep, query `finiteFreeLocus|finiteLocallyFreeLocus|locallyFreeLocus|freeLocus`: 16 hits
  in the ring-module free-locus files and their consumers. Read `FreeLocus.lean`:
  `comap_freeLocus_le` gives only one inclusion for arbitrary scalar extension, and
  `freeLocus_eq_univ` assumes flatness over the total ring, not a separate base.
- leansearch, query “The finite locally free locus of a finitely presented quasi-coherent
  module flat over the base commutes with arbitrary scheme base change”: 8 hits, including
  flat scalar extension and module finite-presentation preservation; no exact theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the locus names found no scheme
  sheaf locus or theorem. There is an algebraic-space sibling
  `AlgebraicGeometry.AlgebraicSpace.finiteFreeLocus` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeFiniteFreeLocusBaseChange`; read it fully.
  It uses the small étale site and algebraic-space points, so it is not a declaration
  on the scheme Zariski module category used by this node.
- Node-id search in `lean/WeilConjectures` found no existing declaration.
  DAG keyword searches found the item and its algebraic-space sibling, not an independent
  scheme-locus definition. No new independent notion or new DAG node was introduced.

Validation: all compiles used `scompile.py`. The final server compile passed cleanly
(3.4 seconds sandbox, 3.2 seconds library). The delivery wrapper printed OK for the
dry run: server preflight and per-file compilation both passed, with no unexpected warnings.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
