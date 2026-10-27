## Worker report

The module `Sheaf.CategoryTheory.RingedToposRelativeLeray` states
`CategoryTheory.exists_ringedTopos_relative_leray_spectralSequence`, with its whole
proof `sorry`. There are no new definitions, dependency repairs, statement corrections,
or other postponed theorems. The original node is changed only in `lean`.

Source read: Stacks `sites-cohomology.tex`, lemma-relative-Leray (0734), lines
2366–2391, and the proofs of lemma-direct-image-injective-sheaf (072Z) and
lemma-limp-acyclic (0731), lines 2211–2309. The node selects the module assertion
of 0734, not its additional bounded-below-complex assertion. The source assumes
no flatness. The docstring carries the four DAG proof steps, including the
all-sheaves total-acyclicity argument, rather than a claim that a_* preserves
injectives.

Hypotheses and clauses, individually:

- The three sites small in a common universe are `{C D T : Type u}` with three
  `SmallCategory` instances and topologies `J`, `K`, `L`. `T` is the node's third
  site E. This realizes def-weil-size-convention as universe polymorphism; that
  dependency is explicitly recorded as a metatheoretic convention. The sites
  are represented by their Grothendieck topologies, the sheaf-category component
  of def-weil-pbc-sites-and-cohomology. No restriction to subcanonical sites or
  to geometric morphisms presented by site functors is imposed.
- The three commutative ring sheaves are `A : Sheaf J CommRingCat.{u}`,
  `B : Sheaf K CommRingCat.{u}`, and `R : Sheaf L CommRingCat.{u}`. The canonical
  `sheafCompose ... (forget₂ CommRingCat RingCat)` retains these very ring sheaves
  in the general ringed-topos interface; it does not introduce different rings.
- `a` and `b` are the recorded `RingedToposMorphism` for these consecutive rings.
  Its inverse/direct sheaf adjunction and left-exact inverse image encode an
  arbitrary geometric morphism, while `modules`, `underlying`, `module_linear`
  encode its induced additive module direct image.
- Work in module sheaves uses the recorded `ringedSiteModules.{u}`, transparently
  Mathlib's `SheafOfModules.{u}`. The spectral sequence takes values in
  `ringedSiteModules A ⥤ ringedSiteModules R`, with the above explicit ring forgets.
  Evaluation at every source module M gives precisely a spectral sequence of
  O_E-modules. No module or map is assumed injective or acyclic in the binders.
- Higher direct images are Mathlib's `Functor.rightDerived`, defined using
  `injectiveResolutions`; `InjectiveResolution.isoRightDerivedObj` identifies
  them canonically with any injective-resolution computation. The existing
  `SheafOfModules.isGrothendieckAbelian`, marked as an instance, together with
  `IsGrothendieckAbelian.enoughInjectives`, supplies resolutions intrinsically.
  These are derived infrastructure, not extra mathematical hypotheses.
- First quadrant and cohomological differentials are exactly
  `E₂CohomologicalSpectralSequenceNat`: page indices are natural-number pairs
  and d_r has bidegree (r, 1-r). The starting page is 2.
- `e₂ p q` identifies `(E.page 2).X (p,q)` with
  `a.modules.rightDerived q ⋙ b.modules.rightDerived p`. It is an isomorphism of
  functors, so its component at M is R^p b_*(R^q a_* M), naturally in M. The
  spectral-sequence page morphisms already commute with all differentials and
  page-transition homology isomorphisms.
- The abutment is `(a.modules ⋙ b.modules).rightDerived m`. This writes the
  composite direct image itself, not a successive application of higher
  derived functors: its underlying set direct image is b_* a_*, and its scalar
  action is O_E -> b_* O_D -> b_* a_* O_C. Thus it is exactly (b composed with a)_*
  on modules, as in step 2 of the DAG proof. No extra chosen composite morphism
  or arbitrary comparison is quantified over.
- `F m : DecreasingFiltration ...` is the recorded decreasing filtration of the
  abutment functor, hence is natural in M; its steps are genuine subfunctors.
  `(F m).step 0 = ⊤` states exhaustivity. The final step is
  `IsZero (Subobject.underlying.obj ((F m).step (m+1)))`, equivalently its
  subobject equals bottom. It states the zero step without triggering the
  costly alternative instance searches for `Bot (Subobject ...)`.
- Stabilization is explicit: for `r > max(p,q+1)`, the page is isomorphic to
  `E.pageInfinity (p,q)`. This existing definition reads the stable term on page
  p+q+2. In the first quadrant the differentials entering and leaving (p,q)
  vanish at that bound.
- For every m,p,q with p+q=m, the final clause identifies
  `(F m).gradedPiece p` with `E.pageInfinity (p,q)`. The recorded graded-piece
  definition is the cokernel of the inclusion of step p+1 in step p. This is
  exactly gr^p R^m(b composed with a)_* M = E_infinity^(p,m-p), including p=0
  and p=m. The isomorphisms are in the functor category, so the graded
  identifications are natural too. `Nonempty` asserts existence of these
  isomorphisms; it is not used to define any object or choose an arbitrary map.
- No flatness, exact tensor pullback, preservation of injectives, chosen
  injective resolution, acyclicity, or additional derived-category existence
  hypothesis is imposed on a or b.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including its full structural-map and
  induced-module-action fields and its additive instance.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, exactly `SheafOfModules`; category and
  abelian structures are inherited, not copied or chosen.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the sheaf component uses the
  associated Mathlib `GrothendieckTopology` and `Sheaf` as the record specifies.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective`, `CategoryTheory.InjectiveResolution`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `CategoryTheory.Functor.rightDerived` and
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
  `Functor.Additive` and `PreservesFiniteLimits` retain the recorded
  def-sp-left-exact-additive meanings.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic` (exposed through the
  upstream extension): `SpectralSequence`, its `Hom`,
  `E₂CohomologicalSpectralSequenceNat`. Upstream
  `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` supplies
  the existing `SpectralSequence.pageInfinity`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration` and
  `WeilConjectures.CategoryTheory.CanonicalFiltration`:
  `DecreasingFiltration`, `step`, `gradedPiece` (alias of `gr`).
- The public Mathlib `Abelian.FunctorCategory` import supplies the standard
  abelian structure on the functor category used in the statement.

Proof-only imports include the recorded
`SheafOfModules.isGrothendieckAbelianOfUniverses` in
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`,
`GrothendieckComposablePair.SendsInjectivesToAcyclics` in
`WeilConjectures.CategoryTheory.GrothendieckComposablePair`, and
`exists_grothendieck_spectralSequence_cartanEilenberg` in
`Sheaf.CategoryTheory.GrothendieckSpectralSequence`.
The double-complex dependency's old `lean.module` no longer declares its recorded
name. Its closed upstream audit gives
`WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex`, which is imported
for `HomologicalComplex₂.exists_spectralSequence` and its flipped version;
these are the actual current full signatures read. No node repair is needed
for a proof-only source relocation.
The two new total-acyclicity proof prerequisites have no Lean records in the
read repository; they are not notions needed to type this statement, and no
private copies or additional assumptions have been supplied for them.

Edge cases checked before writing: m=0 gives F^0=H^0 and F^1=0, with the only
graded term E_infinity^(0,0); p=0 or q=0 is included; r=2 is allowed whenever
the stabilization inequality holds. Empty sites and the zero ring sheaf or
zero module are allowed. Identity geometric morphisms reduce to the ordinary
right-derived identity case. For point topoi with nonflat ring maps such as
Z -> Z/2, the binders remain valid; the result concerns composition of module
restriction functors and does not falsely demand that restriction preserve
injectives. A module universe can be enlarged uniformly; no independent
smaller test-object universe or equality between unrelated size levels occurs.

Searches made on 2026-10-24:

1. `msearch.py ... leanfinder` with query "Relative Leray spectral sequence for
   composition of module direct images of arbitrary ringed topoi without
   flatness": eight hits, chiefly `SheafOfModules.pushforwardComp`,
   `PresheafOfModules.pushforwardComp`, `SheafOfModules.pullbackComp`, and
   `Scheme.Modules.pushforwardComp`. They identify underived functors, not
   the spectral sequence.
2. `msearch.py ... loogle` with query `"SpectralSequence"`: twelve hits,
   including complex shapes and `Abelian.SpectralObject` spectral-sequence
   data; no relative module Leray theorem.
3. `msearch.py ... grep` with query
   `Leray|leray|GrothendieckSpectralSequence`: zero Mathlib hits.
4. `rg -n 'Leray|leray|relative.Leray' lean/Sheaf lean/WeilConjectures`:
   existing global-sections Leray, etale specializations and unbounded
   composition isomorphisms. Read `RingedSiteLeraySpectralSequence.lean` in
   full: its target is abelian groups via global sections, not the module
   category of an arbitrary third ringed topos. It does not state this node.
5. Search for the exact node id in `lean/WeilConjectures` found no match.
   Search for the proposed full declaration name in both project roots,
   Mathlib and `dag/lean_names_upstream.json` found no prior declaration.

Validation: the prescribed `scompile.py NF lem-sfb-ringed-topos-relative-leray`
compiled both the sandbox probe (7.9 s) and the actual library module (9.2 s)
cleanly, under the unchanged 60-second per-file limit. All variables and the
common universe are explicitly bound (`autoImplicit false`). Removed the
unsuccessful temporary synthesis-budget adjustment; the final file uses the
default settings and has no diagnostic commands. No STATEMENT-DISPUTED issue
or node statement fault was found.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
