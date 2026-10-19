## Worker report

The module `Sheaf.Algebra.Homology.TorAmplitudePrincipalCover` states
`DerivedCategory.torAmplitudeIn_of_principal_cover`, with its whole proof postponed.
It states exactly the finite principal-cover descent assertion of Stacks Tag 066N
(`more-algebra.tex`, `lemma-glue-tor-amplitude`). No statement correction, new node,
or dependency repair is needed.

Hypotheses and clauses:

- A commutative ring is `{R : Type u} [CommRing R]`.
- The arbitrary unbounded cochain complex is
  `K : CochainComplex (ModuleCat.{u} R) ℤ`; this includes the square-zero differential data.
- The integers and their ordering are `(a b : ℤ) (_hab : a ≤ b)`.
- The finite family, including length zero, is `(r : ℕ) (f : Fin r → R)`.
- Generation of the unit ideal is `_hf : Ideal.span (Set.range f) = ⊤`.
- The localization ring is `Localization.Away (f i)`, with its canonical `algebraMap`.
- The chosen derived categories are the explicit `HasDerivedCategory` instances on
  `ModuleCat R` and on each localized module category, with independent morphism universes
  `w₁` and `w₂`. These are choices of localization, not mathematical restrictions on R or K.
- The localized complex is the object obtained by applying
  `Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap R
  (Localization.Away (f i)))) (ComplexShape.up ℤ)` to K. Extension of scalars uses
  `R_f ⊗_R K`, canonically the specified `K ⊗_R R_f` over a commutative ring.
- The hypothesis `_hlocal` quantifies over every i and asserts
  `torAmplitudeIn (ModuleCat (Localization.Away (f i))) a b` of that complex's image under Q.
- The conclusion is `torAmplitudeIn (ModuleCat R) a b (Q.obj K)`.
  The source definition `DerivedCategory.torAmplitudeIn` quantifies over EVERY module F
  in degree zero (`singleFunctor ... 0`), with the canonical derived tensor, and requires
  homology concentrated in [a,b]. Thus it renders exactly the displayed vanishing for
  every n outside the interval, with no flatness or boundedness hypothesis on F or K.

Dependency interfaces read and used:

- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away` (through the
  ring localization import), the quotient by powers of the chosen element.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`:
  `SheafOfModules.derivedChangeOfRings`. Its site-level existential functor does not
  need a duplicate specialization: the existing `ModuleCat.extendScalars` is ordinary
  change of rings under the singleton-site identification explicitly required by the node.
  Localization in this statement is termwise ordinary scalar extension; derived tensor
  is the separately supplied canonical monoidal derived tensor, not an arbitrary functor.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`:
  `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`, computing the canonical derived tensor
  on K-flat representatives, without hypotheses on the other complex.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn` (re-exported by FlatModel), whose full definition was read.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`:
  the module-category flat-resolution instance supplies the canonical monoidal API.

All recorded, stated proof dependencies are imported: KFlatResolution,
KFlatModuleBaseChange, HomologyVanishingLocalizationSpan, FlatModel,
Mathlib.RingTheory.Flat.Localization and Mathlib.RingTheory.Flat.Basic.
The declaration docstring carries all four natural-language proof steps and their node ids.

Edge cases: Fin 0 is permitted; its unit-ideal hypothesis forces the zero ring and all
module cohomology vanishes. Zero complexes and zero modules are allowed. The interval may
be a singleton a=b, and a,b may be negative. There is no boundedness condition on K, and
all modules in the coefficient universe are tested, including nonflat ones. No nonzero-ring,
nonempty-family, or finite-generation hypothesis has been introduced.

Searches performed for reuse:

- `msearch.py ... leanfinder "Tor amplitude descends from a finite principal localization
  cover"`: eight cohomological t-structure hits; none states this descent assertion.
- `msearch.py ... loogle "DerivedCategory.torAmplitudeIn"`: zero hits, unknown identifier
  in the Mathlib search service; the upstream source does contain the definition and it is used.
- `msearch.py ... grep "torAmplitude.*local|local.*torAmplitude"`: zero hits.
- `rg` for `TorAmplitude|torAmplitude|tor_amplitude` in the project modules found
  TorAmplitudeFlatModel and related bounds, but no principal-cover descent theorem.
- `rg` for `torAmplitude.*local|local.*torAmplitude` in upstream and `lean/Sheaf`
  found no matching theorem. Searching upstream for this item's exact id gave no hit.
- Read the full upstream TorAmplitude definition and K-flat tensor comparison, and the
  Mathlib extendScalars, DerivedCategory and Away declarations. Existing definitions are
  reused; no private notion or helper is introduced.

Validation: server-only `scompile.py`, nice 19, two threads, 60 seconds per file.
The initial compile caught line-broken dot notation; this was replaced by the explicit
`Functor.mapHomologicalComplex` API. The final compile and delivery dry run are recorded
by their tool output. No local compilation or library build was run.


## Second reading by NW

I independently read the sandbox node and module, Stacks `more-algebra.tex`
lines 17209–17237 (Tag 066N, including its proof), the chapter introduction,
and the recorded dependency declarations. The source uses commutative rings
and the unbounded derived category; it assumes neither Noetherianity nor
nonzero rings. The node additionally fixes the ordered interval a ≤ b, which
is rendered faithfully. There is no statement_change, new definition node,
or dependency module in this delivery.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. Commutative ring R: `{R : Type u} [CommRing R]`. There is no field,
   domain, characteristic or finiteness assumption.
2. Arbitrary cochain complex with square-zero differentials:
   `K : CochainComplex (ModuleCat.{u} R) ℤ`. The bundled complex includes
   precisely the differential data in the node; no boundedness is required.
3. Integers a ≤ b: `(a b : ℤ) (_hab : a ≤ b)`.
4. Finite list of length r ≥ 0: `(r : ℕ) (f : Fin r → R)`.
5. Unit ideal generation: `_hf : Ideal.span (Set.range f) = ⊤`.
6. Canonical rings R[1/f_i]: `Localization.Away (f i)` with their
   `algebraMap R ...`. I opened the recorded Mathlib Away abbreviation and
   the ring localization interface: these invert the powers of f_i.
7. Derived categories: `HasDerivedCategory.{w₁} (ModuleCat.{u} R)` and
   `∀ i, HasDerivedCategory.{w₂} (ModuleCat.{u} (Localization.Away (f i)))`,
   together with `Q`. I read Mathlib DerivedCategory.Basic: these are choices
   of localization at quasi-isomorphisms in the node's chosen morphism
   universes, available via HasDerivedCategory.standard; they impose no
   algebraic restriction. The two morphism universes are independent.
8. Localized complex: `Functor.mapHomologicalComplex
   (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))))
   (ComplexShape.up ℤ)` applied to K. I read extendScalars and its action on
   maps: this is B ⊗_R K termwise, including differentials, canonically the
   node's K ⊗_R B by the tensor symmetry. The local input is ordinary
   localization, exactly as Tag 066N states. The imported sheaf-level
   derivedChangeOfRings was also read: its singleton-site specialization
   supplies the derived interpretation, but no arbitrary functor or extra
   existence hypothesis replaces the actual localization in this signature.
9. Each localized amplitude bound: `_hlocal : ∀ i : Fin r,
   torAmplitudeIn (ModuleCat ... ) a b (Q.obj (... K))`. I opened upstream
   TorAmplitude: its definition quantifies over every module F in degree
   zero, using the canonical derived monoidal tensor. FlatResolution supplies
   its ModuleCat instance without extra hypotheses. Its
   homologyConcentratedIn is IsGE a and IsLE b for the canonical t-structure,
   equivalent to vanishing below a and above b. Thus the quantifier over all
   local modules N, including nonflat N, and every degree outside [a,b] is
   retained.
10. Global conclusion: `torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K)`.
    The same definition gives exactly all R-modules M and all degrees outside
    [a,b], with the quantifiers in the node's order. I read the recorded
    QObjTensorQObjIsoOfKFlatLeft: one K-flat representative suffices, without
    imposing flatness or boundedness on the other factor.

Edge cases: Fin 0 is allowed. Its span condition forces 1=0, hence all
R-modules are zero; no Nonempty or Nontrivial instance excludes this case.
Zero complexes, zero modules, f_i=0, arbitrary characteristics, negative
endpoints and a=b (including [0,0]) are all allowed. Empty schemes are not
objects of this ring statement; the corresponding empty affine spectrum is
covered by the zero ring. All universes are explicitly bound. ModuleCat uses
the same coefficient universe as the existing canonical flat-resolution API;
u is arbitrary, so a ring may be viewed in any larger common universe with
its tested modules. No equality between site object and morphism universes
has been imposed: this statement is directly in ordinary modules.

I also opened the actual signatures in KFlatResolution,
KFlatModuleBaseChange and HomologyVanishingLocalizationSpan. The last two
use this same termwise extendScalars and allow the zero ring/empty family.
The flat-localization and flat-exactness Mathlib imports and the FlatModel
comparison are the recorded proof dependencies. The theorem docstring gives
all four node proof steps: resolve K, use exact localization, compare tensor
models after scalar extension, and detect cohomology vanishing by the
unit-ideal cover. Every stated proof dependency is imported. The file adds
only one theorem with whole proof `sorry`, and no definition or private
notion. Source and blueprint docstrings and the 100-character convention
are satisfied.

Independent reuse searches:

- LeanFinder through msearch: “Tor dimension bounds descend along a finite
  standard open covering of Spec R”: eight hits on standard-open covers,
  local morphism properties and Krull dimension, no matching theorem.
- Loogle through msearch: `"torAmplitudeIn"`: zero hits.
- Grep through msearch: `torAmplitudeIn.*(local|cover)|amplitude.*principal`:
  zero hits.
- LeanSearch through msearch: “Tor amplitude descent for complexes on a
  finite principal localization cover”: service unavailable (Internal Server
  Error); no mathematical verdict inferred from the failed service.
- Direct rg in Mathlib, upstream WeilConjectures and project lean/Sheaf:
  amplitude with cover/localization and the proposed declaration name.
  This found the upstream Etale.torAmplitudeIn_of_openCover. I opened its
  signature: it concerns sheaves on smallEtaleTopology and UpperStar,
  not ring modules and extension along R → R[1/f_i], so it is not this
  statement. Other hits concern Tor stalks and localized algebra modules;
  none duplicates this theorem.

No mismatch found; no Lean or node changes made. The only change is this
independent reading record. I checked by exact string comparison that
lean.statement equals the complete file signature, and checked every line
length. Server scompile.py compiled the sole delivered file cleanly in
1.5 seconds, nice 19, two threads, 60-second per-file limit. No local
compiler or global build was invoked.
