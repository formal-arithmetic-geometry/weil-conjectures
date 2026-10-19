## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleFiniteFreeCoefficients` states
`AlgebraicGeometry.ProEtale.exists_finiteFree_proEtale_coefficients`, with one
postponed proof, `sorry`, and no new definitions. The node statement is unchanged.
The resolved stage-1 repair note was read: this delivery retains its arithmetic,
topological, condensed, localization, naturality, and flatness proof route.

Hypothesis and clause correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The two finite extensions inside the fixed algebraic closure are
  `(E F : PadicAlgCl.FiniteIntermediateField ℓ)`. Their inherited fields, norms,
  embeddings, and finite-dimensional instances are the published constructions.
  Inclusion is `(h : E ≤ F)`, including equality. The integer `d` and equality
  `hd : d = Module.finrank ℚ_[ℓ] F / Module.finrank ℚ_[ℓ] E` name the relative
  degree using the finite-dimensional tower formula. This is a specification of
  the degree, not a restriction on the extensions or on their embeddings.
- An integral basis is a tuple `b : Fin d → PadicAlgCl.integers ℓ F` such that
  every `x : PadicAlgCl.integers ℓ F` has exactly one tuple
  `a : Fin d → PadicAlgCl.integers ℓ E` with
  `∑ i, IntermediateField.inclusion h (a i : E) * (b i : F) = (x : F)`.
  Unique expansion is exactly the basis property. Its codomain is the integer
  ring, not all of F. This avoids imposing any auxiliary algebra structure on F.
  The first conjunct supplies existence of such a basis; the second quantifies
  over every basis satisfying this property, so no particular basis is privileged.
- `r` is a bundled morphism of the existing integral condensed ring objects.
  Its displayed evaluation on every profinite S, every continuous section a,
  and every s in S forces it to be the actual inclusion of integer rings.
  It is neither an arbitrary map nor an extra hypothesis: the conclusion supplies
  it with its complete defining formula, which uniquely determines the map.
- `m₀ i` and `m₁ i` are morphisms of the existing condensed abelian sheaves.
  Their formulas on every continuous function specify multiplication by b_i after
  inclusion. Again these maps are supplied by the conclusion and uniquely
  determined by their formulas. They provide the complete point-level formula
  needed to state the specified map after the non-sectionwise point pullback.
- `e₀ X` is an isomorphism in integral coefficient module objects from
  `Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) d`
  to the regular upper integral coefficient module restricted along p_X^*(r).
  `e₁ X` is the corresponding isomorphism in E_X-module objects, restricted
  along exactly `padicSubfieldRingObjMap X ℓ h`. Thus both asserted isomorphisms
  are linear for the precise scalar inclusions of the node.
- For every i, `(biproduct.ι ... i).hom ≫ (e₀ X).hom.hom` equals
  `(upperStarFromPoint X).map (m₀ i)`, and likewise for e₁ and m₁. A map out of
  this finite direct sum is uniquely specified by these restrictions; additivity
  gives the formula sum_i a_i b_i. No claim that the point pullback is computed
  sectionwise is used.
- The next conjunct is exactly the integral-to-rational square, precomposed
  with each integral summand injection. Its vertical maps are the recorded
  `padicIntegersToPadicSubfield X ℓ E` and its F version.
- The following two conjuncts state the inverse-image squares for every
  `(X Y : Scheme.{u}) (f : X ⟶ Y)`, precomposed with each pulled-back summand
  injection. The right and left vertical maps are the recorded
  `condensedPullbackHom` for the upper and lower integral or rational
  coefficients. Inverse image preserves finite coproducts, so equality on these
  summands is equivalent to the full square, not a weakened naturality assertion.
- The last conjunct gives `PreservesFiniteLimits (Mod.extendScalars ...)` for
  both scalar inclusions, at every X. Extension of scalars is already right exact;
  this is exactly flatness in these abelian module-object categories.
- Scheme objects have unrestricted universe `u`; coefficient sheaves are in
  `Ab.{u+1}` on the published small pro-etale site. No site/coefficient universe
  equality, nonemptiness, nonzero rank, noetherian hypothesis, or restriction on f
  is introduced.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the complete
  coefficient-extension construction and states `Padic.finite_coefficientExtensionRing`.
  Integer coefficient objects here are the published `PadicAlgCl.integers` model,
  namely the unit ball for the fixed embedding in the algebraic closure.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse` is the recorded general universe
  interface. In this node the fields and integer rings lie in Type 0; the
  existing upstream `Profinite.continuousMapRingObj` and
  `Profinite.padicIntegersRingObj` give these same continuous-function objects.
  The latter are used directly to match the recorded coefficient maps exactly.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`,
  `upperStarFromPointComp`, `condensedPullbackHom`, `coefficientPullbackIso`.
  These give the actual pulled-back rings and canonical inverse-image comparisons.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`, `Mod`, `Mod.regular`,
  `Mod.forget`, `Mod.comap`; the isomorphisms are in these module categories.
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`:
  `padicIntegersToPadicSubfield`, read via `scompile.py --source`; it is precisely
  point pullback of `padicIntegersRingObjToContinuousMapRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicSubfieldRingObj`, `padicSubfieldRingObjMap`, the latter the recorded
  coefficient change of the condensed field inclusion.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, defined by `(upperStarFromPoint X).map`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `Mod.extendRestrictAdjunction`, `Mod.coextendScalars`,
  `Mod.restrictCoextendAdjunction`; and its `MapMod` and `ChangeOfScalarsSquare`
  interfaces. `Mod.finiteFree` comes from the existing upstream `ModuleObjects.Free`
  module and is the finite biproduct of the regular module, not a new definition.
- The stated proof dependencies are imported privately: ExtensionIntegersDvr,
  PadicIntegersIntegralClosure, ProEtalePointPullback, ProjectionFormula,
  ChangeOfScalarsSquare, Mathlib integral-closure finiteness and free modules over
  PIDs. Other proof ingredients are available transitively. The localization
  detail `det-prop-sfb-qlbar-colimit-x-invert-ell` has no recorded declaration on
  the read base; it is a proof dependency only, and no substitute is introduced.
  All nine proof steps of the node are included in the theorem docstring.

Edge cases checked before writing: E=F gives degree one and permits any integral
unit basis; the inclusion relation is non-strict. Empty X is permitted and both
module categories and squares specialize to zero objects. All scheme morphisms,
including identities, arbitrary lifts, and maps involving empty schemes, are
quantified. Empty profinite sets have the unique continuous section and satisfy
all evaluation formulas vacuously; nonempty profinite sets determine the maps.
A relative degree zero cannot satisfy hd for finite extensions of fields; no
extra positive-degree premise excludes a legitimate case. All bases, ramified
and unramified extensions, and every prime including 2 are permitted. The basis
criterion tests expansion only for integral x; it does not mistakenly require
integral coordinates for nonintegral field elements.

Searches (all on 2026-10-18):

- `msearch.py leanfinder`, query: "A finite extension of p-adic fields induces
  finite free pro-etale coefficient module sheaves compatible with inverse image".
  Eight hits: BDeRham, BDeRhamPlus, StandardEtalePair.instFormallyEtaleRing,
  Algebra.IsEtaleAt.comp, two formally-etale restriction results, an etale
  idempotent lifting result, and finite-product formal etaleness. None states this
  coefficient-sheaf theorem.
- `msearch.py loogle`, query `Condensed, Module.Free`: zero hits.
- `msearch.py grep`, query `padic.*[Ff]ree|[Ff]ree.*padic|continuousMap.*[Bb]asis`:
  zero hits in Mathlib.
- `msearch.py leansearch`, query: "An integral basis of a finite p-adic field
  extension gives finite free pro-etale coefficient sheaves compatible with
  pullback". Eight hits: NumberField integral bases and their formulas,
  FiniteDimensional.exists_is_basis_integral, and SheafOfModules pullback of free
  modules. These are arithmetic or general module-sheaf tools, not this theorem.
- `rg` in upstream WeilConjectures and `lean/Sheaf` for the node id, finiteFree,
  finite_free, padic/free and basis/condensed patterns: no exact theorem.
  The upstream Compatibility module discusses finite freeness in its docstring
  but states only rational flatness, so it omits both isomorphisms and both
  compatibility clauses. `Padic.exists_integral_basis` is arithmetic only.
  The existing upstream `Mod.finiteFree` was found and reused.

No statement correction, disputed statement, new node, or dependency module is
needed. Definitions and maps are the recorded ones; every additional existential
arrow is characterized by its pointwise formula within the theorem.

Validation: the prescribed `scompile.py Q80
det-prop-sfb-cartesian-coefficients-finite-free` compile passed with exit code 0
and no warnings, including the compile under the actual library module path
(11.5 seconds). The preliminary compile exposed two interface issues, both
repaired: parenthesize the morphism type indexed by `Fin d`, and open the
published `CategoryTheory.Obj` scope to synthesize transported monoid structures.
The statement uses no new instances or file-local notation. Dry run and delivery
are performed with `deliver2.py` after this compile.

## Second reading by Q80

Independent maintainer second reading, 2026-10-18, of immutable delivery
25834c9dea74038173f9ffc41bebb44cfc6b88de. The heading is retained for the
stage-2 report contract; this reading was performed by the independent reviewer,
not attributed to the original worker.

I read packet.md, check-brief2.md in full, the immutable item JSON, all eight
statement-dependency JSON records, the complete delivered module and worker report,
and the source statement and proof. I then opened the dependency constructions in
the read-only group clone and Mathlib. The conclusion is correct in substance.
The original second-reading section was a placeholder, an H11 report defect. This
complete replacement report repairs that defect. No Lean or node correction is needed.

Hypothesis and conclusion audit:

1. The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The extensions are exactly finite
   intermediate fields of the fixed p-adic algebraic closure, via
   `PadicAlgCl.FiniteIntermediateField`. The inclusion `h : E ≤ F` permits equality.
   The degree binder `hd` uses the quotient of the absolute degrees. The tower
   formula gives the relative degree, because the lower degree is positive and
   divides the upper degree. This adds no restriction. The chosen algebraic closure
   and finite subfields are small types, while the scheme universe `u` is arbitrary.
2. The first conjunct supplies an integral basis. The second conjunct applies to
   EVERY integral basis `b`, not merely the supplied witness. Unique expansion is
   tested for every integral `x`, with integral coefficients and inclusion into F.
   Finite coordinate tuples are equivalent to finite-support coordinates, so this
   is precisely a basis over the lower integer ring.
3. The bundled ring map `r` is existentially supplied and characterized on every
   profinite set, continuous section and point as the integral inclusion. These
   evaluation equations determine the natural transformation uniquely; this is
   not an arbitrary scalar map. Similarly the equations for `m₀ i` and `m₁ i`
   determine multiplication by the fixed basis element after inclusion, on all
   continuous functions. These are conclusions, not extra assumptions.
4. `e₀ X` is an isomorphism in the lower integral module category, with target
   `Mod.comap` of the upper regular module along the pullback of r. `e₁ X` is an
   isomorphism in the E_X-module category, restricted along the exact published
   `padicSubfieldRingObjMap`. `Mod.finiteFree R d` is the published finite biproduct
   of d regular modules. Thus these are precisely the two asserted linear
   isomorphisms, rather than abelian-group isomorphisms alone.
5. The first two equations after e₀ and e₁ identify their underlying maps on each
   biproduct injection with the pullback of the corresponding m-map. A map from
   a finite biproduct is determined by its restrictions to these injections;
   additivity recovers the specified sum of a_i b_i. No incorrect sectionwise
   computation of point inverse image is assumed.
6. The next equation, for every X and i, is the integral-to-rational square
   precomposed with the i-th integral injection. Its arrows are the exact
   `padicIntegersToPadicSubfield` constructions for E and F. These component
   equations imply the full square by the coproduct universal property.
7. The next two equations quantify over every X, Y, scheme morphism f and index i.
   They compare inverse image of each summand map with the corresponding map on X,
   using precisely `condensedPullbackHom` for the two coefficient objects.
   Inverse image preserves finite coproducts; the module forgetful functor creates
   these biproducts. Thus these equations imply both full inverse-image squares.
8. The final conjunct states preservation of finite limits by both actual
   extension-of-scalars functors. Their left adjunction gives right exactness;
   finite-limit preservation is the stated flatness, for integral and rational
   coefficients respectively. There is no missing flatness clause.

Every statement dependency was checked against its actual construction:

- `def-weil-l-adic-coefficient-extension`: CoefficientExtensionFinite imports
  CoefficientExtension. Its degree is finrank, its absolute value is spectral,
  and its integer ring is the specified unit ball. The theorem here uses the
  existing embedded-field `PadicAlgCl.integers`, defined from the restricted
  valuation, whose membership condition is norm at most one. Uniqueness of the
  extended absolute value identifies the two mathematical integer rings; no
  private integer-ring definition is added.
- `sk-def-sfb-condensed-ring`: the recorded universe-general continuous-map
  construction and the specialized existing `continuousMapRingObj` were read.
  Both have lifted C(S,T) sections, precomposition restrictions and the ring
  structure from ring sheaves. The small embedded fields use the existing
  specialized construction, as required by the published coefficient maps.
  `padicIntegersRingObj` is the underlying abelian sheaf of the continuous-map
  integer ring. No alternate notion of condensed coefficients is introduced.
- `sk-def-sfb-pulled-back-coefficients`: Basic defines `upperStarFromPoint` as
  point inverse image followed by scheme inverse image, `coefficientRing` by
  mapMon, and `condensedRingObj` as its underlying object. The ring actions in
  this statement are the transported structures, not unrelated chosen actions.
- `sk-def-sfb-module-objects`: its closed audit, despite no `lean` field, records
  Mathlib ModObj, Mod, forget and regular. Their signatures, action laws and
  linear morphisms were opened and reused. No dependency repair is necessary.
- `def-sfb-integers-to-subfield`: the exact EllAdicRationalization source was
  obtained using scompile.py --source. Its map is the point inverse image of
  the underlying continuous-map inclusion of integer rings into fields.
- `def-sfb-subfield-coefficient-map`: Compatibility defines its map by
  `coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X`; the latter condensed
  map is postcomposition by `IntermediateField.inclusion h`. ChangeOfCoefficients
  defines coefficientMap as `(upperStarFromPoint X).map`.
- `sk-def-sfb-coefficient-morphisms`: Basic's comparison is the canonical
  upperStarFromPointComp component. The bundled coefficientPullbackIso and the
  IsMonHom instances certify its ring interpretation. The inverse-image squares
  use these exact comparisons in the correct direction.
- `sk-def-sfb-change-of-scalars`: its closed audit records the existing Mod.comap,
  extendScalars, coextension and adjunctions. I opened their definitions:
  restriction composes the action with the scalar map, extension is the balanced
  coequalizer with the upper-ring action, and coextension the internal-Hom
  equalizer. The finite-colimit and limit preservation interfaces are the ones
  used in interpreting flatness. Nothing is replaced by an arbitrary functor.

Source and proof audit: the source is the main-20261015 blueprint detail
`sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/`
`sk-prop-sfb-cartesian-coefficients-finite-free.md` and its `.proof.md`.
The module and theorem docstrings name this source and blueprint id. The theorem
has all nine immutable-node proof steps: arithmetic finite freeness, clearing
powers of ell, topological coordinates, condensed coordinates, monoidal point
pullback, rationalization and scalar-square identification, inverse-image
naturality, tensor as a finite sum, and finite-limit preservation. The missing
recorded declaration for the rationalization proof dependency is only a future
proof ingredient; it is not an object needed to type this stage-2 statement.
The source-based repairs and citer-audit rules therefore require no new node here.
The current repair note is a resolved stage-1 re-split note, not a route-pivot
note. The item statement is unchanged, so no statement_change/citer audit applies.
None of the eight statement or twenty-two proof dependencies belongs to the
route-pivot dropped list read from origin/newtargets-dag. No infinity/dg/model
machinery is used in the delivered statement or proof plan. This item itself is
about pro-etale coefficients; it does not substitute a pro-etale target for an
ordinary derived assertion.

Edge cases: equality E=F gives degree one; ramification is unrestricted and ell=2
is allowed. Every basis is covered. Empty schemes, identities and arbitrary
scheme morphisms are included. Empty profinite sets have their unique sections;
the all-S evaluation condition still uniquely determines maps. Degree zero cannot
satisfy hd for finite field extensions; no added positivity assumption discards
an intended case. There is no independent undersized test-object universe:
Scheme.{u} and Profinite.{u} use the framework's Ab.{u+1} convention, retaining the
small site's different object and morphism universes. No Noetherian, qcqs,
separatedness, characteristic or nonemptiness hypothesis is added.

Independent searches used rg with the alternative patterns `integral.?basis`,
`finite.?free.*coefficient`, `coefficient.*finite.?free`, and the full declaration
name across the group Sheaf tree, the exact pro-etale framework, older source
and Mathlib NumberTheory/Condensed trees. The close hits were the arithmetic-only
`Padic.exists_integral_basis`, the existing `Mod.finiteFree`, and Compatibility's
rational flatness statement; none includes both basis isomorphisms and both
compatibilities. The worker's LeanSearch, LeanFinder, Loogle and grep searches
were also read. No exact duplicate statement or private replacement was found.

Compiler and static checks: I independently reran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q80
 det-prop-sfb-cartesian-coefficients-finite-free
 snapshot/lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteFreeCoefficients.lean`.
The wrapper returned exit code 0, no diagnostics: sandbox 12.8 s, actual library
module 6.3 s, with the reported private overlay under
`/dev/shm/nt-tmp/nt-local-compile-qko9qi62/.lbuild`. The installed wrapper announces
server execution; I used the prescribed wrapper only, with no direct ssh or
local Lean invocation. This reproduces the recorded per-file success, not a
claim to independently verify the historical 11.5-second timing. I checked the
node's lean.statement against the entire source signature before `:= by`:
verbatim equality holds. All binders are explicit; no line exceeds 100 characters.
There is exactly one new theorem, with sole proof `by sorry`, and no new definition,
axiom, local proof, instance, or notation. No hollow data is introduced.

Finding and disposition: H11, placeholder second reading, fixed by this complete
replacement report. No mathematical or Lean-statement fault was found. The
immutable snapshot and all project clones were left unchanged; no global build,
claim, delivery, merge or live Lean write was performed. Verdict: FIX (report only).
