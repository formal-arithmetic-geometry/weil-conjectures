## Worker report

The delivery states `AlgebraicGeometry.ProEtale.projection_section_normalization`
in `Sheaf.Paper.ProjectionSectionNormalization`. The node's natural statement is
unchanged. The main theorem has `sorry`; its helper maps are real constructions.
Four additional definition nodes supply the explicit canonical arrows and
composites on the existing internal-module functors. The tensor comparison and
monoidal structures are imported from the published module-object framework. The theorem introduces no arbitrary comparison data.

Hypothesis-by-hypothesis rendering:

| Node text | Lean |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Finite extension E/Q_ell, with valuation ring O_E | `E : PadicAlgCl.FiniteIntermediateField ℓ`; the coefficient is `Profinite.padicIntegersRingObj ℓ E.1`, the continuous-function condensed ring of the valuation ring. A finite extension can be embedded in the fixed algebraic closure; the intermediate-field presentation does not restrict its isomorphism class. |
| Field k of positive characteristic p different from ell | `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)`. The prime condition expresses positive field characteristic, which is necessarily prime. |
| Separated finite-type k-schemes X,V | `X V : Over (Spec (.of k))`, with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on each structure map. Finite type is locally finite type plus quasi-compactness. |
| All maps are k-morphisms | `r : V ⟶ X`, `i : X ⟶ V` in the over category. |
| r proper, i closed immersion | `[IsProper r.left] [IsClosedImmersion i.left]`, the recorded Mathlib predicates. |
| ri = id_X | `h : i.left ≫ r.left = 𝟙 X.left`. Equality of these underlying maps is equivalent to equality in the over category. |
| M in L(X) = Loc(Dbc(X,O_E)) | `M : DerivedCategory (Mod ... (condensedRingObj ... X.left))`, with `_hM : CategoryTheory.localizingClosure (constantModelBoundedConstructible ... X.left) M`. This is the closure of Dbc as requested, not the finite-Tor intersection used by the specialized `localizingClosureProEtale`. |

Clause-by-clause rendering (all names below are in
`AlgebraicGeometry.ProEtale.ProjectionSection`):

* `projection Λ f M N` is precisely the stated adjunct. Its transpose is
  `((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app (Rf_* N)` followed by identity tensor the
  counit of `CondensedRing.derivedUpperStarLowerStarAdjunction Λ f`.
* `pullbackSection` is the inverse of `leftDerivedUpperStarComp Λ i r`, transport
  along `h`, then the identity comparison. The latter is the published exact
  comparison `leftDerivedUpperStarIsoMapDerivedCategory` followed by
  `profinitePointModuleDerivedIdentity`.
* `pushforwardSection` is the adjunction conjugate of this same pullback comparison,
  using the composite of the two specified derived adjunctions and `Adjunction.id`.
  Thus no unrelated direct-image comparison is an input.
* `sectionArrow` is the displayed a_M: the i-projection, followed by Ri_* of
  `(pullbackSection.hom.app M ▷ R_X) ≫ (ρ_ M).hom`.
* `forward` inserts the right unitor and the inverse direct-image section comparison
  at R_X, then applies the r-projection, Rr_*(a_M), and the direct-image comparison
  at M. Its source and target are M. The first conjunct of `ProjectionSection.Normalized`, the theorem conclusion, is `forward ... = 𝟙 M`.
* `backward` reverses precisely these arrows and comparisons. The second conjunct of `Normalized` quantifies over invertibility of the r-projection and a_M and states
  `backward ... = 𝟙 M`. Invertibility of a_M is equivalent to invertibility of the
  i-projection, because the other factor in its definition is the image of a
  composition of isomorphisms. No projection is assumed invertible in the first
  conjunct, and the second conjunct makes no unconditional invertibility claim.

The tensor unit in these displays is the unit of the existing derived relative
module tensor. It represents the regular coefficient module R_X in degree zero.
The existing K-flat derived tensor and the generic total derived pullback and
pushforward are used throughout; there is no derived-completeness restriction.
The scheme universe is arbitrary u. The actual small pro-etale site and its
abelian sheaves in u+1 are retained.

Dependency declarations read and used:

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` and its setting. No compactification
  choice enters this identity; the separated finite-type setting is explicit.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `CondensedRing.derivedUpperStarLowerStarAdjunction`,
  `CondensedRing.leftDerivedUpperStarComp`, and
  `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`. These use
  `Functor.leftDerivedFunctor` and `Functor.rightDerivedFunctor` on the actual
  underived composites. The adjunction is also the recorded declaration of
  `def-sfb-module-derived-pushpull-adjunction`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, `lowerStar`, `upperStarComp`, `lowerStarComp`, and
  `upperStarLowerStarAdjunction`. The pullback is transport then extension of
  scalars along the specified coefficient map, not an alternative definition.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, using the finite constant local models
  recorded by `sk-def-sfb-constructible`.
* `Sheaf.Paper.LocalizingAdmissibleCoefficients` publicly imports
  `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.localizingClosure` and
  `IsLocalizingSubcategory`. The general closure applies to Dbc directly; no
  repair or second localizing-closure definition is necessary.
* `Sheaf.Paper.CartesianCoefficients`: the recorded cartesian coefficient
  convention and `cartesianCoefficientPullbackIso`. The helper uses the same
  inverse-alpha comparison through the previously published
  `profinitePointModuleForgetPullbackIso`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor` and `.Hom`:
  `CondensedRing.derivedTensor`, `isLeftDerivedFunctor₂_derivedTensor`, and the
  existing monoidal structure whose internal Hom is `CondensedRing.derivedHom`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its full representative square and ordinary pure-tensor normalization were read.
  The published internal-module comparison gives the representative-defined
  comparison in the actual internal-module presentation.
* `Sheaf.Paper.ProfinitePointPullback`:
  `profinitePointModuleForgetPullbackIso`, `profinitePointModuleIdentity`, and
  `profinitePointModuleDerivedIdentity`. This landed node is added to stmt_deps
  because the explicit identity comparisons are needed to write the statement.

The stated proof dependencies are imported without `public`:
`Sheaf.Paper.RingedProjectionTensorComposition` and
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
The tensor-pullback dependency is also a non-public proof import because its
section-ring representative interface is used to prove identification, whereas
all public maps here use the existing internal-module presentation.
`lem-pd-module-ringed-topos-derived-comparison` currently has no recorded Lean
module and is therefore not importable. It remains an open proof prerequisite;
it is not needed to type this statement, whose maps are constructed directly.
No wait on it or circular projection-coherence assumption is introduced.

Edge cases checked before and after writing: identity retraction and identity
section give the unit-normalized projection; M=0 gives the zero object's identity;
the empty scheme is admitted; V may equal X; no connectedness, nonempty scheme,
smoothness, boundedness of M, or invertibility of the projection is introduced.
The geometric model X=Spec(k), V=P1_k with a rational closed section has the stated
endpoints. The first equality is formal even without properness/constructibility,
but those node hypotheses are retained. The conditional inverse equality uses
only the invertibility stated in its binders.

Searches for the item: msearch.py leanfinder, query "For a proper retraction with
a closed section, the canonical derived projection formula map followed by the
section projection formula map is the identity": 8 hits, concerning split linear
maps, trivial square-zero extensions, and Profinite projections, no match.
Loogle `CategoryTheory.Adjunction, CategoryTheory.Functor, "projection"`: 0 hits.
LeanSearch "Canonical derived projection formula for a morphism with a section is
the identity after composition": 8 section and tensor-algebra hits, no derived
module projection identity. Mathlib grep
`projection.*formula|projection.*composition|counit.*tensor` in CategoryTheory:
17 hits in generic monoidal/adjunction files, no match. The upstream-name index `dag/lean_names_upstream.json` also had no matching
comparison/section-normalization names. The upstream item-id grep
and searches for `projectionSectionNormalization`, `projection_section_normalization`,
and `sectionNormalization` in upstream and lean/Sheaf gave no match. The existing
ringed-topos coherence theorem is a general proof dependency, not the requested
scheme/internal-module specialization with a_M and the inverted clause.

The source clause (1), the stage-1 split proof, and the cited Stacks local sources
were read. No statement fault or STATEMENT-DISPUTED flag was found. The additional interfaces are recorded in the new definition nodes below.
The returned H4/H12 finding was correct: the earlier tensor node duplicated the
published ordinary monoidal structure and derived tensor comparison. That node
and its module are removed from this packet. No global instance is introduced.

## New nodes

`def-sfb-module-projection-section-arrows`, in
`Sheaf.Paper.ModuleProjectionSectionArrows`, supplies `projection`,
`pullbackSection`, and `pushforwardSection`. These are exactly the
maps introduced in the original item's prose, now reusable definitions. The
pullback section is the published composition/identity comparison; its right
adjoint mate is the pushforward section. The section arrow is defined in its own node below.

`def-sfb-module-section-projection-arrow`, in
`Sheaf.Paper.ModuleSectionProjectionArrow`, supplies `sectionArrow`, the displayed
a_M. It uses only the specified i-projection and Ri_* of the canonical pullback
section and right unitor. It introduces no extra property or hypothesis.

`def-sfb-module-projection-section-composites`, in
`Sheaf.Paper.ModuleProjectionSectionComposites`, supplies `forward`, inserting
every unitor and section comparison in the stated forward endomorphism.

`def-sfb-module-projection-section-inverse`, in
`Sheaf.Paper.ModuleProjectionSectionInverse`, supplies `backward`, the reversed
inverse path, conditional on exactly the two specified factors being isomorphisms.
It asserts no identity or invertibility. The item's own module defines the
transparent proposition `ProjectionSection.Normalized` as the two required
identity assertions, and states the theorem using it.

These four map/composite nodes have the same blueprint clause as their source. LeanSearch on
"Canonical derived projection formula map defined by adjunction and normalized
along a retraction and its section" returned eight generic derived-adjunction,
Kaehler retraction, and categorical retract hits, no specialized maps. The additional
LeanFinder query "Canonical derived module projection formula morphism defined
as adjoint of tensor pullback comparison followed by counit, section retraction
composites" returned eight ordinary ModuleCat change-of-ring/Gabriel-Popescu hits.
Loogle `CategoryTheory.Adjunction.homEquiv, CategoryTheory.conjugateIsoEquiv`
returned zero. The earlier Mathlib projection/counit grep returned only generic
monoidal identities. `blueprint_refs.py search 'module projection section'`
returned zero; DAG/project/upstream grep found only affine rectangle section
tensor calculations, which concern ordinary scheme modules, not these derived
internal-module functors. Thus generic adjunction APIs are reused while the
missing specialized maps are defined, rather than replaced by arbitrary arrows.
All four definition nodes are cited directly by the item; their imports and
statement dependencies follow the order arrows, section arrow, forward composite,
inverse composite. The arrows node and the item both cite the existing
`new-proetale-derived-module-pullback-monoidal` node.

## Repair of returned delivery

Return L at immutable head `807612693cf0`, H4/H12: removed
`def-sfb-module-pullback-tensor-comparison.json` and
`ModulePullbackTensorComparison.lean`, including the sorried uniqueness theorem,
the `choose`, both duplicate global instances, and the derived-comparison alias.
The projection now applies the published
`CondensedRing.leftDerivedUpperStarTensor Λ f` directly and follows it with
identity tensor the counit. This is the left-ordered version of the already
published `CondensedRing.moduleObjectProjectionMap` in
`Sheaf.Paper.ModuleObjectProjectionMap`: the latter orders the direct-image
factor first. No arbitrary tensor map or alternate monoidal structure is supplied.

Read with `scompile.py --source`:
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, especially
`upperStar_preservesFlat`, `leftDerivedUpperStarTensor`, its derived-counit
characterization `leftDerivedUpperStarTensor_fac`, and
`leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison`. This uses the
published `monoidal_upperStar` from `UpperLowerStar.MonoidalModule`.
The arrows node and the item cite
`new-proetale-derived-module-pullback-monoidal` as requested. The two typed
abbreviations of the existing derived functors moved into the arrows module;
they change no functor data and are listed in that node's `lean.declarations`.
The remaining four map/composite modules and the theorem retain their signatures.

The current shared-base item was compared with the saved item: its natural
statement, proof, proof dependencies and all metadata remain unchanged; only
`lean` and the authorized statement dependencies are supplied. No dependency
record repair or mathematical statement correction is needed.

## Second reading by Q15

The dispatcher forbids starting another agent. This is the worker's separate
second pass; the maintainer's independent reading remains the delivery review.

I reopened the item, the four definition nodes and all five modules. Every
hypothesis in the table above still occurs verbatim in the main theorem: prime
ell, finite E, positive characteristic different from ell, separated finite-type
k-schemes, k-morphisms, proper r, closed i, ri=1 and M in Loc(Dbc). No small-site
universe changed. The projection is now the actual published K-flat comparison
followed by the adjunction counit. The pullback and pushforward section
comparisons are the same adjoint mates. The forward path inserts the right
unitor and the section comparison, applies both projections, and returns to M;
the backward path reverses exactly these arrows under their two IsIso binders.
The two conjuncts in Normalized still state precisely the two node equalities.

I checked r=i=id, M=0, the empty scheme, V=X, and the rational closed section
Spec(k) into P1_k. The change does not add any geometric, boundedness or
invertibility hypothesis. The only postponed proof is the named main theorem;
all definitions contain real data. There is no remaining reference to the
removed node or its duplicate instances in Lean or DAG records.

## Validation

The prescribed initial dry run was started against the saved six-file packet.
Its compile checks completed, but collection at the end failed because the obsolete
tensor module had been removed during that run. This was an invalidated saved-packet
run, not evidence that the repaired packet passed preflight.

The explicit repaired five-file `scompile.py` command completed with exit 0.
Every private overlay, sandbox and library-path check passed, with no errors or
unexpected warnings. No limit was changed. The wrapper-reported elapsed times
include slot waits; all checks used its standard per-file compiler limit.
The stable repaired packet passed `deliver2.py --no-push` with exit 0:
`OK (dry run): commit ca43b30815 passes the preflight and compiles; nothing pushed`.
The staged inventory contains exactly the report, five node records and five
Lean modules; the removed tensor node/module are absent. The final second pass
confirmed the returned H4/H12 issue is repaired and the theorem's hypotheses and
both clauses remain unchanged.

## Saved-packet timeout return self-check (2026-10-18)

The current return names immutable head `227da443f0f3` and a 60-second timeout
in the private overlay for `Sheaf.Paper.ModuleProjectionSectionArrows`. As the
dispatcher's saved-packet instruction requires, I first read this report and ran
`deliver2.py Q15 lem-sfb-projection-section-normalization --no-push` on the
retained packet, before changing any file. It exited 0 and printed:
`OK (dry run): commit e276c3bdfe passes the preflight and compiles; nothing pushed`.
All five files passed the prescribed server checks, including the private-overlay,
sandbox and library checks of the arrows module. The reported timeout did not
recur. No compiler limit, launcher tool, imported library or Lean definition was
changed. Following the explicit instruction to retain a passing saved packet,
this retry retains all five Lean modules and all five node records.

I completed the self-check with the item and all four new definition nodes open
beside their modules. All five `lean.statement` signatures are verbatim from the
files. Compared with the current shared item, only `lean` and the authorized
additions to `stmt_deps` differ; its statement, proof and proof dependencies are
unchanged. Every definition has real data, and the sole `sorry` is the named
main theorem. All variables and the scheme universe are explicitly bound, and
no Lean line exceeds 100 characters.

The canonical projection remains the transpose of the published pullback tensor
comparison followed by identity tensor counit. The pullback section uses the
composition and identity comparisons, and its conjugate gives the pushforward
section. The section arrow, forward composite and conditional inverse composite
follow the paths in their nodes. Prime ell, finite E, positive characteristic
different from ell, both separated finite-type k-schemes, k-morphisms, proper r,
closed i, ri=1 and M in Loc(Dbc) are all retained. The two conjuncts still assert
the forward identity and, under precisely the two invertibility binders, the
backward identity. The identity section, zero object, empty scheme and V=X
cases remain admitted. No mathematical mismatch was found in this self-check.

## Missing-object return self-check (2026-10-18)

The current return names immutable head `ad633e03e0d9` and a missing published
`Sheaf.Paper.AlgebraicallyClosedCoefficients.olean` while compiling the main
statement. Following the saved-packet instruction, I read this report and first
ran the prescribed unchanged-packet dry run. Its initial overlay attempt checked
all four helper modules cleanly, then reported a missing published
`Sheaf.Paper.DerivedPullbackTensorHom.olean` at the main theorem. The wrapper
continued with its automatic current-server confirmation and exited 0:
`OK (dry run): commit f1010968a5 passes the preflight and compiles; nothing pushed`.
Thus the complete prescribed check passes; neither missing-object diagnostic is
an elaboration error in a delivered definition or theorem. The required
CartesianCoefficients import reaches both named modules through its Tate-twist
imports; its current source was also read with `scompile.py --source`.

As explicitly required for a passing saved packet, all five Lean modules and all
five node records are retained. No launcher tool, live library, compiler limit,
statement or definition was modified. The wrapper performs the authorized
refresh, server confirmation and delivery rebase against current main.

For this retry I reopened all five modules and their nodes. Every recorded
`lean.statement` occurs verbatim in its file; all files disable auto-implicit
variables, explicitly bind their universe, and satisfy the 100-column limit.
The four definition modules contain no sorry; the main theorem is the only
postponed proof and has its source and complete proof docstring. The current
shared item differs only in `lean` and the authorized `stmt_deps` additions.
There is no maintenance repair note for the item.

The hypothesis table and clause-by-clause reading above still apply: prime ell,
finite E, characteristic p positive and different from ell, separated finite-type
k-schemes, k-morphisms, proper r, closed i, ri=1 and M in Loc(Dbc) are all present.
The projection is the canonical tensor-comparison/counit transpose, and the two
section comparisons are adjunction conjugates. The forward path and conditional
inverse path use exactly those arrows, units and comparisons. Identity sections,
M=0, the empty scheme and V=X remain admitted. No mathematical mismatch or node
statement correction was found. This report is the only file updated in this
retry, documenting the passing saved packet and this completed self-check.
