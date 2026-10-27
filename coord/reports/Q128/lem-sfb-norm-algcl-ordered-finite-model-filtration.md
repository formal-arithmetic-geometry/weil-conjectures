## Worker report

Q128, stage 2, 2026-10-22. The module is
`Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration`, with namespace
`AlgebraicGeometry.ProEtale.NormAlgclOrderedModels`. The main theorem is
`orderedFiniteModelFiltration`; its proof is `sorry`. All helper constructions have
actual data. No mathematical statement, split or proof dependency is changed.

The inherited BLOCKED ending concerned a stage-1 unchanged-split refusal. The current
`coord/brief-stage2.md` §0 explicitly authorizes the stage-2 handoff: the current node
is split, has no Lean record, and appears in `coord/queue.tsv` at stage 2. There is no
repair note for this item. The Q139 split and accepted mathematical statement are preserved.

Clause-by-clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; positive characteristic and its exclusion are
  `(p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)`. The base is `(k : Type u) [Field k]`.
- The separated finite-type k-scheme is `X : Over (Spec (.of k))`, with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`.
  The two finite-type instances together are exactly finite type. `noetherianSpace`
  derives the needed topology from these hypotheses; it adds no assumption.
- The chosen algebraic closure with its extended norm is the dependency framework's
  `PadicAlgCl ℓ`. `Profinite.continuousMapRingObj (PadicAlgCl ℓ)` is B, all continuous
  functions, while the separate imported `Profinite.padicAlgClRingObj ℓ` is C, the
  finite-subextension-valued functions. These two are never equated. For
  `E : PadicAlgCl.FiniteIntermediateField ℓ`, `Profinite.continuousMapRingObj E` is A_E;
  finiteness of E over Q_ell is part of that subtype. The topology is the subfield norm.
- `condensedRingObj Λ T` is the existing inverse image p_T^*Λ. `Mod` is the existing
  category of internal module objects. Ordinary scalar extension is `Mod.extendScalars`
  along the inverse image of `scalarInclusion`; it is the relative tensor coequalizer,
  with the actual inclusion of continuous-map rings, not an arbitrary coefficient map.
- `M` is a B_X-module and `hM : IsConstantModelConstructible ... X.left M` uses exactly
  the recorded finite constant local-model constructibility. The imported
  `IsLisseCoefficientModule` means locally finite free and allows rank zero.
- `P : Scheme.Stratification X.left` is the supplied finite constructible locally closed
  scheme partition, including its actual scheme domains and immersions.
  `E`, `L`, `hL` and `φ` respectively give each finite intermediate field, its lisse
  A_E-module, lisseness, and the displayed B tensor L isomorphism to M restricted to P.
- `extension X Λ a ha` uses `coefficientHeartLocallyClosedExtension` itself: open
  extension along `a.toImage`, followed by closed direct image along `a.imageι`.
  Thus its value at L is exactly F_a, with no arbitrary extension functor.
- The existential `R : X.left.FiniteLocallyClosedStratification` supplies actual scheme
  strata. The `V : Fin (R.n + 1) → X.left.Opens` carrier equation gives precisely the
  ordered prefix unions. The endpoint equations give V_0 empty and V_m whole.
  Since X is Noetherian, the locally closed output strata are constructible as well.
- `a : Fin R.n → Fin P.n` and `R.stratum t ⊆ P.stratum (a t)` assert image containment
  only. No factorization through an old stratum is required or supplied.
- `refinedModel` is literally pullback of the old supported extension F_a to R_t.
  The conjunct quantifying over every `b : Fin P.n` and `t : Fin R.n` asserts adaptedness
  to every F_b, with each b's own coefficient field. It in particular gives lisseness
  of V'_t for b = a(t). The existential ψ has exactly source B_R tensor_{A_E,R} V'_t
  and target M restricted to R_t.
- `pullback (R.immersion t) (P.immersion (a t))` is the actual W_t, and `pullback.fst`
  is q_t. The theorem asserts `IsClosedImmersion` and `Surjective` for this map.
- `RestrictionNormalized` fixes ρ_a by the actual closed counit and open unit, using
  `a.toImage_imageι` and `upperStarComp`. This uniquely specifies the canonical
  restriction of a^*a_!L to L rather than an arbitrary isomorphism. `fibreRestriction`
  then uses pullback composition and `pullback.condition` to compare q^*r^*F and b^*L.
  `ModelCompatible` equates q^*ψ, followed by this target comparison, with the composite
  of the inverse canonical scalar-pullback comparison at q, the extension of
  `fibreRestriction` on A_E, the scalar-pullback comparison at b, and b^*φ. This is
  exactly the stated compatibility with the supplied φ on the actual fibre product.
- Each M_t is the existing `coefficientHeartOpenTerm B M (V t)` and its map to M is
  the existing `coefficientHeartOpenCounit`. The theorem asserts each is mono,
  the first object is zero, and the last counit is invertible (M_m = M canonically).
- The arrows `d t` link adjacent open terms, and the equation `d t ≫ ε_(t+1) = ε_t`
  makes them inclusions of the same subobjects of M. Their short exactness also asserts
  that they are monomorphisms. `cokernel (d t)` is therefore the actual quotient, and
  its isomorphism has exactly the displayed locally closed extension of B tensor V'.
- The existential short-exact proof `h` applies to these same arrows and their canonical
  cokernel projections. `h.singleTriangle ∈ distTriang _` is their corresponding
  degree-zero distinguished triangle in the ordinary unbounded `DerivedCategory`.
  Neither a completed nor a bounded substitute is used.

Dependency declarations read and used (publicly imported directly or through their
existing public import closure):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`; its explicit Over/finite-type setting.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj` (background C).
- `Sheaf.Topology.ContinuousMapCondensedRing` and its upstream ContinuousMap import:
  `Profinite.continuousMapRingSheafOfUniverse`, `Profinite.continuousMapRingObj`,
  `Profinite.continuousMapRingSheafMap`. The coefficients are Type 0, so the imported
  upstream version is the same sectionwise construction at coefficient universe zero.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded ordinary
  unbounded derived-category convention; the statement uses `DerivedCategory` itself.
- `Sheaf.Paper.CondensedConstantConstructibility`: `IsConstantModelConstructible`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek` and its adjunction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`, `upperStar`, `upperStarComp`, `upperStarLowerStarAdjunction`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.extendScalars`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`; input constructibility is supplied by the
  existing `Scheme.Stratification` used by the constructibility dependency.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections
  and its commutativity identity.
- `Sheaf.Paper.CoefficientHeartFiltration`: `coefficientHeartLocallyClosedExtension`,
  `coefficientHeartOpenTerm`, `coefficientHeartOpenCounit`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `CondensedRing.pullIso` (canonical adjunction mate).
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`:
  `ShortComplex.ShortExact.singleTriangle`, the existing degree-zero triangle.

The theorem docstring carries all seven proof steps and their named DAG dependencies.
Proof-only imports retain the existing lisse-extension, refinement, restriction,
surjective-closed equivalence, normalized extension, localization and reduced-closed
construction statements for stage 3. No new definition node or dependency repair is
needed: the helpers only spell out constructions and compatibility of this owning node.

Edge cases checked against the types: empty X permits R.n = 0 and no ψ or d;
P.n = 0 forces X empty by its cover axiom; empty strata are permitted; zero M has
zero counit terms and quotients; rank zero is permitted by Mod.IsFree; mixed fields
are indexed separately; no common E or positive-rank/nonempty/connectedness condition
is added. On Spec(k[epsilon]/epsilon^2) with old reduced stratum, image containment
still does not assert a scheme factorization: W and q retain the nilpotent correction.
All scheme/site and index universes use the established Scheme.{u}, Ab.{u+1} convention.

Searches: the retained searches.jsonl records actual msearch.py calls from Q128;
this pass repeated LeanFinder with "Ordered finite field lisse models of constructible
condensed modules and open support filtration on scheme strata", Loogle
`"Sheaf", "filtration"`, grep `(normAlgcl|norm_algcl|orderedFiniteModel)`, and LeanSearch
"Constructible condensed sheaf ordered scheme stratification finite field lisse models
and open extension by zero filtration". LeanFinder returned solid/discrete condensed
module infrastructure and scheme section lemmas; LeanSearch returned condensed-category
constructors; Loogle and grep had no hits. Direct rg of live Sheaf and WeilConjectures
found coefficient inclusions and an existing scalar-constructibility theorem, whose
signature was read: it does not assert this ordered refinement and filtration. Direct
grep of the item's ID in WeilConjectures found no hit. Existing coefficient, lisse,
stratification, tensor and extension definitions were reused. No STATEMENT-DISPUTED
or source correction is needed; the node already records that its norm-topology
reference is WANTED and that this is an extracted support obligation rather than a
separate norm-topology theorem stated in paragraph (3).

## Second reading by Q128

This is Q128's separate rereading, not a claim of an independent second agent. The
explicit dispatcher instruction forbids starting agents; the maintainer supplies the
independent review. I read the accepted seven-step node and the final module side by
side, including the coefficient distinction C versus B, every supplied φ, the adaptedness
quantifier over all old fields, image-only refinement, actual pullback projections,
normalization of ρ and the scalar-comparison orientations. I also checked that the
filtration uses actual open counits, that the d equation is over the same M, that the
cokernel quotient contains the specified refined model, and that the distinguished
triangle is attached to the same short exact sequence. During preparation a stale
positional application of the extension API was replaced with its named public interface;
this changed no statement. No new nodes, dependency modules or statement correction
are included.

Validation: the final generic compatibility formulation passed `scompile.py` against
the live published library. Its library check completed in 19.5 seconds, with no
errors or unexpected warnings. All temporary profiler and checkpoint commands and
heartbeat-limit changes were removed. `set_option autoImplicit false` remains, and
every variable and universe is explicitly bound. The delivery dry run follows.

The first dry run found that lean.statement included the trailing assignment delimiter.
The record now contains precisely the signature before `:=`, as the preflight expects;
the compiled Lean source is unchanged. Nothing was pushed by the failed dry run.
