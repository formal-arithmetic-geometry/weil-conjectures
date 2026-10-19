## Worker report

The delivery states lem-pur-system-compactification-pf-substitution in
`Sheaf.Paper.SystemCompactificationProjectionSubstitution`. Nothing is proved:
the four named theorem bodies are `sorry`. All definitions have actual terms.
The mathematical statement is unchanged. The only added statement dependency is
the already published `def-pur-system-tensor-mate-arrows`, used directly for its
universal presentation and canonical arrows.

Hypothesis and clause correspondence:

- Finite field, characteristic and algebraic closure: `K : FiniteFieldDatum.{u}`
  retains the recorded prime, finite base field and fixed algebraic closure.
  The coefficient prime is `l : ℕ` with `[Fact l.Prime]` and `hl : l ≠ K.p`.
  The coefficient extension is `E : Type (u+1)` with `Field E`,
  `Algebra ℚ_[l] E` and `FiniteDimensional ℚ_[l] E`. The integer ring,
  uniformizer and quotient rings are the existing Padic coefficient constructions.
  Index `n : ℕ` means exponent `n+1`; no positive level is omitted.
- The small pro-etale sites, quotient module systems and ordinary unbounded
  derived categories are the published `SystemTensorMate.S` and `.D`.
  Site object universe is u+1, morphism universe u, module universe u+1,
  and derived localization universe u+2. No equality of site universes is imposed.
- `o : TensorOperations l E` is the published universal presentation, whose
  existence is `tensorOperations_nonempty`. It is not an arbitrary tensor or
  an assumed compatibility equation. Its ordinary left adjoints, exact open
  extensions, scalar units and K-flat tensor representative normalizations are
  all retained. The statement works for every such presentation.
- `P_u`, `R_u`, their canonical adjunction and tensor comparison are `o.P`,
  `pushDerived l E`, `o.derivedAdj` and `o.mu`. The projection map is the existing
  `o.projection`, the counit transpose, and the open comparison is `o.delta`.
- Separated finite-type k-schemes are `[X.Over (Spec (.of K.k))]` and the analogous
  Y instance, with `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on both
  structure morphisms. The morphism f has `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f` and `QuasiCompact f`. These hypotheses belong to the
  Geometry section and are retained in its declarations.
- Compactifications are the recorded `Compactification f`, with `.i` open,
  `.g` proper and `.comm : f = i ≫ g`. Proper refinements are the recorded
  `c₁.Refinement c₂`; `.i_hom` and `.hom_g` render both required triangles.
  `refinementOpenQuasiCompact` uses the existing compactification theorem to
  derive quasi-compactness of the open from `QuasiCompact f`; it is not a new
  hypothesis. Compactification spaces carry their canonical base structures.
- `F_i` is `refinementImage o cᵢ = o.J cᵢ.i ⋙ pushDerived l E cᵢ.g`.
- `refinementGamma` is exactly the recorded `o.gamma` for
  `(j₁,id_X,u,j₂)`, preceded by the canonical identity direct-image comparison.
  It retains the noncartesian, clopen-component projection, rather than using
  a cartesian base-change map or an arbitrary natural isomorphism.
- `refinementDirectId_existsUnique` specifies the identity comparison by its
  section equation along the inverse fibre-product identity. This is the
  identity normalization in the node, not a choice of an unrelated map.
  `refinementPullId` localizes its adjunction conjugate, and `refinementPushId`
  conjugates through the canonical derived adjunction. Their data are determined
  up to equality by the theorem's uniqueness, as required for definitions.
- `refinementPushComp` is the canonical adjunction conjugate of `o.pComp`;
  `refinementCompositor` first uses the equality p₂u=p₁, then this compositor.
  Its direction is R_p1 → R_u followed by R_p2, matching the node's c_(p2,u).
- The clause that gamma is invertible on bounded constructible levels is
  `refinementGamma_isIso`. Its hypothesis is `refinementDomain X M`, namely
  `∀ n, levelBoundedConstructible ... ((refinementLevel X n).obj M)`.
  It imposes neither normalization nor Tor finiteness. Evaluation is used only
  for equivalence detection in the proof plan, never to detect equality.
- `refinementTheta` is the compositor followed by R_p2 of the inverse of the
  specified gamma, with its named invertibility theorem. Its source and target
  are precisely F₁M and F₂M; it is an Iso and has no arbitrary arrow field.
- `refinementPF` is `o.projection c.g` followed by R_c.g of `o.delta c.i`;
  it then inserts the canonical pullback compositor and `c.comm` to identify
  P_j P_p N with P_f N. This is the component of the supplied-domain projection
  word of def-exchange-projection, specialized to the published system arrows.
- The M,N hypotheses of the projection assertion are
  `refinementNormalizedCtf o X M` and `refinementNormalizedCtf o Y N`.
  Its first conjunct is the existing `SemilinearSections.Normalized`, testing
  invertibility of the adjoints of actual horizontal transitions for every
  m≥n. Its second is `∀ n, finiteTorConstructibleSystemLevel ...` on the
  actual evaluated object. The definition-level universe repairs are described
  below. No uniform bound or common stratification is assumed.
- `system_compactification_pf_substitution` concludes that the tensor input has
  the comparison domain and asserts
  `refinementPF c₁ ≫ (refinementTheta r at tensor).hom =`
  `tensor.map (theta_M.hom,id_N) ≫ refinementPF c₂`.
  The existential `hT` is a proof of the domain needed to invert gamma, not
  an additional hypothesis or any independently chosen tensor object.
  Both sides have exactly source F₁M tensor N and target F₂(M tensor P_f N).
- `system_compactification_refinement_coherence` has four conjuncts: theta of
  `Refinement.id` is `Iso.refl`; theta of `r.comp s` is the Iso composite;
  any two spans between the same compactifications give equal
  `refinementSpanComparison`; arbitrary three spans satisfy the cocycle.
  Each is quantified over `M` with `refinementDomain X M`, the broader domain
  in the node's final paragraph, rather than only normalized finite-Tor objects.
  The span map is defined as theta_a.symm followed by theta_b.

Dependency declarations read and used:

- `Sheaf.Paper.SystemTensorMateArrows`: `TensorOperations`, `D`, `S`,
  `Operations.P`, `.J`, `.T`, `.derivedAdj`, `.pComp`, `.gamma`,
  `TensorOperations.projection`, `.delta`, and `tensorOperations_nonempty`.
- `Sheaf.Paper.SemilinearDerivedSections` and its public calculus/models:
  `SemilinearSections.Data`, `e`, `Normalized`, `reduction`, and
  `semilinearDerivedSections`; the level tensor is `.levelClosed` and its
  canonical K-flat model is `.levelTensorModels`.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`,
  `.id`, `.comp`, `.isProper`, `.i_hom` and `.hom_g`; the compactification
  definition and `quasiCompact_openImmersion` are used directly.
  `WeilConjectures.Compactification.Over` supplies canonical base structures.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public import:
  `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing`.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`,
  `normalizedDVRModules` and the actual quotient restrictions. Its normalization
  is rendered on actual systems by the existing semilinear `Normalized`, not
  a new tower with freely supplied transition-adjoint maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  Scheme-morphism-properties and size-convention are conventions, with no new
  declaration to copy.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `SuppliedExchangeProjection.compactificationProjectionFromData` and
  `ExchangeProjectionStage.projection`, the same counit/open-tensor word.
- `Sheaf.Paper.RefinementComparisonIsomorphism`:
  `ProEtale.refinementComparisonAtWitness`, `refinementComparisonIsomorphism`
  and `properTransportRefinement`, read as the finite normalization of the
  system comparison; these are proof imports rather than a fixed-coefficient
  category substituted for the required system category.
- `Sheaf.Paper.SystemClopenTensorCompatibility`:
  `system_clopen_tensor_compatibility`, the specified geometric identity.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization`, supplying the inverse-transpose
  normalization retained by `o.delta`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `ringedToposDerivedPushforwardComposition`, whose canonical comparison is
  realized here by its adjunction-conjugate form with the actual system
  compositor. No smallness hypothesis on the original site is strengthened.
- Proof imports additionally retain `sf_pullback_torAmplitude`,
  `finiteCoefficient_tensor_ctf`, `normalized_tensor_closure`,
  `constructible_proEtale_origin`, and the published strict-tower calculus.
  Dependencies without recorded statement modules (ambient/varying pasting,
  mate pasting, and generic Noetherian facts) have no fictitious Lean import.

Edge cases checked against the definitions and source argument:

- Identity refinements use the section-normalized identity, not an arbitrary
  automorphism. Composition is in the order r followed by s.
- Compactifications need not have dense image. An extra clopen component is
  killed by the existing gamma's clopen projector; no cartesian refinement
  hypothesis is introduced. This agrees with Stacks' warning before 0ATU.
- Empty X, empty strata, and zero objects are allowed. The intrinsic sheaf
  definition retains the recorded positive-number-of-strata convention; empty
  strata are permitted, so the empty scheme is not excluded.
- n=0 is exponent one; no exponent-zero coefficient stage occurs.
- Cohomological and Tor intervals may grow with n. The quantifiers are
  `∀ n` outside the per-level boundedness and `∃ a b`, respectively.
- Normalization tests all m≥n, including m=n and nonflat quotient maps.
- Coherence holds without normalization or finite Tor amplitude; only the
  projection equality uses those hypotheses. No normalization assertion is
  imposed on R_p j_! M.
- Parallel arrows are equalized before cancellation in the proof docstring;
  independence of common objects alone is not mistaken for arrow independence.

Searches made before writing:

- msearch leanfinder: "compactification refinement comparison intertwines strict
  semilinear system projection formula maps". Eight unrelated Profinite/Nobeling
  projection hits; none states this system result.
- msearch loogle: `CategoryTheory.Adjunction.comp_counit`. One exact generic
  composite-counit identity, not the geometric system statement.
- msearch leansearch: "compactification refinement comparison projection formula
  strict coefficient systems". Eight unrelated topological/colimit hits; no match.
- msearch grep: `compactification.*projection|refinement.*projection` in
  CategoryTheory. Zero hits. The generic `comp_counit` tool is used in the proof plan.
- rg in upstream WeilConjectures: related fixed-coefficient etale
  LowerShriekProjectionRefinement results exist, but their categories and domains
  are not the ordinary varying-coefficient system categories of this node.
  The node id has no upstream declaration.
- rg in lean/Sheaf: SystemTensorMateArrows and SystemClopenTensorCompatibility
  supply the canonical notions and one ingredient, not the requested refinement
  substitution and all four coherence clauses. Existing refinement comparisons
  are finite-coefficient etale-origin constructions.
- msearch grep for `IsConstructibleProEtaleModuleSheafOfUniverses|`
  `finiteTorConstructibleSystemLevel`: no Mathlib match. The landed project
  declaration `Scheme.IsConstructibleProEtaleCoefficientModuleSheaf` is the
  existing coefficient-universe constructibility predicate and is reused
  directly; only the finite-Tor system-level specialization is supplied here.

No STATEMENT-DISPUTED issue or source correction was found. Source texts read:
Stacks more-etale.tex 0F7B/0F7C/0F7J, sites-cohomology.tex 0B56,
flat.tex 0ATU including its parallel-arrow equalizer condition; current blueprint
main-20261015 prop-pur-adic-reconstruction-trace-coherence and its proof.

## Dependency modules

`def-weil-proetale-constructible-sheaf` is now used through the landed module
`Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`, whose existing
`Scheme.IsConstructibleProEtaleCoefficientModuleSheaf` has the required
`A : Type (u+1)` coefficient universe and the same finite stratification,
local constancy, and finite stalk clauses. The earlier copied
`ProEtaleConstructibleCoefficientUniverse` module and its node copy were
removed because they duplicated that usable declaration; the dependency node
itself and its statement record were not changed.

`def-weil-finite-tor-amplitude` retains NW's landed existing:true record,
`Sheaf.Paper.FiniteTorAmplitudeSites` / `WeilConjectures.finiteTorConstructibleEtale`,
without any dependency-node copy in this delivery. The three system-level
specialization helpers (`Level`, `levelBoundedConstructible`, and
`finiteTorConstructibleSystemLevel`) now belong to
`SystemCompactificationProjectionSubstitution` and are listed in the item's
`lean.declarations`. They use the actual coefficient category, the existing
constructibility predicate, and the canonical representative-normalized tensor.
They are helper definitions for the system domain of this item; they do not
replace the finite-Tor node's ordinary etale interface.

## Second reading by Q03

I reread the complete item module and matched each clause against the node in
order. The coefficient setup is represented by `K`, `hl`, `E`, the finite
coefficient rings and the fixed `S`/`D` system categories, with no extra
uniform-index assumption. The canonical operations clause is rendered by
`o.P`, `pushDerived`, `o.derivedAdj`, `o.mu`, `o.projection`, `o.delta`, and the
two named system-level mate definitions. The morphism clause retains all
separation, finite-type, quasi-compact, and `IsOver` hypotheses on `f`; the
compactification clause uses the recorded `Compactification` fields and both
refinement triangles. The gamma clause uses the ordered square
`(j₁,id_X,u,j₂)`, including the identity direct-image normalization, and its
invertibility is restricted exactly to `refinementDomain`. The compositor and
theta clauses have the direction `R_{p₁} ≅ R_{p₂}R_u` and apply the inverse gamma
on the stated domain. The projection clause is the specified proper projection,
open tensor comparison, and pullback compositor, with no replacement map. The
main theorem quantifies normalized finite-Tor `M,N`, produces the tensor's
levelwise domain witness, and places the two composites in the node's order with
the tensor map `(theta_M, id_N)`. I checked that the final sentence imposes no
common bound. Finally, the coherence theorem has exactly four conjuncts:
identity, ordered composition, independence of two common-refinement spans, and
the three-endpoint cocycle, all on `refinementDomain` before evaluation. The
edge cases in the preceding audit (identity, empty schemes and strata, zero
objects, extra clopen components, and bounds growing with `n`) agree with these
quantifiers and definitions.

The three finite-Tor helpers in the item module were also read clause by clause.
`Level` names exactly the positive-level pro-etale derived category. In
`levelBoundedConstructible`, finite support of integer-indexed homology renders
boundedness, and the universal cohomology-sheaf clause uses the existing
`Scheme.IsConstructibleProEtaleCoefficientModuleSheaf` with the actual lifted
quotient ring. In `finiteTorConstructibleSystemLevel`, the first conjunct
retains that bounded constructibility; `∃ a b, a ≤ b` provides one ordered Tor
interval at this level; `∀ F` tests every module sheaf in degree zero, and
`i < a ∨ b < i` renders precisely the vanishing outside that interval. The tensor
is the published `levelClosed` tensor. The original finite, integral and field
interfaces remain imported. No constructibility dependency record is delivered.
The previous H13/H4 predicate repair and H11 reading remain present. The current
H13 ownership repair moves the three helpers into the item without changing
their data or the theorem signatures, and removes the finite-Tor dependency
record and standalone helper module from the packet. NW’s landed record remains
untouched. This self-check found no further mathematical mismatch.

## Returned H13 ownership repair, 2026-10-18

The initial saved-packet dry run passed as commit 0605fefa05, but the immutable
review of acba2b686bbe identifies a semantic ownership fault not caught by that
gate. Repaired exactly as requested: moved all three system-level definitions
into the item module with their existing names and bodies, added them to the
item's `lean.declarations`, and removed both the standalone helper module and
the finite-Tor dependency-node override. In particular NW's existing:true
`FiniteTorAmplitudeSites` / `finiteTorConstructibleEtale` record is unchanged.
The helper docstrings now name the item that owns them. The four theorem
signatures, canonical arrows, finite-Tor predicate data and all earlier
constructibility and second-reading repairs are retained.

Historical failed prerequisite attempts and obsolete dependency-rebinding
validation entries have been superseded by this repair.

## Validation

The prescribed `scompile.py Q03 lem-pur-system-compactification-pf-substitution`
check of the sole delivered module exited 0. The sandbox and library-name
checks took 27.2 s and 7.2 s respectively, with no errors or unexpected warnings.
The JSON signature occurs verbatim in the module; JSON uses indent 1, Unicode
and a final newline. All Lean lines are at most 100 characters. Automatic
implicits are disabled. Against the current shared base, only the item's `lean`
and its documented added tensor-mate statement dependency differ. No dependency
node record is present in this delivery, so NW's finite-Tor record cannot be
overwritten by it. The relocated helper data and all theorem statements were
read again after the move against the item statement and returned review.

The repaired-packet dry run passed preflight and compiled the sole module:
`OK (dry run): commit 17aa5e771a`. Its staged set contained only this report,
the item node, and `SystemCompactificationProjectionSubstitution.lean`.
