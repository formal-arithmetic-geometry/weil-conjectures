## Worker report

Item: lem-weil-pbc-pullback-tensor-canonical-shift-unit. Group NQ, stage 2.

The module `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` states the full normalized
comparison, its uniqueness among natural transformations, both integer-shift
squares and both action-unit equations. Its only postponed proof is
`SheafOfModules.PullbackTensorCanonical.pullback_tensor_canonical_shift_unit`.
The helper predicates and structure have real data. No dependency node or
mathematical statement is changed; no independent notion or new DAG node is needed.

Source checked: `literature/stacks-project/sites-cohomology.tex`,
lemma-pullback-tensor-product (07A4), including its proof and the orientation of
its cochain comparison; `more-algebra.tex`, item-shift-tensor (0FNH), including
the sign on the first-factor degree; the recorded cochain-coherence interface
for multiplication units (03EL). The current server source of
`Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` was also read with
`scompile.py --source` to check the published representative signature.

Hypotheses and clauses, matched to Lean:

- Two small ringed sites: independent `uC,vC,uD,vD` for their object and morphism
  universes, common coefficient/module universe `r`, with
  `[EssentiallySmall.{r} C]` and `[EssentiallySmall.{r} D]`. These express exactly
  smallness relative to module size, without equating object and Hom universes.
  Derived localization universes `wR,wS` are independent too.
- Commutative ring sheaves: `R : Sheaf J CommRingCat.{r}` and
  `S : Sheaf K CommRingCat.{r}`.
- Morphism of ringed topoi and arbitrary structural ring map:
  `f : CategoryTheory.CochainPullback.RingedPullback R S` is the already published
  presentation. Its fields give `uInv`, `uPush`, their adjunction, finite limits
  of `uInv`, the algebraic inverse-image ring `RI`, the ring map `coefficient`,
  and the actual module pullback with object and map formulas. The ordinary
  module adjunction in this presentation is the canonical one furnished by
  `ringedPullbackPresentation_exists`; it is not a derived adjunction or a
  flatness assumption on the ring map. There is no bound on complexes.
- The canonical ordinary tensor comparison is `k : Comparison f` and its
  totalized map is `comparison f k P Q`. This is the recorded insertion-of-one
  comparison, not an arbitrary map or arbitrary natural isomorphism. Its inverse
  multiplies the two coefficient factors.
- Unbounded derived pullback: `L` and `epsilon` with
  `hL : L.IsLeftDerivedFunctor epsilon (HomologicalComplex.quasiIso ... (.up ℤ))`.
  This is the universal total left-derived functor of termwise pullback.
  It is the complex-localization version of the dependency's homotopy-localization
  universal property: the quotient is full and surjective on objects, and the
  underived cochain functor already factors through it. Thus natural transformations
  and the right Kan universal property on either presentation are equivalent.
  The statement explicitly concludes invertibility of `epsilon.app P` on every
  flat-term K-flat complex. Those maps are the computation maps e_P in the node.
- All module and derived categories are the recorded ones: `Modules R` is the
  abbreviation of `ringedSiteModules`; `DerivedCategory` is Mathlib localization.
  `derivedTensor R` and `representativeIso R ...` are the already published
  K-flat-derived tensor and resolving comparison, not new tensor choices.
- Canonical shifts on L: the existential `L.CommShift ℤ` together with
  `NatTrans.CommShift epsilon ℤ` pins the comparison to termwise shifts on
  complexes. Those shifts have identity components on module coefficients.
- Canonical tensor shifts: the two existential `CommShift₂Int` structures and
  `HasCanonicalTensorShifts` normalize both fixed-argument shift structures to
  the published representative comparisons. Its `cL,cR` are natural comparisons
  for tensoring by a flat-term K-flat fixed complex on all complexes, with
  `NatTrans.CommShift` and exact agreement with `representativeIso` on resolving
  second arguments. This is precisely the normalization in the fixed-tensor
  dependency. Its chain shifts are Mathlib's `map₂CochainComplex` shifts, unsigned
  in the first input and signed by (-1)^(np) in the second.
- Phi and Psi: the transparent abbreviations are respectively
  `Functor.uncurry.obj (derivedTensor R) ⋙ L` and
  `(L.prod L) ⋙ Functor.uncurry.obj (derivedTensor S)`.
- Existence and normalization of mu: `∃ mu : Phi L ≅ Psi L` and
  `IsNormalized f k L epsilon mu.hom`. For resolving P,Q, that predicate states
  `L(rR.hom) ≫ mu ≫ TS.map(e_P,e_Q) = e_V ≫ Q(c.hom) ≫ rS.hom`.
  This is exactly the node's formula, with `L(rR.inv)` and the two inverse
  computation maps moved across the equation. Their invertibility follows from
  the computation clause, the total-tensor model, and the representative isos.
  The predicate also records that the pulled-back representatives are K-flat
  with flat terms, as guaranteed by the tensor-pullback dependency.
- Uniqueness: `∀ tau : Phi L ⟶ Psi L, IsNormalized ... tau → tau = mu.hom`.
  This includes noninvertible candidate transformations; it is not merely
  uniqueness within natural isomorphisms.
- R[0],S[0]: `HomologicalComplex.tensorUnit (Modules R) (.up ℤ)` and its counterpart over S are
  the existing native cochain tensor units, i.e. the ring modules in degree zero.
  `ActionUnits.unit_kflat` and `.unit_flat` explicitly assert their resolving
  properties. These do not assume any flatness of the structural ring map.
- Canonical action unitors: the `rho` and `ell` fields of `ActionUnits` are natural
  isomorphisms on the entire derived categories. `rho_normalized` and
  `ell_normalized` state `r.hom ≫ rho = Q(ρ_P)` and `r.hom ≫ ell = Q(λ_P)` on
  every flat-term K-flat representative, using the ordinary cochain unitors.
  Thus their components are `r.inv ≫ Q(action)`, precisely the node's action
  formulas x tensor a ↦ ax and a tensor y ↦ ay. The theorem gives both aR and aS
  and `Subsingleton (ActionUnits ...)`, so the stipulated unitors are unique.
- Canonical pulled-back unit: the existential isomorphism u satisfies
  `u.hom = epsilon.app R[0] ≫ Q.map (unit f k).hom`. The imported `unit f k`
  is termwise pullback of the degree-zero ring followed by the normalized
  scalar multiplication isomorphism. The equation specifies u completely.
- First input shift square: the first universal `∀ (n : ℤ) (M N : D(R))`
  equation first applies mu at `(M[n],N)`, then tensoring the canonical L shift
  in its first input, then the target first-input tensor shift. The other side
  is L of the source first-input tensor shift, then the L shift on that tensor,
  then the shift of mu at `(M,N)`. This is `sPsi1 ∘ mu = mu[n] ∘ sPhi1`.
- Second input shift square: the next equation uses the corresponding
  fixed-first-argument tensor map and second-input shift. It is the other
  displayed equation of the node, for every integer n.
- Right action equation: the next universal equation is
  `mu(M,R[0]) ≫ TS(1,u) ≫ rho(LM) = L(rho(M))`.
- Left action equation: the last universal equation is
  `mu(R[0],N) ≫ TS(u,1) ≫ ell(LN) = L(ell(N))`.
- Zero/addition laws are fields of `CommShift` on L and of `CommShift₂Int` on
  each derived tensor; composition gives them for the displayed composite
  comparisons. Naturality for every localized map is encoded by the actual
  functors, natural transformation mu, natural action isos, and coherent shift
  classes on the full derived categories, not just on complex representatives.

Dependency declarations used (module, name):

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`,
  `SheafOfModules.ringedTopoiDerivedPullback` (the universal pullback/computation
  interface, expressed here on complexes as explained above).
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`,
  `SheafOfModules.KFlatFixedTensor.Modules`, `ordinaryTensor`, `totalTensor`,
  `derivedTensor`, `representativeIso`, `kFlat_fixed_tensor_triangulated`.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`,
  `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`, and the instance
  `CategoryTheory.Functor.instCommShift₂IntCochainComplexIntMap₂CochainComplex`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`:
  canonical comparison on resolving representatives. The theorem here uses
  the same representative square with the independently sized cochain comparison.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`,
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, with its public
  `RingedPullback`, `Comparison`, `pull`, `comparison`, and `unit` declarations
  from `CochainTensorCoherenceData`.
- Proof-only import: `Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
  `SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model`.

Edge cases checked before and during writing:

- The nonflat point example Z → Z/2 is admitted: f.coefficient is arbitrary;
  only resolution terms are flat, and no exactness of f.L is assumed.
- Identity morphisms are admitted. Twisting mu by -1 generally breaks its
  normalization and the action equations; the predicate excludes that twist.
- Integer n is unrestricted, including n=0 and negative n. In the second square
  the signed exponent uses the first factor degree, as 0FNH requires.
- Characteristic 2 is included: signed shifts simply identify -1 with 1.
- Zero modules, the zero ring and empty sites are not excluded; no Nonempty,
  nonzero coefficient, or nontriviality hypothesis is introduced.
- Both complexes may be unbounded in both directions. Totals are existing
  direct-sum totals, with all coproduct instances inherited from module sheaves.
- Site object and morphism universes and the two derived localization universes
  are independent. No extra equality was imposed to call a specialized API.

Searches for existing statements and constructions:

- msearch.py leanfinder: "Derived pullback tensor comparison canonical integer
  shifts and action unitors on ringed topoi". Eight ordinary pullback hits,
  including pullbackObjUnitToUnit, pullbackIso, pullbackComp and their ordinary
  unit/adjunction formulas; none states the normalized derived shift/unit result.
- msearch.py loogle: `"mapBifunctorShift"`. Eleven hits, including both canonical
  total-bifunctor shift maps, their summand/naturality formulas and mixed-sign
  relation; reused through the recorded fixed-tensor interface.
- msearch.py grep:
  `derived.*[Pp]ullback.*[Tt]ensor|[Tt]ensor.*[Pp]ullback.*[Ss]hift`.
  Zero Mathlib hits.
- msearch.py leansearch: "Derived pullback tensor comparison of ringed topoi
  preserves both signed integer shifts and tensor unitors". Eight ordinary
  sheaf/presheaf pullback hits, no normalized derived statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: canonical shift/unit and
  tensor/pullback patterns and the precise item id. No exact existing statement.
  Scheme-specific canonical tensor-shift/unit and localized module-comparison
  lemmas are special cases. `RingedProjectionFirstShift` depends on the downstream
  projection-mate theorem and is not used (no dependency cycle).
- rg for ActionUnits/actionUnitor/actionUnit/derived unitors found existing
  `RingedDerivedTensorLeftUnitorModel` and `RightUnitorModel`. They constrain a
  supplied closed monoidal structure and its own tensor-model comparison, and
  do not give these unitors on the recorded siteDerivedTensor functor. ActionUnits
  is only the bundle of the normalization clauses already in this item's statement.
- Checked `dag/lean_names_upstream.json`, and searched all three project namespaces
  for the proposed fully qualified names; no declaration collision found.

No STATEMENT-DISPUTED flag, statement correction, missing-definition node, or
unusable-dependency repair is required.

## Second reading by NQ

This is the assigned worker's second pass, not a claimed independent-agent review;
the dispatcher explicitly forbids starting agents and assigns independent review
to the maintainer. I reopened the node and the complete module and matched all
clauses above. In the draft first-input square I found that `T.flip.map` changed
the wrong input; it was corrected to `T.map`, followed by `T.flip.obj` for extracting
the first-input shift. I also checked the orientation of the representative square
against 07A4 and the direction of both native cochain unitors. The uniqueness
clause quantifies over natural transformations, not only isomorphisms. Both action
unitors are normalized and unique, and u is explicitly the localized degree-zero
pullback unit. No derived adjunction is assumed. Native `CochainComplex` types and
a single section-bound derived localization instance avoid expensive elaboration
through re-bound instances; this changes no mathematical hypothesis. The helper
records do not choose objects from unconstrained existence statements.

## Repair and validation on 2026-10-21

The required first dry run progressed beyond the earlier missing-published-artifact
failure and reached this module. The compiler found two actual draft defects:
cochain monoidal-instance inference exhausted its search budget, and implicit
universes on termwise pullback were inferred incorrectly. The repaired module
uses the existing `HomologicalComplex.tensorUnit`, `rightUnitor`, and `leftUnitor`
explicitly and the recorded `totalTensor` for the total, avoiding repeated searches
for the full cochain monoidal structure. All five universes of `RingedPullback`,
`Comparison`, `pull`, `comparison`, and `CategoryTheory.CochainPullback.unit`
are explicit. The full namespace also avoids resolving `unit` to the unrelated
parent-namespace declaration. K-flat predicates on expressions whose printed type
is `HomologicalComplex` are written with `CochainComplex.IsKFlatIndependentCoefficients`.
These are elaboration repairs of the same objects and maps, with no extra
hypothesis, statement correction, or dependency repair. Default heartbeat budgets
and the required 60-second per-file limit remain in force.

Second reading after repair: reopened the current node, the source construction
in Stacks 07A4, the sign convention 0FNH, and the repaired complete module. The
representative square still has exactly the prescribed orientation. The two
shift squares still change the corresponding tensor input, and both unit equations
use the normalized action unitors. The explicit tensor unit and unitors are the
constructors underlying the former monoidal notation, and the total is the same
existing bifunctor. The right and left equations include every derived object;
normalization and uniqueness include all natural transformations. The independent
site and localization universes remain unrestricted. Refreshed stale base audit
metadata so the node delivery changes only `lean`; its signature was extracted
verbatim from the repaired file.

The complete repaired module compiled against current server sources in 59.4 s.
That pass reported only a single 101-character line; the line was wrapped before
the final required dry run. The current dependency artifacts are available. The local wrapper still
occasionally exceeds 60 seconds and then performs its prescribed server
confirmation; the complete statement passes that server check within the same
60-second limit.

Final dry run: `deliver2.py NQ lem-weil-pbc-pullback-tensor-canonical-shift-unit
--no-push` printed `OK (dry run): commit 13af270511b passes the preflight and
compiles; nothing pushed`. The final self-check confirms the current base node
is unchanged outside `lean`, the recorded signature is verbatim, all lines have
at most 100 characters, no diagnostic commands remain, and the only `sorry` is
the named theorem's complete proof.
