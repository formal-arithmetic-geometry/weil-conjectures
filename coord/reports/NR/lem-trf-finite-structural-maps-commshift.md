# NR: lem-trf-finite-structural-maps-commshift

## Worker report

The retained module `Sheaf.Paper.FiniteStructuralMapsCommShift` states
`WeilConjectures.finiteStructuralMaps_commShift`, with one `sorry` and real definitions
for the named canonical maps and shifts. The node's mathematical statement is unchanged.
The saved packet lacked this report; this continuation supplied it and checked the source
interfaces against the current published library. Server scompile compiled both the sandbox
and library module cleanly (7.1 seconds each).

Hypothesis correspondence:

- `D : FiniteFieldDatum` supplies the finite base field and its fixed algebraic closure.
  `[CharP D.k D.p]` spells out the stated characteristic, and `hl : l ≠ D.p` is the
  invertibility convention. The section binds `l`, `[Fact l.Prime]`, `E : Type u`,
  `[Field E]`, `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]` explicitly.
- `n : ℕ` indexes the positive level `n+1`. `structuralCoefficient` abbreviates precisely
  `ULift (finiteCoefficientRing l E (n+1))`; no level zero is included, and every positive
  level occurs. The ring is the recorded quotient by the chosen uniformizer power.
- `X Y Z : Scheme.{u}` with the three `Over (Spec (.of D.k))` instances are the geometric
  schemes. `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on their structure maps
  express separated finite type. The morphisms `f`, `g`, their `IsOver` instances, and the
  same three morphism properties express the two separated finite-type k-morphisms.
- `HasCompactification` on `f`, `g`, and `f ≫ g` selects the compactifications used by the
  published operations; compactifiability follows from the stated geometry. These are
  construction witnesses, with the comparisons retaining their recorded normalization.
- Ambient objects are `DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat ...))`, the
  canonical fixed-scalar presentation of constant-ring module sheaves. The coefficient
  universe is `u+1`, while schemes have universe `u`; no site universes are equated.

Clause correspondence:

1. The first conjunct quantifies over `[IsProper f]` and `M` satisfying
   `ProEtale.DerivedCategory.boundedConstructible ... Y M`. `structuralUnit` is literally
   the unit of `derivedUpperStarLowerStarAdjunction`. Its displayed equation is
   `eta(M[1]) ≫ chi(Rf_*Lf^*) = shift.map (eta(M))`; the identity comparison is identity.
2. The second conjunct is on bounded constructibles of X, with proper f.
   `structuralProperComparison` is `trfOriginCompactificationComparison` from the selected
   compactification to `Compactification.ofIsProper f`, followed by
   `structuralProperIdentity`, the identity-open adjunction identification. Its two
   equations give the square for `.hom` and `.inv`, using `structuralDirectShift` and
   `structuralSupportShift`. The inputs `⟨M, hM.plusEtaleOrigin⟩` and
   `⟨M[1], (hM.shift 1).plusEtaleOrigin⟩` retain the required origin domain.
3. The third conjunct uses exactly `ProEtale.originCompositionAmbient`, the ambient
   realization of the recorded `originComposition`, on the same bounded constructible
   origin objects. The first equation is for the compositor and the second for its
   inverse. `structuralCompositionShift` is the composite canonical shift on Rg_! Rf_!;
   the other comparison is `structuralSupportShift` for `f ≫ g`.
4. The last conjunct quantifies over `constructibleFiniteTor ... Y M`.
   `structuralCounit` is the normalized composite: compact-support site comparison in
   its pro-etale-to-etale orientation, followed by nu^* of the etale counit, followed by
   the derived comparison counit. `trfExceptional` is literally nu_X^* f^times Rnu_Y,*.
   `structuralExceptionalCommShift` equips the etale right adjoint with
   `rightDerivedUpperShriekAdjunction.rightAdjointCommShift`; the remaining factors use
   their canonical derived shifts. `structuralCounitShift` is the resulting composite
   comparison for Rf_! Rf^!. The equation is epsilon(M[1]) = chi ≫ epsilon(M)[1].
   Thus the exceptional shift is specified before the equation, not chosen from it.

All equations use Lean's left-to-right composition `≫`, which is the node's displayed
right-to-left composition. The shift is always `(1 : ℤ)`. Both inverse equations are
included. All helper declarations have source and blueprint docstrings; the theorem
contains the node's full thirteen-step natural-language proof plan.

Dependency interfaces read and used (including canonical presentations exposed by their imports):

- `def-trf-coefficient-conventions`: `Sheaf.Paper.TraceFormulaCoefficientConventions`, `WeilConjectures.TraceFormulaCoefficientConventions`.
- `def-fix-six-functor-datum`: `Sheaf.Paper.SixFunctorOperationDatum`, `WeilConjectures.SixFunctorOperationDatum`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `thm-sf-comp-composition`: `Sheaf.Paper.CanonicalOriginCompactSupportComposition`, `AlgebraicGeometry.ProEtale.originComposition`.
- `def-weil-triangulated-category`: recorded Mathlib match `{"declaration": "CategoryTheory.Pretriangulated", "file": "Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean", "how": "exact: a pre-triangulated category is `[Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n, (shiftFunctor C n).Additive] [Pretriangulated C]` (Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:43 and :65; TR1 = isomorphic_distinguished, contractible_distinguished, distinguished_cocone_triangle; TR2 = rotate_distinguished_triangle, an iff; TR3 = complete_distinguished_triangle_morphism; binary biproducts, hence additivity, are an instance at :562); a triangulated category adds `[IsTriangulated C]` (Mathlib/CategoryTheory/Triangulated/Triangulated.lean:305, TR4); an exact functor is `[F.CommShift ℤ] [F.IsTriangulated]` (Mathlib/CategoryTheory/Triangulated/Functor.lean:186; additive by the instance at :237). The shift [1] is an autoequivalence (HasShift by ℤ) rather than a strict automorphism, the usual reading. [HasZeroObject C] added to this 'how' at the re-check of 2026-10-09"}`.
- `def-sf-etale-origin-subcategory`: `Sheaf.Paper.EtaleOriginDerivedCategory`, `AlgebraicGeometry.ProEtale.EtaleOriginDerivedCategory`.
- `def-weil-scheme-morphism-properties`: `None`, `None`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-trf-admissibility`: `Sheaf.Paper.TraceExceptionalAdmissibility`, `WeilConjectures.IsExceptionallyAdmissible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.

In particular, `TraceExceptionalAdmissibility` exposes `trfExceptional` and
`trfOriginCompactificationComparison`; `CanonicalOriginCompactSupportComposition`
exposes `originCompositionAmbient`; `FixedFiniteExceptionalAt.sfFiniteExceptionalAt`
is included in the exceptional-inverse-image node's current recorded declarations.
The intrinsic compact-support and constructibility definitions retain their canonical
fixed-module realizations, as their recorded interface notes explain. No new notion or
replacement operation is introduced here.

Edge cases checked by reading the definitions: the smallest finite level is n=0 in this
indexing, hence A_{E,1}; l=p is excluded; there is no nonemptiness or positive-dimension
hypothesis on any scheme, so empty schemes and zero complexes are included. Identity and
proper maps use the identity-open compactification. The compositor is never applied to an
arbitrary ambient pro-etale complex; its object carries the origin property, and its
shifted object is obtained by `hM.shift 1`. The exceptional counit is restricted to the
finite-Tor domain. No arbitrary map or bare Nonempty natural isomorphism replaces a
canonical comparison.

Searches retained from `searches.jsonl`:

- msearch LeanFinder: "canonical derived adjunction unit counit compact support composition
  natural transformation commutes with shifts". Eight generic derived-adjunction hits,
  including `Adjunction.CommShift.CompatibilityUnit` and `CompatibilityCounit`; none states
  this four-clause finite-coefficient assertion.
- msearch Loogle: `CategoryTheory.NatTrans.CommShift,
  CategoryTheory.Adjunction.rightAdjointCommShift`. No hits.
- msearch grep: `CommShift|compatibilityCounit`, Mathlib `CategoryTheory/Shift`.
  Generic shift/adjunction infrastructure, no matching geometric theorem.
- msearch LeanSearch: "canonical finite coefficient compact support proper comparison
  composition and exceptional adjunction commute with shifts". Generic adjunction shifts,
  `CommShift.commShift_counit`, and right-adjoint comparison formulas; no exact match.
- Current rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and proposed main/helper declaration names: no existing match.
  Current rg for boundedConstructible, constructibleFiniteTor, plusEtaleOrigin and CommShift
  located the existing finite-coefficient constructibility and shift interfaces used here.

No STATEMENT-DISPUTED claim, statement correction, new node, or dependency-node replacement.

## Self-check by NR

This is a self-check of the retained packet; no second agent was started, as the dispatcher
forbids that. I reread the four conjuncts against the node. Properness is scoped to clauses
(1) and (2); (3) contains both directions on the origin domain; (4) retains the specified
composite shift of the exceptional formula. The positive-level reindexing and the canonical
fixed-module presentation are explicit above. No mathematical statement change was made.
The maintainer's independent review remains the independent reading of this delivery.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
