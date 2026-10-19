## Worker report

The retained packet was inspected first and its required initial `deliver2.py --no-push`
passed (dry-run commit `3c41956f95`). Mathematical self-check against the return at
`4946fc328067` nevertheless confirmed its H3 defects; the packet has been repaired,
not re-pushed unchanged. The current repository node and the sandbox node agree outside
`lean`. The delivery wrapper rebases the packet on current `newtargets-dag`.

`Sheaf.TraceFormula.DerivedCechDiagramFunctorialModules` states
`AlgebraicGeometry.Etale.compatible_roof_of_augmented_cosimplicial_module_complexes`.
Its only postponed proof is that named theorem, with the node's six-step proof in its
docstring. Every helper has real data (or a fully specified Prop), a source place and
the owning blueprint id; all helpers are recorded in `lean.declarations`.

The node statement is unchanged. Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node text | Lean rendering |
| --- | --- |
| Commutative ring Λ; schemes Y and Y'; arbitrary h and integer a | `(Λ : Type (u + 1)) [CommRing Λ]`, `(Y Y' : Scheme.{u})`, `(h : Y' ⟶ Y)`, `(a : ℤ)` |
| Constant-Λ module sheaves on the small étale sites | `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and its Y' version, the established constant-module encoding |
| Augmented cosimplicial complexes, with chain-map augmentation, cofaces and codegeneracies | `A` and `B : CosimplicialObject.Augmented (CochainComplex.Plus ...)`; the inclusion `Plus.ι` gives the underlying integer cochain complexes |
| Every input complex is zero below a | `hA` and `hB`, for every `Option SimplexCategory` index; `none` is the augmentation and `some q` is degree q |
| b is a morphism after exact module inverse image | `b : (pulledCechDiagram Λ h).obj A ⟶ B`, where this functor is augmented whiskering by `(upperStar (ModuleCat Λ) h).mapCochainComplexPlus` |
| Choose bounded functorial injective resolutions | `I` and `I'` are functors `Plus C ⥤ Plus C`; `η : Plus.ι _ ⟶ I ⋙ Plus.ι _` and `η'` have exactly the dependency theorem's interface |
| Resolution quasi-isomorphisms, injective terms, simultaneous preservation of every lower bound | `hηq`, `hη'q`, `hI`, `hI'`, `hIbound`, `hI'bound`; every complex argument belongs to `Plus`, and bounds range over all integers |
| Existence hypotheses for these choices | The Grothendieck, functorial-embedding and bounded-resolution dependency modules are imported as the proof plan; there is no new existence assumption on all unbounded complexes |
| Four displayed vertices, and three actual arrows with precisely the displayed directions | `CompatibleRoof`: `u : Γ I A ⟶ Γ I' h⁻¹ I A`, `v : Γ I' h⁻¹ A ⟶ Γ I' h⁻¹ I A`, `w : Γ I' h⁻¹ A ⟶ Γ I' B`; `resolvedCechDiagram` expands these exact functor compositions |
| u is section restriction followed by η' | `CanonicalRoofU`, in both branches: every internal component is `globalSectionsUpperStarMap ... ≫ Γ.map (η'.app ...).f i` |
| v is Γ I'(h⁻¹η) | `CanonicalRoofV`, in both branches: sections of `I'.map` of the pullback of the actual full-subcategory lift of `η.app` |
| w is Γ I'(b), including augmentation | Equality of entire augmented morphisms `R.w = (resolvedCechDiagram Λ Y' I').map b`; its left and right components are both fixed |
| Every arrow commutes with all cofaces, codegeneracies and augmentation | All three fields of `CompatibleRoof` are morphisms in `CosimplicialObject.Augmented (CochainComplex (ModuleCat Λ) ℤ)` |
| All four displayed column families have internal degrees at least a | `CompatibleRoofColumnsGE ... a` quantifies over the four vertices and every ordinary or augmentation column |
| Each column of v is a quasi-isomorphism, including augmentation | `∀ q : Option SimplexCategory, QuasiIso (augmentedCechColumnMap R.v q)` |
| The roof represents res_h followed by RΓ(b_q), for every q ≥ -1 | `CompatibleRoofDerivedIdentification`: inverse r of `Q(v_q)`, normalized identifications eA and eB, and the equality `Q(u_q) ≫ r ≫ Q(w_q) ≫ eB.hom = eA.hom ≫ res_h ≫ RΓ(b_q)` in both branches |
| Identifications are those of the existing RΓ, not arbitrary ones | eA and eB satisfy `eA.hom ≫ RΓ(Qη) = resolvedCechSectionsToDerived ...` and its B analogue. This helper is the existing derived-functor unit with the existing quotient comparison isomorphisms. Since Qη is invertible, these equations fix the identifications uniquely |
| Canonical res_h has the unit recipe of node proof step 6 | The right side uses `RΓ.map ((mapDerivedUpperStarLowerStarAdjunction ...).unit.app ...)` followed by `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso.hom.app`; `mapDerivedCategoryFactors.hom.app` then identifies the target with the termwise pulled-back representative before `Q.map b_q.hom` |
| Actual alternating-coface double-complex maps and differential δ + (-1)^q d | `CompatibleRoof.alternatingMaps` constructs all three maps using Mathlib's `alternatingCofaceMapComplex` in the category of internal complexes. These are cochain complexes in cochain complexes, with coface differential δ and internal differential d; their two chain-map equations preserve the signed total differential. The original augmented morphisms retain the augmentation maps alongside these nonnegative horizontal complexes |
| One compatible roof of diagrams | A single existential `R : CompatibleRoof ...` satisfies all predicates; no separate choice of u, v or w for individual columns is allowed |

The module uses the canonical `HasDerivedCategory` instances already used by the existing
`rightDerivedGlobalSections`, rather than imposing an independently chosen localization
instance. This avoids a mismatch of localized categories and adds no hypothesis. The
old monomorphism and zero-morphism-preservation assumptions on the resolution functors
were removed: the recorded bounded-resolution theorem supplies natural quasi-isomorphisms
on `Plus`, injective terms and bound preservation, and those suffice for every clause.

Dependency declarations read and used (directly in the statement or as its proof imports):

- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  this is Mathlib's general ringed-site category, and constant coefficients here use the
  project's existing `Sheaf ... (ModuleCat Λ)` presentation, not a new category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`. The current node's upstream binding
  is used; the retired Sheaf duplicate is not imported. Its current complete source was
  read with `scompile.py --source` because it is newer than the old source checkout.
- `Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution`:
  `CochainComplex.exists_functorial_bounded_injective_resolution`, read in full. Its
  quantified I and α are on `Plus`, with exactly the three properties assumed here.
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`:
  `AlgebraicGeometry.Scheme.etaleModuleSheaves_grothendieckAbelian`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`:
  `CategoryTheory.IsGrothendieckAbelian.instHasFunctorialFactorizationMonomorphismsRlp`,
  the Mathlib match for the functorial-injective-embedding dependency. Its factorization
  of `X ⟶ 0` supplies the object functor and the monic injective embedding.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`:
  `CochainComplex.etale_kinjective_resolutions_exist`, especially its bounded-below clause.
- `Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined`:
  `AlgebraicGeometry.Etale.rgamma_unbounded_well_defined`, with its representative and
  comparison equations, not merely abstract existence of an isomorphism.

Additional existing APIs used: `Functor.mapCochainComplexPlus`, `ObjectProperty.homMk`,
`globalSectionsUpperStarMap`, `Functor.rightDerivedFunctorUnit`,
`DerivedCategory.quotientCompQhIso`, `Functor.mapHomotopyCategoryFactors`,
`mapDerivedUpperStarLowerStarAdjunction`,
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`,
`Functor.mapDerivedCategoryFactors`, and `AlgebraicTopology.alternatingCofaceMapComplex`.
The derived restriction formula is written using these canonical maps in the predicate;
no independent restriction-map definition, arbitrary comparison, or existence choice was
introduced. The identically purposed helper in the downstream finite-cover theorem was
read but is not imported, avoiding a dependency cycle.

Source reading: `literature/stacks-project/derived.tex`, the full proof of
`lemma-functorial-injective-resolutions` and `remark-match` at Tag 0141, agrees with
`Comp⁺`, not all complexes. The node's six proof steps supply the exact inverse-image,
section restriction, and derived comparison recipe; the Lean docstring now reproduces
these steps with their dependency ids.

Edge cases checked mathematically against the formulas:

- `h = id`: restriction is the adjunction-unit restriction, and v inverse followed by u
  identifies the two resolution models by naturality. No invertibility of pullback
  restriction for arbitrary h is asserted.
- `b = id` when its endpoints agree: w is the image of the identity as an entire augmented
  morphism. In particular its augmentation cannot be changed independently.
- Zero A and B and the zero ring are allowed. There is no nontriviality or nonemptiness
  assumption; the functors' lower-bound property applies to zero complexes too.
- Empty Y or Y' is allowed. No point or stalk is chosen in the statement.
- Negative a, a = 0, ordinary degree zero, all higher degrees, and augmentation q = -1
  are covered. The `none` branch explicitly has both inverse equations and the full
  derived equality; it cannot accidentally be omitted by a natural-number quantifier.
- Different bounded-below complexes can have different bounds under I; the same I works
  for all integers, while this diagram's hA and hB specify the common bound a. No resolution
  of a genuinely unbounded complex is assumed.
- No additivity or preservation of zero morphisms is imposed on I or I'. Actual functors
  and natural units suffice to preserve cosimplicial identities. Exact pullback and
  sections use their existing additive functors.

Searches retained from the previous packet include LeanFinder and LeanSearch for functorial
resolved Čech diagrams, Loogle for `"rightDerived"`, and Mathlib grep for
`rightDerived.*[Ss]ection|[Ss]ection.*rightDerived|[Cc]ech.*[Ii]njective`, with no exact match.
The old invalid unquoted `CechNerve` query was explicitly not treated as evidence.
New repair searches, all through the prescribed wrapper or named source directories:

- `msearch.py leanfinder`: “Compatible common resolution roof of augmented cosimplicial
  bounded below module sheaf complexes under exact inverse image, normalized as derived
  restriction”: eight generic LeftResolution/Mayer–Vietoris/object-derived-functor hits;
  none is the node's statement.
- `msearch.py leansearch`: “Functorial bounded below injective resolution of augmented
  cosimplicial complexes and maps of diagrams”: eight objectwise injective-resolution
  hits, not the augmented common roof.
- `msearch.py loogle '"mapCochainComplexPlus"'`: twelve hits, including exactly
  `Functor.mapCochainComplexPlus` and its inclusion comparison; those APIs are used.
- `msearch.py grep 'mapDerivedCategoryFactors|rightDerivedFunctorObjQIso' CategoryTheory`:
  zero hits (not evidence of absence outside that subdirectory); direct Mathlib and
  upstream `rg` found and supplied the exact-functor and K-injective APIs.
- `rg` in `WeilConjectures` and `lean/Sheaf` for `CompatibleRoof`, `compatible_roof`, and
  `resolvedCechSectionsToDerived`, and for the node id: no exact pre-existing theorem.
  Separate searches for `rightDerivedGlobalSections` and `globalSectionsUpperStarMap`
  found the canonical derived unit/Leray recipe in the finite-cover consumer and the
  upstream generic constructions used here.

No new DAG node or dependency module is required: these helpers belong to the owning
node's roof and comparison, as authorized by brief-stage2 §1. No statement correction
or `STATEMENT-DISPUTED` flag is needed.

## Repair of returned delivery 4946fc328067

H3 (resolution domain): replaced all-complex endofunctors by `Plus C ⥤ Plus C`; units
now have the exact inclusion-to-resolved-inclusion type of the dependency. Removed the
extra monomorphism and zero-preservation assumptions, which that dependency does not give.
The augmented inputs are Plus-valued and their hA/hB bounds include the augmentation.

H3 (augmentation of w): replaced the old ordinary-column equalities by equality of
whole augmented morphisms. The augmentation is now exactly sections of I'(b.left).

H3 (derived roof): replaced a bare existential inverse in ordinary columns by the
unit-normalized eA/eB comparison, both inverse equations for v, and the equation to the
existing derived-unit/Leray restriction followed by RΓ(b), in both ordinary and
augmentation branches. Added the explicitly missing four-vertex bound clause, and the
actual alternating-coface map construction.

H8: every helper now has its source and owning blueprint marker, all helper names are
listed in lean.declarations, and the theorem docstring gives all six proof steps.

H11: the second reading below checks the final node and Lean clause by clause, including
the previously missed augmentation and derived-map normalization. The report's obsolete
claim that a bare inverse was the derived identification has been removed.

## Second reading by NR

I reopened the unchanged node statement, the final theorem signature, every predicate
it uses, and the canonical comparison's body after the successful file compile.

1. Coefficients and geometry: Λ is commutative, Y/Y' and h are arbitrary, and a is an
   arbitrary integer. The two coefficient categories are the established constant-Λ
   étale module-sheaf categories. No field, finiteness, constructibility, or nontriviality
   assumption was introduced.
2. Diagrams: A and B are full augmented cosimplicial objects in Plus. Thus all input
   cofaces, codegeneracies, and augmentation maps are chain maps. hA/hB cover `none`
   as well as `some q`. This is equivalent to the node's uniform bound on its input
   complexes and uses the same category as the resolution dependency.
3. Resolutions: I/I' and η/η' now exactly match that dependency's functor and unit
   types. Its three clauses are precisely hηq/hη'q, hI/hI', and hIbound/hI'bound.
   The initial packet's all-complex, monomorphism, and zero-preservation assumptions
   were mismatches and were repaired.
4. Given morphism: pulledCechDiagram is exact inverse image on the underlying complexes,
   lifted by the existing Plus functor; b is a morphism of the whole augmented diagram.
5. Roof: I checked each of u's, v's and w's endpoints against the four displayed
   vertices. The middle target is I'(h⁻¹I(A)), whereas v and w start at I'(h⁻¹A).
   No arbitrary intermediate complex is quantified.
6. Canonical components: CanonicalRoofU gives section restriction followed by η';
   CanonicalRoofV gives ΓI'(h⁻¹η). Both match branches cover every internal degree
   including the augmentation. Whole-morphism equality fixes w = ΓI'(b); the old
   unconstrained left component was repaired.
7. Compatibility: u/v/w are themselves augmented morphisms, so the coface, codegeneracy
   and augmentation compatibilities use the same arrows in every column.
8. Bounds: CompatibleRoofColumnsGE explicitly covers each of the four vertices and
   both kinds of column. This conclusion was absent in the old Lean signature.
9. Quasi-isomorphism: the universal Option-indexed QuasiIso clause includes the
   augmentation, not only the nonnegative degrees.
10. Derived equality: for each branch I checked the source and target of r, both inverse
    equations, and the eA/eB normalization equations against the unit comparison. The
    final composite has the node's composition order u, inverse v, w, then eB; its
    right side is eA followed by derived restriction and RΓ of b. The comparison
    from exact derived inverse image to the pulled-back representative has the correct
    hom direction. The augmentation carries the identical formula. These clauses
    repair the missing derived identification rather than declaring an arbitrary iso.
11. Double complexes: alternatingMaps applies the existing alternating coface functor
    to the actual right components. Its outputs are maps of cochain complexes in
    cochain complexes; their internal chain equations and their horizontal chain
    equations preserve δ + (-1)^q d. Original left components and augmented naturality
    retain the augmentation; no independent column maps are substituted.
12. Documentation and records: every helper is a real construction or an explicit Prop,
    carries source/blueprint documentation, and is recorded. The only sorry is the
    main theorem with the six-step proof plan. The node's lean.statement is copied
    verbatim from the final explicit theorem signature; all non-lean node fields agree
    with the current repository. No other node was edited.

Verification: the prescribed `scompile.py` compiled both the sandbox and library versions
cleanly after the repairs (10.1 s and 9.7 s respectively, with no diagnostics). The final
mechanical dry run and delivery below also compile the delivered file separately within
the required limit. No library or global build was run.
