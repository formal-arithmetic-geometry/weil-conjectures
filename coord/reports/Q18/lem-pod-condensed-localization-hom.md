## Worker report

Q18, item lem-pod-condensed-localization-hom, stage 2, 2026-10-21.
The delivery states the node in Sheaf.Paper.CondensedLocalizationHom. The main
statement is AlgebraicGeometry.ProEtale.CondensedLocalization.condensed_localization_hom.
The item JSON changes only `lean`. No mathematical statement correction, new DAG
node, or dependency-record repair is needed. All theorem proofs are `sorry`.
All definitions have real data; the only chosen ring homomorphism is uniquely
specified by the named theorem scalarRingMap_existsUnique.

Source read: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf,
Definition 3.3, Section 5.3, Lemma 5.3 and Proposition 5.5 and its proof.
Definition 3.3 supplies exactly the finite stratified dualizability condition.
The global Hom comparison in Proposition 5.5 specializes to the multiplicative
system of powers of t and passage to degree r. The module docstring and main
theorem docstring describe the construction and all eight node proof steps.

Hypotheses and clauses, in the order of the node:

1. Arbitrary commutative condensed ring: the explicitly bound variable
   `(Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]`. There is no topological
   presentation, discreteness, finiteness, or admissibility assumption on Λ.
2. Scalars R and t: `R Λ` abbreviates the existing `condensedScalarRing Λ.X`,
   namely evaluation at the terminal profinite space, and the theorem binds
   `(t : R Λ)`. `scalarSection` restricts this particular element from the point
   to every profinite object, with its compatibility proof supplied in full.
3. Localization: `localizedRing` is the existing sheafified sectionwise ring
   localization `ringedLocalizationRingOfUniverses` at that compatible section.
   `localizedRingMap` is its actual unit map. `localized` merely passes this
   existing commutative ring sheaf through the existing RingCat-to-Ab functor
   and packages its actual internal multiplication. Thus this is the ring
   localization whose underlying module is the t-telescope, not a freely chosen
   coefficient ring. `localizedComm` proves only pointwise commutativity.
   `coefficientLocalizationMap` is the actual localization map, and its named
   theorem postpones only the monoid-hom proof. `scalarRingMap` is uniquely
   determined by evaluation of this same map at the terminal profinite space.
4. B and B': `D Λ Y` and `D (localized Λ t) Y` use exactly
   `condensedRingObj Λ.X Y` and `condensedRingObj (localized Λ t).X Y`, the existing
   p_Y^* construction on the original small pro-etale site. Its object universe
   is u+1 and morphism universe u; neither is collapsed. Inverse image commutes
   with the localization telescope, so the second coefficient is also B[1/t].
5. Ordinary unbounded D and ordinary relative derived tensor: `D` is a transparent
   abbreviation for `DerivedCategory (Mod (Sheaf ... Ab.{u+1}) ...)` of the
   published upstream internal-module framework. This is the module-object
   presentation of the recorded ringed-site category, via the existing section
   module equivalence, not a different category or a copied module definition.
   Its tensor/unit/braiding are the published K-flat ordinary relative derived
   structures. No completed tensor product or post-derived balancing is used.
6. Finite stratification: `stratifiedDualizable Λ Y M` quantifies over the recorded
   `Scheme.FiniteLocallyClosedStratification Y`. That structure contains a finite
   disjoint covering partition, actual stratum schemes and immersions, and their
   locally closed images. The separate conjunct `∀ i, Topology.IsConstructible
   (s.stratum i)` imposes the node's constructibility requirement.
7. Duals and contractions: each restriction is the actual exact functor
   `(CondensedRing.upperStar Λ.X (s.immersion i)).mapDerivedCategory.obj M`.
   `Nonempty (HasRightDual ...)` supplies an object D and the exact pairing
   evaluation D tensor M → unit and coevaluation unit → M tensor D, with both
   triangle identities and the actual unitors/associators. These existential
   strata and duals are separately bound for each M, not shared by M and N.
8. qcqs: the Hom conclusion quantifies over `(Y : Scheme.{u}) [CompactSpace Y]
   [QuasiSeparatedSpace Y]`. No Noetherian, dimension, connectedness or component
   finiteness assumptions occur. Some canonical constructions are supplied for
   every scheme, so they do not impose additional hypotheses on Y.
9. E: `extension Λ (coefficientLocalizationMap Λ t) Y` is exactly the existing
   `Mod.extendScalars (coefficientMap ... Y)` left derived functor. Its ordinary
   construction is balanced scalar extension, derived by the published K-flat
   machinery. The theorem asserts the ordinary extension is exact (`exactness`);
   it does not assume this as a hypothesis. `extensionShiftIso` is explicitly
   constructed from the canonical LF ≅ DF comparison for this exact extension
   and the canonical termwise-derived shift comparison. No arbitrary shift
   structure or identification E(N[r]) = E(N)[r] is assumed.
10. Hom bijectivity, all degrees, formula: `IsHomComparison` quantifies over M,N
    satisfying `stratifiedDualizable` and every `r : ℤ`. It supplies an additive
    equivalence from `(M ⟶ N⟦r⟧) ⊗[R Λ] Localization.Away t` to the precise target
    Hom in the node. Its pure-tensor equation is
    `e (f ⊗ₜ a) = a • (E.map f ≫ (extensionShiftIso ... N r).hom)`.
    Taking a=t^(-n) is exactly f/t^n ↦ t^(-n)(1 tensor f). Additivity fixes the
    map on every tensor; hence these equivalences are the canonical maps,
    rather than arbitrary bijections between sets of the same cardinality.
11. Scalar actions: `IsScalarAction` fixes every asserted linear structure to
    the existing `stratifiedHomScalarMap Λ X`, acting on the source of a morphism.
    For localized coefficients it uses the map `k : R[1/t] →+* Γ(*,Λ[1/t])`.
    The equation `k.comp (algebraMap ...) = scalarRingMap Λ t` fixes the extension
    of the actual coefficient map; uniqueness is the ordinary localization
    universal property. The linear structures and exactness are existential
    conclusions, normalized by equalities, not extra assumptions on the item.
12. Naturality, identities, composition, raw fully faithful functor:
    `IsHomComparison` also supplies an actual additive functor from
    `ScalarLocalization (R Λ) (stratifiedDualizable Λ Y).FullSubcategory t`, with
    `F.Full` and `F.Faithful`. Its object equation is precisely E(M), and its
    pure-tensor equation fixes F(a tensor f)=a E(f), using HEq only to transport
    along the displayed object equality. Functor laws explicitly carry identity
    and composition; the prescribed formula implies naturality in both objects.
    The Hom-first displayed tensor and the scalar-first tensor in the recorded
    raw scalar localization are interchanged by the ordinary tensor symmetry.
    This raw category keeps the original objects. There is no Karoubi envelope,
    idempotent completion, density, or essential-surjectivity assertion.
13. Tensor/unit: `IsExtensionMonoidalNormalized` fixes the ordinary tensorator
    by its square with the actual `Mod.tensorObjπ` and `Mod.extendUnit`, and fixes
    its unit comparison by `Mod.extendπ` followed by ring multiplication. These
    are the balanced formulas (a tensor x) tensor (b tensor y) ↦ ab tensor
    (x tensor y), and a tensor b ↦ ab, with the chosen comparison written in
    the opposite, oplax direction. `IsDerivedComparisonNormalized` fixes its
    derived tensorator by the actual derived-tensor counit square on homotopy
    representatives. Every derived object has such a representative; for
    localization the exact extension comparison is invertible, so this fixes
    the canonical derived comparison. Monoidal coherence also determines the
    unit comparison from this tensorator. The asserted `Functor.Monoidal`
    structures make both comparisons isomorphisms and include associativity
    and unit coherence; `Nonempty (Functor.LaxBraided E)` adds symmetry
    coherence for the existing Koszul braiding. The full subcategory contains
    the unit and is closed under tensor, explicitly asserted in the theorem.
14. qcqs restriction: `restrictionIso` is constructed, rather than postulated,
    by conjugating the existing `CondensedRing.derivedPullIso` with canonical
    LF ≅ DF isomorphisms of exact inverse images. The theorem asserts its
    `NatTrans.IsMonoidal` for every g:Z→Y between qcqs schemes, with coherent
    monoidal structures on both coefficient inverse images. The last conjunct
    says restriction carries `stratifiedDualizable` objects to the corresponding
    subcategory on Z. The fixed scalar actions, the canonical coefficient-change
    isomorphism, and the fraction formula give the Hom restriction square.
    There is no finite-type, separated, or other condition on g.

Dependency declarations used (all read at their signatures and docstrings):

- Mathlib.Topology.Defs.Filter: `CompactSpace`.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: `QuasiSeparated` and
  `QuasiSeparatedSpace`, the latter the scheme's quasi-separated underlying space.
- Sheaf.Topology.ProfiniteCondensedRing: `Profinite.CondensedRing`.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: `coefficientRing`,
  `condensedRingObj`, `coefficientMap`, `upperStarFromPointComp`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`;
  Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence supplies the existing
  section-module presentation used by the published internal-module framework.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom:
  `CondensedRing.derivedHom`, the published derived monoidal category and its
  relative `CondensedRing.derivedTensor`.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  `Scheme.FiniteLocallyClosedStratification`.
- Mathlib.Topology.Constructible: `Topology.IsConstructible`.
- Mathlib.CategoryTheory.Monoidal.Category: `MonoidalCategory`;
  Mathlib.CategoryTheory.Monoidal.Rigid.Basic: `HasRightDual`, `ExactPairing`.
- Sheaf.CategoryTheory.ScalarLocalization: `ScalarLocalization` and its canonical
  category structure. This is the recorded raw localization, with unchanged objects.
- Sheaf.AlgebraicGeometry.CondensedScalarRealization: `condensedSectionRing`,
  `condensedScalarRing`; Sheaf.Paper.StratifiedDualizableHomContinuity:
  `stratifiedHomScalarMap` (reused as soon as this dependency landed).
- Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses:
  `ringedLocalizationRingOfUniverses`, `ringedLocalizationRingUnitOfUniverses`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients:
  `CondensedRing.derivedPullIso`; the published `Mod.extendScalars`,
  `Mod.extendUnit`, `Mod.extendπ`, and `Mod.tensorObjπ` define all balanced maps.
- WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal:
  `Functor.derivedTensorLeftDerivedCounit`,
  `Functor.leftDerivedDerivedTensorCounit`, and the ordinary-complex tensorator.

Every recorded proof-dependency module is imported (statement dependencies publicly,
remaining proof modules with plain imports). This includes the newly landed
Sheaf.Paper.StratifiedDualizableBounded and
Sheaf.Paper.StratifiedDualizableHomContinuity, as well as localization reflection,
the scalar telescope, filtered module localization, normalized derived adjunction,
ringed tensor coherence, canonical ringed-topos tensor pullback, pro-etale inverse
image and constructible inverse image. The main docstring cites all corresponding
DAG ids and explains their uses step by step.

Edge cases checked before and during statement writing:

- Y empty: the empty finite partition is allowed; no nonempty stratum is required.
- Λ=0 or t=0: localization is the actual zero ring; every localized Hom is zero.
- Nilpotent t: the same zero-ring case is included, with no nonzero denominator
  hypothesis or faithful-localization assumption.
- t a unit or t=1: the canonical maps reduce to scalar extension by an isomorphism.
- M or N zero: both Hom sides are zero and no nonzero dual is required.
- Negative, zero and positive r: the quantifier is ℤ, using the canonical shift iso.
- Non-Noetherian qcqs schemes, schemes with infinitely many irreducible components,
  and arbitrary coefficients: no condition excluding them appears.
- M and N may have distinct finite partitions and distinct dual choices.
- General morphisms of qcqs schemes: restriction uses their actual base change,
  not containment of images or a guessed immersion.
- Universes: profinite objects u+1, small pro-etale objects u+1 and Hom u,
  coefficients/homs u+1, derived objects u+2. No extra universe equality is imposed.

Searches for an exact existing declaration:

- msearch.py leanfinder, query: "For a qcqs scheme and stratified dualizable
  condensed sheaves, derived Hom commutes with localization of a scalar".
  Eight results concerned light condensed internal Hom or related constructions;
  none was this stratified qcqs Hom-localization assertion.
- msearch.py loogle, query: "DerivedCategory, IsLocalization". Zero results.
- msearch.py grep, query: "condens.*localiz|localiz.*condens|[Hh]om.*[Ll]ocaliz".
  Twenty-five results included generic module localization and condensed monoidal
  infrastructure, but no theorem with this statement.
- msearch.py leansearch, query: "Constructible condensed sheaves on a qcqs scheme
  have derived Hom commuting with scalar localization". Eight results included
  condensed definitions and underived/discrete fully faithful comparisons;
  none was the item.
- rg searches of lean/WeilConjectures and lean/Sheaf for condensed/localization,
  scalar localization, and Hom localization; grep of WeilConjectures for the
  exact node id. No declaration of the item exists. Generic
  internalHomLocalizationComparison has different continuity/boundedness inputs.
- tools/blueprint_refs.py search 'stratified dualizable': no separate matched unit.
  The existing localization, stratification, scalar realization, duality and raw
  localization notions were reused; no duplicate independent notion was added.
- Re-read the newly available boundedness and Hom-continuity modules; replaced
  the draft scalar-unit realization normalization by their actual canonical
  scalar center map. This avoids a second definition of the scalar action.

Validation: scompile.py compiled the full module cleanly, including its named
library path, with only the expected postponed proofs. After final naming/record
updates, the delivery dry run recompiles this exact final file and runs the
maintainer preflight. Definitions do not conceal arbitrary objects behind existence
proofs. No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q18

This is the dispatcher's single-worker delivery. No second agent was started,
as expressly required by the brief; the maintainer performs the independent
review. The following is my own second reading with the JSON and final Lean open.

The unchanged node permits every commutative condensed ring and every qcqs scheme.
The final context has exactly those assumptions. The stratification definition
uses the recorded immersed finite partition and adds constructibility explicitly;
it uses HasRightDual with both contractions. The Hom domain and target match in
all integer degrees, and the source tensor is Hom-first as displayed in the node.
The raw functor is full and faithful with the exact fraction normalization; there
is no completion or essential-surjectivity clause. Canonical ordinary balanced
maps and the derived representative square fix the tensor comparison, while the
monoidal and braided assertions carry all coherence. Restriction uses the actual
published coefficient-change isomorphism and preserves the subcategory.

Issues found and corrected during this reread: (1) the left-derived functor has
no directly inferred CommShift instance in this API, so the canonical shift iso
is now explicitly constructed by transport from exact termwise extension;
(2) the Hom-continuity module landed during work and supplies the canonical
central action, so the draft independent realization-based normalization was
removed in favor of that declaration; (3) the raw localization uses scalar-first
Hom tensors and full-subcategory morphisms wrap their underlying arrows, so the
formula uses that ordering and `.hom`; (4) tensor closure and containment of the
unit are explicit, ensuring that the asserted tensor comparison really restricts
to the full subcategory. All these adjustments leave the node statement unchanged.
