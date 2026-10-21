## Worker report

The delivery states lem-sfb-ring-localization-sheafification in
Sheaf.CategoryTheory.RingLocalizationSheafification. No mathematical statement,
source, proof plan, or dependency list is changed. All theorem proofs are `sorry`.
All definitions have actual data; in particular the localization is Mathlib's
Localization.Away and the unit is a specified composite, not a chosen map.

Source read: literature/stacks-project/sites-modules.tex, lemma-simple-invert
(Tag 0EMC), including its surrounding sectionwise localization construction.
The lemma states the ring-sheafification universal property; its proof is omitted.
The node's six-step proof supplies the internal-ring reformulation and unique
comparison, and is carried in the main theorem's docstring. Ordinary localization
uses Tags 00CO and 00CP, as in the dependency records.

Hypothesis and clause correspondence:

- A small site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
  The Grothendieck topology is the associated topology of the site convention in
  def-weil-pbc-sites-and-cohomology; the theorem works for every such topology.
  No terminal object, pullback instance, points, or enough points is required.
- The value universe is `max u v w`, with u, v, w independent. Thus it contains
  both objects and arrows, without equating their universes or requiring a
  successor universe. `sfbLocalization_hasSheafify` and
  `sfbLocalization_monoidalLocalEquivalences` supply the two structural prerequisites
  from this size condition; they are named Prop-valued statements in this same
  node's interface, with proof docstrings. There is no extra sheafification or
  tensor-exactness hypothesis on the main theorem.
- Abelian sheaves use AddCommGrpCat's existing tensor over the integers, imported
  from WeilConjectures.CategoryTheory.RingObjects.Ab through the dependency
  modules. The existing Sheaf.monoidalCategory and Sheaf.braidedCategory are
  registered as exported instances. These are the localized tensor packaged by
  sfbSheafTensorStructure, not a cartesian tensor or a fresh monoidal structure.
- An arbitrary commutative internal ring is
  `R : CommMon (Sheaf J AddCommGrpCat.{max u v w})`. This stores MonObj and
  IsCommMonObj on R.X and uses internal ring morphisms throughout.
- A global section is `t : (sectionRings J R.X ⋙ forget CommRingCat).sections`.
  Its value at U is t.val U; t.property is its restriction compatibility. The
  actual section rings come from the recorded reconstruction, with multiplication
  induced by the internal tensor product and unit evaluated at 1.
- `sfbLocalizationPresheaf A t` has value
  `CommRingCat.of (Localization.Away (t.val U))` at U, with its ring type explicitly
  fixed to A.obj U. Its restrictions are IsLocalization.map on A.map f, using
  t.property to map the powers submonoids. The functor laws are assembled from
  existing localization equalities. This is a real presheaf, not existential data.
- `sfbLocalizationFraction t r n` is Localization.mk with denominator t^n.
  `sfbLocalizationPresheaf_spec` gives surjectivity of these fractions, the exact
  existential power-torsion equality relation, the stated addition and
  multiplication formulas, and the exact restriction formula, in that order.
  The numerator expressions use explicit `@id (A.obj U)` casts to retain the
  actual section-ring operations. Naturals encode every n,m,k ≥ 0.
- `sfbLocalizationPresheafUnit` is the sectionwise algebra map r ↦ r/1.
  `sfbLocalizationRingObject J R t` applies the existing strong symmetric monoidal
  sheafification mapCommMon to the actual localized presheaf ring. It uses the
  existing ring-presheaf MonObj/IsCommMonObj constructions and therefore specifies
  its internal multiplication and unit.
- The final conjunct of sfbRingLocalizationSheafification says that arbitrary
  presheaf ring maps P → sectionRings(D) extend uniquely to internal ring maps
  aP → D, with equality on every element under the actual toSheafify unit.
  By the recorded section-ring reconstruction this is precisely ring
  sheafification. Hence using abelian sheafification with its induced internal
  ring structure renders the ring sheafification in the node, with its canonical
  normalization, rather than an unrelated ring sheaf with a similar name.
- `sfbLocalizationUnderlyingUnit` is the inverse sheafification counit on R.X,
  followed by sheafification of r ↦ r/1. The named theorem
  sfbLocalizationUnderlyingUnit_isMonHom postpones only its compatibility proof.
  `sfbLocalizationUnit` bundles this very same map as a CommMon morphism.
  The first conjunct of the main theorem gives its exact sectionwise r/1 formula.
- The second conjunct states that the image of t is a unit in every section ring.
  This is equivalent to invertibility of the global section: sectionwise inverse
  elements restrict compatibly because a two-sided inverse is unique. It neither
  assumes enough points nor merely tests stalks.
- The third conjunct quantifies over every internal commutative ring D and
  morphism f:R→D, assumes exactly invertibility of f(t), and gives
  `∃! g : aP ⟶ D, sfbLocalizationUnit ... ≫ g = f`.
- The fourth conjunct quantifies over every L and j:R→L, requires j(t) invertible
  and exactly the same unique-factorization property for all D,f, and gives
  `∃! γ : aP ≅ L, sfbLocalizationUnit ... ≫ γ.hom = j`.
  Thus existence, uniqueness, the ring-object category, and the normalization of
  the comparison are all retained.
- No regularity or nonzero-divisor hypothesis on t, and no Nontrivial instance,
  is present anywhere.

Dependency declarations read and used:

- Sheaf.CategoryTheory.SheafTensor: sfbSheafTensor_properties and its imported
  sfbSheafTensorStructure; this identifies the sheafified tensor and strong
  symmetric monoidal sheafification. Its general site and value universes were read.
- WeilConjectures.CategoryTheory.RingObjects.RingPresheaf:
  Functor.monObjCompForget₂, Functor.isCommMonObj_compForget₂,
  Sheaf.monObj_presheafToSheaf_obj, and the sheaf-ring transport declarations.
  The recorded MonObj/IsCommMonObj and mapCommMon framework is reused.
- Mathlib.CategoryTheory.Sites.Sheafification: HasSheafify, presheafToSheaf,
  toSheafify and sheafificationAdjunction, including the counit normalization.
- Sheaf.CategoryTheory.SiteCoveringAxioms: Precoverage.IsSiteForCoverings and
  its associated Grothendieck-topology convention. We impose no stronger
  hypothesis about chosen covering families or global pullbacks.
- Mathlib.GroupTheory.MonoidLocalization.Away: Localization.Away; and
  Mathlib.RingTheory.Localization.Away.Basic: IsLocalization.Away.lift, lift_eq;
  Mathlib.RingTheory.Localization.Defs: IsLocalization.ringHom_ext, map,
  map_eq and map_comp. The complete recorded signatures were read.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence: sectionRings,
  sectionRingSheaf, commMonToRing and the sectionModuleEquivalence interface.
  Its object-size, morphism-size and coefficient-size assumptions were read.
- The proof-only node det-def-sfb-ring-object-sheaf has an unavailable, withdrawn
  module (its record notes deletion on 2026-10-20; scompile --source confirms it
  is unavailable). No import of that deleted module is emitted. The actual data
  needed here are supplied by the recorded upstream RingPresheaf module, and
  its reconstruction/unique-extension argument remains in the proof docstring.

Searches for existing declarations:

- msearch.py leanfinder, query “Sheafification of sectionwise localization at a
  global section is the universal ring sheaf inverting the section”: eight hits,
  including TopCat.Presheaf.totalQuotientPresheaf,
  TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf and structure-sheaf
  fraction/localization facts. No arbitrary-site internal-ring universal property
  or unique normalized comparison is provided by these hits.
- msearch.py loogle, query “IsLocalization.Away.lift”: six hits, including lift,
  lift_eq and lift_comp. These give the ordinary ring ingredient, not this theorem.
- msearch.py grep, query “localizationPresheaf|awayMap” under Topology/Sheaves:
  five hits in Mathlib/Topology/Sheaves/CommRingCat.lean. Read its localization
  presheaf and algebra/IsLocalization instances; its site is the opens of a
  topological space, whereas this node has an arbitrary small site.
- rg of WeilConjectures and Sheaf for localization/sheaf keywords and for the
  item ID found no existing declaration of this theorem. Exact new declaration
  names were also searched in both roots and dag/lean_names_upstream.json; no
  collision was found.
- Read Sheaf.CategoryTheory.RingedSectionLocalization and
  RingedSectionLocalizationRing. They construct section localization modules and
  rings with a common universe and SmallCategory. They do not provide this
  internal-ring theorem. The helper here supplies the actual objectwise presheaf
  at arbitrary object, morphism and coefficient sizes; no independent new
  mathematical notion or duplicate ring/tensor definition is introduced.

Edge cases checked against the statements: t=1 makes localization the original
ring; t=0 and nilpotent t (including 2 in Z/4) give zero localizations and force any
target inverting t to be a zero ring. The zero ring is admitted. n=0 and k=0 are
included in the fraction formulas. The empty site is admitted and all quantified
section conditions are then vacuous in its terminal sheaf category. Independent
site object and morphism universes remain available. No statement fault or
STATEMENT-DISPUTED issue was found.

All compilation uses the prescribed scompile.py wrapper, never a global build.
The delivery dry run is performed with deliver2.py --no-push before the push.

## Second reading by Q62

A fresh self-audit matched the complete node with the exported declarations:
checked the power-torsion relation rather than a cancellative relation; checked
both operations and restriction on every fraction; checked the actual inverse
counit and r/1 normalization; checked internal CommMon morphisms rather than
bare additive maps; checked that the codomain D and alternative localization L
are arbitrary; and checked uniqueness of an isomorphism with the specified
composite, not just existence of an unnormalized isomorphism. Checked that
pointwise invertibility of a global section gives a compatible global inverse
by uniqueness. Type annotations and explicit universes repaired elaboration
ambiguities without changing any mathematical clause. Sheafification and
monoidal local equivalences are supplied from the size convention, with no
extra hypothesis in the main theorem. This is a self-audit; the dispatch brief
forbids other agents and assigns independent review to the maintainer.
