## Worker report

The module `Sheaf.AlgebraicGeometry.ValuativelySaturatedTranslateGluing` states
`AlgebraicGeometry.ValuativelySaturatedTranslateGluing.exists_gluing`, with `sorry`, and
constructs two helpers with real data: `integralPointSubgroup` is the range of the
Yoneda restriction homomorphism B(D) → B(F), and `translatedGenericInclusion` is the
product of the constant rational section and the generic inclusion in the given group
object. These are helpers belonging to this node, listed in lean.declarations; they do
not introduce a separate group-scheme or gluing notion. No statement change or
new/dependency node is needed.

Hypotheses and objects, clause by clause:

- D is `[CommRing D] [IsDomain D] [IsDiscreteValuationRing D]`. F has `[Field F]
  [Algebra D F] [IsFractionRing D F]`. All universes are explicit. `Spec (.of D)`
  is S, and `B : Over (Spec (.of D))` gives B/S.
- `[CommGrpObj B]` uses Mathlib's commutative group object in the category of
  S-schemes. It supplies multiplication, unit, inverse and precisely the group
  and commutativity diagrams. `[Smooth B.hom] [IsSeparated B.hom]` renders smooth
  and separated; `[LocallyOfFiniteType B.hom] [QuasiCompact B.hom]` renders finite
  type using the recorded convention.
- G is the actual pullback B ×_S Spec F. Points G(F) are expressed as the
  canonically equivalent type `Over.mk (Spec.map (ofHom (algebraMap D F))) ⟶ B`;
  the pullback universal property identifies these with sections of G over F.
  The statement does not choose a new model of the generic fibre.
- `hsat` quantifies over all valuation domains `V : Type u`, all `φ : D →+* V`,
  an `IsLocalHom φ`, and `Function.Injective φ`. For each rational section a,
  its left side gives exactly a V-section x over φ with the same restriction
  to `FractionRing V` as the scalar extension of a. The latter is the canonical
  `IsFractionRing.map hinj`. The right side says a lies in the image of B(D).
  Thus the biconditional is precisely the asserted equality of subsets. Taking
  the canonical fraction field loses no fraction field L: every fraction-field
  realization is uniquely isomorphic over V. V shares the universe of the schemes,
  matching Mathlib's valuative criterion, not an independent smaller universe.
  `ValuationRing` has the stated either-x-or-inverse characterization in its TFAE.
- `integralPointSubgroup` uses `yonedaGrpObj`, whose restriction homomorphism has
  underlying function precomposition by Spec F → Spec D. Separatedness makes it
  injective on B(D); its range expresses the subgroup without postponing any
  data or needing an auxiliary injectivity theorem.
- The quotient in the types of a and j is exactly B(F)/image(B(D)), using the
  standard subgroup quotient. `ha : ∀ γ, QuotientGroup.mk (a γ) = γ` says a is
  a choice of representatives, with no compatibility requirement.

Conclusions, clause by clause:

- `∃ (Z : Over S) (j : Γ → (B ⟶ Z))` provides the S-scheme and one copy of B
  per quotient class. `Smooth Z.hom ∧ IsSeparated Z.hom ∧ LocallyOfFiniteType Z.hom`
  is exactly the three asserted properties. No quasi-compactness is claimed for Z.
- `∀ γ, IsOpenImmersion (j γ).left` states the chart condition. Joint surjectivity
  `∀ z, ∃ γ, ∃ b, (j γ).left b = z` says these charts cover Z, which is part of
  being the resulting gluing rather than a larger scheme containing its charts.
- For every unequal pair, `IsPullback` uses G as its upper-left object, the
  generic projection G → B in chart γ, and the translated generic inclusion
  for `(a δ)⁻¹ * a γ` into chart δ. Thus it states both the specified transition
  (the square commutes) and the exact scheme-theoretic intersection (the square
  is cartesian). For equal indices each chart is an open immersion, hence mono,
  so the self-intersection is its whole copy of B, as required by gluing data.
  This covering open atlas with cartesian overlaps characterizes the gluing
  of lem-weil-pbc-glue-schemes up to unique compatible isomorphism; no choice of
  an arbitrary unrelated glued scheme is assumed.
- `q` is an isomorphism in `Over (Spec F)` from the actual pullback Z_F to G.
  The last equation says the generic chart followed by q, after the projection
  G → B, equals `translatedGenericInclusion B (a γ)`. Together with equality
  of the structural maps in Over(Spec F), the pullback universal property makes
  this exactly the map b ↦ a_γ b into G. No choice of an arbitrary generic-fibre
  isomorphism can satisfy this without the specified translations.
- The node explicitly disclaims Néron-model and torus-extension assumptions;
  neither appears in the signature.

Dependency declarations read and used:

- def-sc-discrete-valuation-ring: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, local nonfield PID.
- def-weil-affine-spectrum and def-pc-scheme: `Spec`, `Spec.map`, `Scheme`,
  `Scheme.Hom`, `Mathlib.AlgebraicGeometry.Scheme` (exposed through the direct
  imports). Spectrum maps are contravariant as in the equations.
- def-sbc-smooth-morphisms: `Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- def-weil-closed-immersion: `IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, exposed by Separated;
  `IsSeparated` is precisely the closed immersion of the diagonal.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `.QuasiCompact`.
- def-pc-base-change: public import of recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; its documented
  scheme/morphism realization is `Limits.pullback`, its projections and
  `Over.pullback`, all used verbatim. Its `moduleBaseChange` concerns O-modules
  and is not needed here, exactly as its record's note explains.
- def-weil-open-immersion: `IsOpenImmersion`, `Mathlib.AlgebraicGeometry.OpenImmersion`.
- lem-weil-pbc-glue-schemes: `Scheme.GlueData` and its `glued`,
  `ι_isOpenImmersion`, `ι_jointly_surjective`, `glue_condition`,
  `vPullbackConeIsLimit`, `Mathlib.AlgebraicGeometry.Gluing`. The conclusion uses
  their intrinsic covering/cartesian-overlap specification rather than a second
  definition of gluing or an extra input hypothesis that gluing already exists.
- Proof imports: `Mathlib.AlgebraicGeometry.Noetherian` exposes IsLocallyNoetherian,
  LocallyOfFiniteType.isLocallyNoetherian and IsNoetherianRing (the recorded
  pqf-def-locnoeth, pqf-lem-locnoeth-lft and def-weil-pbc-noetherian-ring);
  `Mathlib.AlgebraicGeometry.ValuativeCriterion` exposes the recorded
  `IsSeparated.eq_valuativeCriterion` of lem-sfb-locnoeth-valuative-separatedness.
  Smooth exposes the source-local instance and
  `IsZariskiLocalAtSource.iff_of_iSup_eq_top` of
  lem-weil-pbc-smooth-local-on-source. No proof-dependency import is omitted.

Edge checks before writing: the quotient is nonempty (identity class), so there
is always a chart; a trivial quotient produces just B and no distinct overlap
conditions. Infinite quotients are allowed and Z is only locally of finite type.
The group scheme cannot be empty since it has its unit section. Field valuation
rings, arbitrary-rank valuation rings and structural maps through the special
point are included in the valuative proof plan; saturation itself is used only
for local injective maps as stated. The generic-fibre square orientation is
γ → δ with a_δ^{-1}a_γ, and q has the direction Z_F → G. No assumption about
connectedness, residue characteristic, excellence, completeness, being a Néron
model, or being a torus extension is introduced.

Searches made with msearch.py (Q04, this item):

- leanfinder: "Gluing generic translates of a smooth separated group scheme with
  valuatively saturated integral points is separated" — 8 hits, including
  IsSeparated.of_valuativeCriterion and IsSeparated.valuativeCriterion, but no
  saturated-translate gluing statement.
- loogle: `"Scheme.GlueData"` — 12 hits for GlueData and its glued/atlas/overlap
  APIs; these supply general gluing, without the saturation argument.
- grep Mathlib/AlgebraicGeometry:
  `saturat.*translat|translat.*saturat|valuative.*glue|glue.*valuative` — zero hits.
- leansearch: "Glue smooth group schemes along generic fibre using translations
  by representatives of rational points modulo integral points" — 8 hits for
  gluing constructions, none giving this assertion.
- rg of the same notions and group-object names in WeilConjectures and Sheaf,
  plus the exact blueprint id in WeilConjectures — no existing statement.
  `GroupScheme.Basic` supplies field-group translations, but the helper here is
  the translated inclusion into B over D, formed from the original group-object
  multiplication without constructing a second generic-fibre group structure.
  Exact helper/declaration-name searches in the project and Mathlib found no
  existing declarations with these names.

Read the primary BLR scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
PDF pp.297–299 (printed pp.291–293), Example 5 and Proposition 7: generic-fibre
translation gluing is the indicated construction. The full six-step proof plan
of this node is included in the theorem docstring; no source claim is weakened
or enlarged to a Néron mapping assertion.

Validation: the prescribed scompile.py checked both sandbox and actual module
names, with no errors or warnings. All definitions have real data; the only
postponed theorem is exists_gluing and its full proof plan is in its docstring.
The report and record will also be checked by the prescribed deliver2.py dry run.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
