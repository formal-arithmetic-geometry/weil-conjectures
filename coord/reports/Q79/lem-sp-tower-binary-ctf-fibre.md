## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SpTowerBinaryCtfFibre.binary_ctf_fibre`
in `Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre`. Its only postponed proof is the
item's theorem, with the complete seven-step DAG proof in its docstring. The five
helpers are real constructions belonging to this node: open restriction, nested
restriction, their canonical composition comparison, evaluation of a selected
restriction isomorphism, and exact evaluation in fixed-scalar coordinates. No
new notion, dependency replacement, or statement correction was needed. The node
copy changes only `lean`.

Sources read: the complete node and its seven proof steps; every statement
dependency and its recorded Lean interface; the latest blueprint's
`sec-smooth-purity/sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md`,
Gluing and Uniformity, together with the node's retained corrected fibre proof.
The latest blueprint paragraph still describes the cone informally; this node
already specifies the corrected, unshifted right-direct-image fibre, and that is
the construction stated here. The recorded generic binary-descent theorem was
read with its full signature and proof docstring, including its canonical
counit formulas and the orientation of its overlap comparison.

Hypothesis and clause correspondence:

- The prime ell is `l : ℕ` with `[Fact l.Prime]`. The coefficient field is
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`. `R l E n` is exactly
  `Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n+1)`.
  Natural index zero means the paper's first positive level; no exponent-zero
  quotient is introduced. The ring of integers and quotient maps are the
  dependency constructions, not uniformizer-power substitutes.
- The field setting is `p : ℕ`, `[Fact p.Prime]`, `k : Type u`, `[Field k]`,
  `[CharP k p]`, and `_hlp : l ≠ p`. In particular p is positive. The scheme
  `Z : Over (Spec (CommRingCat.of k))` has `[IsSeparated Z.hom]`,
  `[LocallyOfFiniteType Z.hom]`, and `[QuasiCompact Z.hom]`, precisely separated
  finite type. All other schemes are its open subschemes and carry their
  induced k-structure maps. All inclusion morphisms are therefore k-morphisms;
  no independent morphisms with unspecified base structure are introduced.
- `b : SpTowerShriek.Base l E` and `o : SpTowerShriek.Operations l E b` are
  the already recorded, section-normalized ordinary tower calculus supplied by
  `tower_shriek_levels`, rather than new geometric hypotheses. They fix the
  same varying quotient rings, ordinary derived operations, coefficient maps,
  and composition comparisons. The contextual compactification choices and
  notation F_h of the node are supplied by this calculus's existing `F` for
  a coefficient-independent compactification; no F_h occurs in the binary
  descent assertion itself. No preservation or shriek assumption is imposed
  on P or Q.
- The ambient category is `SpTowerShriek.D l E T`: the ordinary derived
  category of modules on the ringed sequence site, with coefficient system
  `B l E T` and actual transitions `tau l E T`. `Base.realization T` is the
  recorded equivalence with `spCoefficientTowers l E T`; its `sections`,
  `restrictions`, and `morphisms` fields fix every module and transition.
  This is not a diagram category of already derived objects. `Ev` is its
  exact, ordinary derived level evaluation.
- The binary cover is `U V : Z.left.Opens` and `_hcover : U ⊔ V = ⊤`.
  W is literally `U ⊓ V`, and its two arrows are
  `Z.left.homOfLE inf_le_left` and `Z.left.homOfLE inf_le_right`.
  The three j_D are the actual open-inclusion maps `U.ι`, `V.ι`, `(U ⊓ V).ι`.
- The intervals are `a₀ b₀ s t : ℤ`, `_hab : a₀ ≤ b₀`, `_hst : s ≤ t`.
  The paper's Tor endpoints u,v are renamed s,t to avoid confusing them
  with the universe u. They are independent of the natural level n.
- P and Q are ambient objects `D l E U.toScheme` and `D l E V.toScheme`.
  The `_hP` and `_hQ` hypotheses each have exactly the same three tests at
  every n: intrinsic constructibility in every degree, cohomology zero
  outside `[a₀,b₀]`, and Tor amplitude in `[s,t]`. These expand membership in
  the unnormalized full subcategory with the supplied witnesses for its
  common bounds. No common stratification across n is imposed.
- Constructibility uses the dependency's recorded
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf` itself. `fixedLevel` is
  `Ev` followed by `(sfIntrinsicModuleEquivalence T (R l E n)).inverse.mapDerivedCategory`.
  This exact canonical equivalence transports the constant coefficient action
  to `ULift (R l E n)` and preserves the cohomology sheaf. The predicate
  retains a positive finite number of immersed locally closed constructible
  strata, locally constant restrictions, and finite geometric stalks. It
  includes arbitrary finite modules, not only free modules or etale-origin
  witnesses. This avoids relying on a name alone for constructibility.
- The cohomological test is the ordinary `DerivedCategory.homologyFunctor` on
  `(Ev ... n).obj P` or Q, with `IsZero` when `i < a₀ ∨ b₀ < i`.
  Tor amplitude uses the existing `Scheme.HasProEtaleTorAmplitude` in the
  ordinary constant-ring module category, retaining its universal degree-zero
  module test and derived tensor. The old and fixed-scalar presentations are
  connected by the canonical realization, not an assumed comparison map.
- `c` is an actual isomorphism between the two ordinary derived tower
  restrictions to the overlap. It is not a family of unrelated level maps.
- The conclusion chooses G in `D l E Z.left`, arrows f,d,delta, and actual
  isomorphisms aU and aV to P and Q. The final quantified conjunction is
  exactly the same three level tests with exactly the input intervals. Thus
  G belongs to C_Z, its levels belong to C_{Z,n}, and its cohomology is
  intrinsically constructible, bounded in the prescribed common interval.
- `d = biprod.desc (...) (-...)` spells out the displayed signed arrow.
  Each restriction arrow is the recorded `CategoryTheory.restrictionAdjunctionMap`
  for the canonical derived adjunction. The first is followed by
  `(push ...).map c.hom`; the second has the minus sign. The direct images
  are ambient total right derived functors. They have no constructibility,
  finite Tor, normalization, or boundedness premise.
- `Triangle.mk f d δ ∈ distTriang _` is precisely the displayed distinguished
  fibre triangle. Delta's target is `(shiftFunctor _ (1 : ℤ)).obj G`.
  Consequently G is its first object, without an extra shift.
- The next two equalities identify aU,aV with restriction of f, projection
  from its biproduct, and the direct-image counit. These specify the selected
  local models from the binary-descent construction itself. The overlap
  equation is `compU.hom.app G ≫ rUW.map aU.hom ≫ c.hom =
  compV.hom.app G ≫ rVW.map aV.hom`, with `restrictionComp` supplying the
  actual canonical iterated-restriction comparison. It is precisely
  aV|W = c composed with aU|W, in Lean's left-to-right composition order.
- `evaluatedRestrictionIso U aU n` and its V version explicitly construct
  the selected finite local models using the *specified*
  `Geometry.pullEvaluation`, followed by `Ev.mapIso aU` or `Ev.mapIso aV`.
  Hence these level isomorphisms are derived evaluations of the chosen tower
  isomorphisms, with the canonical coefficient identification. Applying
  `Ev` on the overlap to the displayed compatibility equality gives its
  evaluated compatibility; no existence of lifts of arbitrary families is
  assumed. This clause is supplied as real data, rather than another sorry.
- The final paragraph's topos and slice description is the concrete meaning
  of the chosen model, not an additional unspecified presentation. Its
  coefficient ring is `SemilinearSections.systemRing` on
  `coefficientSequenceTopology (ProEt.topology Z.left)`. The constant
  representable subterminal and its open slice are those of
  `SequenceOpenOrdinary.H`, `constantRepresentable`, `slice`, `localization`,
  and `ring_identity` in the imported sequence-open theorem. Its `L_obj`,
  `L_restrict`, and `coefficientRestriction_section` retain actual sections
  and every quotient map. `Scheme.ProEt.sliceEquiv` and the unique
  constant-section isomorphism in `weaklyEtale_localization` identify these
  with the pro-etale sites and coefficient rings of U,V,W. The published
  `Geometry.generic`, coefficient/transition equalities, ordinary-adjunction
  equality and ordinary/derived evaluation equalities retain the same
  canonical geometric operations. The statement's `restrictionComp` is
  localized ordinary composition, using `Operations.comp_termwise`; its
  equality transport uses `Scheme.homOfLE_ι` and changes no map.

Dependency declarations used and read:

- `sk-def-sfb-dc-setting`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its
  explicit separated finite-type Over-scheme setting.
- `def-weil-l-adic-coefficient-extension`: module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, reexporting
  `Padic.coefficientExtensionIntegers` and the original coefficient constructions.
- `sk-def-sp-coefficient-towers`: module `Sheaf.Paper.SmoothPurityCoefficientTowers`,
  `spCoefficientTowers`, `spEllIdeal`, `spCoefficientRings`, and quotient reductions.
- `det-sp-coefficient-towers-abelian`: module
  `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
  `SpCoefficientTowersAbelian`, `spCoefficientEvaluation`, and
  `sp_coefficient_towers_abelian`.
- `sk-def-sp-normalized-towers`: module `Sheaf.Paper.SmoothPurityNormalizedTowers`,
  the ordinary derived tower/evaluation and unnormalized level conditions of
  `spConstructibleTorTowers`; `spEllQuotientFinite` supplies the same finite rings.
- `def-weil-proetale-constructible-sheaf`: module
  `Sheaf.Paper.ProEtaleFixedModuleConstructible`,
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `def-weil-proetale-tor-amplitude`: module
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`, which publicly
  retains `Scheme.HasProEtaleTorAmplitude` in addition to the fixed-scalar interface.
- `det-sp-tower-shriek-levels`: module `Sheaf.Paper.SmoothPurityTowerShriekLevels`,
  `SpTowerShriek.R`, `B`, `tau`, `S`, `D`, `Ev`, `Base`, `Geometry`, `pull`,
  `push`, `adjunction`, `Operations`, and `tower_shriek_levels`.
- `lem-weil-proetale-weakly-etale-localization`: module
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
  `Scheme.ProEt.sliceEquiv` and `weaklyEtale_localization`.
- `lem-sp-ringed-topos-binary-descent`: module
  `Sheaf.CategoryTheory.RingedToposBinaryDescent`, `ringedTopos_binary_descent`;
  its publicly imported Defs module supplies `restrictionAdjunctionMap`.
- Further proof imports are the recorded
  `Sheaf.Paper.SequenceSiteOpenExtension` (`sequenceSiteOpenExtension`),
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` (`localizedSystemExact`),
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
  (`ringedTopoiCanonicalDerivedTensorPullback`),
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (`proEtaleSheafInverseImage`),
  and `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
  (`geometric_inverse_image_constant_module`). The constructible-subset
  proof dependency is the Mathlib match `Topology.IsConstructible` in
  `Mathlib.Topology.Constructible`, imported as a proof dependency.

Edge cases checked by reading the types and the proof:

- U or V empty, one open equal to Z, and empty overlap are allowed: no
  Nonempty assumption on any scheme or intersection appears. The actual
  restriction functors, their counits and negative overlap arrow remain typed.
- Empty Z is permitted. The recorded constructibility predicate's positive
  stratum convention is met by a single empty stratum, as in proof step 6.
- Zero P,Q are permitted; there is no nonzero, free, lisse, or normalized input
  condition. A single-degree cohomological or Tor interval is allowed.
- The closed endpoints are retained; vanishing is tested strictly outside
  each interval. The cohomological and Tor intervals may differ.
- n=0 represents exponent one and all n cover exactly the positive levels.
  The ramification index is not assumed one; the actual ell-power quotient
  is used, so ramified coefficient fields are included.
- Small pro-etale site objects have universe u+1 and morphisms universe u;
  coefficients/module sections have universe u+1. No equality of these site
  universes, small-site substitution, or etale-origin assumption is introduced.

Searches actually run:

- `msearch.py ... leanfinder "Glue constructible finite Tor amplitude strict
  coefficient towers on a binary open cover by the derived direct image fibre
  triangle"`: eight hits, including DerivedCategory truncation/fraction
  statements and scheme gluing, none the coefficient-tower assertion.
- `msearch.py ... loogle "CategoryTheory.Pretriangulated.Triangle,
  CategoryTheory.Limits.biprod.desc"`: OK, zero hits.
- `msearch.py ... grep "binary_descent|ctf.*fibre|tower.*gluing"`: OK, zero
  Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  binary-ctf/tower-binary terms, and SmoothPurity restriction/derived/bounds
  declarations found the recorded generic descent and tower infrastructure,
  but no existing theorem for this node. The source-read searches found and
  reused `restrictionAdjunctionMap`, `Operations.comp`,
  `sfIntrinsicModuleEquivalence`, and `Geometry.pullEvaluation`; no private
  versions were introduced.

Validation: scompile.py compiled this module under its sandbox module name and
its actual library module name. The final delivery is checked again by the dry
run and its prescribed server preflight. `set_option autoImplicit false` is
active, every universe and variable is bound, all helper data are constructed,
and only the main theorem uses sorry. No statement dispute or node fault.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
