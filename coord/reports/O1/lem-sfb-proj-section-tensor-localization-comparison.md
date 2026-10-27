## Worker report

The delivery states `AlgebraicGeometry.Proj.projSectionTensorLocalizationComparison` in
`Sheaf.AlgebraicGeometry.ProjSectionTensorLocalizationComparison`. Its only postponed proof is
this named theorem, whose docstring contains all eight steps of the node's proof. The original
node statement, dependencies, proof and every field other than `lean` are unchanged.

Source read: `literature/stacks-project/properties.tex`, `lemma-proj-quasi-coherent` (0AG5),
lines 5074–5130; `constructions.tex`, `lemma-when-invertible` (01MS),
`lemma-apply-modules` (01MT), and `lemma-principal-open` (01MV), including the local
multiplication and inverse-frame argument. Only the formal identification inside the proof of
0AG5 is asserted, so the quasi-compactness and quasi-coherence assumptions needed for the
subsequent identification with sections on the open are correctly absent here.

Clause-by-clause correspondence:

- A nonnegatively graded commutative ring is `{S : Type u} [CommRing S]`,
  `𝒜 : ℕ → AddSubgroup S`, `[GradedRing 𝒜]`; `X` is exactly `Proj 𝒜`.
- The degree-one standard-open cover is exactly the `cover` binder,
  `∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f`. There is no finite generation assumption.
- The arbitrary O_X-module is `F : (Proj 𝒜).Modules`; no quasi-coherence instance is bound.
- O_X(n) is the recorded `Proj.twist 𝒜 n`, and F(n) is `F ⊗ twist 𝒜 n`.
  N is the literal direct sum `⨁ n : ℤ, Γ(F ⊗ twist 𝒜 n, ⊤)` in the theorem conclusion.
  The existential `mN` supplies its S-module structure; `actionN` fixes the action of each
  homogeneous coefficient on every summand by `F ◁ twistMul n hv`. Additivity then fixes
  the action on arbitrary coefficients and finite sums. It is not an arbitrary action.
- L is literally `twist 𝒜 1`. Its invertibility is the first conclusion of the theorem.
  The later universal binder over this proposition's instance does not assume invertibility:
  it allows the existing B ring operations to be elaborated after invertibility is concluded.
- B is the existing `InvertibleSectionRing (twist 𝒜 1)`, whose degree e is
  `SectionRingComponent L e = Γ(L.tensorPow e, ⊤)`, with its existing tensor multiplication.
  P is the literal integer direct sum with `projSectionTensorPower L n` in the theorem.
  This helper is a direct match on integers, using the existing `L.tensorPow n` for ofNat
  and `L.dual.tensorPow (n+1)` for negSucc. It supplies real data, with no existence choice.
- The maps beta_n are `β : ∀ n : ℤ, projSectionTensorPower L n ≅ twist 𝒜 n`.
  `beta_zero` identifies degree zero with the canonical `unitIsoTwistZero`;
  `beta_succ` makes positive powers the iterated `twistTensorIso` multiplication;
  `beta_dual` normalizes the dual map by the actual `dualEvaluation L`;
  `beta_neg_succ` fixes every further negative degree by iterated multiplication of the dual.
  The right unitor in the degree -1 equation accounts for `tensorPow 1 = L.dual ⊗ O_X`.
- `φ : S →+* InvertibleSectionRing L` is required to send a degree-e coefficient to the
  e-summand containing `β_e.inv` applied to its canonical `unitToTwist` section.
  The explicit `eqToHom (congrArg (twist 𝒜) (zero_add (e : ℤ)))` only removes the
  upstream `unitToTwist` index `0+e`; it changes no section.
- `scalarP` and `actionP` give the B-module structure on P and its multiplication on all
  homogeneous inputs. For n≥0 this is `tensorPowAddIso n e`; for n<0 this is the
  explicit `projSectionTensorMultiply` contraction built from `dualEvaluation` (see the
  return repair below). No beta map or twist multiplication defines this action.
  `γ : P ≃+ N`,
  `gamma_homogeneous`, and `gamma_linear` give the graded S-module identification after
  restriction along φ. Homogeneous action and gamma formulas determine these maps on the
  whole direct sums, rather than merely asserting an unrelated equivalence.
- For every `f` and `hf : f ∈ 𝒜 1`, s is exactly
  `(unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)`. `nonvanishing` uses the existing
  `Scheme.Modules.nonvanishingLocus` (germ outside maximal ideal times stalk), and equates it
  with the underlying set of `basicOpen 𝒜 f`. `generator` says that the restriction of this
  same global section is an `IsFreeGenerator`, on every subopen by that predicate's definition.
- `localization f hf` gives `ProjSectionLocalizedComparison`.
  Its `Z` is an additive subgroup of `LocalizedModule.Away f N`; `carrier_eq` requires its
  carrier to be exactly the existing `degreeZeroFractions` for the ring and the actual
  summand-image grading of N. `fraction_mem` explicitly includes every numerator t in N_a.
  Thus this is N_(f), not an abstract replacement or an unspecified localization.
- P_(s) is exactly the existing `SectionFractionPresentation L F s`: the direct sum of
  nonnegative numerator degrees modulo the relations identifying t/s^a with
  (t tensor s^b)/s^(a+b). This recorded definition explicitly presents the degree-zero
  localization of the integer tensor-power module; negative components are irrelevant
  to degree-zero numerators, but are retained in P and the global comparison.
- `scalarZ` and `scalarQ` are genuine module structures over `HomogeneousLocalization.Away 𝒜 f`.
  `scalarZ_fraction` fixes the former as multiplication in the ordinary localization.
  `scalarQ_fraction` fixes restriction of scalars along v/f^b ↦ φ(v)/s^b by the actual
  tensor multiplication: `tmulSection t` with the beta_b-inverse coefficient section,
  followed by the associator and `(L.tensorPowAddIso a b).inv`. It does not transport
  multiplication through beta_a or beta_(a+b). Thus linearity compares the independently
  defined tensor action with the canonical twist action.
- `θ` is an actual `LinearEquiv` over S_(f), with both module instances explicitly passed.
  `fraction` is exactly θ(t/f^a)=β_a^{-1}(t)/s^a, with the identity on F expressed by
  `F ◁ (β (a : ℤ)).inv`. Invertibility of θ includes its inverse fraction formula.
- `common_power` states that equality of either pair of fractions is equivalent to
  `∃ c : ℕ, f^c • (f^b • ιN a t - f^a • ιN b v) = 0`.
  `common_power_transport` spells out its equivalence with the same relation on P using
  `φ(f)^c`, `φ(f)^b`, `φ(f)^a` and the beta-inverse numerators. The homogeneous formula
  identifies φ(f) with s in B_1. No cancellation or non-zero-divisor condition occurs.
- `divide` is an additive map on P_(s), fixed by `divide_fraction` as restriction followed
  by division by the tensor-power free frame. `restriction_compatibility` requires that
  its composite with θ sends t/f^a to the section whose tensor with `twistPowSection a hf`
  is t restricted to D_+(f). Since this is a free frame, this is exactly
  t restricted to D_+(f) tensor f^(-a). This formulation avoids choosing inverse sections
  or suggesting division on a bare module. There is no assertion that `divide` is bijective.

Dependency declarations read and used:

- `def-pc-proj`: Mathlib `AlgebraicGeometry.Proj`, `Proj.basicOpen`,
  `Proj.basicOpenIsoSpec`, and `ProjectiveSpectrum.basicOpen`; also the recorded upstream
  `Proj.isAffineOpen_basicOpen_and_nonempty_iso` docstring in
  `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`.
- `def-weil-pbc-proj-twisting-sheaf`: `Proj.twist` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`, `twistMul`,
  `unitIsoTwistZero`; `Proj.unitToTwist` in the sibling `UnitToTwist` module;
  `twistPowSection` in `Twist.TensorObj`.
- `lem-sfb-standard-proj-twist-tensor`: `Proj.standardProjTwistTensor` in
  `Sheaf.AlgebraicGeometry.StandardProjTwistTensor`; its canonical `twistTensorIso`
  is the public upstream construction in `Twist.TensorIso`. Its complete theorem and
  chart-interface predicates were read. We do not replace any of those maps.
- `def-pur-sheaf-tensor-product`: the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly imported through
  `StandardProjTwistTensor`; scheme tensor, whiskering and tensor sections use the existing
  scheme interface, `Scheme.Modules.tensorPow` and `tmulSection`.
- `def-sc-invertible-module`: `Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, and the actual `dual` and
  `dualEvaluation` from `Modules.Dual`.
- `def-weil-sheaf-of-modules-category`: public import of
  `Sheaf.CategoryTheory.RingedSiteModules`, with its actual `SheafOfModules` abbreviation;
  scheme modules are the existing specialization, not another module category.
- Proof imports: `SheafOfModules.tensorClosed` in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`;
  `Proj.twistSectionBasicOpen` in `Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen`;
  `Proj.standardOpenProperties` in `WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`;
  `TopCat.Sheaf.restrictHomEquivHom`, `extend_hom_app`, `hom_ext`,
  `isIso_iff_isIso_basis` in Mathlib `Topology.Sheaves.SheafCondition.Sites`.
  `lem-pc-tensor-dual-invertible` is supplied by the publicly imported `Modules.Dual`,
  including its `nonempty_iso_dual_dual` and evaluation construction.
- Existing supporting definitions: `InvertibleSectionRing`, `sectionRingGrade` and its
  operations were read in `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`;
  `SectionFractionPresentation`, `sectionFractionRelations`, `sectionFraction` were read in
  `WeilConjectures.AlgebraicGeometry.SectionFractionPresentation`;
  `LocalizedModule.degreeZeroFractions` in `WeilConjectures.Algebra.Module.DegreeZeroFractions`;
  `nonvanishingLocus` in `WeilConjectures.AlgebraicGeometry.Ample`.
  Their recorded nodes were checked. These existing definitions are reused directly.

Edge cases checked: degree zero uses the actual unit isomorphism; the degree-one tensor power
has a right unit factor, which is handled by the beta recursion and dual normalization;
all negative integers are included by negSucc; an empty Proj makes the cover vacuous and the
nonvanishing and generator equations remain meaningful; F may be the zero module or an
arbitrary non-quasi-coherent module; f=0 or nilpotent gives an empty standard open and a zero
localized module, with the common-power relation still valid (no cancellation). The cover
may be infinite. No field, reducedness, compactness, separatedness or quasi-coherence condition
is introduced. All variables and the universe are explicit, with both auto-implicit options off.

Searches actually run:

- `msearch.py leanfinder`: “Identify integral tensor powers of O(1) with Proj twists and the
  degree zero localizations of their twisted global section modules”. Eight hits, consisting
  of Proj `awayToΓ`, `awayι`, `basicOpenIsoAway`, `awayToSection`,
  `fromOfGlobalSections_morphismRestrict`, `awayToSection_apply`,
  `projIsoSpecTopComponent`, `toBasicOpenOfGlobalSections`; none is this module comparison.
- `msearch.py loogle`: `AlgebraicGeometry.Proj.twist, LinearEquiv`. Zero hits, with
  `unknown identifier 'AlgebraicGeometry.Proj.twist'` reported by Loogle; not treated as
  proof that no upstream twist exists (its recorded source was read and reused).
- `msearch.py leansearch`: “Integral tensor powers of the twisting sheaf O(1) on Proj identify
  twisted global section localizations”. Eight structure-sheaf and affine-localization hits,
  including `Proj.pow_apply`, `Γ_restrict_isLocalization`, `Proj.basicOpenIsoAway`, and
  `ProjectiveSpectrum.Proj.awayToSection_apply`; no exact comparison.
- `msearch.py grep` in Mathlib AlgebraicGeometry:
  `twist.*localiz|tensorPower|sectionModule`: zero hits.
  `ProjSectionTensorComparison|projSectionTensorLocalizationComparison|twist.*localiz`:
  zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and `dag/lean_names_upstream.json`
  for the four delivered names: no existing names. The exact item id search in upstream
  yielded no declaration. The item-id search in Sheaf found only the proof-docstring use
  in the downstream `ProjSectionModuleReconstruction`, which cannot be imported here.
- Broader `rg` searches for tensor powers, graded sections and section localization in
  `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` found the
  reused `InvertibleSectionRing`, `SectionFractionPresentation`, `InvertibleSectionLocalization`,
  `ProjHomogeneousSectionTensorPowersData` and the Serre section-module interfaces. The
  existing tensor-power theorem is restricted to the polynomial projective line and
  nonnegative exponents, not this arbitrary graded ring and all-integer comparison.
  `InvertibleSectionLocalization` requires compactness, quasi-separatedness and
  quasi-coherence and asserts the stronger open-sections isomorphism, so is not reused
  as this statement or imported as a hypothesis. No second localization is defined here.
- `tools/lean_names_upstream.py show` was consulted; direct rg checked the name index.

Validation: `scompile.py O1 lem-sfb-proj-section-tensor-localization-comparison <module>`
compiled the delivered module both as sandbox and by its library module name without errors
or warnings. The first probes caught the need for a public UnitToTwist import and explicit
`0+e=e` transport; both were repaired. Line widths are at most 100. The delivered file
contains one `sorry`, exactly the theorem's whole proof. No node correction, disputed
statement, new DAG node, or dependency repair is needed.

## Second reading by O1

This is the dispatcher's single worker's separate rereading, not a claim to be an independent
agent review; the maintainer supplies the independent review, and the prompt prohibits
starting another agent. I reopened the node, the completed Lean file and the source places.

The ring, degree-one cover, arbitrary module and all integer summands match exactly.
The independent return on head 3bcfba40ec18 correctly found that my earlier reading missed
an H3 mismatch: the action formulas used beta to transport the twist actions, instead of
asserting compatibility with the usual tensor actions. That made the intended comparison
vacuous. I replaced both formulas and reread their right-hand sides independently of the
beta equations. `actionP` now has no occurrence of beta or twistTensorIso. For n≥0 its
helper selects the existing tensorPowAddIso, and for n<0 it selects genuine evaluation
contraction. `scalarQ_fraction` uses beta only to obtain the coefficient section in L^b;
its multiplication of that section with t uses tensorPowAddIso a b. In particular beta_a
and beta_(a+b) cannot cancel in either action formula. Gamma-linearity and theta-linearity
therefore assert compatibility between independently specified actions.

The helper recursion was read at n=-1,e=1 (evaluation to the unit), n=-2,e=1
(one dual factor remains), n=-1,e=2 (contract then retain one positive L), and e=0
(the right unitor). These include crossing through exponent zero. For n≥0 the helper
selects tensorPowAddIso directly. The negative recursion decreases the natural coefficient
exponent; it is a real terminating definition, with no object selected from existence.
The comparison on sections still includes the identity on F through whiskering; the
restriction/division equations and all previously accepted clauses are unchanged.
There is still no compactness or quasi-coherence assumption. No remaining mismatch
was found in this rereading.


## Returned delivery repair

Return: L, immutable head `3bcfba40ec18`, H3, with two required replacements.

1. `scalarQ_fraction`: replaced the beta_a / twistMul / beta_(a+b)^(-1)
   transport with exactly the numerator requested in the return. It is
   `((α_ F L^a L^b).hom ≫ F ◁ (L.tensorPowAddIso a b).inv).app ⊤`
   applied to `tmulSection t` and the beta_b-inverse of the canonical section of v.
   The existing explicit `0+b=b` index transport is retained on that coefficient.
2. `actionP`: replaced the beta_n / twistTensorIso / beta_(n+e)^(-1)
   transport with tensor sections followed by the associator and
   `F ◁ projSectionTensorMultiply L n e`. This helper uses tensorPowAddIso
   for nonnegative n and a new, explicit dual-evaluation contraction for negative n.
   The four real-data helper definitions are in the owning module and recorded in
   `lean.declarations`, with source and blueprint docstrings:
   `projSectionDualContractOne` moves an L next to a dual factor using associators and
   braiding, applies the actual `dualEvaluation L`, then removes the unit;
   `projSectionTensorStep` contracts once in negative degree and tensors once in
   nonnegative degree; `projSectionTensorContract` consumes coefficient factors
   recursively and handles passage through zero; `projSectionTensorMultiply`
   selects ordinary tensorPowAddIso in nonnegative degrees and this contraction
   in negative degrees. None takes beta, a twist, or any comparison as an argument.

The current main node was compared with the retained returned node: there were no
non-lean-field differences, and main still has no Lean binding for this item. Main has
no source module at this path. The retained version matched the two returned formulas
before editing. The repaired node is rebuilt from current main with only `lean` set;
the delivery wrapper rebases onto its freshly fetched live branch.

Additional search: rg for the four new helper names in `lean/WeilConjectures`,
`lean/Sheaf` and Mathlib found no existing declaration. Concept searches for dual-power
contraction and signed tensor multiplication in the same algebraic-geometry directories
found no existing construction; `Modules.Dual` supplies the actual evaluation map and
`Modules.Invertible` supplies tensorPowAddIso, both reused. These helpers are explicitly
authorized by the return and are construction data for this same comparison, not new
independent theorem nodes.

The repaired module passed `scompile.py` in sandbox and library module-name modes,
with no errors or warnings. No timeout option was changed. All lines are at most 100
characters. There is exactly one postponed proof, the original named main theorem.
