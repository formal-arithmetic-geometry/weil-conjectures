## Worker report

The delivery states `AlgebraicGeometry.Scheme.Hom.exists_affineChart_stalk_differentials`
in `Sheaf.AlgebraicGeometry.AffineChartStalkDifferentials`. Its sole proof is `sorry`.
There are no new definitions or auxiliary theorems. The original node changes only in
`lean`; no statement correction, dependency repair, or new node is necessary.

Hypothesis and clause correspondence:

- Schemes, their morphism, local finite presentation, and a point are exactly
  `{X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)`.
  The point `s` is written directly as `f x`, with no additional parameter or hypothesis.
- The affine neighbourhoods are existential `W : X.Opens`, `V : S.Opens`,
  `hW : IsAffineOpen W`, `hV : IsAffineOpen V`, `hx : x ∈ W`, and
  `hWV : W ≤ f ⁻¹ᵁ V`. Thus `hWV hx` also supplies `f x ∈ V`.
  Their coordinate rings are the actual section rings `A = Γ(X,W)` and `R = Γ(S,V)`;
  the canonical chart maps are `hW.fromSpec` and `hV.fromSpec`, provided by Mathlib.
  This chooses coordinate rings for the existential affine charts, without imposing
  a further restriction on the schemes or charts.
- The induced coordinate map is precisely `f.appLE V W hWV`, not an arbitrary map.
  The conjunct `(f.appLE V W hWV).hom.FinitePresentation` asserts finite presentation
  of `A` over `R` using the ring-map formulation, without introducing a second
  algebra structure.
- The prime `q : PrimeSpectrum Γ(X,W)` is specified by
  `q = hW.primeIdealOf ⟨x,hx⟩`. Its contraction is explicitly
  `q.comap (f.appLE V W hWV).hom`, and the next equality identifies this contraction
  with `hV.primeIdealOf ⟨f x,hWV hx⟩`. Thus it represents exactly `s=f(x)`.
- The existential ring equivalences `e` and `h` have types
  `O_{S,f x} ≃+* Localization.AtPrime p.asIdeal` and
  `O_{X,x} ≃+* Localization.AtPrime q.asIdeal`, respectively. The first two
  conjuncts following the equivalences send the germs of every coordinate section
  to `algebraMap _ _` of that section. These conditions specify the canonical
  localization identifications, not merely some abstract ring isomorphisms.
- The third conjunct gives the compatible stalk-map square pointwise:
  `h (f.stalkMap x b) = Localization.localRingHom p.asIdeal q.asIdeal phi.hom rfl (e b)`.
  Here `p` is the contraction already written out, and `phi` is `f.appLE V W hWV`.
  This is exactly the canonical fraction map. Mathlib's definition
  `Localization.localRingHom` is `IsLocalization.map` for `phi`, and its lemma
  `Localization.localRingHom_mk'` explicitly states `r/t ↦ phi(r)/phi(t)`;
  `Localization.localRingHom_mk` gives the quotient-constructor variant.
  These are actual prime localizations, so the denominator condition is built in.
- The differential module is the recorded Mathlib interface
  `CommRingCat.KaehlerDifferential (f.appLE V W hWV)`. Its definition is exactly
  `KaehlerDifferential R A` with the algebra structure induced by this same ring map.
  The target of `theta` is its actual `LocalizedModule q.asIdeal.primeCompl`.
  Its source is `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
  f.relativeDifferentials`, the recorded relative differential sheaf at the ambient point.
- `theta` is an additive equivalence and the explicit conjunct
  `theta (b • m) = h b • theta m` states all scalar compatibility. This is exactly
  linearity over `A_q` after identifying `O_{X,x}` with `A_q` through `h`.
  Using an additive equivalence plus this equation avoids implicit inverse-ring-map
  typeclass parameters required by Lean's semilinear-equivalence notation.
- The next conjunct applies `theta` to
  `f.relativeDifferentials.presheaf.germ W x hx (f.relativeDifferentialsDerivation.d a)`
  and obtains `LocalizedModule.mk (CommRingCat.KaehlerDifferential.d a) 1`.
  This is the required germ-of-`da` to `da/1` formula for every `a ∈ A`, and pins
  down the canonical differential comparison together with scalar compatibility.
- The flatness clause uses `RingHom.Flat` for both the actual ambient stalk map
  and the same canonical `Localization.localRingHom` appearing in the square.
  It is an iff, with neither direction dropped.
- The last clause quantifies over every `r : ℕ`, which is exactly every integer
  `r ≥ 0`, and uses `Fin r`-indexed spanning families on the two modules. The
  scalar rings of the two spans are the actual `O_{X,x}` and `A_q`, respectively.
  The families are existential in each side of an iff, so no independence or
  minimality is asserted, and neither implication is dropped.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme.Hom.appLE`, `Scheme.Hom.stalkMap`. Covers def-pc-scheme and
  def-weil-affine-spectrum, with canonical coordinate and stalk maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, and its affine coordinate
  condition `Scheme.Hom.finitePresentation_appLE`; covers
  def-sbc-locally-finite-presentation.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`, and its fraction formulas; covers
  def-weil-pbc-localization-at-prime. The node's residue-field and fibre-ring
  interfaces are not needed by this particular statement.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`.
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`:
  `CommRingCat.KaehlerDifferential` and `CommRingCat.KaehlerDifferential.d`.
  The bundled ring-map interface is definitionally the same differential module,
  with the induced algebra instance; covers def-weil-pbc-kahler-differentials.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `Scheme.Hom.relativeDifferentialsDerivation`,
  and `Scheme.Hom.relativeDifferentialsRestrictFromSpecIso`; covers
  def-sc-relative-differential-sheaf. Read the definition, universal-property
  interface, and affine/restriction isomorphisms in their current source.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, whose definition uses
  `Module.Flat` with the given map's algebra structure; covers def-weil-pbc-flat-ring-map.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.mk`, and its localization-map interface; covers
  def-weil-pbc-module-localization.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor` supplies the standard stalk-module structure.
- The proof-only Mathlib nodes have no project `lean` record and are used through
  their `mathlib_match`: `IsAffineOpen.SpecMap_appLE_fromSpec` (AffineScheme),
  `Scheme.localRingHom_comp_stalkIso` and `Spec.algebraMap_stalkIso_inv`
  (AffineScheme), `IsAffineOpen.fromSpec_app_self`, `fromSpec_primeIdealOf`,
  `isLocalization_stalk` (AffineScheme), the open-immersion stalk isomorphism
  (OpenImmersion), `Scheme.Hom.germ_stalkMap` (Scheme), and
  `AlgebraicGeometry.tilde.toStalk` with its `IsLocalizedModule` instance (Modules.Tilde).
  The module directly imports each recorded proof-source module, using plain
  imports for OpenImmersion and Modules.Tilde, and public imports where the
  statement already uses that module.

Sources read: the complete assigned node and all eight statement dependencies,
all four proof comparison nodes' Mathlib matches; Stacks morphisms.tex,
`definition-finite-presentation` (01TP), `lemma-differentials-restrict-open` (01US),
`lemma-differentials-affine` (01UT), and `lemma-smooth-at-point` (01V9);
schemes.tex `lemma-spec-sheaves` (01HV), clauses (6)-(7) and functoriality.
The current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md`
was also read; this supporting affine comparison does not alter the unit statement.

Edge cases checked before writing:

- Empty `X`: no point `x` is available, exactly as in the natural-language statement.
  There is no nonemptiness or global affineness assumption. A zero coordinate ring
  cannot carry the selected prime; this follows from the supplied point, not an
  additional hypothesis.
- Identity morphisms and open immersions: the differential modules on both sides
  vanish, the fraction comparison is still canonical, and the flatness iff holds.
- `r=0`: `Fin 0` is empty and its span is zero; the last iff therefore means that
  one module is zero precisely when the other is. For positive `r`, repetitions
  and zero padding are allowed, as required for a generating family.
- The nonflat closed point `Spec F_p → Spec Z` satisfies local finite presentation.
  Neither side of the flatness iff is asserted flat; both are false in this example.
  For `Spec k[epsilon]/(epsilon^2) → Spec k`, nilpotents and arbitrary characteristic
  cause no restriction on the chart, primes, or differential comparison.
- Generic/nonclosed points, e.g. the generic point of `A^1_k`, are included by
  `PrimeSpectrum`; no maximality, rationality, residue-field finiteness, or
  Noetherian assumption appears. Denominators are prime-complement subtypes.
- `u` is explicitly bound and the schemes, section rings and localization modules
  use their natural common scheme universe. There is no smaller universe of test
  objects and no additional universe equality. `autoImplicit` is explicitly false.

Searches for an exact existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder "Affine charts of locally finitely presented morphisms
  identify stalk maps and relative differential stalks with prime localizations
  and their universal derivations"`: 8 hits, including
  `HasRingHomProperty.stalkMap`, `IsAffineOpen.isLocalization_stalk'`,
  `Scheme.arrowStalkMapSpecIso`, and `localRingHom_comp_stalkIso`.
  These provide individual ring comparisons, not the full chart/differential theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.stalkMap, KaehlerDifferential"`:
  0 hits.
- `msearch.py ... grep "relativeDifferentials.*[Ss]talk|[Ss]talk.*relativeDifferentials|localRingHom_comp_stalkIso"
  AlgebraicGeometry`: 9 hits, all the Spec/projective-Spec stalk-map compatibility
  results, not the present statement.
- `msearch.py ... leansearch "Affine differential sheaf stalk is localization of
  Kahler differentials with germ derivation compatibility"`: 8 hits, including
  `ModuleCat.Tilde.stalkIso`, `KaehlerDifferential.isLocalizedModule`,
  `StructureSheaf.stalkToFiberRingHom_germ`, and `IsAffineOpen.isLocalization_stalk`.
  Again these cover components, not the full statement.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `affine.chart.*stalk|stalk.*[Dd]ifferential|relativeDifferentials.*[Ss]talk|[Ss]talk.*relativeDifferentials`
  finds the existing smoothness criterion, special field/conormal comparisons,
  and consumers mentioning the item in docstrings, but no exact theorem.
  `rg -n lem-trf-affine-chart-stalk-differentials lean/WeilConjectures` has no hits.
  The requested exact new declaration name was also checked in Mathlib, the
  upstream/project Lean, and `dag/lean_names_upstream.json`: no prior declaration.

Validation: every compile used the prescribed `scompile.py` wrapper. The first
compile revealed the inverse-ring-map typeclass issue described above; the encoding
was repaired without changing the mathematical statement. A style warning was
fixed by wrapping the docstring. The final clean compile and `deliver2.py --no-push`
results are recorded by the delivery tool. No local/global build or direct Git
operation was used.

## Second reading by Q134

A separate in-thread rereading compared the complete node against the final module
and checked its canonical maps against the dependency sources. No other agent was
started, as the dispatcher explicitly prohibits starting agents. This section does
not claim an independent second worker; the maintainer's independent review remains
required by the assigned brief.

The binder list has exactly schemes, morphism, local finite presentation, and point.
The six chart witnesses give affine opens, containment, and the prime representing
`x`; `hWV hx` supplies the target neighbourhood condition. The finite-presentation
conjunct and contraction equality use the identical `appLE` map. Both ring equivalences
are pinned by the required germ equations, and the square uses the canonical
`Localization.localRingHom`, whose fraction formula was read directly. The
additive differential equivalence has an explicit scalar equation over `h`, and
its `da`-germ equation uses the actual sheaf derivation and the universal algebraic
derivation for that same coordinate map. The final two clauses are biconditionals,
with all natural numbers including zero in the generator clause. No flatness,
smoothness, Noetherianity, closedness of the point, freeness, or exact generator
count is silently imposed. The only implementation mismatch found on the first
pass was the semilinear inverse-instance encoding, repaired by writing its scalar
law explicitly. No mismatch with the node's mathematical statement remains.
