## Worker report

Item: `lem-trf-monoid-chart-characteristic-fan`, group Q51, stage 2.

The module `Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFan` states
`AlgebraicGeometry.monoid_chart_characteristic_fan`, with its proof entirely `sorry`.
Three helper definitions give the actual unit face, bundle the existing characteristic
sheaf as a monoidal space, and give its canonical quotient-and-sheafification section map.
Their data contain no `sorry`, choice of a map, or existence-based object construction.
They belong to the fixed-chart notion of this item; the quotient and sheafification
notions themselves are reused from `def-trf-fine-fan-blowup`.

Source read: ILO PDF, printed pp.98--100 (PDF pp.104--106), especially 3.1.1--3.1.10;
printed pp.106--108 (PDF pp.112--114), especially 3.3.2, 3.3.4(ii), and 3.3.12.
Section 3.3.12 explicitly states that sharpening a monoscheme chart is a fan chart.
The node's six proof steps are included, with their dependency names and the
pushout, localization, basis-gluing, germ-isomorphism and restriction arguments.
No statement correction and no statement dispute were necessary.

Hypotheses and every clause of the statement:

- Locally Noetherian fs log scheme `(U,M,alpha)` is
  `X : FineSaturatedLogScheme.{u}`. Its fields are the given scheme, its
  `IsLocallyNoetherian` witness, its actual étale log structure and its fs-chart condition.
  No log regularity, integrality of the scheme, or torsion-free chart is assumed.
- The fine saturated chart monoid is `Q : Type u`, `[CommMonoid Q]`, and
  `hQ : IsFineSaturatedMonoid Q`. Multiplicative notation replaces the node's additive
  notation: `1` is `0`, products are sums, and group inverses are negatives.
- The prescribed global chart is `c` and `hc : X.logStructure.IsChart ... c`.
  Sections are evaluated at `Scheme.Etale.mk (top : X.scheme.Opens).ι`.
  This is a final object of the small étale site, canonically isomorphic to the identity
  étale object, so it is precisely global log sections, without restricting the chart.
- `S(Q)` is exactly `FineFan.affine Q`, from the recorded dependency. It uses
  `MonoidPrime Q`, the existing spectrum topology, and the sheafified unit quotient
  of the existing monoid spectrum sheaf.
- `E_u` is `X.logStructure.globalChartUnitFace c x`. This is the preimage submonoid
  of `IsUnit` under the composite of `c`, the given `alpha`, the top-open ring
  isomorphism, and the ordinary ring germ at `x`. The formula uses no residue-field
  or geometric-ring substitute for the ordinary local ring in the node.
- The associated Zariski log structure is the existential `Z`; the comparison map
  is `e : Z.toZariskiPrelogStructure.EtaleMap X.logStructure`, with `e.IsAssociation`.
  This is the recorded universal property of association, not just an arbitrary
  isomorphism of underlying monoids. The chart `z`, `Z.IsChart top z`, and
  `(e.sectionMap top).comp z = c` keep the original chart and structure map.
- The node's `overline M` is `Z.characteristicMonoidalSpace.presheaf`, namely
  `(FineFan.sharpSheaf Z.monoidSheaf.obj).obj`. The log axiom identifies the units
  of the log sheaf with the inverse image of `O^times`; thus this existing
  sectionwise unit quotient followed by sheafification is exactly the characteristic
  sheaf of the Zariski log structure specified in the node.
- The local morphism is `f : Z.characteristicMonoidalSpace -> FineFan.affine Q`
  together with `FineFan.IsLocalMorphism f` and sharp source stalks.
  Its point formula is `q in (f.hom.base x).carrier iff q notin globalChartUnitFace c x`.
  As `MonoidPrime` is a structure extending an ideal, this equality of membership
  determines the prime as the complement of the given face.
- The sheaf map is induced by the original chart: the equation involving
  `FineFan.stalkMap f x (FineFan.affineGerm ... q)` identifies it with the actual
  characteristic germ of `z q`. Every localized and sharpened section is determined
  by these numerators. This normalizes the whole sheaf map, not only its point map.
- The inverse-image sheaf map is an isomorphism: the clause
  `forall x, Function.Bijective (FineFan.stalkMap f x)` is its exact stalk criterion.
  The stalk of the inverse-image sheaf at `x` is the target stalk at `f x`; hence these
  are the stalk maps of the adjoint inverse-image map. A map of monoid sheaves is an
  isomorphism exactly when its underlying set-sheaf maps are bijective on stalks.
  The theorem's proof docstring gives the germ-lifting, uniqueness and gluing argument.
  This avoids imposing an unrelated `HasColimits CommMonCat` assumption just to use
  Mathlib's more general inverse-image functor API. It is the same mathematical
  assertion, not merely bijectivity of the direct-image section maps.
- The ordinary characteristic stalk identification is the family `a x` of monoid
  equivalences to `Associates (Algebra.faceLocalization Q (globalChartUnitFace c x))`.
  `faceLocalization` is the actual submonoid `Q-E` of `Q^gp`. Face sharpening identifies
  its units with `E^gp`, so its `Associates` is exactly `Q_E/E^gp`. The numerator clause
  requires `r.val = GrothendieckGroup.of q` and sends the chart germ to `Associates.mk r`.
  This specifies the canonical quotient identification rather than an abstract equivalence.
  Composing `a x` with the bijective `FineFan.stalkMap f x` identifies the fan stalk
  at `c_Q(x)` with the same quotient, with the same normalization.
- Every geometric point is quantified by `Omega : Type u`, `[Field Omega]`,
  `[IsAlgClosed Omega]`, and `t : Spec (.of Omega) -> X.scheme`.
  The point underneath it is `t default`, as in the recorded étale-stalk API.
  `b Omega t` identifies the actual `X.logStructure.characteristic t` with the same
  ordinary-unit-face quotient. The equation for every open `V`, pointed lift `w`,
  membership proof `hx`, and log section `s` says that `b` after the genuine comparison
  section map `e.sectionMap V` equals `a` on its actual characteristic germ.
  Thus `b.symm` composed with `a` is the canonical comparison and is an isomorphism.
- Restriction compatibility is the `forall W` clause. The equivalences `aW` identify
  the actual stalks of the restricted characteristic sheaf with the same quotients.
  Their equation with `FineFan.stalkMap (characteristicMonoidalSpace.ofRestrict ...)`
  is the commuting restriction diagram for all elements. The next equation uses the
  same global geometric equivalence `b`, all `V <= W`, and all actual local log
  sections, so the comparison also commutes with restriction; it does not introduce
  a second independently chosen geometric comparison. The fan morphism restricts
  by composition with this same `ofRestrict`, including its sheaf map and point map.
- The final `forall p : FineFan.MonoidPrime Q` clause ranges over every fan stalk,
  whether or not `p` occurs in the image of the scheme. Saturation is the existing
  `PowSaturated` predicate on the image in the actual group completion (the convention
  in `FineFan.Fan.IsSaturated`). The quantified implication `0 < n -> g^n = 1 -> g = 1`
  is torsion-freeness of that completion, matching `FineFan.Fan.IsTorsionFree`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtalePrelogStructure.germ`,
  `EtaleLogStructure`, `EtaleLogStructure.IsChart`, `EtaleLogStructure.characteristic`,
  and `FineSaturatedLogScheme`. Read their full signatures and source docstrings;
  also read the node's main recorded `IsSaturatedLogBlowup` declaration.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `FineFan.affine`, `sharpSheaf`,
  `sharpPresheaf`, `MonoidPrime`, `IsSharp`, `stalk`, `germ`, `affineGerm`, and
  `IsLocalMorphism`. The spectrum and quotient constructions, all relevant signatures
  and docstrings, and the node's main recorded `SmoothFunctorialDesingularization`
  declaration were read.
- `Sheaf.AlgebraicGeometry.ZariskiLogStructure`: `ZariskiLogStructure`,
  `ZariskiLogStructure.IsChart`, `ZariskiPrelogStructure.EtaleMap`, and its
  `IsAssociation`. Its already-landed definition node `def-trf-zariski-log-structure`
  is added to `stmt_deps`; it is reused unchanged, not restated.
- `Sheaf.TraceFormula.FaceLocalizationFs` (exposed through FineFanBlowup):
  `Algebra.faceLocalization`. `IsFineSaturatedMonoid` and `Associates` are reused
  through the recorded fs and fan modules, not copied.
- Plain proof imports are the recorded modules for
  `zariski_prelog_logification_comparison`, `associatedLog_universal_stalks`,
  `affineFan_localization_sections`, `face_sharpening`, `constantSheaf`, and
  `GeometricMorphism`. The commutative-monoid-sheafification node is a Mathlib match;
  its `mathlib_match` cites sheafification and preservation of the forgetful functor,
  already imported by these proof dependencies. It needs no new module.

Edge cases checked before writing and checked again against the statement:

- Empty scheme: no geometric-point or nonempty-scheme hypothesis occurs. The
  all-prime assertion about `S(Q)` remains present, rather than becoming vacuous.
- Empty open: the restriction clause includes it. Its pointwise conditions are
  vacuous, as appropriate for the unique monoid-sheaf sections on the empty open.
- Trivial monoid and rank zero: permitted; no generator or positive-rank assumption.
- A chart monoid that is a group, including a finite torsion group: permitted by
  `IsFineSaturatedMonoid`. The sharpening and every characteristic stalk are trivial,
  so no false torsion-free assertion about the *unsharpened* completion is made.
- All chart elements are local units: `E=Q` and the image prime is empty, which the
  existing `MonoidPrime` definition explicitly permits.
- No chart element outside units, zero-valued/noninjective structural maps, and
  arbitrary residue characteristics: no extra exclusion or injectivity is imposed.
- Restriction includes the whole open and arbitrary nested opens. It retains the
  same geometric comparison `b`, rather than choosing an unrelated isomorphism.
- Site, monoid, stalk and geometric-field universes follow the recorded `u`-small
  log-structure interface; every universe and variable is explicitly bound.

Searches for existing notions/statements:

1. Prescribed msearch `leanfinder` query: "A global fine saturated monoid chart induces
   a characteristic fan chart and identifies Zariski and geometric characteristic stalks".
   Result: 8 hits, including `AlgebraicGeometry.over_def`, `instIsPreimmersionFromSpecStalk`,
   `Scheme.toSpecGamma_base`, `SpecToEquivOfLocalRing_eq_iff`, and ordinary scheme-stalk
   maps. Read the returned signatures; none is a logarithmic fan chart comparison.
2. Prescribed msearch `loogle` query `"LogStructure"`: 0 hits.
3. Prescribed msearch `grep` query `LogStructure|MonoidalSpace|KatoFan`: 0 Mathlib hits.
4. Prescribed msearch `leansearch` query: "A fine saturated logarithmic chart has
   characteristic stalk equal to localization at its unit face modulo units".
   Result: 8 ordinary scheme/module localization hits, including
   `StructureSheaf.IsLocalization.to_stalk`, `StructureSheaf.stalkIso`, and
   `ModuleCat.Tilde.stalkIso`; none gives the logarithmic statement.
5. `rg` in `lean/WeilConjectures` for the node id and for the log/fan notions found
   no existing version. `rg` in `lean/Sheaf` found and led to reading the actual
   fine-fan, fs-log, Zariski-log, Zariski logification, affine localization,
   LogFanChartBlowup, ZariskiFsMonoidChart, and FanChartLocalMonoidLift modules.
   The latter existing theorems concern local chart existence or downstream fan
   blowups, not this fixed given chart. Their étale-restriction sharpSpace is not
   substituted for the node's specified Zariski-log characteristic sheaf.
6. Exact-name `rg` across Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no
   previous `globalChartUnitFace`, `characteristicMonoidalSpace`,
   `ZariskiLogStructure.characteristicSection`, or `monoid_chart_characteristic_fan`.
   No new independent notion or new definition node is required.

Validation: scompile.py compiled the delivered module separately in both sandbox
and library mode, cleanly. The first compile diagnosed the stalk-dependent unit-face
helper as noncomputable; it was marked `noncomputable`, without changing its data.
All later statement elaboration succeeded. No definitions or tests were added to
or compiled in the shared read-only checkout, and no direct Git commands were run.

## Second reading by Q51

The dispatcher forbids starting other agents; the maintainer supplies the independent
review after direct delivery. This section records Q51's own second pass, not an
independent worker review. Reopened the node and final module and checked the
hypothesis/clause correspondence above. In particular: the chart uses the final
open subscheme with the canonical `topIso` in the ordinary ring germ; `e` is an
association, the point map is the original unit-face complement, all map normalizations
are equations on actual germs, the inverse-image assertion is the exact stalk criterion,
and the last quantifier is over all fan primes. During this pass the original
open-compatibility draft used a separately existential geometric equivalence `bW`.
It was replaced by the shared global family `b` and an explicit equation with the
restricted stalk maps, making preservation of the same comparison unambiguous.
The original node statement, proof plan and proof dependencies remain unchanged;
only its Lean record and the additional already-landed definition dependency change.

The prescribed deliver2.py --no-push dry run passed server preflight and both
per-file compilation modes (dry-run commit e53af6d70a3). A final local text check
confirmed the exact signature record, one theorem-only sorry, and no Lean line
longer than 100 characters.
