## Worker report

This delivery states `sk-def-purity-conv` in `Sheaf.Paper.PurityConventions` and repairs
`def-pur-section-invariant` and `def-pur-dnc-section-family` under section 1(B). The
primary declaration is `WeilConjectures.PurityConventions.coordinateKummer`. The
remaining declarations in the record are the exact coefficient comparison and its
normalization, pullback/power compatibility, torsor interpretation and the precise
regular-immersion convention needed to assemble this compound definition. Definition
data are real constructions. Only named proposition-valued statements use `sorry`.
Their docstrings give sources and full natural-language arguments.
`P.intrinsicSiteSmall` fixes the original site size to its existing object universe;
it uses Mathlib’s standard small-model theorem, avoiding an imported instance with
an unconstrained coefficient-universe parameter.

The source was read at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/_section.md`.
The node's mathematical statement is unchanged. No statement is disputed. The six
added `stmt_deps` are already landed nodes supplying the coefficient setting, affine
line, canonical root pullback, exceptional image, ordinary operations and derived
tensor; no new definition node is needed for helpers belonging to this definition.

Clause-by-clause reading, including every hypothesis:

1. The fixed global field and finite coefficient data are
   `WeilConjectures.PurityFiniteSetting`: `field`, `coefficients` (including primality
   and the different-characteristic condition), `extension`, `level`, `level_pos`.
   `P.Ring` is the actual DVR coefficient quotient and `P.Coefficient` its universe
   lift. `FiniteFieldDatum.k` is the specified algebraic closure, not an arbitrary
   algebraically closed base. `P.intrinsicCoefficientFinite` uses the published
   finiteness theorem. No freeness assumption on this coefficient ring is added.
2. Small pro-etale sites are `Scheme.ProEt.topology T` on the original `T.ProEt`,
   with object universe `u+1` and morphism universe `u`. Derived coefficients are
   `Scheme.proEtaleDerivedCategory T P.Ring`, the recorded intrinsic constant-ring
   module category with its standard derived localization. Membership in exactly
   the bounded constructible finite-Tor subcategory is `finiteTorConstructible`
   from `Sheaf.Paper.FiniteTorAmplitude`. In particular the Picard assertions below
   retain membership of BOTH the object and its inverse; mere ambient invertibility
   is not substituted for the node's assertion.
3. The existing signed twists and tensor convention are reexported from
   `Sheaf.Paper.ProEtaleTateTwists` (`ProEtale.spComplexTwist`) and
   `Sheaf.Paper.PbcCoefficientTwists` (`Scheme.pbcTateTwist`). The tensor used for
   the section and deformation objects is the actual published K-flat tensor
   `SheafOfModules.siteDerivedTensorIndependentCoefficients`, specialized to the
   intrinsic constant ring by `P.intrinsicCoefficientTensor`. Its site, coefficient
   and standard derived-localization universes are retained separately.
4. The exceptional functor in the finite-type setting is the published
   `ProEtale.sfFiniteExceptional`, through the canonical intrinsic realization of
   the finite fixed-scalar functor. `P.intrinsicDualizing` applies that functor to
   the actual coefficient unit `P.intrinsicCoefficientUnit`. The source-domain
   interface `P.sectionInvariantFinite` has `[Smooth g]`, `[IsSeparated g]` and
   `[QuasiCompact g]`, with `aB : B → Spec k`, `[LocallyOfFiniteType aB]` and
   `[QuasiCompact aB]`. Smoothness implies local finite type of g, so these say
   precisely finite type of g and B, hence V. `P.sectionCompactifiable` discharges
   compactifiability by Nagata. No pro-etale exceptional-adjoint admissibility
   hypothesis is introduced.
5. For the affine-line datum, `coordinateKummer` binds `Y`, its specified k-map
   `aY`, `[IsSeparated aY]`, `[LocallyOfFiniteType aY]`, `[QuasiCompact aY]`.
   It uses the recorded `PurityFiniteSetting.Line`, `coordinate`, `zeroSection`,
   `Punctured`, `openImmersion`, `lineProjection`, `puncturedProjection` and
   `coordinateUnit` from `Sheaf.Paper.PurityAffineLineDatum`. These are the actual
   affine line with zero-coordinate section, coordinate basic open and its global
   coordinate unit. No affine-line scheme, section or unit is supplied as arbitrary
   data. The old coefficient-dependent `coordinateKummer` in that module is NOT
   used: it requires e dividing n, which this node explicitly does not require.
6. An arbitrary positive exponent N is represented uniquely by `r : ℕ`, N=r+1.
   `finiteLine T l A r hA` is the underlying abelian sheaf of the recorded
   `Scheme.tateFiniteLine` (root module tensor A). `hA` is exactly the equation
   `(l^(r+1) : A)=0`. The generic helpers take any finite commutative A in the
   stated coefficient universe; specializing A to `P.Coefficient` is the node's
   quotient ring. This generality adds no hypothesis to that specialization.
   `finiteLineTransition_existsUnique` and `finiteLineTransition` are precisely
   the published `spFiniteKummer` with the unique ZMod quotient scalar maps, fixed
   on EVERY coefficient section and root by the canonical root power. Thus they
   retain the supplied inverse-limit Tate-twist identification and its coherence,
   rather than choosing arbitrary isomorphisms between abstract rank-one objects.
7. `defaultAnnihilator` states l^n=0 at n=`P.level`, using the identity
   `(level-1)+1=level` from `level_pos`. `coordinateKummer` uses this admissible
   exponent. `coefficientPower_isUnit` derives invertibility of every positive
   power from the k-structure and l different from the characteristic. The optional
   smaller N=n/e and equality of ideals/module freeness of rank ef are exactly the
   imported `Sheaf.Paper.PurityFiniteKummerLevel` declarations. The e-divisibility
   hypothesis occurs in that freeness result only, never in the new Kummer class.
8. The boundary in `kummer` is the actual
   `Scheme.kummerδ₀ (l^(r+1)) hT`, coming from `kummerSequence_shortExact`. It is
   followed by `Sheaf.H.map` of the recorded `kummerCoefficientInsertion` at
   `1 : A`. `coefficientModule` uses the canonical unital quotient homomorphism
   `finiteEtaleTwistScalar`, not a chosen scalar action. This is precisely root
   tensor coefficient extension; no Z/l^N-module structure on the units sheaf is
   asserted or used.
9. `kummer` next applies the canonical `ProEtale.comparisonCohomologyMap` and
   `Sheaf.H.map (coefficientComparison ...).hom`. Thus its target is precisely
   H1 of the pro-etale finite twist. `rootRestriction_existsUnique` fixes the
   direct-image root comparison by the kernel inclusions into the identical units
   on etale objects. `rootRestriction` is this uniquely determined map; its adjoint
   is restriction of roots along the inverse-image representatives. The predicate
   `IsCoefficientComparison` fixes the comparison-adjunction mate on every local
   root tensor EVERY a in A, and `coefficientComparison_existsUnique` asserts an
   actual unique isomorphism with this formula. Its proof docstring explains the
   common etale trivialization, finite-constant identification, tensor universal
   property and gluing. The definition's choice is from a UNIQUE normalized map,
   never a mere unspecified `Nonempty` isomorphism.
10. `rootTorsor` is the actual `Sheaf.Torsor.lifts` of v in the exact Kummer
    sequence: its sections are precisely local roots. `rootCover` is the actual
    `Scheme.kummerCover`, built from the monic quotient polynomial and relative
    spectrum. `rootTorsor_represented` identifies its sections naturally with maps
    over T to that constructed cover. `kummer_torsor` states existence of the
    contracted-product torsor using the recorded `ContractedProductPresentation`
    and states that its canonical class becomes exactly `kummer` after comparison.
    This retains the equivalent torsor description without replacing the class
    definition by an arbitrary torsor or arbitrary cohomology element.
11. `finiteLinePullback_existsUnique` fixes the adjoint of the coefficient pullback
    on all constant-coefficient/root tensors by the recorded canonical
    `proEtaleRootsOfUnityDirectImageMap`. `constantPullbackIso` is the canonical
    constant-sheaf inverse-image comparison. `finiteLineCohomologyPullback` uses
    exact inverse image and that constant-integer identification, followed by the
    normalized line isomorphism. `kummer_baseChange` states the actual equality
    for an arbitrary scheme map f and the pulled-back unit `Units.map f.appTop.hom v`.
    The two displayed unit witnesses merely state the inherited invertibility
    condition, not any exceptional geometric restriction. For k-schemes they are
    supplied by `coefficientPower_isUnit`.
12. `kummer_exponent_independent` states that `Sheaf.H.map` of the normalized
    power-transition identification sends the large-exponent class to the small
    one. It allows every pair r≤n for which the annihilator equations hold, including
    equality. Any two positive exponents are comparable; use this isomorphism or
    its inverse. No e-divisibility or freeness of A over either residue ring is used.
13. `PurityNormalBundle.normalCone`, `projection`, `zeroSection` are the recorded
    relative spectrum of the conormal associated graded and its augmentation.
    `ConormalGradedAlgebra.piece i 1` and `symmetricComparison i` are exactly the
    conormal sheaf and canonical symmetric-to-graded map, not arbitrary bundles.
    `IsRegularOfPureCodimension i c` binds `[IsClosedImmersion i]`, each point z of Z,
    an affine open neighbourhood U of i(z), and a list of length c which is regular
    in Γ(X,U) and generates `i.ker.ideal U`. There is no positivity condition on c
    and no condition at points outside Z. `regularNormalBundle` states locally
    free rank c of this conormal and invertibility of exactly the canonical graded
    comparison. Relative spectrum then gives the rank-c vector bundle with the
    SAME augmentation zero section, as explained in the docstring.
14. The section invariant is exactly `P.sectionInvariantFinite g aB s hs`, with
    `s : B → V`, `[IsClosedImmersion s]`, and `hs : s ≫ g = 𝟙 B`. Its body is
    `sfIntrinsicDerivedPullback ... s` applied to the exceptional image of the
    constant coefficient unit. The invertibility theorem has both tensor orders,
    the actual coefficient unit, and finiteTorConstructible membership. It neither
    fixes a relative dimension nor chooses an orientation/Tate identification.
15. `purityDncIntrinsicFamily` uses the ACTUAL
    `Scheme.Hom.deformationSpaceProj g s` and `s.deformationSpaceSection` of the
    extended-Rees construction, equivalent to the specified blowup minus the
    scheme-theoretic strict transform. `purityDncIntrinsicBase`, `Source`, `Map`
    and `Section` retain their k-structures. `Section_comp_map`, `Domain` and
    `Compactifiable` state the source-implied geometry and section identity.
    `purityDncIntrinsicFamily_pic` explicitly asserts finiteTorConstructible
    membership and an inverse with both derived tensor isomorphisms. The total
    space, maps, coefficient unit and resulting family are constructed, not supplied
    as arbitrary scheme or derived-object data.

Dependency declarations were read at their recorded source signatures/docstrings.
The principal interfaces are the modules and declarations listed above. In addition:

- Mathlib `AffineSpace`, `IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`, `RingTheory.Sequence.IsRegular`,
  and `SheafOfModules.IsFiniteLocallyFreeOfRank` are used with their ordinary meanings.
- `Scheme.rootsOfUnitySheaf`, `kummerSequence_shortExact` and `kummerδ₀` are from
  upstream `WeilConjectures.AlgebraicGeometry.Sites.Kummer`.
- `Sheaf.H`, its connecting maps and `mapFunctor` are the recorded sheaf-cohomology
  model, with naturality of the right-derived universal delta functor. Comparison
  is from `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`;
  the site functors are the recorded comparison morphism.
- The torsor class is upstream `Sheaf.Torsor.classH1`/`classH1_lifts`; coefficient
  functoriality and the contracted-product presentation are imported from the
  recorded `EtaleTorsorH1Functoriality` and `ContractedProductPresentation` modules.
- The normal-cone input uses `Sheaf.Paper.PurityNormalBundle`,
  `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` and
  `Sheaf.RingTheory.RegularSequenceGradedPolynomial`. The existing regular-bundle
  convenience predicate requiring positive codimension is deliberately not used.

Edge cases checked before writing: n=1; ramification index e=2 with n=1, where e does
not divide n but N=n is valid; two distinct positive annihilators; equal exponent
transition; the unit 1 (trivial root torsor); identity/arbitrary base change; the empty
scheme; c=0 with empty sequence, including a proper clopen component; empty Z; identity
section of a relative-dimension-zero smooth morphism; nonconstant smooth relative
dimension. The conditions in the signatures cover these cases. In particular the
regular-sequence condition is only near Z, and the Picard proof uses clopen dimension
loci rather than imposing a constant dimension.

Searches for reuse (wrapper search output is retained in searches.jsonl):

- LeanFinder: "Kummer class of a unit with finite ring coefficients obtained by root
  sheaf scalar extension and etale proetale cohomology comparison". Eight returned
  cyclotomic/ring-theoretic hits do not define the sheaf class or these conventions.
- Loogle: `AlgebraicGeometry.Scheme.kummerδ₀, CategoryTheory.Sheaf.H.map` returned no
  hit (unknown-identifier query; not counted as evidence of nonexistence).
- Mathlib grep: `kummer|Kummer` in AlgebraicGeometry returned no hit.
- LeanSearch: "Kummer class of a unit finite ring coefficients sheaf cohomology"
  returned unrelated units/root statements and the generic module-sheaf unit.
- `rg` of upstream WeilConjectures and side `lean/Sheaf` for Kummer, purity conventions,
  normal cone, section invariant, roots comparison and the item id found the concrete
  building blocks cited above. The recorded affine-line class imposes e|n, and the
  frame-class convenience module mixes retired/current imports. Neither states this
  compound general-exponent convention. Existing geometry and tensors are reused;
  only the missing normalized interfaces are supplied here. The upstream
  `Etale.HasKummerClass` supplies abstract class data and does not specify this
  boundary/coefficient/comparison composite, so it is not substituted for the datum.

## Dependency modules

`def-pur-section-invariant`: its recorded module imports retired
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso` together with the current
finite-coefficient API. The compiler reports that both declare
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`. The replacement
`Sheaf.Paper.PuritySectionInvariantIntrinsic` imports the published finite intrinsic
operations, states the same actual Ls* Rg! coefficient unit, supplies the finite-type
compactification consequence, and expresses Picard membership in exactly the recorded
intrinsic finiteTorConstructible category. Only this dependency's `lean` field changes.

`def-pur-dnc-section-family`: the recorded module imports that unusable section module.
`Sheaf.Paper.PurityDncFamilyIntrinsic` retains the same constructed DNC, k-map and
augmentation section and defines the actual family using the compatible intrinsic
section invariant. Its Picard assertion includes bounded constructibility and finite
Tor amplitude for the family and inverse. Only this dependency's `lean` field changes.
The compactifiability proposition is imported from the published
`WeilConjectures.purityDncCompactifiable` in `Sheaf.Paper.PurityDncFamily`, whose
signature is identical; the intrinsic module no longer redeclares that theorem.
The finite-stage scope agrees with the existing records; higher stages are their
specified coefficient transports, not newly chosen data.

## Second reading by Q28

The dispatcher expressly forbids starting another agent, so an independent second
worker was unavailable. This is a separate self-review of all three modules with the
source node open; the maintainer performs the independent review after delivery.

The review found and repaired three mismatches before delivery: the old affine-line
class added e|n to the general Kummer convention; the old positive-codimension
regularity predicate excluded the source's c=0 case; and using the unbounded intrinsic
section object alone omitted the required finiteTorConstructible/Picard assertions.
The new class uses N=n without e|n, the affine-local predicate includes c=0 only near Z,
and the section/deformation assertions explicitly retain finite-Tor membership and a
two-sided inverse. The comparison is normalized on every tensor coefficient, not only
on root insertion at 1. Pullback and exponent maps are fixed by their canonical root
formulas. All binding universes and variables are explicit (`autoImplicit false`).
No definition contains a `sorry`, and no class, geometric object or orientation is
chosen from an unspecified existence assertion.

The returned-delivery repair removed the duplicate `purityDncIntrinsicCompactifiable`
declaration. `PurityDncFamilyIntrinsic` now imports `Sheaf.Paper.PurityDncFamily` and
uses its existing `purityDncCompactifiable` theorem directly; the dependency node's
declaration record was updated accordingly.

Validation: the prescribed `scompile.py Q28 sk-def-purity-conv` command compiled all
three delivered files separately in dependency order, including server sandbox and
library confirmation, with exit code 0 and no warnings beyond the permitted sorry
policy. The successful result retained the original small-site object/Hom universes;
no universe equality or extra mathematical admissibility hypothesis was imposed.
