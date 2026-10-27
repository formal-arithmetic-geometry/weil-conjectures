## Worker report

The module `Sheaf.SixFunctors.TriangleProjectionNormalForm` states
`AlgebraicGeometry.ProEtale.AmbientProperOpen.triangleProjectionNormalForm`.
Every proof is postponed by `sorry`; definitions contain actual composites only.
Two named instances construct Noetherianity from the existing finite-type and
quasi-compactness theorems, so the square's quasi-compact opens are consequences,
not added hypotheses. No new DAG nodes or dependency repairs are needed.

Clause-by-clause correspondence:

- The fixed algebraic closure of a finite field is `F : FiniteFieldDatum`.
  Its `k`, `k₀`, algebraic-closure instance, cardinality and characteristic data
  are the recorded datum used by `AmbientProperOpen.Spaces`.
- The prime different from the characteristic is `(l : ℕ) [Fact l.Prime]
  (_hl : l ≠ F.p)`. The finite extension is `E`, with `Field`, `Algebra ℚ_[l]`
  and `FiniteDimensional ℚ_[l]` instances. Its valuation ring, uniformizer and
  quotients are the recorded `Padic.coefficientExtensionRing` construction.
- Positive levels are represented by `n + 1` for arbitrary natural `n`.
  `ULift.{u+1}` puts this very ring in the published module coefficient universe;
  it does not change its ring structure. `positiveCoefficientFinite` supplies
  finiteness from the recorded `finite_coefficientExtensionRing` theorem.
- The six finite-type k-schemes are `X V B Y D Z : Spaces F`, with B = Xbar,
  D = Ybar. `Spaces` is the full subcategory of finite-type objects over Spec k;
  it imposes no separatedness on their structure maps. Its morphisms are over k.
- The arrows `j b i q p s` have exactly the node's sources and targets. The three
  open immersion and three properness instances are precisely the node's
  assumptions. `h : b ≫ p = q ≫ i` is pb = iq. There is no Cartesian hypothesis.
- The finite categories are `ProperOpenDerived A T.obj.left`, the actual ordinary
  unbounded derived categories of pro-etale A-module sheaves. The system categories
  are `IntegralSystemRealization.System l E T.obj.left`, the ordinary derived
  categories of strict semilinear quotient systems, not completed integral objects.
- `ProperOpenPull`, `ProperOpenPush`, `ProperOpenShriek` and `ProperOpenTensor`
  are P, S, J and derived tensor in the finite clause. The system clause uses the
  recorded `pull`, `Operations.push`, `Operations.shriek` and
  `(calculus ...).systemClosed.tensor` on the actual simultaneous sequence site.
- `finiteInput` and `systemInput` are exactly K' = K tensor P_j P_q P_i P_s L.
  T = P_s L, U = P_i T and M = J_j K are expanded directly in both words.
  The unused shorthand f=qj and g=si introduces no additional mathematical data.
- `finiteC` is `(ordinary F A).sComp p s` followed by direct image of
  `properOpenShriekComp j b`; this is the C formed from c and e. At components
  the functor associators are definitional. `systemC` uses the recorded conjugate
  `z.compositors.pushComp` and `z.compositors.openComp` in exactly this order.
- The finite gamma is `properOpenMate`, the canonical clopen alpha's proper mate,
  definitionally the `ordinary` calculus's `gamma`. The system gamma is the
  intrinsic `z.properOpen.gamma`, normalized by its open adjunct characterization
  and its canonical bridge to the simultaneous construction.
- Finite pi is `properOpenProjection`, the published counit-defined projection;
  system pi is `properProjection`. Finite delta is `properOpenTensorIso.hom`;
  system delta is `z.openComparisons.projection.hom`, with its specified open-unit
  transpose. These are existing maps, not arbitrary comparison parameters.
- `finiteLeft`/`systemLeft` list in Lean's left-to-right composition convention:
  pi_s, S_s(delta_i), S_s J_i(pi_q followed by S_q(delta_j)), S_s(gamma at J_j K'), C.
  Thus the last two factors are precisely alpha at K'.
- `finiteRight`/`systemRight` list: S_s(gamma_M) tensor identity, pi_s at S_p J_b M,
  S_s(pi_p), S_s S_p(delta_b followed by J_b(delta_j)), C. Between delta_b and
  J_b(delta_j) the canonical inverse pullback-square comparison transports
  P_b P_p T to P_q P_i T. This is the identification expressly required by the
  node, and is the only comparison inverted in the normal word.
- The endpoints of both words are G F K tensor L and H K'. `finiteC` explicitly
  records its target S_(sp) J_(bj); the system compositor has the same target.
  The two tensor functors are curried/product presentations respectively, each
  retaining the node's parenthesization, so no tensor rebracketing is suppressed.
- The conclusion is the conjunction of the finite equality for all K,L and the
  system equality for all K,L and every canonical operation presentation o,z.
  These presentations include derived universal certificates, normalized open
  adjoints and intrinsic gamma; they add no conditions on the input objects.
  The realization existence is supplied by the imported dependency framework.
  Naturality is inherited from the displayed natural transformations and their
  whiskerings; the universal component equality is their equality by extensionality.
  No evaluation, total limit, projection inverse, Tor bound, constructibility or
  boundedness hypothesis occurs.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the imported actual quotient and
  transition definitions in `CoefficientExtension`.
- `Sheaf.SixFunctors.AmbientProperOpenPasting`: `Spaces`, `ordinary`, `Calculus.sComp`,
  `Calculus.jComp`, `Calculus.gamma`, `positiveCoefficientFinite`; the latter
  supplies the positive-level ring instance. `ambientProperOpenPasting` identifies
  these with the prescribed normalizations in the two ambient settings.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`: `ProperOpenDerived`, `ProperOpenPull`,
  `ProperOpenPush`, `ProperOpenShriek`, `ProperOpenTensor`, `properOpenProjection`,
  `properOpenTensorIso`, `properOpenMate`, `properOpenPullSquareIso`,
  `properOpenShriekComp`; proof dependencies `properOpenProjectionMate` and
  `properOpenProjectionMateSystems` implement the inner substitution.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `openTensorNormalization` and its
  normalized open comparison interfaces, used by the proper/open dependencies.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, `AdjunctionEvaluation`, `evaluation_mate`, providing
  simultaneous operations on actual module systems. No equality-detection by
  evaluation is used.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the counit projection convention
  `compactificationProjectionFromData`, `ExchangeProjectionStage.projection`.
  The actual finite and system maps use this same published adjunction projection.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` (publicly available
  through the proper/open dependency): `Operations`, `Realizations`, `properProjection`,
  `System`, `pull`, `calculus`, `Compositors.pushComp`, `Compositors.openComp`,
  `Compositors.square`, `OpenComparisons.projection`, `ProperOpenCoherence.gamma`.
- `Sheaf.Paper.RingedProjectionTensorComposition`:
  `SheafOfModules.ProjectionCoherence.ringedProjectionTensorComposition`, whose
  first-variable naturality gives the outer substitution.
- Mathlib `AlgebraicGeometry.Noetherian`: `LocallyOfFiniteType.isLocallyNoetherian`,
  `IsNoetherian`, `IsNoetherian.noetherianSpace`,
  `quasiCompact_of_noetherianSpace_source`; `QuasiCompact.compactSpace_of_compactSpace`
  from the quasi-compact morphism module. The scheme-property dependency is an
  explicitly documentary collection with no notion or Lean record of its own.

Edge cases checked: n=0 in the parameter means the valid coefficient level A_1;
all positive levels occur, with no A_0 substitution. Empty open immersions and
zero K or L are permitted by the existing exact extension and tensor definitions.
Identity arrows use the same canonical conjugate compositors, without selecting
special comparison maps. Nonseparated finite-type structure maps remain permitted;
properness belongs only to q,p,s. Systems need not be cartesian or normalized.
Arbitrary unbounded objects and every adjacent quotient transition remain present.
There is no disputed statement or statement correction.

Searches (2026-10-23): `msearch.py leanfinder` with “Expanding compact support
projection through a proper open square gives the counit tensor triangle normal
form” returned eight unrelated condensed, coalgebra and Dold–Kan results;
`msearch.py loogle` with `CategoryTheory.Adjunction.counit_naturality,
CategoryTheory.NatTrans` returned zero; `msearch.py grep` with
`projection.*normal[Ff]orm|triangle.*projection` returned zero.
`msearch.py leansearch` with “naturality of the counit defined projection formula
under proper open interchange” returned generic adjunction counit naturality and
other generic counit results, not the specified formula. Source `rg` searches for
`triangleProjection|triangle.*[Nn]ormal|Triangle.*Projection` in both
`lean/WeilConjectures` and `lean/Sheaf` found no statement of this formula; the
broader matches concern unrelated support/cohomology triangles. The exact node id
has no upstream Lean occurrence. Existing proper/open and projection declarations
were reused rather than restated.

## Second reading by Q136

The dispatcher explicitly assigns a single worker and forbids starting other agents;
the maintainer supplies the independent review. A separate self-check compared
all clauses above against the node and reopened both word definitions. It found
that P_b P_p T and P_q P_i T need the inverse square comparison, which is now
explicit between delta_b and J_b(delta_j). It also checked C's compositor order,
alpha's argument J_j K', the first projection's argument J_i S_q J_j K, and the
right word's outer projection argument S_p J_b J_j K. Both versions use all six
schemes and the correct canonical mate; neither adds quasi-compact-open binders,
a Cartesian condition, or a normalized-system condition. This is a self-check,
not a claim that an independent worker reviewed the delivery.
