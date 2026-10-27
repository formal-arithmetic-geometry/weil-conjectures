## Worker report

The module `Sheaf.Paper.ExceptionalDualizingBaseChangePasting` states
`AlgebraicGeometry.ProEtale.exceptionalDualizingBaseChangePasting`, with proof `sorry`.
Its supporting definition `exceptionalDualizingBaseChangePastingEquation` expands the
requested equality into the actual specified canonical maps. There is no postponed
definition data and no additional postponed theorem.

The source read was the current blueprint (`literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-composition.proof.md`), especially
its final arbitrary-base-change sentence. The detailed node supplies the normalization
which that sentence abbreviates. Stacks `more-etale.tex`, Tag 0F7L,
`lemma-base-change-shriek`, states compatibility with the compositor of Tag 0F7J.
The full five-step DAG proof is included, in order, in the theorem docstring.

Hypotheses and clauses, matched individually:

- The finite-field, characteristic, unequal prime, finite coefficient extension,
  valuation quotient, canonical uniformizer and positive level are precisely the recorded
  `P : WeilConjectures.PurityFiniteSetting.{u}`. `P.Coefficient` is the existing
  `ULift` of `P.Ring`, not a substitute coefficient ring. No ramification-index
  divisibility condition is imposed.
- Each of X, Y, Z, X', Y', Z' has an `Over (Spec (.of P.field.k))` structure and
  `LocallyOfFiniteType` and `QuasiCompact` structure morphism. These are precisely
  finite-type k-schemes; absolute separatedness is never imposed.
- The seven arrows f, g, f', g', s, h, t have the stated endpoints and individual
  `IsOver` instances, hence are k-morphisms. The two original arrows have
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` instances, exactly
  separated finite type. No property of t beyond being a k-morphism is assumed.
- `sqf : IsPullback s f' f h` and `sqg : IsPullback h g' g t` present the two
  cartesian squares. They identify Y' with Y times_Z Z', and their vertical paste
  identifies X' with X times_Z Z'. Presenting fibre products by their universal
  property includes every literal fibre product and every choice of its canonical
  isomorphic presentation. The outer square is literally `sqf.paste_vert sqg`.
- `cf`, `cg`, `cfg` retain the three compactifications specified by the node.
  The equation installs their `hasCompactification` instances and those of
  `cf.ofIsPullback sqf`, `cg.ofIsPullback sqg`, and
  `cfg.ofIsPullback (sqf.paste_vert sqg)`. Thus the primed choices really are
  the base-changed compactifications, not unrelated choices. The two needed
  primed quasi-compactness instances are derived by `MorphismProperty.of_isPullback`.
- The domains are the same small-site fixed-ModuleCat finite coefficients already
  used by the recorded cohomological-smoothness and base-change interfaces.
  `comparisonUpperStar ... X' |>.mapDerivedCategory` maps the displayed morphisms
  into the actual small pro-etale derived category. These are canonical etale-origin
  coordinates, not an assertion about an arbitrary endpoint isomorphism. Both
  endpoints are the recorded Dctf objects; since that subcategory is full, equality
  of their ambient morphisms is exactly equality of Dctf morphisms.
- The left side is comparison pullback of
  `Etale.dualizingComplexBaseChangeMap P.Coefficient (sqf.paste_vert sqg)`:
  exactly beta_{gf,t} from the recorded `finiteComparedBaseChangeClause`.
- The first right-side factor is comparison pullback of derived pullback along s
  of `(finiteExceptionalComposition P.Coefficient f g).hom.app (𝟙_ _)`:
  exactly Ls*(c_{Lambda_Z}).
- The second factor is the recorded `standingExceptionalBaseChangeCompared P sqf
  cf (cf.ofIsPullback sqf)` evaluated at
  `Etale.dualizingComplex ... g`: exactly b_{f,h;omega_g}. This declaration is
  comparison pullback of the mate of the inverse of the specified proper/open
  compact-support exchange, not an unconstrained map supplied by a hypothesis.
- The third factor is comparison pullback of the exceptional functor along f'
  applied to `Etale.dualizingComplexBaseChangeMap ... sqg`:
  exactly G_{f'}(beta_{g,t}).
- The final factor is comparison pullback of
  `(finiteExceptionalComposition P.Coefficient f' g').inv.app (𝟙_ _)`:
  exactly c'_{Lambda_Z'} inverse. The existing definition is `conjugateIsoEquiv`
  of the specified `Etale.unboundedEtaleLowerShriekCompIso`, with the actual etale
  adjunctions. This is the normalized compositor of `standingExceptionalComposition`
  computed in the same etale-origin coordinates. Its data do not use an arbitrary
  `Nonempty` choice or either tensor-formula hypothesis.
- `Etale.dualizingComplexBaseChangeMap` includes the action of G' on
  `leftDerivedUpperStarUnitIso ... .hom` by definition, so the coefficient-unit
  pullback identifications on both beta maps are included explicitly by that API.
  The final source and target are comparison pullback of Ls* omega_gf and omega_g'f'.
- The equation contains the specified four factors in Lean's left-to-right
  composition order. It asserts equality, not just invertibility. There is no
  assumption of cohomological smoothness, either tensor formula, an inverse
  dualizing object, an invertible beta or b, or an ambient pro-etale adjunction.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its `Ring` and `Coefficient`, imported directly.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the recorded finite-Tor predicates,
  including `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`.
  The unit and exceptional images are in this domain by the cited proof inputs;
  the equation is written in its fully faithful ambient inclusion.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded derived operations; the
  finite comparison-coordinate pullback used here is the exact inverse image's
  left derived functor, as in the recorded canonical map interface.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and
  `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: the transported exceptional
  functor `sfFiniteExceptionalAt`, whose etale-origin value is comparison of the
  ordinary etale exceptional image.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `finiteComparedDualizing`, `finiteComparedBaseChangeClause`, which specify the
  comparison-coordinate beta used here, imported directly.
- `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`,
  the actual base change with its proper and open factors, imported directly.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, the recorded
  proper-then-open exchange underlying the counit mate.
- `Sheaf.Paper.ConstructibleTensorComposition`: its unconditional compositor
  construction in `CompactSupportTranspose.conjugate` and `conjugateInv` (via
  `CompactSupportCompositeTransposeDomains`). No use is made of the conditional
  tensor-isomorphism conclusions of `constructible_tensor_composition`.
- `Sheaf.Paper.StandingExceptionalComposition`: `standingExceptionalComposition`,
  the normalized double transpose. The coordinate compositor is the already
  landed `WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition` from
  `Sheaf.Paper.PurityFiniteExceptionalComposition`. Its existing definition node
  `def-pur-finite-exceptional-composition` is added to stmt_deps; nothing is redefined.
- `Sheaf.Paper.StandingExceptionalBaseChangeCompared`:
  `standingExceptionalBaseChangeCompared`, used directly at omega_g.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`:
  `Etale.rightDerivedUpperShriekBaseChangeMap` and
  `Etale.dualizingComplexBaseChangeMap`, whose full definitions fix the inverse
  compact-support-exchange mate and the coefficient-unit normalization.

All recorded proof-dependency modules with a Lean record are imported as proof
imports unless already publicly imported for a statement dependency. The two
pure mate-calculus nodes are Mathlib leaves: `lem-weil-pbc-mate-pasting` records
`mateEquiv_vcomp`, `mateEquiv_hcomp`, `mateEquiv_conjugateEquiv_vcomp` and
`conjugateEquiv_mateEquiv_vcomp`; `def-weil-pbc-adjunction-conjugate` records
`CategoryTheory.conjugateEquiv` and `conjugateIsoEquiv`. Their recorded module
`Mathlib.CategoryTheory.Adjunction.Mates` is imported as a proof dependency.

Edge cases checked before writing: identity f or g, identity t, zero objects,
empty X and empty base, and a non-separated finite-type base. No dimension integer,
nonemptiness, absolute separatedness, or arbitrary exchange-isomorphism hypothesis
enters the statement. Pullback squares handle all these cases. At identity base
change the beta maps still carry their canonical unit maps; nothing was replaced
by strict identity. Positive level n = 1 is covered without an extra divisibility
assumption. The coefficient module universe is u+1, and both sites have the
existing object/morphism universe convention; no universe equality was imposed.

Searches actually run for an existing statement:

1. msearch leanfinder: "Canonical exceptional dualizing base change mate under
   composition of separated finite type morphisms". Eight results, including
   `Scheme.Modules.conjugateEquiv_pullbackComp_inv`, ordinary module pullback
   composition and geometric base-change stability; no exact statement.
2. msearch loogle: `"mateEquiv_hcomp"`. The ordinary categorical and bicategorical
   general mate-pasting lemmas exist; neither states this normalized pro-etale beta
   identity.
3. msearch grep in Mathlib CategoryTheory:
   `mateEquiv_hcomp|rightDerivedUpperShriekBaseChange`. Seven hits, all general
   adjunction/bicategory mate calculus; no scheme exceptional beta statement.
4. msearch leansearch: "The canonical exceptional inverse image base change map
   of a composite is the composite of counit mates". Eight general category and
   ordinary module hits, no exact match.
5. rg in WeilConjectures and Sheaf for the node id, exceptional pasting, dualizing
   base-change, and composition/base-change. No occurrence of the item id in the
   upstream sources. The upstream `UpperShriekCanonicalMapsComposition` theorem
   `isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff` only relates invertibility,
   so cannot be recorded as this equality. `SmoothExceptionalTensorPasting` states
   a tower equation bundled with tensor compatibility for separated vertical maps;
   that is a different domain and additional conclusion, not an exact match.
6. The compositor-name search found the existing
   `Sheaf.Paper.PurityFiniteExceptionalComposition` and its definition node. This
   exact existing construction is reused, without introducing another compositor.

No statement correction, disputed assertion, new node, or dependency repair was needed.

Validation: scompile.py compiled the delivered module in sandbox and library modes
with no errors or non-sorry warnings. Delivery preflight and final compile follow.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
