## Worker report

Item: sk-prop-sfb-qlbar-colimit-x. Module:
Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients. Main declaration:
AlgebraicGeometry.ProEtale.sfb_completed_coefficients.

The declaration states all three comparisons through universal properties. The only
postponed proof is the main theorem, whose docstring gives the complete nine-step
DAG argument (grouped into seven paragraphs). All other declarations construct the
diagrams, canonical scalar maps, coefficient inclusions and module structures, or
expand the first two comparison clauses as a Prop. There is no selected isomorphism
or other data chosen from the theorem, and no new coefficient-ring construction.
The node's statement, dependencies, proof, and other existing fields are unchanged.

Hypothesis and clause correspondence:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. No characteristic, finiteness, separation,
  Noetherian, nonemptiness or quasicompactness condition is imposed on a scheme.
- A finite subextension E in the fixed algebraic closure: the first conjunct binds
  `E : PadicAlgCl.FiniteIntermediateField ℓ`, the framework's actual intermediate
  fields in `PadicAlgCl ℓ`, with their inherited absolute-value topologies.
- Its ring of integers and an arbitrary uniformizer: `PadicAlgCl.integers ℓ E`,
  `π` in that ring, and `maximalIdeal = Ideal.span {π}`. The theorem includes every
  uniformizer; it does not choose a special one.
- Pullback from the point and transported ring structures: `coefficientRing`,
  `condensedRingObj`, and `(upperStarFromPoint X).mapMon` are the recorded upstream
  constructions. `sfbPullbackFromPoint` is their recorded project alias, whose
  module is imported. All sheaves use the small pro-etale site, with object
  universe u+1, morphism universe u, and abelian groups in universe u+1.
- The first displayed isomorphism: expand `SfbCompletedCoefficientComparison`.
  The existential `ρ` is a cone of ring objects whose vertex is the actual
  condensed integer ring. Its legs, after precomposition with
  `sfbConstantToContinuous`, are exactly the sheafified quotient homomorphisms
  `Ideal.Quotient.mk (I ^ n)`. The reductions in the tower are the actual quotient
  factors. The cone pulled back by `p_X^*` is a limit in ring objects. Its diagram
  is isomorphic, as an entire diagram of ring objects, to the standard constant
  quotient diagram `sfbCoefficientQuotientTower R I ⋙ sfbConstantRing X`.
  Thus uniqueness of limits supplies the required comparison isomorphism with
  the same reductions. The maps on the point are normalized on all constants,
  equivalently on singleton test objects; naturality determines the reductions
  on arbitrary profinite test objects. No preservation of arbitrary limits by
  inverse image is asserted.
- The constant finite quotients: `sfbConstantRing X` is precisely
  `RingCat.toMonAb ⋙ (constantSheaf ... Ab).mapMon`. By the recorded monoidal
  constant-sheaf construction and constant/forget compatibility this is the
  ordinary constant sheaf of rings. `sfbCoefficientQuotientTower` uses
  `R / I^n` with `I = span {π}`, hence `O_E / π^n`; the ring maps are quotient
  reductions. The natural diagram isomorphism identifies their pulled-back
  point versions with these actual constant sheaves, rather than merely saying
  that each term is locally constant with unspecified value.
- The second displayed isomorphism: the sequential diagram consists of the
  regular integer module and `ℓ • identity` as module morphisms. Its cocone
  vertex is the actual coefficient field, restricted along the actual integer
  inclusion `padicIntegersToPadicSubfield X ℓ E`. The expanded property takes
  this existing family of ring maps as data, and the main theorem supplies the
  canonical inclusion explicitly (no arbitrary-map hypothesis is added). The zero-th leg equals the pulled-back inclusion. The colimit
  universal property is in `CategoryTheory.Mod`, not in unital ring maps.
  Multiplication by ell on the vertex is invertible. Cocone compatibility then
  uniquely specifies the m-th leg as `ell^(-m) phi`. The final clause of the
  expanded property says that every ring homomorphism from the integers to a
  ring object in which ell is invertible factors uniquely through this same
  field ring. This is the localization ring structure on the module colimit,
  and determines the displayed isomorphism with its structure map.
- The third displayed isomorphism: `sfbFiniteSubfieldRingDiagram` is the existing
  finite-subfield diagram lifted to ring objects with `Mon.ofHom`.
  `sfbFiniteSubfieldRingCocone` has vertex `Profinite.padicAlgClRingObj ℓ` and
  precisely the existing inclusion legs. Its image under `p_X^*.mapMon` is
  asserted to be a colimit of ring objects. In particular the result is about
  sheaves of rings, rather than only their underlying additive groups.
  The index is the actual directed, nonempty set of finite subextensions.
- Every inverse image: the integral clause explicitly says the mapped limit
  cone is still a limit under every `f : X ⟶ Y`. Because this is the cone
  pulled back from the point, `upperStarFromPointComp` identifies its vertex,
  reductions and ring structure with the cone over X. The rational clause
  gives the commuting square for every m-th leg using the same canonical
  `condensedPullbackHom`. For the field colimit the mapped cocone is a colimit,
  and the last conjunct gives the commuting square on every finite-field leg.
  Monoidality of the recorded composition comparison supplies the ring
  structures in these identifications. The first two naturality clauses are
  inside the expanded property, so they apply also to the Z_l specialization.
- E = Q_l: a separate conjunct instantiates the entire completed comparison
  property with actual `PadicInt` and `Padic`, `I = span {ell}`, and
  `PadicInt.Coe.ringHom`. The following conjunct gives a natural isomorphism of
  the entire quotient tower with the tower `ZMod (ell^n)`, normalized by
  `PadicInt.toZModPow` on every integer. This records compatibility with
  reductions explicitly and supplies the final displayed ZMod formula.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `sfbPullbackFromPoint`, its right adjoint and specification theorem. The alias
  unfolds to the `upperStarFromPoint` used by the recorded coefficient rings.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `upperStarFromPoint`, `coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, and `upperStarFromPointComp`, `coefficientPullbackIso`,
  `condensedPullbackHom`, with the monoidal and ring-map instances. This is the
  dependency record for sk-def-sfb-pulled-back-coefficients.
- The closed upstream declaration records for sk-def-sfb-condensed-ring and
  sk-def-sfb-qlbar-condensed are used directly, without re-recording these nodes:
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`,
  `continuousMapRingSheaf`, `continuousMapRingObj`, `continuousMapRingSheafMap`;
  and `.Condensed.EllAdic`, `padicIntegersCondensedRing`, `padicIntegersRingObj`,
  `padicAlgClCondensedRing`, `padicAlgClRingObj`. Their source docstrings and full
  signatures were read in the published shared framework. In particular Qbar
  means finite-subextension-valued maps, not all continuous Qbar-valued maps.
- `Mathlib.NumberTheory.Padics.PadicNumbers`, `Padic`; `.PadicIntegers`,
  `PadicInt`; `.RingHoms`, `PadicInt.toZModPow`, `ker_toZModPow` and
  `zmod_cast_comp_toZModPow` implement def-weil-l-adic-numbers.
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` was
  read with `scompile.py --source`, because its current source is missing from
  the local source trees. Its `padicIntegersRingObjToContinuousMapRingObj` and
  `padicIntegersToPadicSubfield` are the exact point and scheme inclusions of
  def-sfb-integers-to-subfield-point and def-sfb-integers-to-subfield, named in
  their upstream audit records. The main theorem uses the latter directly;
  the generic map helper is used for the separate actual Z_l-to-Q_l case.
- Existing finite-field inclusions, diagram and additive colimit were read in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`
  and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
  Their additive colimit is only one clause of this node and is not a match for
  the full statement. It is reused, not restated as a second additive theorem.
- `constantSheaf`, `Functor.mapMon`, `Mod.regular`, `Mod.comap`,
  `Functor.ofSequence`, `Functor.ofOpSequence`, and `Ideal.Quotient.factor`
  supply the standard categorical constructions in the helper declarations.
- The stated proof dependencies SheafTensor, ProetaleSiteProperties, and
  ProEtaleToposFunctorialityInverseImage are imported for the proof route, as
  are the Mathlib adjunction and Yoneda tools. The integral-limit and
  invert-ell proof nodes currently have no published Lean declarations; they
  are described in the proof docstring and are not additional hypotheses.

Edge cases checked: arbitrary schemes, including the empty scheme; every prime,
including 2; every finite subextension including the bottom field; every choice
of uniformizer; m=0 in the rational sequence; and every scheme morphism including
identities. The inverse system is indexed by all n>=0: n=0 is the zero-ring
quotient, a terminal object, so adjoining it to the positive-exponent tower does
not change the limit. The ZMod tower has `ZMod 1` at n=0, also the zero ring.
Universes are explicit, with no restriction tying the site's object universe to
its morphism universe. There are no file-local notations, local instances,
auto-bound variables, or definition data containing sorry.

Searches made:

- msearch.py leanfinder, query: "On a scheme pro-etale site the pulled back
  condensed ring of integers is the inverse limit of finite quotients,
  rational coefficients invert the prime, and algebraic closure coefficients
  are the colimit of finite subfields". Returned eight hits, including
  BDeRhamPlus, BDeRham, Condensed.profiniteSolid,
  PadicInt.adicCompletionIntegersEquiv, Padic.adicCompletionEquiv, and
  instCommRingBDeRhamPlus. None states these comparisons.
- msearch.py loogle, `PadicInt, IsLimit, IsColimit`: query rejected for unknown
  identifier IsLimit, no mathematical conclusion drawn. Retried `CondensedMod`:
  twelve generic condensed-module/limit/colimit results, none the proposition.
- msearch.py grep, `padic.*(limit|colimit)|IsColimit.*[Pp]adic|IsLimit.*[Pp]adic`:
  one result, Mathlib/NumberTheory/Padics/RingHoms.lean's documentation of lift.
- rg in the upstream WeilConjectures source for the item id: no match. Searches
  for `padicSubfieldRingObj`, `padicAlgClRingObj` in both upstream source roots
  found the published shared Colimit.Compatibility framework. Read it: its
  isColimitPadicAlgClRingObjCocone is only the additive third comparison.
- rg in lean/Sheaf for the item id and coefficient-comparison names found
  mathematical consumers and the profinite-integer-tower theorem, but no
  complete comparison theorem. Searches for every proposed declaration name
  in Mathlib/upstream/project sources found no clashes.

Validation: scompile.py compiled both the sandbox and intended library module
with no errors or warnings, in about seven seconds per file after the final
source-reuse adjustment. The first deliver2.py --no-push run passed preflight
and both compiles. A final dry run is performed with the updated source and
verbatim node signature before delivery.

No statement correction, new independent notion/node, dependency-record repair,
or STATEMENT-DISPUTED flag is needed. The helper declarations belong to the
canonical comparison diagrams of this node and are listed in lean.declarations.

## Second reading by Q13

This is the author's clause-by-clause self-check, not an independent review.
The worker brief specifies that the maintainer performs the independent reading
and expressly forbids starting another agent. The node and module were reread
against the current blueprint. The additive-only upstream theorem was rejected
as an incomplete existing match; the draft was expanded to rings, all three
comparisons, inverse-image compatibility, and the explicit normalized ZMod tower.
The hypothesis and clause correspondence above records the check in detail.
