## Worker report

Existing declaration: `AlgebraicGeometry.ProEtale.coefficientRing`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. No module is supplied:
this is the existing canonical construction, with the three coefficient inputs below.
The item defines the notation R_{X,T} by applying the already recorded general
construction to already recorded condensed rings; it introduces no further construction.
The node changes only in `lean`. There are no new nodes, dependency repairs,
statement corrections, new axioms, or new postponed theorems.

Read the item, its six statement dependencies and their recorded interfaces, the
main-20261015 source `sec-smooth-purity/sk-def-sp-coefficient-towers/`
`pur713-def-coefficient-rings.md`, the example CompactObject module and node,
the stage brief, stage document, and delivery-errors H. No item repair note exists.
Read current published Basic, EllAdic and Compatibility sources through
`scompile.py --source`, as well as the shared framework sources and side interfaces.

Hypotheses and every clause:

- Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]` in the coefficient-input declarations.
  The chosen algebraic closure with extending valuation is the existing `PadicAlgCl ℓ`.
  This fixed model is the existing dependency's convention, not a new assumption
  restricting the isomorphism class of the algebraic closure.
- A finite intermediate extension is `E : PadicAlgCl.FiniteIntermediateField ℓ`,
  namely an intermediate field of `ℚ_[ℓ]` in `PadicAlgCl ℓ` with
  `FiniteDimensional ℚ_[ℓ] E.1`. Its coercion to a field has the inherited norm.
- The valuation ring O_E is `PadicAlgCl.integers ℓ E`. Its definition uses the norm
  induced by the embedding in `PadicAlgCl ℓ`, with bound one and subspace topology.
  `Profinite.padicIntegersCondensedRing` installs precisely this induced norm.
- An arbitrary scheme is `(X : Scheme.{u})`; the construction has no nonempty,
  characteristic, Noetherian, dimension, or finite-type condition on X.
- The choice `T = O_E` is rendered by
  `coefficientRing X (Mon.mk (Profinite.padicIntegersRingObj ℓ E))`.
- The choice `T = E` is rendered by
  `coefficientRing X (Mon.mk (Profinite.continuousMapRingObj E))`.
  Its underlying object is definitionally `padicSubfieldRingObj X ℓ E` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
- The choice `T = Qbar_ell` is rendered by
  `coefficientRing X (Mon.mk (Profinite.padicAlgClRingObj ℓ))`.
  Its underlying object is definitionally `padicAlgClRingObj X ℓ` in Compatibility.
  No coproduct, new selector, or private definition of these notions is required.
- The O_E and E input sheaves have continuous-map sections, pointwise operations,
  and precomposition restrictions, from `Profinite.continuousMapRingSheaf` and
  `Profinite.padicIntegersCondensedRing`. The unbundled ring objects retain these
  operations via `Sheaf.monObj_sheafCompose_obj`.
- Qbar input is `Profinite.padicAlgClRingObj ℓ`, the underlying abelian sheaf of
  `Profinite.padicAlgClCondensedRing ℓ`. Its presheaf is exactly the dependency's
  `Profinite.padicAlgClRingPresheaf`. The carrier of its sections is ULift of
  `PadicAlgCl.finiteIntermediateFieldValued ℓ S`, whose existential intermediate
  field is inside the condition on each individual continuous map. Thus the finite
  field can depend on the section. It is not the full continuous-map ring.
- The target category is exactly `Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})`:
  ring objects in abelian sheaves on the small pro-etale site. `RingCat` at the
  input stage retains the commutative rings' data, while commutativity is supplied
  by the respective `IsCommMonObj` instances.
- The defining equality R_{X,T} = p_X^* underline T is the body
  `(upperStarFromPoint X).mapMon.obj Λ`. `coefficientRing_X` identifies its
  underlying object with `(upperStarFromPoint X).obj Λ.X`.
  The recorded dependency `sfbPullbackFromPoint X` is definitionally this same
  `upperStarFromPoint X`, not an arbitrary inverse image.
- The monoidal unit composite is `Functor.LaxMonoidal.ε F ≫ F.map η[Λ.X]` for
  `F = upperStarFromPoint X`; the multiplication composite is
  `Functor.LaxMonoidal.μ F Λ.X Λ.X ≫ F.map μ[Λ.X]`.
  These are the actual fields of Mathlib's `Functor.monObjObj`, used by `mapMon`.
  Since F is strong monoidal they are exactly the displayed isomorphism then
  image-of-unit/image-of-multiplication maps. The probe checks both by `rfl`.
- Each pulled-back input is commutative by the exact existing instance
  `isCommMonObj_condensedRingObj input X`; the three input commutativity instances
  are the continuous-map instance, `Profinite.isCommMonObj_padicIntegersRingObj`,
  and `Profinite.isCommMonObj_padicAlgClRingObj`. On the bundled `coefficientRing`
  presentation, passing this witness explicitly avoids instance-search unfolding
  limitations. This needs no new theorem or strengthened hypothesis.
- The Lambda_X identification is exactly the declaration already recorded on
  `sk-def-sfb-pulled-back-coefficients`, specialized to these inputs. The
  unbundled presentation is `condensedRingObj input X`.
- No value formula on a pro-etale U is asserted: every chosen expression applies
  the canonical inverse-image functor to the point sheaf. In particular the
  unrelated `padicSubfieldSheaf`/`continuousMapRingSheaf X T` construction on X
  is not substituted for the point inverse image.

Dependency interfaces used:

1. `pur713-def-continuous-rings`: Mathlib `TopCat.commRingYoneda`, in
   `Mathlib.Topology.Sheaves.CommRingCat`, read with its pointwise ring and
   precomposition declarations. Its `Profinite.toTopCat.op` restriction is the
   unlifted continuous-ring presheaf. The existing upstream
   `Profinite.continuousMapRingPresheaf` uses the equivalent ULift encoding
   required for Ab.{u+1}; `continuousMapRingPresheafForgetIso` identifies its
   underlying functions. No dependency repair or duplicate presheaf is needed.
2. `pur713-def-qbar-ring`: `Profinite.padicAlgClRingPresheaf`, in
   `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
3. `sk-def-sfb-condensed-ring`: its recorded
   `Profinite.continuousMapRingObjOfUniverse` in
   `Sheaf.Topology.ContinuousMapCondensedRing` is the general-universe version.
   For the small fields here its body specializes to the same presheaf and
   abelian sheaf as upstream `Profinite.continuousMapRingObj`; their sheafness
   proof fields are proof-irrelevant. The same node's closed upstream audit
   explicitly records `continuousMapRingSheaf`, `continuousMapRingObj`,
   `padicSubfieldCondensedRing`, and `padicIntegersCondensedRing` in
   `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` and
   `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
   Those established declarations supply exactly the inputs used here.
4. `sk-def-sfb-qlbar-condensed`: its closed upstream audit records
   `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj` in EllAdic.
5. `sk-def-sfb-pullback-from-point`: `sfbPullbackFromPoint` in
   `Sheaf.AlgebraicGeometry.ProEtalePointPullback`, an abbreviation for the
   exact published `upperStarFromPoint`, as checked in the probe.
6. `sk-def-sfb-pulled-back-coefficients`: `coefficientRing`,
   `coefficientRing_X`, `condensedRingObj`, `isCommMonObj_condensedRingObj` in Basic,
   with Mathlib `Functor.monObjObj`, `mapMon` and `isCommMonObj_obj` in
   `Mathlib.CategoryTheory.Monoidal.Mon` and `Mathlib.CategoryTheory.Monoidal.CommMon_`.

Edge cases checked: the degree-one subextension is the bottom intermediate
field, so E = Q_ell is included (also elaborated in the probe). Empty profinite S
has the unique function, which satisfies the finite-field condition by choosing
the bottom intermediate field. For finite S, finitely many algebraic values lie
in a finite compositum. Infinite profinite S still requires a finite field for
each section; continuous sequences of unbounded algebraic degree converging to
zero are excluded by this predicate, as required. X may be empty, and ell may
equal the residue characteristic of X. The site and coefficient sizes are the
existing `Scheme.{u}`, object universe u+1, morphism universe u, Ab.{u+1}
convention, with arbitrary explicit u; no additional universe equality is imposed.

Searches made (2026-10-18):

- msearch LeanFinder: "The coefficient ring on the small pro-etale site of a
  scheme is the inverse image of the condensed ring of continuous functions to
  a finite p-adic extension or its integers, or the finite-subextension-valued
  algebraic closure". Eight results, including BDeRham, Condensed.profiniteFree,
  Scheme.smallEtaleTopology, CondensedMod.ofSheafProfinite; no whole-item match.
- msearch LeanSearch: "coefficient ring pro-etale sheaf inverse image condensed
  ring". Eight results, including CondensedMod.ofSheafProfinite,
  Condensed.ofSheafProfinite and LightCondensed; no scheme coefficient pullback.
- msearch Loogle: `CategoryTheory.Functor.mapCommMon`, twelve results.
  Read its source and `Functor.monObjObj`/`mapMon`: these give precisely the
  transported structure once the published point pullback is supplied.
- msearch grep: `upperStarFromPoint|padicSubfieldRingObj|padicIntegersRingObj|coefficientRing`,
  zero Mathlib hits. Direct rg in the slopmaster2 WeilConjectures source for
  coefficientRing/condensedRingObj and the item id found no matching framework.
  Direct rg in shared `lean/Sheaf` found existing users of coefficientRing,
  and in the prescribed shared `lean/WeilConjectures` framework found Basic,
  EllAdic and Compatibility. Reading those declarations establishes the exact
  existing match. The upstream names index has no item-specific alternate name.
- DAG reads also found `def-sfb-subfield-coefficient-ring` and
  `def-sfb-qlbar-coefficient-ring`, already bound to the exact Compatibility
  specializations. This confirms those notions must not be defined again.

Validation: the sandbox-only `scratchpad/Check.lean` is compiled by scompile.py,
checking all three bundled specializations, their explicit commutativity
witnesses, both named specializations, the point-pullback abbreviation, both
structure-map formulas by definitional equality, and the bottom-field case.
It is not part of the delivery. The normal delivery tool additionally compiles
its existing-declaration probe. No global build or direct git command is run.

## Second reading by Q06

Author self-check under the dispatcher's direct-delivery protocol; independent
review is the maintainer's responsibility. Reopened the node, its source and
all cited interfaces. Matched prime and finite-extension parameters, the
valuation ring and induced topology, each of the three coefficient choices,
finite-subextension-valued Qbar sections, sheaf and commutativity structures,
arbitrary X and the small site, canonical p_X^*, both displayed monoidal maps,
Lambda_X and absence of a section formula as detailed above. The available
construction already defines all three objects by specialization, so adding a
new module would duplicate it. The probe's first version needed explicit
`isCommMonObj_condensedRingObj` witnesses for the bundled presentation and the
correct opened unit/multiplication notation; these are probe elaboration fixes,
not mathematical changes. No mismatch in the node or existing definition was
found, and only the item's `lean` record is changed.
