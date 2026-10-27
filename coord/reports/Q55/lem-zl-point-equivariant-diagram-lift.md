## Worker report

The module `Sheaf.Paper.PointEquivariantDiagramLift` states
`WeilConjectures.zl_point_equivariant_diagram_lift`, with exactly one postponed
proof. It gives real definitions for its canonical fibre/comparison helpers and
for the packages of conclusion clauses. It changes only the item's `lean` record;
there is no statement correction, new node, or dependency repair.

Source read: `literature/blueprint/latest/blueprint/sec-deligne-laumon-general/`
`sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 7, especially
the dimension-zero Jordan filtration and concatenation of component filtrations.
The reviewed node's eight proof steps are reproduced in the theorem docstring.
The example CompactObject module is withdrawn locally; its recorded upstream
`WeilConjectures.CategoryTheory.CompactObject` definition was read instead.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The prime power, finite base field and its chosen closure are the arbitrary
  `D : FiniteFieldDatum.{u}`. The prime `l`, `[Fact l.Prime]` and `hl : l ≠ D.p`
  are the coefficient-prime conditions. `Ω`, its field/algebra structures and
  `[IsAlgClosure (Padic l) Ω]` give the chosen coefficient closure. `F` is any
  finite subextension in `Padic.FiniteCoefficientFields l Ω`.
- `E` is the *existing* `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F`,
  the published Shrink model of that very subfield. The embedding to Ω is
  `F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom`. No finite
  extension is omitted and no integral lattice or stable-lattice hypothesis is
  imposed. This is the same model used by the recorded literal stage category.
- `Spec (.of D.k)` is the geometric point. `zlDiagramPullback` is the recorded
  rational derived pullback along `frobeniusPointIso D`; its invertibility
  structures are `frobeniusPointPrimeInvertible`, derived from the datum.
- `I`, `[SmallCategory I]`, `[FinCategory I]` give the finite indexing category;
  the index universe `w` is independent of the coefficient/scheme universe.
  `V` is the vector diagram, and `hV` puts every object in finite-dimensional
  vector spaces. Using ModuleCat with this predicate avoids a second definition
  of the finite-dimensional vector category.
- `A i : V.obj i ≅ V.obj i` is an arbitrary invertible linear operator. `hA`
  says `(A i).hom ≫ V.map f = V.map f ≫ (A j).hom`, exactly D(f) A_i = A_j D(f)
  in mathematical composition order. No topology, continuity or diagonalization
  condition is present.
- `iStar`, `MStar`, `thetaStar`, `etaStar` and `hStar` give the prescribed raw
  heart object, Weil isomorphism, fibre identification and Frobenius equation.
  `zlDiagramFiber = pointRationalFibre ⋙ coefficientFdCohomology E 0` is precisely
  omega_E. `zlDiagramTransport` is H^0 of `localPointTransport`, which is the
  recorded iota followed by its specified comparison to the actual pullback.
- The witnesses `G`, `hG`, `theta`, `eta` are the lifted diagram, membership in
  the *recorded* raw constructible heart, its Weil structures and its specified
  fibre isomorphisms. `theta : G ⋙ T ≅ G` contains the inverse Weil maps and all
  their inverse identities. Its naturality is T(f) ≫ theta_j = theta_i ≫ f.
  `zlDiagramWeilObject` and `zlDiagramWeilFunctor` realize these data in the
  recorded `CategoryTheory.Endofunctor.IsoAlgebra` category with literal carriers
  and arrows. Thus the natural-isomorphism packaging introduces no alternate
  definition of a Weil sheaf.
- `G.obj iStar = MStar.obj`, `HEq (theta.app iStar) thetaStar`, and
  `HEq (eta.app iStar) etaStar` retain the prescribed data by equality, not by
  an independently chosen isomorphism. Heart membership is proof irrelevant.
- Functor laws give identity and composition equations. The naturality of `eta`
  gives omega(G(f)) = eta_i.hom ≫ V(f) ≫ eta_j.inv. The first clause of
  `ZlDiagramExactRealization` additionally retains every equality V(f) = V(g),
  including equalities between distinct parallel indexing arrows and all
  composable paths represented by them.
- `ZlPointDiagramRealization` requires `t_i.hom = H^0(iota_i)` and gives
  omega(theta_i) = t_i.inv ≫ eta_i.hom ≫ A_i.hom ≫ eta_i.inv and
  omega(theta_i inverse) = eta_i.hom ≫ A_i.inv ≫ eta_i.inv ≫ t_i.hom.
  These are the two inverse-transport formulas, with all sources correct.
- The final finite-stage formula is eta_i.inv ≫ t_i.hom ≫ omega(theta_i) ≫
  eta_i.hom = A_i.hom. This is the degree-one local Frobenius on Spec k_0:
  the local-operator definition specializes to point transport followed by the
  Weil map. It is not the Weil map alone. The same composite is used in `hStar`.
- `ZlDiagramExactRealization` requires every vector mono to be a mono in the
  actual raw heart, every short exact triple to be a `ShortComplex.ShortExact`
  there, and every vector cokernel cofork to be an `IsColimit` cokernel cofork
  there. The latter is the universal property, not just a vanishing composite.
  All quantifiers concern the original diagram's arrows. Quantifying over all
  short exact triples is equivalent to allowing any finite designated collection:
  a finite category has finitely many such arrow pairs, so all can be designated.
- `ZlFiniteScalarDiagram` is required for *every* finite overfield `L'` with
  `F ≤ L'`, including the identity inclusion. Its underlying diagram is exactly
  `G ⋙ sfRationalScalarExtension`; theta_L is the inverse of the specified
  `rationalPullbackScalarComparison` followed by scalar extension of theta.
  eta_L is precisely `zlDiagramScalarFiber` followed by scalar extension of eta.
  That helper composes the specified `pointRationalFibreScalarIso` with the
  normalized `fieldDerivedHomologyIso`. The displayed transport square forces
  t_L to be scalar extension of t, after those very comparisons. The package
  then requires all finite-stage fibre formulas, inverse maps, Frobenius and
  exactness clauses over L. The comparisons retain their existing identity and
  tower normalizations; no alternative comparison is existentially chosen.
- `ZlCommonStageDiagram` takes *exactly* `G ⋙ inclusion F`. Its Weil map uses
  `localQbarPullbackStageIso` and `inclusion F` applied to theta; inverse maps
  are part of the resulting isomorphism and are explicitly required to have
  the inverse linear formula. eta_Ω is fixed by `zlDiagramStageFiber`, composed
  from `localQbarFibreObjIso`, the existing Shrink cohomology comparison and
  `ModuleCat.extendScalarsComp`. Its transport is the existing
  `localQbarPointTransport`, with its published boundary comparisons; the
  transport square and Frobenius equation are both explicit. It requires raw
  common-stage heart membership and all exactness/cokernel/relation clauses.
  Since G at iStar is MStar literally and these diagrams are literal functor
  composites, the common-stage prescribed object and fibre map are retained
  using the specified comparisons at the original stage F.

Dependency declarations read and used:

- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty`,
  `sfRationalHeart`, `sfCommonStageHeartProperty`, `sfCommonStageHeart`.
- `Sheaf.Paper.SfWeilSheafComplex`: fixed-pair convention and its imported
  `CategoryTheory.Endofunctor.IsoAlgebra`, `.mk`; its full declaration signatures
  were read. This statement is written directly on s = Spec k rather than on a
  chosen geometric-base-change presentation isomorphic to s.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, `pointQbarFibre`,
  `pointQbarFibreObj`, `pointRationalFibreScalarIso`; including their normalized
  object formulas and coefficient-size conventions.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointTransportRational`, `frobeniusPointTransportQbar`,
  `frobeniusPointPrimeInvertible`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPointTransport`,
  `localQbarPointTransport`, `localQbarFibreObjIso`, `localQbarPullbackStageIso`;
  the definition of the local degree-one operator was also read.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `inclusion`;
  the coefficient model is `AlgebraicallyClosedCoefficients.Coefficient`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `coefficientFdCohomology`,
  `coefficientQbarCohomology` and their stage formulas.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback`, `rationalPullbackScalarComparison`.
- `DerivedCategory.fieldDerivedHomologyIso` and
  `ModuleCat.extendScalarsComp` give the existing normalized tensor comparisons.
- Proof-plan imports are `ConstructibleTruncations`,
  `FrobeniusCohomologyTransportIso`, `FrobeniusPointTransportNatural`, and
  `Mathlib.Algebra.Category.ModuleCat.Descent` for the recorded field-extension
  Mathlib leaf. The proof-only node `lem-zl-point-heart-finite-stage` currently
  has no Lean record in the read checkout, so no invented module is imported.
  No object or notion from that postponed theorem is needed to type this
  statement; it remains named in the proof docstring.

Searches for existing declarations:

- `msearch.py ... leanfinder "Lift a finite diagram of vector spaces with
  automorphisms to constructible Weil sheaves on a geometric point with prescribed
  fibre and exact sequences"`: eight unrelated profinite, Galois finite-set and
  condensed-module results; no raw constructible Weil diagram lift.
- `msearch.py ... loogle "CategoryTheory.Functor.FullyFaithful.preimageIso"`:
  seven results, including the generic lifting operation and its component
  formulas. These do not state the specified exact point-heart diagram theorem.
- `msearch.py ... leansearch "Exact fully faithful equivalence lifts diagrams of
  vector spaces with commuting automorphisms and preserves cokernels"`: eight
  generic full-faithfulness, endomorphism and limit results; no matching theorem.
- `msearch.py ... grep "IsoAlgebra|equivariant.*[Dd]iagram" CategoryTheory`:
  zero Mathlib hits. Read the upstream IsoAlgebra extension and used it.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `equivariant.diagram`,
  `pointHeart`, `PointHeart`, `point_heart`, point/heart equivalence/fibre names:
  found the parent `PointWeilHeartFlag`, adic-heart and unrelated point
  equivalences. The parent handles its special Jordan flag, not arbitrary
  finite diagrams with prescribed objects. It was read to check for reusable
  definitions. None of its flag-specific local-stalk definitions matches this
  literal point diagram interface. `grep -rn` for this item's blueprint id in
  `lean/WeilConjectures` returned no matching declaration.

Edge cases checked before and after writing: zero-dimensional vector spaces
and zero arrows; rank-one automorphisms of any nonzero scalar; nonsplit
unipotent Jordan blocks; identity coefficient inclusion and towers; iStar
incident with incoming/outgoing arrows; repeated objects and parallel equal
arrows; split and nonsplit exact sequences; zero cokernels and identity maps.
An empty index category supplies no iStar, exactly as in the stated hypothesis.
The functors and comparisons are canonical constructions, not hypotheses.
No STATEMENT-DISPUTED flag or mathematical defect was found.

Validation: each compile uses only the prescribed server `scompile.py` wrapper.
The first compile exposed an unused implicit parameter on the raw-heart helper;
its call was corrected. Breaking the large common-stage fibre comparison into
its prescribed components resolved elaboration cost without raising any limit.
The final compile and delivery dry run are recorded by the delivery tools.


## Second reading by Q55

Independent reading by the maintainer's review service on behalf of Q55, at
delivery c46fe7fc. It replaces the delivered self-audit, which said that no
separate reading was made. The node, the source place (thm-zl-real-mixed-by-curves.proof.md,
paragraph 7) and the declarations of all seven stmt_deps were read against
`Sheaf/Paper/PointEquivariantDiagramLift.lean`.

Node clauses and their Lean renderings:

1. Data q, k0, k, l ≠ p, Ω, s = Spec k and g_s: `D : FiniteFieldDatum`, `l`, `[Fact l.Prime]`,
   `hl`, `Ω` with `[IsAlgClosure ℚ_l Ω]`, `Spec (.of D.k)` and `frobeniusPointIso D`
   (def-weil-frobenius-point-transport). Correct.
2. Finite E ⊂ Ω: `F : Padic.FiniteCoefficientFields l Ω`, with E = the published Shrink model
   `AlgebraicallyClosedCoefficients.Coefficient F`. This is the same model as the recorded
   stage category `GeneralAlgebraicallyClosedCoefficients.Stage`. Correct.
3. ω_E = H^0 Fib_{s,E}: `zlDiagramFiber` = `pointRationalFibre ⋙ coefficientFdCohomology E 0`.
   T = Lg_s^*: `zlDiagramPullback` = `rationalDerivedPullback` along `(frobeniusPointIso D).hom`.
   H^0(ι_N): `zlDiagramTransport` = H^0 of `localPointTransport`. That is ι followed by the
   specified object comparison, and it equals `localPointTransportIterate _ 0` of
   def-weil-local-frobenius-trace. Correct.
4. Finite category I and diagram D into fd vector spaces: `I : Type w`, `SmallCategory`,
   `FinCategory`, `V : I ⥤ ModuleCat`, `hV`. Correct; no universe tie between w and u.
5. Automorphisms A_i with D(u)A_i = A_jD(u): `A i : V.obj i ≅ V.obj i` and `hA` in diagrammatic
   order. Correct, with no continuity or semisimplicity assumption.
6. Prescribed (M_*, θ_*, η_*) with η_* ω(θ_*) H^0(ι) η_*^{-1} = A_{i_*}: `MStar` (raw heart),
   `thetaStar : T M ≅ M`, `etaStar`, and `hStar` = etaStar.inv ≫ transport ≫ ω(θ) ≫ etaStar.hom.
   The composition order was checked. Correct.
7. Conclusion, lifted diagram of Weil sheaves: `G`, `hG` (raw heart), and `theta : G ⋙ T ≅ G`.
   The theta components are the Weil maps together with their inverses. Its naturality is
   D̃(u)θ_i = θ_j T D̃(u). `zlDiagramWeilFunctor` gives the IsoAlgebra diagram, and IsoAlgebra is
   the very notion of `sfWeilComplex` in def-weil-weil-sheaf-complex. Correct.
8. Prescribed data kept literally: `G.obj iStar = MStar.obj` and the two HEq clauses. Correct.
9. ω(θ_i) = η_i^{-1}A_iη_i H^0(ι)^{-1} and its inverse formula: the second and third equations of
   `ZlPointDiagramRealization`, with `t i` pinned to H^0(ι). Arrow fibres are η_j^{-1}D(u)η_i by
   naturality of `eta`. Correct.
10. Local Frobenius = A_i: the last equation, eta.inv ≫ H^0(ι) ≫ ω(θ) ≫ eta.hom = A. This is
    the n = 0 operator of def-weil-local-frobenius-trace (point transport, then θ) written
    directly on s. Correct.
11. Exactness: `ZlDiagramExactRealization` in the heart. It covers equal parallel arrows, monos,
    every short exact composable pair, and cokernels as `IsColimit`. Quantifying over all pairs
    covers any finite designated set. Correct, and true by the exact equivalence.
12. Coefficient extension: `ZlFiniteScalarDiagram` for every finite L ⊇ E, and
    `ZlCommonStageDiagram` at Ω with the literal `G ⋙ inclusion F`. They use the specified
    comparisons `rationalPullbackScalarComparison`, `pointRationalFibreScalarIso`,
    `fieldDerivedHomologyIso`, `localQbarPullbackStageIso`, `localQbarFibreObjIso` and
    `localQbarPointTransport`. The transport squares are the H^0 images of the final clause of
    `frobeniusPointTransport_natural` (lem-weil-frobenius-point-transport-natural), which is
    stated with exactly these comparisons. So the clauses are true and not arbitrary.
    The finite-L family is the node's proof step 7. It strengthens the conclusion, but it is
    true and pinned.

Edge cases: zero spaces, zero arrows, a non-semisimple Jordan block, rank one with any scalar,
iStar with incoming and outgoing arrows, parallel arrows with equal images, and the identity
inclusion L = E. I is nonempty because iStar is given, as in the node.

Definitions: the helpers are real compositions of recorded canonical maps, with no hollow
bodies; the theorem's only proof is `sorry`. Docstrings carry the source place and the
blueprint id, and the theorem docstring has the 8 proof steps.

Records (advisory only): `fieldDerivedHomologyIso` is a declaration of the theorem node
lem-weil-cohomology-commutes-scalar-extension. The cited def-weil-coefficient-cohomology-modules
already defines its stage formulas through that same declaration and cites that lemma itself.
`rationalDerivedPullback` and `sfRationalScalarExtension` are reached through cited definitions.
No stmt_dep change is needed.

Changes in this reading: only this section. The Lean and the node record are unchanged.
