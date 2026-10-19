## Worker report

The delivery states `AlgebraicGeometry.Scheme.affine_strict_local_ring_comparison`
in `Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`. Its only postponed
proof is the named theorem for this DAG node. The docstring contains all ten steps
of the node's proof, including comparison with the specified algebraic cocone,
unique henselian lifting in both directions, and the final residue square.

The auxiliary definition `affineStrictLocalChartMap` constructs the actual chart
colimit leg. It forms the affine pointed neighbourhood `(Spec D, xD)`, sends it to
the chosen small representative category with `equivSmallModel`, transports global
sections along the inverse unit isomorphism, and then uses the coprojection of
`strictHenselizationAffineDiagram`. Precomposing with `(ΓSpecIso D).inv` gives a
map from D itself. Every part is specified categorical data; there is no arbitrary
ring-map parameter and no choice from a bare existence statement.

Hypothesis-by-hypothesis correspondence:

- The arbitrary scheme X is `{X : Scheme.{u}}`.
- The commutative chart ring D and its affine spectrum are `(D : CommRingCat.{u})`
  and `Spec D`. The affine open immersion is `(i : Spec D ⟶ X) [IsOpenImmersion i]`.
- The geometric field is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`. Its point on X
  is `xD ≫ i`, where `xD : Spec (.of Ω) ⟶ Spec D` is the unique chart lift. This
  parametrizes every point of X whose image lies in the chart: an open immersion
  admits exactly this lift. It adds no condition on such a point.
- The prime is `(p : Spec D)`. Its `asIdeal` carries the required primality instance.
  The binder `[Algebra p.asIdeal.ResidueField Ω]` names the embedding of κ(p) into Ω.
  The equation `hxD` says precisely that the resulting field-spectrum morphism is
  the given lift. It simultaneously fixes the prime and its residue embedding:
  `Spec.residueFieldIso D p` identifies the scheme residue field with the residue
  field of the prime localization, and `fromSpecResidueField` is its canonical point.
  Thus these binders name the data already determined by xD, rather than permitting
  an unrelated algebra structure. The open immersion identifies this with κ(x).
- K is always the actual intermediate field
  `separableClosure p.asIdeal.ResidueField Ω`, with its actual `subtype` inclusion.
  It is never replaced by an unrelated separable closure or an arbitrary isomorphic
  field. `IsAlgClosed Ω` supplies its `IsSepClosure` instance.
- L is always `Localization.AtPrime p.asIdeal`, not an existential local ring.
  `p.asIdeal.ResidueField` is its local residue field, as required by the existing
  `Algebra.IsStrictHenselization` definition (confirmed by elaboration).
- The chosen algebraic strict henselization is `(H : Type u) [CommRing H]` with
  `[Algebra L H]` and a chosen `P : Algebra.StrictHenselizationPresentation L K H`.
  This is exactly a witness of the existing predicate's defining cocone, universality,
  and algebra isomorphism. The L-algebra structure on K and the `IsScalarTower L κ(p) K`
  binder say that its structural map is the prescribed composite through κ(p), as
  in the source and in the dependency definition. They impose no extra condition.
- The geometric colimit and strict localization are the existing
  `strictHenselizationRing (xD ≫ i)` and its spectrum; the existing structural map is
  `strictHenselizationStructuralMap (xD ≫ i)`. The D-map is the constructed chart leg.

Conclusion-by-conclusion correspondence:

- `∃ θ : strictHenselizationRing (xD ≫ i) ≃+* H` gives the isomorphism. The first
  conjunct, `θ.toRingHom.comp (affineStrictLocalChartMap D i xD) = ...`, is exactly
  its D-algebra condition, written with structural ring maps instead of installing
  two more algebra instances. The map on the right is D → L → H.
- The second conjunct is `Spec.map θ ≫ strictHenselizationStructuralMap ... =
  Spec.map (D → L → H) ≫ i`. This is the node's scheme equation with precisely its
  contravariant orientation: both sides have source Spec H and target X.
- The two existential class witnesses are `IsStrictlyHenselianLocalRing C` and
  `IsStrictlyHenselianLocalRing H`. Locality and henselianity are conclusions,
  never assumptions about either of these rings.
- ψ is the specified `P.residueMap`, constructed by descent from this P's pointings,
  transported by this P's algebra identification. `Function.Surjective P.residueMap`
  and `RingHom.ker P.residueMap = IsLocalRing.maximalIdeal H` are the two required
  residue-map properties.
- `K.subtype.comp (P.residueMap.comp θ.toRingHom) =
  strictHenselizationPointEvaluation ...` is the exact geometric-evaluation equation.
- `Set.range (strictHenselizationPointEvaluation ...) = (K : Set Ω)` states image K,
  including the fixed embedding into Ω; the following kernel equality states m_C.
- The ring equivalences `eC : C ⧸ m_C ≃+* K` and `eH : H ⧸ m_H ≃+* K`, with the
  two equations on quotient maps, are the residue identifications induced by ψθ
  and ψ. They are not arbitrary residue identifications. The final equation for
  every representative c says `eH([θ(c)]) = eC([c])`. Quotient representatives are
  surjective, so this is precisely that θ induces the identity of K under these
  identifications. No quotient-map existence or compatibility is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.SpecToEquivOfField`,
  `Scheme.Spec.residueFieldIso`, `Scheme.fromSpecResidueField`.
- `Mathlib.FieldTheory.SeparableClosure`, `Mathlib.FieldTheory.IsSepClosed`:
  `separableClosure`, `IsSepClosure`, `separableClosure.isSepClosure`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and its
  canonical algebra and local-ring instances.
- `Sheaf.RingTheory.IsStrictHenselization`: `Algebra.IsStrictHenselization`, whose
  exact diagram and existential witnesses are exposed by the dependency module below.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `strictHenselizationRing`,
  `strictHenselizationNeighbourhoods`, `strictHenselizationCoordinateRings`,
  `strictHenselizationAffineDiagram` (the published small representative diagram).
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `strictHenselizationStructuralMap`. The live source was read with `scompile --source`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Sheaf.Paper.StrictHenselizationPointEvaluation`:
  `strictHenselizationPointEvaluation`. The module retains the canonical colimit-desc map.
- Proof imports: `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`,
  `Sheaf.RingTheory.StrictHenselizationTriples`, `Sheaf.RingTheory.EtaleHenselianRingLift`,
  exposing `etale_local_ring_triples`, `strictHenselization_triples`, and
  `etale_henselian_ring_lift`. Their declarations and docstrings were read, together
  with the recorded upstream triple modules through `scompile --source`. The proof
  imports also supply the residue-triple diagram and ring-colimit API used by the plan.

Edge cases and fidelity:

- The empty scheme and zero chart ring have no geometric point in the chart; the
  existing geometric-point binders exclude exactly those impossible data.
- D may be a field, p may be zero or maximal, X may itself be affine, and i may be
  the identity. No Noetherian, reduced, domain, finite-type, characteristic, dimension,
  or separability-of-Ω hypothesis is imposed.
- In characteristic p, Ω can contain a purely inseparable extension of κ(p). The
  asserted image is its relative separable closure K, not Ω. The statement retains
  the specified inclusion K → Ω.
- If K = Ω the range equation and evaluation identity have their expected specialization.
- H and its defining cocone are arbitrary chosen realizations of the colimit; the
  residue map is tied to exactly that chosen cocone. No canonicity claim is lost.
- One arbitrary universe u is shared by rings and schemes, consistently with all
  recorded geometric-point and strict-henselization dependency interfaces. There is
  no independently smaller universe for test algebras. Every variable is explicit.
- The two quotients are used only after existentially concluding strict locality.
  The scheme equation was type-checked in the direction Spec H → X.

Sources opened: `etale-cohomology.tex`, lemma-describe-etale-local-ring (Tag 04HX),
including its affine/triples proof; `algebra.tex`, lemma-strict-henselization-different
(Tag 04GW), including its fixed separable closure and residue-field argument. No
natural-language statement correction or mathematical dispute was needed.

Searches for an existing statement or construction:

- `msearch.py ... leanfinder`, query “The strict local ring of a geometric point in an
  affine open Spec D is the strict henselization of the prime localization of D with
  residue field compatibility”: eight results about ordinary residue fields and
  `fromSpecResidueField`; no strict-local comparison.
- `msearch.py ... loogle`, query `Localization.AtPrime, IsStrictlyHenselianLocalRing`:
  zero hits; Loogle does not know the project strict-henselian class.
- `msearch.py ... leansearch`, query “The affine pointed etale neighborhood ring colimit
  is the strict henselization of the local ring compatible with evaluation in a separable
  closure”: eight hits, including `HenselianLocalRing.TFAE`, etale localization lemmas,
  and locally ringed-space colimits; no match.
- `msearch.py ... grep`, query `strictHensel|StrictHensel` in Mathlib/AlgebraicGeometry:
  zero hits.
- `rg` in upstream WeilConjectures and the project's Sheaf library, for this node id
  and affine/strict/comparison patterns: no matching theorem. The related
  `strictHenselizationRing_local_presentation` only gives existential q and K; it
  neither compares an arbitrary chosen H nor preserves this specified residue map.
  `strictHenselizationPointEvaluation_comparison` compares a triple colimit with
  geometric evaluation, but does not give the algebraic strict-henselization comparison.
- `rg` of the source, Sheaf library, and `dag/lean_names_upstream.json` for
  `StrictHenselizationPresentation`, `strictHenselizationPointedDiagram`,
  `affineStrictLocalChartMap`, and the new theorem name found no prior declarations.
- `msearch.py ... leanfinder`, query “A specified colimit cocone of pointed etale
  algebras defining a strict henselization and its canonical residue evaluation map”:
  eight results (`StandardEtalePair.lift`, ordinary residue-field maps, and related
  etale lemmas); no chosen-presentation interface.
- `msearch.py ... grep`, query
  `StrictHenselizationPresentation|strictHenselizationPointedDiagram|affineStrictLocalChartMap`:
  zero Mathlib hits. DAG search for these identifiers found no independent definition
  node; the presentation belongs to the existing def-sc-ring-strict-henselization.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py`, with no errors or warnings. The naturality proof inside the evaluation
cocone is a structural category equation (`Over.w`); no theorem has been proved in
this delivery. The only theorem body is `by sorry`. All definitions have real data.

## Dependency modules

`def-sc-ring-strict-henselization`: the old `Algebra.IsStrictHenselization` is a Prop
whose existential cocone and isomorphism are sufficient for merely recognizing a
strict henselization, but its interface does not expose a specified presentation
and the induced residue map belonging to it. The new module
`Sheaf.RingTheory.StrictHenselizationPresentation` imports and preserves that predicate,
and supplies its actual witness type `Algebra.StrictHenselizationPresentation`, the
same pointed-algebra forgetful diagram, its tautological pointing cocone, and
`StrictHenselizationPresentation.residueMap`. A witness consists exactly of the
cocone, its universal property, and an algebra isomorphism to H; Nonempty of this
witness type is the old predicate. The residue map is the composite of the inverse
of that chosen isomorphism and the colimit-desc map to K. The original definition
node's statement, dependencies, and every field other than lean are unchanged.
There are no new DAG nodes, no new axioms, and no additional postponed helper theorems.

## Second reading by Q97

Independent maintainer second reading of immutable delivery
1ace89902d57e75ddbeb78eb7c93126e9d001a02, 2026-10-17. The reader did not author
this delivery. The original placeholder in this section did not satisfy H11;
this section records the actual reading. The worker report above is preserved.

Hypotheses and objects checked against the node and sources:

- X: arbitrary `Scheme.{u}`; D: arbitrary `CommRingCat.{u}`; chart:
  `i : Spec D ⟶ X` with `IsOpenImmersion i`. These are the recorded scheme,
  spectrum and open-immersion notions. No finiteness or separation condition.
- The geometric point is `xD ≫ i`, with `Field Ω` and `IsAlgClosed Ω`.
  Parametrizing by its chart lift covers exactly all geometric points whose image
  lies in this open: `Spec Ω` has one point and an open immersion has the unique
  lift. The theorem does not assert an extra hypothesis on those points.
- The prime is `p : Spec D`. `Spec.residueFieldIso D p` identifies the scheme
  residue field with `p.asIdeal.ResidueField`. `hxD`, using
  `fromSpecResidueField`, binds that prime and its residue embedding to xD.
  The `Algebra` instance names the embedding; it does not allow an unrelated one
  once hxD is imposed. The open immersion identifies this residue field with κ(x).
- K is precisely `separableClosure p.asIdeal.ResidueField Ω`, with its actual
  `subtype` inclusion into Ω. Mathlib's `separableClosure.isSepClosure` applies
  because Ω is algebraically closed. No abstract replacement of K is made.
- L is precisely `Localization.AtPrime p.asIdeal`. Its residue field is
  definitionally `p.asIdeal.ResidueField`. The L-action on K and scalar-tower
  instance express exactly the prescribed composite L → κ(p) → K.
- H is an arbitrary commutative L-algebra, with chosen
  `Algebra.StrictHenselizationPresentation L K H`. This structure retains the
  defining cocone, `IsColimit`, and algebra identification. Its `Nonempty` is
  exactly the imported `Algebra.IsStrictHenselization` predicate after unfolding;
  locality or strict henselianity of H is not assumed.
- C is the recorded `strictHenselizationRing (xD ≫ i)`, and its spectrum and ρ
  are the existing strict-henselization scheme and structural morphism.
  `affineStrictLocalChartMap` constructs the chart coprojection, transporting
  along the inverse unit of `equivSmallModel` and precomposing with
  `(ΓSpecIso D).inv`. Its opposite-arrow direction is correct. It is not an
  arbitrary map satisfying a later condition.

Every conclusion checked:

- The existential ring equivalence θ, together with its first equation on the
  chart map, is exactly a D-algebra isomorphism C ≃ H for D → L → H.
- `Spec.map θ ≫ strictHenselizationStructuralMap ... = Spec.map (D → L → H) ≫ i`
  has source Spec H and target X and is the required contravariant square.
- The two existential `IsStrictlyHenselianLocalRing` witnesses conclude locality,
  henselianity and separably closed residue fields for both C and H.
- ψ is exactly `P.residueMap`, formed from this P's inverse identification and
  `P.isColimit.desc` of the tautological pointing cocone. Its surjectivity and
  maximal-ideal kernel are separate conclusion clauses, not hypotheses.
- The equation `K.subtype.comp (P.residueMap.comp θ.toRingHom) =
  strictHenselizationPointEvaluation ...` preserves the specified geometric
  evaluation into Ω. The range equation states image equal to the embedded K;
  the kernel equation states precisely the maximal ideal of C.
- eC and eH identify the two residue quotients with K; their equations on the
  quotient maps force them to be the identifications induced by ψθ and ψ.
  The final equation on every representative c is the identity of K under these
  identifications. Surjectivity of quotient maps makes this the full residue-field
  assertion. No clause is weakened or strengthened.

Dependency and source reading:

All twelve statement-dependency nodes were read in the snapshot, including their
statements, source fields and Lean records. The exact definitions used were read:
Mathlib `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`, `IsOpenImmersion`, `IsAlgClosed`,
`Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.SpecToEquivOfField`,
`Spec.residueFieldIso`, `fromSpecResidueField`, `separableClosure`,
`separableClosure.isSepClosure`, `Localization.AtPrime`, and `Ideal.ResidueField`.
The upstream `IsStrictlyHenselianLocalRing` extends `HenselianLocalRing` with
`IsSepClosed` of the residue field. The existing predicate in
`Sheaf.RingTheory.IsStrictHenselization` has exactly the same pointed-etale
forgetful diagram and existential witnesses as the new presentation structure.
The §1(B) note accurately explains why this consumer needs specified witness data.
No second independent strict-henselization predicate was introduced.

Sources read: Stacks `etale-cohomology.tex:4257` (04HX, complete statement and
proof), `algebra.tex:43400` (04GW, complete statement and proof), and the blueprint
source of `def-weil-pbc-strict-henselization-limit`. In particular these allow
arbitrary rings and keep the chosen separable residue closure throughout.
Current upstream `WeilConjectures.AlgebraicGeometry.StrictHenselization` and
`StrictHenselizationStructuralMap` were also read through `scompile.py --source`:
the former constructs the small opposite-indexed coordinate-ring colimit; the
latter is the common composite of its limit legs. The point-evaluation source was
read locally and through the wrapper: it is descent of the geometric pointings.
The old local source checkout is not used as an alternative mathematical model.
The three proof imports were inspected, including `etale_local_ring_triples`,
`strictHenselization_triples`, and `etale_henselian_ring_lift`. Their signatures
supply the chart comparison, the strict locality/residue properties, and the
unique lifts with prescribed base and residue maps required by the ten-step plan.
Transport from an existential triple colimit to any chosen colimit uses its
universal property. No new unstated prerequisite or universe transport is needed.

Independent searches used `rg` in Mathlib, the upstream WeilConjectures tree and
the group clone's Sheaf tree, with strict-henselization, affine, chart, comparison
and presentation spellings. The nearby `strictHenselizationRing_local_presentation`,
`strictHenselizationPointEvaluation_comparison`, `strictHenselization_comparison`
and `strictHenselization_chart_maximalIdeal` were opened. None states this
arbitrary chosen algebraic presentation comparison with its fixed residue map and
all the structural and residue conclusions. No existing named chart leg or
presentation interface was found. The worker records all three required kinds of
search, including LeanSearch, LeanFinder/Loogle, and textual searches.

Edge cases and pilot gates:

- Empty X or zero D admits no chart geometric point, exactly as in the source.
  Identity charts, fields, p = 0 when prime, maximal primes and non-Noetherian
  rings are covered. No reducedness, domain, characteristic or finite-type
  assumption occurs. In positive characteristic the image is K even when Ω
  contains purely inseparable elements over κ(p); K = Ω also specializes correctly.
- All variables and the arbitrary universe u are bound. The common universe for
  schemes, rings and test algebras agrees with the recorded interfaces and with
  the dependency node's explicit size convention. No smaller test universe or
  equality of independent site universes is imposed. No pro-etale replacement.
- Both `lean.statement` fields were compared with the complete declaration
  signatures, character for character, and are verbatim. Both node records differ
  from their read-only clone versions only in `lean`. No natural-language statement
  correction was made, so a §1(C) citer audit is not triggered.
- The canonical maps contain real data; no definition has a sorry. Module and
  declaration docstrings carry sources and blueprint identifiers, and the main
  theorem's docstring follows all ten node proof steps. The only theorem body is
  `by sorry`. Lines are at most 100 characters and declaration lists cover all
  helpers. The replacement dependency module uses the existing `Over.w` directly
  for pointing-cocone naturality, removing the original local tactic block.
- No repository mutation, live Lean write, claim, delivery, merge or global build
  was performed. All reviewer writes are under this review's fixes directory
  or in review.md.

Compiler evidence:

The immutable pair was compiled separately in dependency order through
`scompile.py Q97 lem-exc-affine-strict-local-ring-comparison`, passing both files
as siblings. The wrapper reported clean private-overlay/preliminary/sandbox
checks and clean server library confirmation: presentation 3.3 s and item 3.6 s.
The replacement presentation and unchanged item were then checked together by the
same wrapper. Final exit 0, no errors or warnings: private overlay 15.2 s,
preliminary presentation 7.0 s, sandbox probes 12.6 s and 4.9 s, server library
confirmation 9.3 s for the presentation and 53.9 s for the item. An intermediate
replacement check reported unused S/T binders; these were renamed `_S`/`_T`
before this final clean check. The 60-second per-file limit was retained. The installed wrapper currently performs the private overlay
and confirmation on the server; no direct ssh or alternate compiler was invoked.

Findings and disposition: FIX for H11 (placeholder second reading), repaired by
this complete report, and mechanical cleanup of the local naturality tactic block
for the pilot's no-local-proof gate. The theorem and all declaration signatures,
node statements and dependency records are unchanged. No substantive mathematical
fault remains.
