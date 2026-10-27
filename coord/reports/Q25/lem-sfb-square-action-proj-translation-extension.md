## Worker report

The item is stated by `AlgebraicGeometry.SchemeAction.exists_proj_translation_neighborhood`
in `Sheaf.AlgebraicGeometry.SquareActionProjTranslationExtension`. The node statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the new
definition node `def-sfb-section-ring-proj-affine-base`. The theorem proof is `sorry`.
The proved dependency records remain exactly as on live; neither is in this packet.

Hypothesis and conclusion correspondence:

- `S : Scheme.{u}` and `[IsAffine S]` give the affine base.
- `H X : Over S` give exactly the two structure morphisms. `[GrpObj H]` is the
  group scheme structure, with multiplication, identity and inverse laws. `[ModObj H X]`
  gives the action morphism and precisely its unit and associativity laws.
- `[Smooth H.hom]`, `[IsSeparated H.hom]`, `[LocallyOfFinitePresentation H.hom]`,
  `[QuasiCompact H.hom]` express smooth, separated and finite presentation. Separatedness
  supplies quasi-separatedness; no independent condition is imposed on the base.
- `hH : ∀ s : S, ConnectedSpace (H.hom.fiber s)` is connectedness of each ordinary
  residue-field fibre, including nonemptiness, without imposing geometric connectedness.
- The separated, locally finitely presented and quasi-compact instances on `X.hom`
  express exactly its separated finite-presentation hypothesis.
- `M : X.left.Modules` and `[M.IsInvertible]` use the existing locally rank-one module.
- In `Over S`, `X ⊗ B` is the actual chosen pullback of `X.hom` and `B.hom`.
  `(tensorPullback (fst X B).left).obj M` is precisely `M_B`, and the second
  projection is `q_B`. The expression
  `(lift ((snd X B ≫ g) • fst X B) (snd X B)).left` is the translation
  `(x,b) ↦ (g(b)x,b)`, built directly with Mathlib's action and fibre product.
- `hsquare` quantifies over every `B : Over S` and `g h : B ⟶ H`, without
  affineness or smoothness restrictions on this hypothesis. Its `g * h` is multiplication
  of group-valued test points. It asserts an invertible `N : B.left.Modules` and
  `Nonempty` of exactly `τ_(gh)^* M_B ⊗ M_B ≅ (τ_g^* M_B ⊗ τ_h^* M_B) ⊗ q_B^* N`.
  Thus only existence of each isomorphism is required, with no coherence or linearization.
- `hcover` uses every positive degree `d` and homogeneous section `s` and the recorded
  `nonvanishingLocus`. Each degree subgroup is the image of all sections of `M.tensorPow d`,
  so this is exactly the cover in the node, without an affine-open hypothesis.
- `sectionRingGrade M` is the original grading on `InvertibleSectionRing M`, and
  `Proj (sectionRingGrade M)` is precisely `P`. `sectionRingProjMap M hcover`
  chooses the morphism of `exists_sectionRing_proj_morphism`, including BOTH its
  inverse-image equality and its fraction formula. Those chart conditions determine it.
- `sectionRingProjStructure X.hom M` is the actual induced morphism `P → S`:
  `Proj.toSpecZero`, followed by Spec of the degree-zero coefficient map composed with
  `X.hom.appTop`, and then the inverse affine-scheme isomorphism of `S`.
- The conclusion quantifies over every affine `B : Over S` with smooth `B.hom` and
  every `g : B ⟶ H`. Its ambient scheme of opens is exactly
  `pullback (sectionRingProjStructure X.hom M) B.hom = P_B`.
- The existential `rB` is pinned down by BOTH pullback projections:
  `rB ≫ pullback.fst = (fst X B).left ≫ sectionRingProjMap M hcover` and
  `rB ≫ pullback.snd = (snd X B).left`. These uniquely specify `r ×_S id_B`.
  Existence is asserted inside the item, so no unstated over-base theorem is used
  in a definition and no assumption about an arbitrary map is added.
- `U U'` are genuine opens of `P_B`, and `σ : U.toScheme ≅ U'.toScheme` is an
  actual scheme isomorphism. The maps `rU` and `rU'`, with their two factorization
  equations, say that BOTH opens contain the entire image of `r_B`. Factoring through
  an open is equivalent to this containment, and its factor is unique.
- The third equation is preservation of the projection to `B`, so `σ` is a
  `B`-isomorphism. The final equation is `σ_g ∘ r_B = r_B ∘ τ_g` after factorization.
  All witnesses occur inside the quantifiers for the single `B,g`; no compatibility
  across different translations is asserted.

Dependency declarations read and used:

- Mathlib `Scheme`, `Over`, `GrpObj`, `ModObj`, the cartesian `Hom` action, and the
  scheme-over-base product from `Mathlib.AlgebraicGeometry.Pullbacks`.
- Mathlib `Smooth`, `LocallyOfFinitePresentation`, `IsSeparated`, `QuasiCompact`,
  `Scheme.Hom.fiber`, `Scheme.residueField`, `ConnectedSpace`, `Limits.pullback`
  and its projections, `Scheme.Opens.toScheme`, and `Proj` / `Proj.toSpecZero`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `IsInvertible`, `tensorPow`;
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`: `unitSectionsEquiv`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the public existing
  `tensorPullback` functor; `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
  retains the recorded sheaf tensor construction. The scheme monoidal tensor is the
  existing `WeilConjectures` scheme-module tensor; no tensor is defined in the delivery.
- `WeilConjectures.AlgebraicGeometry.Ample`: `nonvanishingLocus` (not `IsAmple`, which
  would add the unjustified affine-section-open requirement).
- `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`: `SectionRingComponent`,
  `InvertibleSectionRing`, `sectionRingGrade` and `sectionRingGradedRing`.
- `WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap`:
  `exists_sectionRing_proj_morphism`, with the entire normalized signature.

The stated proof dependencies are imported plainly: `Cohomology.EulerChar`,
`NagataAffineProjScalarExtension`, `AffineFiniteTypeGeneratingSections`,
`RelativeProj.Functoriality`, and `Modules.PullbackMonoidal`. The smooth-flat,
quasi-compact and separated base-change declarations are in the already imported
Mathlib morphism modules. `lem-sfb-cofinal-section-opens-proj-neighborhood` has no
recorded Lean declaration at the time of writing; it is a proof dependency only,
not needed to type this statement, so no nonexistent import is invented.
The recorded `finrankH_pullback` interface is more specialized than the generic flat
base change in the natural-language proof; this does not enter the statement and
will need attention when that proof dependency is proved or given its full interface.

Edge cases checked: empty `S`, empty `X`, empty test `B`, identity translation,
trivial group, trivial invertible module, zero homogeneous sections and degree zero.
Connectedness excludes an empty fibre only over an actual point of `S`; the empty
base is allowed. No nonempty source is assumed. The cover uses positive degrees,
while the section ring and canonical fraction formula retain degree zero. There
are no restrictions on characteristic, reducedness, Noetherianness, integrality,
properness or commutativity of the group. All schemes and test schemes use the same
arbitrary universe `u`, as does the existing scheme fibre-product API; no lower
independent test universe makes the square condition vacuous.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: “Translations extend to isomorphisms of open
  neighborhoods in Proj of the section ring of a line bundle satisfying the theorem
  of the square.” Eight hits, all standard Proj chart comparisons, not this assertion.
- `msearch.py ... leansearch`: “Translations of a square condition invertible module
  extend to isomorphisms of open neighborhoods of the image in the section ring Proj.”
  Eight hits concerning affine/Proj chart sections and isomorphisms on sections/stalks;
  none constructs the translation extension.
- `msearch.py ... loogle`: `"Proj", "IsIso"`. Four hits: two derived-functor
  isomorphisms and the two standard Proj-chart-to-Spec isomorphisms, no match.
- `msearch.py ... grep`: `squareCondition|translation.*Proj|Proj.*translation`
  in Mathlib `AlgebraicGeometry`: zero matches.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, translation/Proj,
  square-condition and coefficient/base-structure names found no statement match or
  existing degree-zero ring homomorphism / section-Proj affine-base construction.
- A concurrently landed downstream module `SquareActionProjImmersionLocusStable`
  contains `squareActionTranslation` with the opposite fibre-product factor order.
  It cites this item as a proof dependency, so importing it would close that proof
  import route. The delivery does NOT define another named translation: its statement
  directly uses Mathlib's `lift`, projections and existing test-point action.
- `tools/blueprint_refs.py search 'translation Proj'`: zero blueprint nodes.
  The current `literature/blueprint/latest` search did not expose an alternative
  assertion for this auxiliary Guo result.

I read Guo sections 5.6 and 6.1 and Proposition 6.2 in the cited March 31, 2026 PDF.
Its use of inverse-labelled translations is immaterial because every group section
is quantified; the Lean keeps the node's convention `x ↦ gx` exactly.
No node-statement correction or dispute is needed.

## New nodes

`def-sfb-section-ring-proj-affine-base`, in the item's chapter and unit, owns
`Sheaf.AlgebraicGeometry.SectionRingProjOverBase`. It defines the coefficient map
`sectionRingZeroCoefficient`, its named law statement `sectionRingZeroCoefficient_laws`,
the resulting `sectionRingZeroRingHom`, the normalized `sectionRingProjMap`, and
`sectionRingProjStructure`. It uses the live, proved `InvertibleSectionRing` and
`exists_sectionRing_proj_morphism` without replacing either record. Its statement
spells out all four coefficient-map laws and the Proj-to-affine-base composite.
The coefficient map has actual direct-sum data. Its law theorem postpones only
proofs of those explicitly stated operations. The canonical map is chosen from
the full chart characterization, which uniquely determines the morphism.

New-node searches were rerun with `msearch.py`: LeanSearch for the degree-zero
coefficient and affine-base structure returned eight standard structure maps;
Loogle for `AlgebraicGeometry.Proj.toSpecZero` returned eleven general Proj facts;
grep for `sectionRingZero|sectionRingProj|fromOfGlobalSections_toSpecZero` returned
only `Proj.fromOfGlobalSections_toSpecZero`. I opened that signature: its input is
a graded ring map into ordinary global functions, not tensor-power sections of an
invertible module, so it does not supply this interface. Local `rg` in both Lean
roots and `dag/nodes` returned no coefficient/affine-base interface, and
`blueprint_refs.py search 'section ring'` returned zero nodes. Actual logged search
records are copied into the new node. The generic `Proj.toSpecZero` is reused.

Source reading: Stacks 01PZ `lemma-map-into-proj` gives the normalized canonical
morphism on the positive-section cover; Stacks 01N8 `lemma-converse-construction`
constructs it by the stated fraction maps. The degree-zero map uses the tensor
unit in the already proved section ring. Its laws follow by componentwise
addition, the zero-degree unit, and tensor multiplication in degree (0,0).
The base structure is exactly the degree-zero structure map followed by Spec of
the pullback of base functions. These constructions work for empty schemes and
the zero ring, and require no finite-type or nonempty hypothesis. For a trivial
line bundle, the coefficient inclusion is the usual degree-zero inclusion.

## Repair of returned head 95cf7e707592

H13, first dependency: removed the sandbox copy of
`lem-sc-ample-proj-canonical-map.json`. Its live M1 primary declaration remains
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_morphism`, with its
proved normalized signature. Removed `sectionRingProjMap_over` entirely. There
is no separate unrecorded theorem asserting that r lies over S.

H13, second dependency: removed the sandbox copy of
`def-sc-invertible-section-ring.json`. Its live M1 primary declaration remains
`AlgebraicGeometry.Scheme.Modules.InvertibleSectionRing`, with the proved grading
and multiplication laws. The new helpers are attached solely to the new definition
node, never to either old dependency node.

H13, helper ownership and r_B: consolidated the two old helper files into the
new definition node's module and removed `SectionRingDegreeZero.lean`. Removed
`sectionRingProjBaseChange`; the item now existentially supplies r_B with both
pullback-projection equations, then asserts the same two image factorizations,
over-B identity and translation identity. The projections uniquely determine the
canonical base change. Their existence is part of the item, rather than a new
unrecorded sorried identity. No natural-language node statement was changed, and
no statement correction is required: this is the reviewer's requested explicit
rendering of the already specified base change. The item docstring now explains
how the degree-zero fraction normalization supplies the over-base identity in
its proof before using the pullback universal property.

Minor point: the second reading below is the author's own pass. The maintainer
performs the independent review; this report does not represent an independent
review by another agent.

## Second reading by Q25

Author's second pass after the H13 repair. I reopened both final modules and both
new packet node records, and compared the dependency declarations to live. Only
the item's `lean` and its added definition dependency change; the two proved
dependency records are absent from the packet. In the item I checked affine S,
the smooth separated finitely presented group with ordinary connected fibres,
the action laws, separated finitely presented X, invertible M, the square
condition for unrestricted test schemes, the positive-degree cover and the smooth
affine test bases in the conclusion. The square condition still includes gh, the
untwisted factor, both translated factors and the invertible base twist. I checked
the two new r_B projection equations against the pullback factors: the first is
r after projection to X, the second is projection to B. Both open factorization
equations use that very r_B, the isomorphism commutes with projection to B, and
the last equation is sigma after r_B equals r_B after translation. No coherence
between different g is asserted. The new definition node includes the four laws
of the coefficient homomorphism, the full affine-base composite, and the normalized
canonical map, and its module matches them. Every variable and universe is
explicit, and both files disable automatic implicit binding. No additional
postponed over-base theorem or hollow definition remains.

## Repair validation

The explicit `scompile.py` run accepted both repaired modules. It reported one
line-length warning in the item docstring; that line was already wrapped in the
saved file while the server was compiling its captured input. The subsequent
delivery dry run compiles the final saved files and performs server preflight.

The final saved files compiled cleanly in `deliver2.py --no-push`, which reported
`OK (dry run): commit 6ec5244da59 passes the preflight and compiles; nothing pushed`.
The dry-run staged file list contains only the item, the new definition node,
their two modules and this report. Neither old dependency node is staged.
