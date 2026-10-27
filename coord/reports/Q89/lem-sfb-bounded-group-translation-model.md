## Worker report

The delivery states `AlgebraicGeometry.exists_bounded_group_translation_model` in
`Sheaf.AlgebraicGeometry.BoundedGroupTranslationModel`. Its only postponed proof is the
whole proof of that named theorem. All definitions have explicit data/formulas. The node's
statement, proof, proof dependencies and source remain verbatim; statement dependencies gain
only the two new definition nodes described below.

Source checked: BLR, Néron Models, 1.1 Definition 2 and 4.3 Proposition 4(iii), printed
pp.106–107, in the primary Stony Brook scan named by the node. The local literature copy
is still WANTED. The proposition's local base change is the local ring at a generic point
of the special fibre of a smooth test scheme, exactly as the assigned node specifies.
The theorem docstring carries all four accepted proof steps and their dependency names.

Hypothesis and clause correspondence:

- R is a DVR: `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
- E is its fraction field: `[Field E] [Algebra R E] [IsFractionRing R E]`.
  The base is `Spec (.of R)`, and its residue field is built into
  `Y.hom.fiber (IsLocalRing.closedPoint R)`. No separately chosen residue field is substituted.
- G is an E-group scheme: `G : Over (Spec (.of E))` and `[GrpObj G]` use the existing
  category of schemes over E and group-object diagrams. No commutativity is assumed.
- Smooth, separated, finite type: `[Smooth G.hom] [IsSeparated G.hom]`,
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`. IsSeparated is exactly the condition
  that the diagonal is a closed immersion.
- A geometric point over the closed point: `[Field Ω] [IsAlgClosed Ω]`,
  `t : Spec (.of Ω) ⟶ Spec (.of R)`, and `ht : ∀ x, t x = IsLocalRing.closedPoint R`.
- Its strict henselization is the recorded `Scheme.strictHenselizationRing t`.
  `HasBoundedStrictHenselianPoints R E t G` quantifies a genuine fraction field F and
  an E-to-F homomorphism agreeing with the canonical R-to-strict-henselization map.
  Spec.preimage extracts that canonical ring map from the recorded structural morphism.
  F is not an arbitrary extension: `IsFractionRing` fixes the fraction-field property.
- Boundedness uses `HasBoundedValuedPoints`: finite `Fin n` affine opens covering G;
  E-algebras `B i`; isomorphisms from their spectra over E; finite generating lists
  with `Algebra.adjoin E (Set.range ...) = ⊤`; subsets C of the affine F-points that
  cover all G(F), with the correct E-structure; and a common nonzero denominator d.
  For a DVR a finite collection of integer lower valuation bounds is equivalent to
  this denominator condition. If c is the minimum lower bound, take a sufficiently
  high nonnegative power of a uniformizer as d; conversely d gives the lower bound
  minus its valuation. Both encodings include zero coordinates. The denominator is
  quantified in the actual strict-henselization ring, not a replacement valuation ring.
- The output `Y : Over (Spec (.of R))` has Smooth, IsSeparated, LocallyOfFiniteType and
  QuasiCompact of its structure map. `e` is an isomorphism in the category over E
  from its actual generic pullback to G. Nonempty of the special fibre is explicit.
- Every smooth finite-type Z is quantified, without an added separatedness assumption.
  ξ ranges over the actual special fibre. Membership of its closure among irreducible
  components is written as `∃ C ∈ irreducibleComponents ..., IsGenericPoint ξ C`.
- A is exactly `Z.left.presheaf.stalk (Z.hom.fiberι _ ξ)`. The domain and DVR structures
  are conclusions, existentially quantified before taking its `FractionRing` L.
- The spectrum map `j : Spec L ⟶ Spec E` is supplied in the conclusion with the
  commutative structural square `hj`. This states existence of the induced E-structure
  on L, so the translation assertion cannot become vacuous for lack of such a map.
  Its uniqueness is the fraction-field universal property. No E-algebra hypothesis on
  this stalk is assumed.
- `g : Over.mk j ⟶ G` means every point of G(L); `right : Bool` selects both sides.
  `IsGenericGroupTranslation` tests τ on every scheme W over L using the already defined
  group structure on Hom into G. For true it is x*g, for false g*x. Testing all W is
  the functor-of-points characterization of the actual translation morphism.
- `translationModelGenericComparison` is constructed from `Over.pullbackComp`, equality
  transport along hj, and the pullback of e. Its displayed conjugation transports τ
  to the generic fibre of the actual local base change Y_A, with no arbitrary map choice.
- `HasFiberwiseBirationalExtension` gives an A-morphism f from an open U of Y_A,
  whose generic base change is τ under that comparison, with U and the image of f
  dense in every fibre. `IsOpenImmersion f.left` makes f an isomorphism onto that open
  image, hence represents precisely an A-birational map. Its final universal condition
  makes U the full domain of definition, not merely a smaller domain on which the
  map happens to be an open immersion.
- There is no output group structure or mapping-property condition on Y.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom, Spec, Spec.map.
- Mathlib.RingTheory.DiscreteValuationRing.Basic: IsDiscreteValuationRing.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: recorded base-change convention;
  actual scheme base changes are CategoryTheory.Over.pullback / Limits.pullback, and
  Mathlib.AlgebraicGeometry.Fiber supplies Scheme.Hom.fiber and Scheme.Hom.fiberι.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and Separated:
  AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsSeparated.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj; the group on Hom is the
  existing CategoryTheory.Hom.group. The recorded group-scheme interface was also
  read in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Mathlib.FieldTheory.IsAlgClosed.Basic and Mathlib.AlgebraicGeometry.ResidueField:
  IsAlgClosed and Scheme.SpecToEquivOfField (the latter's signature was checked; the
  geometric point itself is used directly as authorized by its dependency record).
- WeilConjectures.AlgebraicGeometry.StrictHenselization:
  Scheme.strictHenselizationRing; its adopted structural morphism is
  Scheme.strictHenselizationStructuralMap in the corresponding StructuralMap module,
  cited by the new bounded-points node.
- Mathlib.AlgebraicGeometry.Morphisms.Proper is a plain proof import for the stated
  lem-pc-proper-base-change. Its smooth base-change instance is in the already public
  Smooth module. The other assigned proof nodes currently have no lean record and
  add no imports. None is needed to type this statement, and none is restated here.

Edge cases checked: the empty affine cover describes only an empty scheme, so cannot
satisfy the group hypothesis; empty generating lists allow zero-dimensional charts;
zero coordinate values satisfy the denominator condition; negative valuation bounds
are allowed through a nonzero denominator; no residue characteristic, completeness,
excellence, properness, connectedness or commutativity hypothesis is added. Empty test
schemes have no special-fibre generic points and give the intended vacuous local clause.
Disconnected test schemes and special fibres are included through the component-generic
point quantifier. Both translations include the identity element. The trivial group is
included. On a trait the fibrewise density test is exactly density in the two fibres;
the helper's all-base-points form also handles empty fibres correctly. All variables
and universes are explicit; autoImplicit is disabled. A common universe u is arbitrary
and can be enlarged for all the scheme/ring objects.

Searches: msearch leanfinder with “A bounded smooth algebraic group over a discrete
valuation field has a smooth model on which left and right translations extend
birationally” returned Weierstrass good reduction and standard-smooth algebra results,
not this theorem. Loogle “AlgebraicGeometry.Scheme.Birational, CategoryTheory.GrpObj”
returned zero hits. msearch grep “BirationalOver|birational|valuation” in AlgebraicGeometry
found ordinary birational maps and valuation primitives. LeanSearch “Bounded rational
points of a scheme over a discretely valued field” found valued integer rings and
valuation bounds, not coordinate boundedness. LeanFinder “Fibrewise dense open subschemes
and relative birational maps over a base scheme” and LeanSearch “A rational map defined
on an open dense in every fibre of a scheme morphism” found ordinary dense-domain
PartialMap/RationalMap, which do not impose density in the special fibre. Mathlib,
WeilConjectures and Sheaf were searched by rg for the new declaration names and by
concept (Neron, birational, fibrewise/fiberwise dense, bounded points). No matching
notion was found. The upstream name index and the item-id search in WeilConjectures
also provide no matching statement. blueprint_refs search of “fibrewise dense” and
“bounded valued points” returned zero blueprint nodes. The DAG's relevant bounded
Néron-model statements introduce these notions inline; no existing definition node
carries them. Raw outputs of the three search kinds and source/project grep are stored
in each new node's mathlib_searches.

Validation: every delivered Lean file was compiled separately in dependency order by
scompile.py against the live published library. They compile with no errors or additional
warnings. No statement correction or STATEMENT-DISPUTED flag is needed.

## New nodes

`def-sfb-bounded-valued-points`, module Sheaf.AlgebraicGeometry.BoundedValuedPoints,
defines finite affine coordinate boundedness by a common denominator and its strict-
henselization specialization. Source: BLR 1.1 Definition 2 and 4.3 Proposition 4.
The searches above show that the valuation primitives exist, while the scheme-point
boundedness predicate does not. Its two declarations are one notion and its exact
strict-henselian specialization; it constructs no model and postpones no theorem.

`def-sfb-fiberwise-birational-extension`, module
Sheaf.AlgebraicGeometry.FiberwiseBirationalExtension, defines fibrewise density and
the existence of a maximal-domain birational extension by an open immersion. Source:
BLR 2.5 and 4.3 Proposition 4(iii). Ordinary Mathlib rational maps only require total-space
density, so they cannot replace density in every trait fibre. This new predicate uses
existing scheme fibres, opens and open immersions directly and has no postponed proof.

## Second reading by Q89

Written by the maintainer's independent reviewer, because the delivered section was only the
author's own self-check. It replaces that section; the Worker report above is unchanged.
I read the item node (BLR 4.3 Proposition 4(iii) and 1.1 Definition 2), the two new nodes,
the dependency records, the three delivered modules and the cited Mathlib/upstream declarations.

Clause by clause (node → Lean → verdict):

- R a DVR, E = Frac R, T = Spec R → `[IsDomain R] [IsDiscreteValuationRing R]`,
  `[Field E] [Algebra R E] [IsFractionRing R E]`, base `Spec (.of R)`. Correct.
- k = R/m_R, fibres as base changes → `Scheme.Hom.fiber` at `IsLocalRing.closedPoint R`
  (Mathlib pullback along the residue field). Correct; no separate residue field chosen.
- G/E smooth separated finite-type group scheme → `G : Over (Spec (.of E))`, `[GrpObj G]`
  (recorded def-sc-group-scheme interface), `Smooth`, `IsSeparated`,
  `LocallyOfFiniteType` + `QuasiCompact`. Correct; no commutativity or connectedness added.
- geometric point over the closed point → `Ω` algebraically closed, `t`, `ht`
  (def-weil-geometric-point inline form). R^sh = `Scheme.strictHenselizationRing t`
  (recorded def-weil-pbc-strict-henselization-limit). Correct.
- boundedness of G(E^sh) → `HasBoundedStrictHenselianPoints R E t G`: some fraction field F of
  R^sh with E → F agreeing with R → R^sh → F (via `Spec.preimage` of the recorded
  `strictHenselizationStructuralMap`); such F and E → F exist and are unique up to unique
  isomorphism (R → R^sh injective, R → E epi), so existence is not weaker than the node.
  `HasBoundedValuedPoints`: finite affine cover `Fin n`, K-algebras B_i with Spec B_i ≅ U_i
  over K, finite generating lists (`Algebra.adjoin = ⊤`), C_i ⊆ U_i(F) over E covering every
  `Over.mk j ⟶ G`, and one d ≠ 0 in R^sh with d·b_ij(x) ∈ R^sh. Since R^sh is a DVR with
  fraction field F, this is equivalent to integer lower bounds c_i (take d = π^max(0,-min c_i);
  conversely c_i = -v(d)); zero values are covered. Correct.
- output Y: smooth separated finite-type T-scheme, nonempty special fibre, Y_E ≃ G →
  `Y : Over (Spec (.of R))`, `e` an isomorphism over E, the four morphism classes, `Nonempty`
  of the closed fibre. Correct.
- every smooth finite-type Z, every generic point ξ of Z_k → `Z` with `Smooth`,
  `LocallyOfFiniteType`, `QuasiCompact`; `ξ` in the closed fibre with
  `∃ C ∈ irreducibleComponents, IsGenericPoint ξ C`. Correct; no separatedness added.
- A = O_{Z,ξ} a DVR, L = Frac A → `stalk (fiberι ξ)`, `IsDomain` and `IsDiscreteValuationRing`
  as conclusions, `FractionRing`. Correct.
- the E-structure of L → `∃ j, hj` (commuting square). It exists (A is R-flat, so π is a
  nonzerodivisor of A) and is unique (Spec E → Spec R is a monomorphism), so no choice
  enters and the clause is not vacuous. Correct.
- left/right translation by g ∈ G(L) → `g : Over.mk j ⟶ G`, `right : Bool`, `τ` with
  `IsGenericGroupTranslation`: for every W over L and x, x ≫ τ corresponds under
  `Over.mapPullbackAdj j` to x·g (right) or g·x (left) in the Mathlib group on Hom into G.
  By Yoneda τ is exactly the translation. Correct.
- extends to a Spec A-birational self-map of Y_A, open immersion on its domain of definition →
  `HasFiberwiseBirationalExtension q Y_A (cmp.hom ≫ τ ≫ cmp.inv)`, cmp =
  `translationModelGenericComparison` (canonical: `Over.pullbackComp`, eqToIso along hj,
  pullback of e). The helper gives U ⊆ Y_A and an A-morphism f : U → Y_A with f_L = τ|U_L,
  U and f(U) dense in both fibres, f an open immersion (so an isomorphism between Spec A-dense
  opens, i.e. birational), and every V with an extension h satisfies V ⊆ U. The last clause
  is the domain of definition, not stronger: Y_A is flat (smooth) and separated over A, so h
  and f agree on V ∩ U (generic fibre schematically dense) and glue to a representative on
  U ∪ V. Correct.
- no group law or mapping property on Y → none asserted. Correct.

Edge cases: empty Z (no ξ, vacuous); disconnected Z_k (component-generic quantifier); g = e;
trivial G; empty fibres in the density predicates (vacuous); negative valuation bounds
(d ≠ 0); universes: everything in one u, as Scheme morphisms require.

One definition per notion: rg in Mathlib, lean/WeilConjectures and lean/Sheaf of the live clone
for fibrewise-dense opens, rational/birational extensions and bounded points found only
Mathlib's `Scheme.Birational(Over)`/`PartialMap` (total-space density only) and unrelated
`*RationalMap` defs; grep of def-* nodes in dag/nodes for S-rational maps, fibrewise density
and bounded points found no carrier. The two new definition nodes are needed; their fields
(import_flags [], three search kinds, created, blueprint, lean_audit, stmt_deps = cited ids)
follow brief-stage2 §5. The item changed only in `lean` and by adding the two new nodes to
`stmt_deps`.

Form: no hollow definition; the only `sorry` is the theorem; module and declaration
docstrings carry source place and blueprint id; the theorem docstring carries the four
proof steps; `lean.statement` fields are verbatim substrings of the files; no line over 100.
Advisory: the private import `Mathlib.AlgebraicGeometry.Morphisms.Proper` is not needed for
the statement (recorded as a proof import for lem-pc-proper-base-change).

Verdict: the statement says what the node and BLR 4.3/4(iii) say.
