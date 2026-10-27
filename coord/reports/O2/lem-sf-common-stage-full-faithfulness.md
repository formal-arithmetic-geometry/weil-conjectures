## Worker report

Item: lem-sf-common-stage-full-faithfulness. The module
`Sheaf.Paper.SfCommonStageFullFaithfulness` states
`WeilConjectures.sfCommonStageFullFaithfulness`, with one named theorem and
`sorry` as its entire proof. It constructs no replacement categories or functors.
The node changes only in `lean`. No new nodes, dependency repairs, or statement
corrections are needed. No statement dispute was found.

Hypotheses and clauses, in node order:

- Prime ell is `(l : ℕ) [Fact l.Prime]`; the algebraic closure is
  `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The base field is `(k : Type u) [Field k]`; invertibility is
  `_hl : IsUnit (l : k)`. The schemes are `Z X : Scheme.{u}`, with structure
  maps `z` and `x` to `Spec (.of k)`. Each is `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`, exactly separated finite type.
  These assumptions are retained although the categorical argument uses none
  of their geometric content.
- The finite fields are `Padic.FiniteCoefficientFields l Ω`. The rational
  categories are the recorded `GeneralAlgebraicallyClosedCoefficients.Stage`.
  Their small coefficient models are equivalent copies of the finite
  subfields, not a restriction on Ω's universe. StageSystem uses the recorded
  tensor transitions and canonical associators, fixed by
  `stageSystem_existsUnique`. The pair categories in the conclusion are the
  recorded `generalAlgebraicallyClosedConstructibleCategory l Ω Z` and its X
  counterpart. These are literally `stageSystem.PairCategory`; their arrows
  are the existing quotient classes, not a Karoubi completion or new colimit.
- `F : StageSystem.Morphism` of those two particular systems supplies all
  `Phi_E` as `F.Φ E`. The natural isomorphism `F.β h` has direction
  `Phi_E ⋙ T_X ≅ T_Z ⋙ Phi_L`; thus it is exactly the inverse of the node's
  theta. It has no exactness, linearity, or essential-surjectivity fields.
- `hΦ : ∀ E, (F.Φ E).FullyFaithful` supplies exactly the finite-stage Hom
  bijections, with their unique preimages.
- `F.coh` is the tower square. With left-to-right Lean composition it reads
  `T_X(beta_EL) ≫ beta_LM ≫ Phi_M(a_Z) = a_X ≫ beta_EM`.
  Multiplying by beta inverses gives exactly the node's displayed theta
  equation. No extra coherence is imposed.
- `_hunit` is identity normalization in the actual tensor model:
  `beta_EE = unit_X ≫ Phi_E(unit_Z inverse)`. HEq only accommodates the
  published equality between `stageSystem.T` and the tensor transition;
  its endpoints are identified by `stageSystem_existsUnique`. It does not
  identify different canonical maps. Under the specified unit identifications
  this equation is theta_EE = identity. Literal identity transitions are not
  silently substituted for the published tensor functors.
- `∃ h : F.functor.FullyFaithful` asserts full faithfulness of the existing
  functor, whose quotient construction already proves well-definedness,
  identity and composition. Its `preimage`, `map_preimage` and `preimage_map`
  fields give the inverse Hom map and its two inverse identities.
- The first conjunct is the exact object formula `(E,P) ↦ (E,Phi_E P)`.
- The second conjunct gives the forward formula on every `mkHom L hA hB u`:
  `beta_source ≫ Phi_L(u) ≫ beta_target inverse`, which is the node's
  theta_source inverse, Phi_L(u), theta_target in Lean composition order.
- The third conjunct gives the inverse on every target representative:
  `h.preimage [L,v] = [L, (hΦ L).preimage
    (beta_source inverse ≫ v ≫ beta_target)]`.
  The inner finite preimage is precisely b_L inverse(v). The same globally
  defined `h.preimage` occurs for ALL choices of L and v. Consequently equal
  classes have equal inverse classes, including representatives obtained by
  any enlargement. This is the explicit representative-independence clause,
  rather than merely an unspecified assertion of bijectivity.
- No essential-surjectivity or scalar-transition-full-faithfulness assumptions
  occur. There is no Karoubi envelope.

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is a convention record with no owning
  declaration. Its separated and finite-type notions are the Mathlib
  `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.Separated` and `.FiniteType`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, retains all the coefficient
  constructions by public import. The theorem itself uses the finite-field
  index recorded in the pair-category dependency, not a new coefficient type.
- `Sheaf.Paper.SfRationalizationKaroubi`,
  `WeilConjectures.sfRationalConstructibleCategory` and
  `sfRationalScalarExtension`: the raw stages and their scalar extensions.
- `Sheaf.Paper.SfScalarExtensionComposition`,
  `WeilConjectures.sfRationalScalarComp` and `sfRationalScalarUnit`: the
  canonical associators and multiplication units reused by the next module.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
  `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.Stage`,
  `stageSystem`, `unitor`, `Pair`, `representatives`, and
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`: the
  prescribed intrinsic pair categories and their eventual-equality criterion.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`,
  `CategoryTheory.StageSystem.Morphism`, `.mapAt`, `.functor`,
  `.tr_mapAt`, and `.functor_map_mkHom`: existing coherent descent construction.
- `Mathlib.CategoryTheory.Functor.FullyFaithful`,
  `CategoryTheory.Functor.FullyFaithful` and `.preimage`: full faithfulness
  includes the two inverse identities. The main theorem's docstring records
  all six proof steps from the node, citing the pair-category dependency.

Edge cases checked before drafting: either or both schemes may be empty;
zero objects and zero arrows remain ordinary representatives; E = E' and
L = E are covered by le_refl and the unit square; repeated fields in the
coherence square are allowed; no transition injectivity is used when different
representatives become equal only later. Both endpoints need not have the
same field. The finite-field index is nonempty (it contains Q_l) and directed
by composita, so no artificial nonempty-index hypothesis is added. Ω has its
own universe v, independent of the scheme/coefficient-model universe u.
Characteristic zero and positive characteristic different from ell are both
covered by IsUnit. No finite-field datum is imposed on the base.

Searches (2026-10-22):

- msearch.py leanfinder: "A coherent family of fully faithful functors induces
  a fully faithful functor on common-stage pair categories, with inverse on
  representatives". Eight hits: induced-category full faithfulness, comma
  constructions, fullyFaithful.ofCompFaithful and filtered intermediate
  inclusions; none states this descent theorem.
- msearch.py loogle: "CategoryTheory.Functor.FullyFaithful,
  CategoryTheory.StageSystem.Morphism". Zero hits: StageSystem is upstream,
  not a Mathlib identifier. The follow-up "CategoryTheory.Functor.FullyFaithful"
  gave twelve hits, including the structure, preimage, hom-equivalence and
  composition APIs; no stagewise descent theorem.
- msearch.py grep: "StageSystem|commonStage|[Ff]ully[Ff]aithful.*filtered"
  in CategoryTheory. Five hits in Filtered/Final.lean concern filteredness and
  finality, not descent of Hom bijections.
- msearch.py leansearch: "A morphism of directed stage systems with fully
  faithful component functors induces a fully faithful functor on the pair
  categories". Eight hits concern induced categories, the FullyFaithful
  structure, mapMon and ofCompFaithful; no exact match.
- rg over lean/WeilConjectures and lean/Sheaf for common-stage/full-faithfulness
  patterns found the existing StageSystem.Functor construction and the more
  specialized framework descent module, but no theorem with stagewise full
  faithfulness or the inverse representative formula. A search of
  lean/WeilConjectures for the exact node id found nothing. Restrict.lean has
  full-subcategory inclusions, not arbitrary fully faithful component functors.
  The exact chosen declaration name was absent in both project roots.

Validation: prescribed scompile.py compiled the sandbox and final library
module separately, in 17.2 s and 12.4 s, with no errors or non-sorry warnings.
The only postponed theorem is the item's own matching declaration. All
universes and variables are explicit and autoImplicit is disabled.

## Second reading by O2

The dispatcher brief assigns the maintainer an independent review and prohibits
starting another agent. This section records the worker's final second pass,
not an independent-agent review. I reopened the node, its six proof steps and
the complete module. I checked the beta/theta reversal against both displayed
formulas, and checked the tower square by multiplying by inverse beta factors.
I checked the identity hypothesis against the actual tensor unitor rather than
requiring a literal equality T_EE = identity. I checked that the existential
FullyFaithful witness supplies both inverse identities and that its preimage
formula is quantified over every pair, common field, inclusion and target
representative, hence retains both independence assertions. The geometric
hypotheses, arbitrary field k and independent Ω universe are present; no
extra exactness, linearity, essential-surjectivity or scalar-faithfulness
assumptions slipped in. No mismatch or correction was found in this pass.
The item's original statement and dependency lists are unchanged.
