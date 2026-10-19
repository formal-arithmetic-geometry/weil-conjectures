## Worker report

Repair of the returned head 08e0ccb761ef (H2/H3, H1, H8). This delivery supplies the
previously absent owning module, its complete item `lean` record, this report, and
source/blueprint docstrings for every delivered declaration. There is one postponed
theorem, `AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageCoherence`.
Its docstring gives the complete nine-step proof; this stage does not prove it.
The other declarations construct or bundle the objects of this same comparison.
No definition contains `sorry`.

The owning module is `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence`.
All helper names below belong to `AlgebraicGeometry.Scheme.FiniteFreeDirectImage`.
The English statement, proof, and proof dependencies are unchanged. The only change
besides `lean` is adding the three already landed normalization/adjunction nodes to
`stmt_deps`, since their interfaces occur explicitly in the statement.

Hypotheses and objects, clause by clause:

- Arbitrary schemes and morphism: `{Z W : Scheme.{u}} (q : Z ⟶ W)`. There are no
  geometric restrictions, base field, properness, completeness, constructibility,
  boundedness, or finite-coefficient hypotheses.
- Actual small sites: `Z.ProEt`, `W.ProEt`, with `ProEt.topology`. Their object
  universe is `u+1`, morphism universe `u`; these are not identified. Coefficient
  sheaves and module values use universe `u+1`, with the existing derived-category
  instance at `u+2`. All variables/universes are bound and `autoImplicit` is false.
- Ring sheaves `R_T`, `S_T` and the fixed inverse-image isomorphisms: the two
  `Coefficients q` records `R`, `S`. The fields `target`, `source`, `identification`
  are precisely these objects and the specified `q⁻¹ R_W ≅ R_Z`, respectively.
- The two coefficient maps and their commuting square: `a : CoefficientMap R S`.
  Its equation is `R.identification.hom ≫ a.source = inverseImage.map a.target ≫
  S.identification.hom`; there is no additional condition on those maps.
- Finite freeness of `S_W` over `R_W` of rank `d ≥ 0`: `d : ℕ` and the displayed
  `Nonempty` isomorphism from scalar restriction of the unit `S_W`-module to
  `SheafOfModules.free (ULift (Fin d))` over `R_W`. This asserts existence of a
  global finite basis without choosing a basis as part of the comparison.
- Categories are `DerivedCategory (proEtaleRingModules T R_T)`, the ordinary
  unbounded derived categories of the already defined module-sheaf categories.
- Scalar extension is `(sT.presentation a).derived`. `Presentation` is an
  abbreviation of the landed `SuccessiveDerivedQuotient.Presentation`, whose
  ordinary objects/maps are precisely `changeOfRings`/`changeOfRingsHom` and whose
  derived functor has the universal derived counit. It is not a second tensor.
  The existential `ScalarModel` witnesses supply these universal presentations,
  their normalized adjunctions/associators and multiplication units; they are
  conclusions, not extra hypotheses on schemes or coefficient maps. All their
  data are fixed up to the canonical isomorphism of universal derived pairs.
- Pullback, direct image, and adjunction are the existing
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`, and
  `proEtaleRingDerivedAdjunction` at each supplied coefficient identification.

Conclusions and canonical normalizations, clause by clause:

- `balancing sW sZ a` is the canonical `μ`. It is constructed by
  `conjugateIsoEquiv` from `proEtaleRingRestrictionDerivedDirectImage`, whose
  identity-on-sections ordinary comparison and derived-unit normalization fix
  it uniquely, using scalar adjunctions normalized on flat K-flat complexes.
  Thus it is the ordinary balanced tensor comparison after localization, not an
  arbitrary isomorphism assumed to satisfy coherence. Its construction uses no
  downstream theorem about `comparison`.
- `comparison sW sZ a` is `mateEquiv` applied to `balancing.hom`, for the actual
  coefficient-specific pullback/direct-image adjunctions. By the mate definition
  its transpose is `μ` followed by `C_Z(ε_R)`, exactly the node's counit-tensor
  arrow. Its components are arrows in `D(S_W)`, before any scalar forgetting.
- Naturality is part of the natural-transformation type of `comparison`.
  `IsIso (comparison sW sZ a)` is invertibility of that very transformation.
- `NatTrans.CommShift (comparison sW sZ a) ℤ` is the input-shift square at every
  integer, with canonical cochain shifts. `scalarCommShift` is constructed as the
  left-adjoint shift of exact termwise restriction; no arbitrary shift structure
  is quantified. The first two conjuncts state triangulatedness of scalar
  extension and shift compatibility of its universal counit at both sites.
  The two further `IsTriangulated` clauses explicitly give exactness of the
  source and target composite functors of the natural isomorphism.
- Identity coefficients: `CoefficientMap.id R` keeps the given `c_R`, even if
  it is not literally an identity. `ordinaryUnit_pure` fixes multiplication as
  `r ⊗ x ↦ r • x`, and `unit_normalization` fixes its derived localization.
  The displayed composite `(unit_W).inv ≫ comparison_id ≫ Rq_*(unit_Z).hom = 𝟙`
  is exactly the identity assertion under these multiplication units.
- Tower: `a : CoefficientMap R S`, `b : CoefficientMap S B`, and `a.comp b` use
  the same three specified inverse-image identifications. The two `Nonempty`
  hypotheses say `S_W/R_W` and `B_W/S_W` are finite free, of ranks `d,e : ℕ`.
  `sT.normalization.derived a b` is the landed associator with its pure-tensor
  and flat K-flat normalization. In Lean's left-to-right `≫` order the equality
  is `π_BR = a_W.inv ≫ C_B/S,W.map π_RS ≫ π_BS ≫ Rq_B.map a_Z.hom`.
  This is the node's full equation, at every `M`, in `D(B_W)`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Qh`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly reexports the
  arbitrary ring-sheaf operations; the used declarations are `proEtaleRingModules`,
  `proEtaleRingModules_hasDerivedCategory`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, `proEtaleRingDerivedAdjunction` and
  `proEtaleSheafInverseImage` from the operations/canonical-adjunction modules.
- `Sheaf.Paper.EtaleDerivedScalarTensor`, the current recorded module for
  `lem-pur-derived-change-of-rings`, publicly reexports its unchanged general
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` interface. This
  arbitrary-ring-sheaf interface supplies the universal pairs used here;
  the constant-etale specialization itself is not used as a replacement.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its normalized comparison is cited in the proof. The equivalent construction
  here uses conjugation of the actual right adjoints.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.Presentation`, `Normalization`,
  `sectionTensor`, and `successive_derived_quotient_normalization`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, for the normalized
  scalar adjunction and its flat K-flat unit formula.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars`, `proEtaleRingRestrictionDerivedDirectImage`,
  `proEtaleRingSheafChangeAdjunction`, with the ordinary/derived normalizations
  stated in that module. `Mathlib.CategoryTheory.Adjunction.Mates` supplies
  `mateEquiv` and `conjugateIsoEquiv`.
- The stated proof modules for tensor functoriality, exact derived functors,
  independent-coefficient K-flat resolutions, and `derivedAdjunctionShiftCompatible`
  are imported. Mathlib supplies adjunction shifts and the free module sheaf.

Edge cases checked before and during the statement audit: rank zero uses `Fin 0`
and the zero free sheaf, including the zero ring; empty schemes impose no nonempty
hypothesis; zero complexes and all negative/zero/positive shifts are included;
identity `q`, identity coefficient maps with nontrivial fixed identifications, and
identity stages or zero-rank stages in a tower are included. Tensor multiplication
and the two tower associator directions have been checked against their source
signatures. No conclusion is moved to underlying abelian groups or scalar-forgotten
Hom sets. No statement dispute or source correction is needed.

Searches for an existing statement (2026-10-17):

- `msearch.py ... leanfinder "Finite free coefficient sheaves commute with unbounded
  derived direct image with canonical counit mate, shift and successive scalar
  coherence"`: eight free-sheaf/pullback/pushforward-adjunction hits, including
  `SheafOfModules.freeFunctorCompPullbackIso`; none is this derived coherence theorem.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.shiftFunctor"`:
  generic adjunction-shift compatibility and uniqueness declarations; used the
  adjoint shift construction, no finite-free comparison theorem found.
- `msearch.py ... grep "finiteFree.*(DirectImage|directImage)|projectionFormula|projection_formula"
  CategoryTheory`: zero Mathlib matches.
- `rg` searches for finite-free/projection-formula/coefficient-coherence names in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf`,
  plus the literal item identifier in upstream sources: no existing declaration
  containing all these clauses. The normalized tensor/scalar interfaces found in
  the project were reused. The local Stacks source at Tags 0B56 and 0944 was read;
  its finite-free proof supplies the basis reduction in the theorem docstring.

## Second reading by N4

Independent maintainer second reading, 2026-10-17, by the reviewer of immutable
head bcec2936b58d851ea087c93d01e026a9ca8ce1c8. I did not write or previously
second-read this delivery. This replaces the original section, which explicitly
described the author's own second pass rather than an independent reading.
The original Worker report and its historical validation evidence are preserved.

I read the item, all nine statement-dependency records, the complete delivered
module and its docstrings, and the exact dependency declarations in the read-only
N4 clone and pinned Mathlib. I checked Stacks sites-cohomology.tex, lines
13658–13710 (0B56/0944), against the defining counit map and finite-free argument.
The extra shift and tower equations are correctly described as extracted
coherences, not quoted clauses of 0944. No statement correction is needed.

Objects and hypotheses: `{Z W : Scheme.{u}} (q : Z ⟶ W)` is unrestricted.
`Coefficients q` supplies both ring sheaves and the specified inverse-image
isomorphism. `CoefficientMap` supplies the two ring maps and exactly their
commuting square. The actual `ProEt.topology` is used throughout. Site objects
have universe u+1 and morphisms u; coefficients/modules have universe u+1 and
the standard derived localization uses u+2. There is no equality of site
universes, constant-coefficient substitution, completion, boundedness,
constructibility, properness, torsion or base-field hypothesis.

Finite freeness: the displayed isomorphism from restriction of the S-unit module
to `SheafOfModules.free (ULift (Fin d))`, for `d : ℕ`, is precisely existence of
a global finite R-basis. Mathlib's `free` is the coproduct of unit modules.
The `Nonempty` here expresses the basis hypothesis; it does not choose the
comparison or replace a canonical construction.

Scalar and geometric operations: `Presentation` abbreviates the landed
`SuccessiveDerivedQuotient.Presentation`. Its ordinary object/map equations
fix changeOfRings/changeOfRingsHom and its universal counit fixes the derived
pair. `ScalarModel` is existentially supplied in the conclusion, not assumed.
Its normalized units, adjunctions and associators present those existing
functors; it introduces no new module category or tensor operation. The
geometric functors are the actual arbitrary-ring-sheaf `proEtaleRingDerivedPullback`
and `proEtaleRingDerivedDirectImage`, with the tensor-unit-normalized
`proEtaleRingDerivedAdjunction`.

Canonical arrow: `balancing` conjugates the normalized
`proEtaleRingRestrictionDerivedDirectImage` under the composite adjunctions.
That dependency fixes the ordinary map by identity on sections and the derived
map by its right-derived unit equation. `ScalarModel.adjunction_unit` fixes the
scalar adjunction on flat K-flat representatives. Thus conjugation gives the
balanced pullback comparison, not an arbitrary isomorphism. I checked
`conjugateIsoEquiv` and `mateEquiv` in Mathlib: the final symmetry in balancing
has the required direction, and comparison has transpose μ followed by the
scalar image of the R-counit, exactly as in the node.

Conclusions: comparison is a natural transformation into D(S_W); `IsIso` refers
to that transformation itself. `NatTrans.CommShift ... ℤ` uses the adjoint shift
of exact termwise restriction, with universal-counit shift compatibility in
the first two conjuncts. The two composite `IsTriangulated` assertions give
exactness of the source and target. These are the canonical cochain shifts,
including the negative shifted differential, not freely supplied structures.
All equalities remain in the coefficient module derived categories.

Identity and tower: the unit is fixed by `ordinaryUnit_pure` (multiplication)
and `unit_normalization` (localization counit). The identity equation is exactly
unit_W.inv, comparison_id, then Rq_*(unit_Z.hom). The tower uses the landed
normalized associator, with its sectionwise and K-flat formulas. Reading `≫`
left to right, its four factors are a_W.inv, C_B/S,W(π_S/R), π_B/S evaluated
at C_S/R,Z(M), then Rq_B(a_Z.hom), exactly the node's equation in D(B_W).
Both finite-free hypotheses and all three coefficient identifications are
present. The basis is used only to detect invertibility, not to define π.

Edge cases checked: d=0 and e=0, zero coefficient ring and zero complexes,
empty schemes, q=id, identity stages in a tower, and identity coefficients
with a nontrivial specified inverse-image identification. Fin 0 gives the empty
coproduct/zero object, and the right adjoint preserves the terminal zero object.
There is no nonempty or nonzero assumption. All integer shifts and unbounded
complexes remain covered.

Independent duplicate searches used rg for projection-formula, finite-free
pushforward/direct-image and coherence terminology in Mathlib, the N4
lean/Sheaf and lean/WeilConjectures trees, and slopmaster2/WeilConjectures.
Existing projection-formula, finite-constant, coefficient-forgetful and
completed-scalar interfaces do not state this arbitrary-ring-sheaf theorem
with its coefficient-linear identity/shift/tower equations. Existing categories,
scalar extension, adjunction and normalized associator are reused. No new
independent notion or missing DAG prerequisite needs a new node here.

Mechanical checks: lean.statement is byte-for-byte the theorem signature;
all ten named owning declarations are recorded; no line exceeds 100 characters;
module and declaration docstrings identify source and blueprint, and the main
statement docstring gives all nine proof steps. There is one theorem and its
entire proof is sorry. Definitions contain real data. The elementary category-law
proof fields in identity/composition of coefficient squares merely construct
those records; no mathematical theorem is proved locally.

Reproduced the immutable module through the prescribed scompile.py wrapper.
Exit 0, no errors or warnings: sandbox 16.1 s, owning library module 18.9 s;
private overlay /dev/shm/nt-tmp/nt-local-compile-75n8aasg/.lbuild. The wrapper
currently performs server confirmation; no direct ssh, global build, live Lean
write, project-clone edit, git mutation or delivery command was run by me.

Finding H11: the original second-reading section was explicitly a self-review.
This independent section supplies the missing review and clause audit. No
mathematical, Lean, node-record, universe or source correction was required.

## New nodes

None. The auxiliary records bundle existing notions needed to state this node's
canonical comparison. The three added statement dependencies already exist and
are landed nodes; their declarations are reused unchanged.

## Dependency modules

None. The currently recorded dependency modules reexport the required general
interfaces, and no dependency record is changed by this delivery.

## Validation

Every compile uses the prescribed `scompile.py` wrapper, one delivered file at a
time, against the current live/side overlay; no global build is run. Final clean compile:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py N4 lem-sp-finite-free-direct-image-coherence /home/ubuntu/weil-newtargets-stage2-sandbox/N4/lem-sp-finite-free-direct-image-coherence/lean/Sheaf/AlgebraicGeometry/FiniteFreeDirectImageCoherence.lean`

Exit 0, no errors or warnings. Private overlay
`/dev/shm/nt-tmp/nt-local-compile-xop092e5/.lbuild`: sandbox file 16.2 seconds,
owning library module 14.6 seconds, each compiled separately. The exactness instance
is available through the published `PbcActualScalarPullback` import; no new
exactness hypothesis or local instance is imposed.

`deliver2.py N4 lem-sp-finite-free-direct-image-coherence --no-push` returned
`OK (dry run): commit ba6be1f29e passes the preflight and compiles; nothing pushed`.
All three expected files were staged: the item JSON, owning Lean module, and report.
