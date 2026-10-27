## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeProperSetSheafBaseChange` states
`AlgebraicGeometry.scheme_proper_setSheaf_baseChange`, with its entire proof `sorry`.
The only supporting definition is `AlgebraicGeometry.Scheme.setSheafBaseChangeSquare`:
it constructs the transposed actual scheme pullback square using
`pullback.condition.symm`, `pullbackSymmetry p v`, and its two projection equations. Its data contains no `sorry`.

Source read: Stacks `etale-cohomology.tex`, label
`lemma-proper-base-change-f-star` (Tag 0A3U), including the adjoint-unit definition
of the canonical map and the stalk proof. The node's five proof steps are carried
in the theorem docstring, including the represented-germ compatibility omitted
by Stacks. Also read the current blueprint unit at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.

Clause-by-clause rendering:

- The scheme base is `(S : Scheme.{u})`.
- The schemes over S are `(X Y Y₁ : Over S)`. Their underlying schemes are `.left`;
  the structure arrows and compatibility of morphisms over S are bundled in `Over`.
- The proper S-morphism is `(p : X ⟶ Y) [IsProper p.left]`. This is scheme properness,
  explicitly the scheme convention to which the node's space-properness definition
  agrees. The properness definition is separated, universally closed and locally
  finite type; universal closedness supplies quasi-compactness, giving finite type.
- The arbitrary S-morphism is `(v : Y₁ ⟶ Y)`, with no property instance.
- X₁ is literally `pullback p.left v.left`, with w = `pullback.fst p.left v.left`
  and p₁ = `pullback.snd p.left v.left`; the helper directly chooses the
  transposed square `(p₁,w,v,p)` using `pullbackSymmetry p.left v.left`. Thus no unintroduced or arbitrary comparison map occurs.
- Every set sheaf is quantified as `A : Sheaf X.left.smallEtaleTopology (Type (u + 1))`.
  `u` is explicit; small etale objects live in `u+1` and morphisms in `u`.
  This is the existing project's set-sheaf size convention, without equating the
  object and morphism universes or restricting stalks to finite sets.
- The map is the existing `Etale.setBaseChangeArrow` on the transposed chosen square.
  Its source is v⁻¹p_*A and its target is p₁,*w⁻¹A. In the definition's notation,
  `(f,g,h,e) = (v,p,p₁,w)`, so it pulls back p_*(unit_w), applies the canonical
  direct-image composition comparisons, and then the v counit.
  `setUnderivedExchangeSectionwise` clause (1) identifies precisely this arrow
  with the adjoint under p₁ of the inverse-image square comparison followed by
  w⁻¹(counit_p). This is exactly the map the node specifies, not merely an
  unspecified morphism of the same endpoints.
- Invertibility is `∀ A, IsIso (Etale.setBaseChangeArrow ... A)`.
- Naturality is the second conjunct, for each `a : A ⟶ B`: the source functor's
  map on a followed by β_B equals β_A followed by the target functor's map on a.
  Together with invertibility this gives the natural comparison isomorphism.
- No group structure, torsion, Noetherianity, finite presentation, or surjectivity
  occurs in the binders or conclusions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its representable, etale, surjective, small-site and topology definitions.
- `def-weil-size-convention` is a convention record, implemented by explicit `universe u`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  the same record retains Mathlib's `Sheaf` for the sheaf clause.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: the recorded `cotangentRingMap`
  and publicly imported `EnlargedEtaleRingedSite` scheme-restriction model,
  `enlargedSetEquivalence`, `enlargedSmallDirectImage`, and its geometric morphism.
  These are context for the algebraic-space formulation; scheme sites and their
  adjunctions are used directly here, as the node concerns schemes.
- `Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism`:
  `AlgebraicSpace.enlarged_chart_ringed_morphism`, including geometric adjunctions
  and their transport to scheme-object small sites.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; schemes here use the actual Mathlib pullback.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsProper` and its component predicates; for schemes the stated agreement
  uses Mathlib's `IsProper`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including both projection equations.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`:
  `Etale.setUpperLowerAdjunction`, `Etale.setBaseChangeArrow`.
- Proof-only `Sheaf.AlgebraicGeometry.SetUnderivedExchangeSectionwise`:
  `setUnderivedExchangeSectionwise` identifies the counit transpose in proof step 1.
  Its module is imported without `public`; no declaration from it occurs in the
  delivered signature or helper definition.

The two definition nodes `def-weil-pbc-cartesian-square` and
`sbc-def-base-change-map` are added as already-landed statement dependencies.
`proof_deps` is retained exactly as on sheaf-dag. The sectionwise module remains
a non-public import for the docstring's counit-transpose justification; its node
is not added to either dependency list, following the corrected H2/H7 review.
This adds no new node or duplicate notion.

All recorded proof-dependency modules are imported without `public` unless already
statement dependencies. They include `EtaleSectionsBaseFieldExtension`,
`EtaleSetInverseImageCompositionUnits` (through the proof-only sectionwise module),
`EtaleSetInverseImageStalkGerm`, `SetsPushforwardStalkStrictHenselization`,
`StrictHenselizationFunctoriality`, and `BaseChangeTheorems.DegreeZero`.
Mathlib proof leaves are the proper base-change instances, the separated-to-quasi-
separated instance, and the geometric-point conservative-family theorem.

Proof-interface observation: the recorded strict-henselian H⁰ theorem in
`DegreeZero` has module coefficients; it does not itself provide the arbitrary-set
clause of that DAG node. This is only a proof dependency here, and the present
statement does not substitute an abelian theorem for the set-valued assertion.
Its source-based set interface will be needed when proving this item in stage 3.
The current theorem and its canonical exchange are fully typed without that interface.

Edge cases checked before writing: p=id and v=id give the usual identity comparisons;
X empty and empty geometric fibres have singleton section sets; Y₁ empty gives
sheaves on the empty target, so the stalk criterion uses the empty family. A set
sheaf need not have a global section, and no inhabitedness is assumed. A proper
closed immersion need not be surjective, and is admitted. Non-Noetherian proper
schemes and arbitrary base changes are admitted. The pullback is canonically over S
by composing either projection with its structure map, by `Over.w` and the pullback
condition. There is no finite-presentation or constant-sheaf specialization.

Searches for an existing full statement (2026-10-24):

- `msearch.py ... leanfinder "Proper base change for arbitrary sheaves of sets on small etale sites of schemes"`:
  eight hits, including properness stability, etale stability and the small site;
  none states the sheaf exchange is invertible.
- `msearch.py ... loogle '"baseChange", "Sheaf"'`: two hits, both abstract
  precoverage sheaf-condition equivalences; no proper set-sheaf theorem.
- `msearch.py ... grep 'proper.*(sheaf|baseChange)|baseChange.*proper' AlgebraicGeometry`:
  25 hits, morphism-property and site infrastructure, not this assertion.
- `msearch.py ... leansearch "Proper base change for arbitrary etale sheaves of sets"`:
  eight hits concerning ring etale base change and proper/etale scheme stability.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for proper/set/base-change
  combinations, `setBaseChangeArrow`, and the exact node id: no existing theorem
  for proper arbitrary set sheaves; found and reused the exchange definition and
  its sectionwise/counit-transpose theorem. Flat degree-zero base change has a
  different hypothesis. Existing proper degree-zero results use algebraic coefficients.
- Searched public constructions of `ChosenCartesianSquare`: the exact generic
  scheme pullback construction is not public; existing generic flipped helpers
  are private, and public geometric-fibre helpers require a field-valued base map.
  The helper in this delivery fills the actual square fields only.

There is no statement correction and no STATEMENT-DISPUTED finding.

Validation: `scompile.py Q30 lem-sfb-scheme-proper-set-sheaf-base-change <module>`
compiled the repaired sandbox and library modes cleanly (2.5 s each), with no errors
or warnings. Every variable and universe is bound explicitly; autoImplicit is false.

## Second reading by Q30

A separate rereading of the node and completed source checked the square orientation:
directly constructed `(p₁,w,v,p)` on `pullback p v`, hence precisely
v⁻¹p_* → p₁,*w⁻¹. There is no call to `exchangeTranspose` in the module.
Checked the source of `setUnderivedExchangeSectionwise` clause (1): its p₁-adjunction
and w-pulled p-counit agree with the node's defining transpose. Checked the second
conjunct against the node's naturality clause: its left side uses β_B and its right
side β_A, with the source and target functor maps in their correct order.
`Over S` retains all structure morphisms and their compatibility, rather than adding
an auxiliary hypothesis. `IsProper p.left` is scheme properness and no property of
v is imposed. The helper uses canonical pullback symmetry to construct the
transposed actual fibre-product square, with both projection equations. All set sheaves in the project's universe convention
are quantified; no additive or finiteness condition appears. No mismatch or change
was found in this rereading. This is the dispatcher's single-worker delivery;
the maintainer's independent reading remains the external review of the delivery.

## Repair of returned heads 4367c6ae6228 and 2fcea2bb8d77

H2 at 4367c6ae6228: the helper now directly constructs
`ChosenCartesianSquare (pullback.snd p v) (pullback.fst p v) v p`, using
`pullback.condition.symm`, `pullbackSymmetry p v`, and its projection lemmas.
Every occurrence of `setBaseChangeArrow` receives that helper directly.
Only the owning definition nodes `sbc-def-base-change-map` and
`def-weil-pbc-cartesian-square` are added to `stmt_deps`. No theorem-module
declaration is used in the statement or helper data.

H2/H7 at 2fcea2bb8d77: restored `proof_deps` exactly, in order, from current
sheaf-dag. The previous review's instruction to move the sectionwise theorem
into `proof_deps` was retracted by this return. The sectionwise import remains
non-public, and the Lean module, binding, two added landed statement dependencies,
and original DAG proof steps are retained. The lean record's explanatory note
now reflects this correction. The natural-language statement is unchanged and
no `statement_change` is needed or added.

Compared the retained returned packet with current main: the only substantive
node differences are now `lean` and the two added definition `stmt_deps`.
Confirmed every other node field, including `proof` and `proof_deps`, equals
current main. Confirmed the Lean module remains byte-for-byte the reviewed
module. The prescribed delivery wrapper rebases the packet on current server main.

A fresh rereading checked the correction specifically: the helper still supplies
the canonical transposed pullback with both projection equations; the signature
contains no `exchangeTranspose`, `setUnderivedExchangeSectionwise`, or theorem
choice. Its source and target remain v⁻¹p_*A and p₁,*w⁻¹A, and the naturality
equation retains its reviewed orientation. No mathematical or universe change
was made in this metadata repair.
