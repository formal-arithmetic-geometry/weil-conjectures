## Worker report

This is the stage-2 repair of `lem-trf-oriented-closed-base-localization` for NJ. The module
`Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization` states
`CategoryTheory.oriented_closed_base_localization`, with `sorry` as its entire proof. It
also supplies three explicit packaging/construction declarations belonging to this same
node: `ClosedBaseLocalization.ComplementData`, `ModuleAssertion`, and
`representedOpenComplement`. They have real structure fields or defining expressions;
there is no data `sorry`, choice of an unspecified map, or new independent notion.

The returned immutable head `a298407bcb81` had only a stage-1 split-field change and no Lean
module or Lean record for this item. The retained sandbox contained only the launcher
markers. I compared its node and report with the current shared node. The current node
retains the same mathematical statement and the maintainer's corrected step 2, including
explicit descent of addition and the constant scalar action. This delivery starts from
that current node, retains its proof and all other stage-1 fields, and supplies the missing
stage-2 module, Lean record and worker report. The original return was the
`--apply-fixes` rejection of a repository-relative report filename as a stage-2 fix packet.
The repair is now an ordinary complete stage-2 sandbox packet consumed by `deliver2.py`;
no such malformed fixes directory is passed. It is not an unchanged re-push of that head.

### Hypothesis and clause correspondence

The theorem has three conjuncts, corresponding to the three paragraphs of the node.

| Node text | Lean rendering |
| --- | --- |
| An arbitrary Grothendieck topos T, in the stated size convention | First conjunct: `E : Type u`, `[Category.{v} E]`, `IsGrothendieckTopos.{w} E`. This is the recorded small-site-presentation predicate, not an arbitrary category assumed to have a few limits. |
| A subterminal U, equivalently a monomorphism to the terminal object | `U : E`, `IsSubterminal U`. The terminal structure and products follow from being a topos; the theorem supplies `products : HasBinaryProducts E`, rather than adding a hypothesis. |
| The full subcategory of H such that U times H projects isomorphically to U | The existing `(closedComplementObjects U).FullSubcategory`, whose predicate is `IsIso (prod.fst : U ⨯ H ⟶ U)`. No second definition of this predicate is supplied. |
| This full subcategory is a Grothendieck topos Z | `ComplementData.closedTopos`. |
| The geometric embedding i has inclusion direct image | `ComplementData.i`, `inclusion : i.direct ≅ (closedComplementObjects U).ι`, and `fullyFaithful : i.direct.FullyFaithful`. A natural isomorphism is the categorical identification with the actual inclusion. |
| j is the open slice T/U to T | `ComplementData.openTopos`, `j : GeometricMorphism (Over U) E`, and `openInverse : j.inverse ≅ Over.star U`. Thus j is the slice morphism, up to its unique adjoint comparison. |
| For every Grothendieck topos H, composition with i identifies maps to Z with maps a annihilating U | `factorization` quantifies over arbitrary `H : Type uH`, `[Category.{vH} H]`, `IsGrothendieckTopos.{w} H`, and all `a : GeometricMorphism H E`. A factor `b` exists with `(b.comp i).direct ≅ a.direct` iff `Nonempty (IsInitial (a.inverse.obj U))`. |
| The identification includes every 2-morphism, in the direct-image convention | The second half of `factorization` is `Function.Bijective (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ i.direct)`. These are all natural transformations, not just natural isomorphisms. With essential-image equality, this is exactly equivalence onto the full subcategory. |
| The inverse image of Z along every a is the closed complement of a inverse U | `baseChange` constructs the full category for `a.inverse.obj U`, its inclusion geometric embedding `k`, a geometric morphism `r` to Z, and the direct-image comparison square `(r.comp i).direct ≅ (k.comp a).direct`. For every topos G and every `b : GeometricMorphism G H`, factorization through k is equivalent to factorization of `b.comp a` through i. Right whiskering by k is also bijective on all natural transformations. This expresses the inverse-image universal property, including 2-morphisms, rather than only an object-level analogy. |
| Any commutative coefficient ring Lambda, and the specified constant-ring module sheaves | Second conjunct: arbitrary small-site presentations `C D O : Type w`, their topologies `J K L`, and `Λ : Type w`, `[CommRing Λ]` inside `ModuleAssertion`. `ConstantLeftModuleInverseImage.Modules J Λ` is the recorded `ringedSiteModules` over `(constantSheaf J RingCat).obj (RingCat.of Λ)`, and similarly for K and L. |
| On these presentations, i and j denote the same closed and open embeddings | `ModuleAssertion` requires `i.direct.FullyFaithful` and `i.direct.essImage H ↔ closedComplementObjects U H`; for j it requires an equivalence `e : Sheaf L (Type w) ≌ Over U` with `j.inverse ⋙ e.functor ≅ Over.star U`. These express the named embeddings, not extra geometric conditions. The first conjunct guarantees the closed and open topoi; their small-site presentations are supplied by `IsGrothendieckTopos`. |
| The inverse images and module adjunction are induced by the geometric morphisms | `di` and `dj` are `ConstantLeftModuleInverseImageLift` for exactly `i.inverse`, `i.direct`, `i.adj`, `i.leftExact` and the corresponding j fields. This existing interface normalizes the scalar action, underlying-set comparisons and actual unit. It excludes arbitrary unrelated functors. The assertion holds for every such normalized lift; the existing inverse-image theorem supplies the lifts. |
| Module direct image i star is exact | `PreservesFiniteLimits di.moduleDirect ∧ PreservesFiniteColimits di.moduleDirect`, the exactness condition in these abelian categories. No exactness hypothesis on direct image has been added. |
| Module direct image is fully faithful | `di.moduleDirect.Full ∧ di.moduleDirect.Faithful`. |
| Its actual adjunction counit is invertible | For every `N : Modules K Λ`, `IsIso (di.moduleAdj.counit.app N)`. |
| Its essential image is exactly modules killed by j inverse image | For every `M : Modules J Λ`, `di.moduleDirect.essImage M ↔ IsZero (dj.moduleFunctor.obj M)`. |
| Equivalently, for every supported M the actual unit is invertible | The final clause is `IsZero (dj.moduleFunctor.obj M) → IsIso (di.moduleAdj.unit.app M)`. This names the adjunction unit itself. |
| Every scheme closed immersion k : F to S, on the recorded small etale topoi | Third conjunct: arbitrary `F S : Scheme.{t}`, `k : F ⟶ S`, `[IsClosedImmersion k]`; the sites are `F.smallEtaleTopology` and `S.smallEtaleTopology`, with set values `Type (t + 1)`. |
| The subterminal represented by the complementary open S minus F | `representedOpenComplement k` is `presheafToSheaf` applied to `uliftYoneda` at `Scheme.Etale.mk k.openComplement.ι`; this is the actual complementary open of k, not a freely chosen open or sheaf. The conclusion includes `IsSubterminal` for this sheaf. The small etale site is subcanonical. |
| The scheme-induced geometric morphism identifies F Et with that closed complement | The conclusion gives an equivalence `e` from the F set-sheaf category to `(closedComplementObjects (representedOpenComplement k)).FullSubcategory`, and `e.functor ⋙ inclusion ≅ AlgebraicGeometry.etaleSetDirectImage k`. The latter is the recorded scheme-induced direct image, with its existing actual adjunction. Thus this is an equivalence over the ambient topos, not just an unrelated equivalence of categories. |

All category and object universes are explicitly bound. The arbitrary-topos part retains
separate object and morphism universes for E, H and G; it imposes no equality between them.
The module part uses the recorded small-site/coefficient-universe convention of the
constant-module lift: w is the universe containing both the sites and the coefficients,
and can be taken as large as required. The scheme clause separately retains the actual
small etale site's object universe t+1, morphism universe t, and set universe t+1. No scheme
site is forced to be a `SmallCategory` in the smaller universe.

### Dependency declarations read and used

- `def-weil-size-convention`: its recorded convention has no mathematical declaration;
  it is rendered by the explicit universes described above.
- `def-weil-pbc-ringed-topos-morphism`: `Sheaf.CategoryTheory.RingedToposMorphism`,
  `CategoryTheory.RingedToposMorphism`, read in full. The node invokes its direct-image
  natural-transformation convention, not a ring structure on arbitrary T. The existing
  unringed `CategoryTheory.GeometricMorphism` from
  `Sheaf.CategoryTheory.Sites.GeometricMorphism` implements exactly the adjunction and
  left-exactness part and its composition; its 2-morphisms are these same natural
  transformations. No site-induced restriction is imposed on the generic morphisms.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, the transparent abbreviation of Mathlib's
  `SheafOfModules`, read with its docstring. It is used through the existing
  `ConstantLeftModuleInverseImage.Modules`, not copied.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, read with its full class signature and docstring.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology` and `Scheme.Etale`, read with their signatures and covering
  description. The scheme clause uses these exact sites.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, read with its sheafification definition and docstring;
  used through `ConstantLeftModuleInverseImage.Modules`.
- `def-weil-pbc-topos`: `Sheaf.CategoryTheory.Sites.GrothendieckTopos`,
  `CategoryTheory.IsGrothendieckTopos`, read in full and used for all topoi.
- `def-trf-geometric-morphism`: `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism` and `.comp`, read in full.
- `lem-trf-topos-complement-factorization`:
  `Sheaf.CategoryTheory.Sites.ToposComplementFactorization`,
  `CategoryTheory.closedComplementObjects` and `topos_complement_factorization`;
  both signatures and the complete proof docstring were read. Its existing full
  subcategory is used in the statement and its theorem is step 1 of the proof plan.
- `lem-pe-constant-left-module-inverse-image`:
  `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
  `ConstantLeftModuleInverseImage.Modules`, `ConstantLeftModuleInverseImageLift`,
  and `constant_left_module_inverse_image`. I read the entire normalized-lift structure,
  including its addition/scalar/unit equations, and the existence theorem's signature
  and proof docstring. These are the actual module functors in the statement.
- `lem-trf-etale-closed-complement-sets`:
  `Sheaf.TraceFormula.EtaleClosedComplementSets`, `AlgebraicGeometry.etaleSetDirectImage`,
  `etaleSetInverseImage`, `etaleSetAdjunction`, `etaleClosedComplementSets`; I read all
  four definitions/statements and their docstrings. The final comparison uses this exact
  direct image. The theorem is step 3 of the proof plan.

The five already recorded project nodes used in the signature have been added to
`stmt_deps` under the rule allowing landed nodes. They already exist, and no dependency
record is changed. The original `proof`, `proof_deps`, statement and other fields remain
those of the current main node. The three proof-dependency modules are all imported.
There is no import of `lem-trf-topos-complement-module-stalks`, which is downstream of this
item and would close the previously reported cycle.

### Source and edge-case checks

I read the local Stacks source: `sites.tex`, `lemma-closed-subtopos` (08LY),
`definition-closed-subtopos` (08LZ), `definition-immersion-topoi` (08M0), and
`lemma-closed-immersion` (08M1); `sites-modules.tex`, `lemma-i-star-equivalence` (08M3);
and `etale-cohomology.tex`, `proposition-closed-immersion-pushforward` (04CA(1)).
The module clause is the constant-ring specialization together with the explicitly
supported essential-image description, as explained in the retained DAG proof.
The module docstring contains the entire three-step proof plan, including descent of
module operations and the supported-cokernel argument; stage 2 proves none of it.

- If U is initial, the closed full subcategory is the whole topos and the open topos is
  degenerate. The module statement reduces to the identity embedding on all modules.
- If U is terminal, the closed full subcategory consists of terminal objects. Its module
  category is zero, and `IsZero (j^* M)` is exactly the zero-module condition. No
  nondegeneracy or nontrivial coefficient-ring assumption excludes this case.
- Lambda may be the zero ring. Every module is zero and all clauses still have their
  expected interpretation. No characteristic or invertibility condition is present.
- For F empty and F=S, the represented complementary opens are respectively S and empty;
  the equivalence specializes to the zero or identity closed embedding, as required.
- S itself may be empty. The sites and sheaf categories remain the actual small etale
  ones. There is no reducedness, quasi-compactness, noetherianity, or separatedness binder.
- Arbitrary geometric morphisms and all natural transformations are retained, including
  identity base changes, morphisms between degenerate topoi, and noninvertible 2-morphisms.

There is no statement correction and no `STATEMENT-DISPUTED` finding.

### Searches for an existing declaration

The following searches were run with `msearch.py NJ lem-trf-oriented-closed-base-localization`:

- LeanFinder: `Closed complementary subtopos of a Grothendieck topos has exact fully
  faithful direct image on constant ring module sheaves with essential image modules
  vanishing on the open complement`. Eight hits: condensed/light condensed locally
  constant functors, their full-faithfulness/adjunctions and AB4/AB4-star instances.
  These do not state the closed-complement theorem.
- Loogle: `CategoryTheory.GeometricMorphism, CategoryTheory.Sheaf` gave no hit and reported
  that the project-only `GeometricMorphism` identifier is unknown to Mathlib search. I
  reran using the Mathlib query `CategoryTheory.Sheaf, CategoryTheory.Adjunction`:
  twelve hits for sheafification adjunctions, localization, sheaf-composition comparisons,
  and Grothendieck-topology adjunction identities. None is this statement.
- Mathlib grep: `closed.?[Ss]ubtopos|closedComplement|closed_complement`, subdirectory
  `CategoryTheory`: zero hits.
- LeanSearch: `Closed complementary subtopos supported sheaves of modules exact direct
  image`: eight hits for topological linear-map closed complements, structure-sheaf scheme
  module pushforward, a continuous module-pushforward right adjoint, and closed sieves.
  None concerns general closed subtopoi with this universal property and module support.

I also used `rg -n` over upstream `WeilConjectures` and current `lean/Sheaf` for
`closed.?[Ss]ubtopos|closedComplement|closed_complement` and the exact node id; and checked
`oriented_closed_base_localization|ClosedBaseLocalization` in Mathlib, upstream and the
project name index. There is no exact declaration. Upstream matches concerned scheme
open/closed decompositions; the project match `closedComplementObjects` and the theorem
`topos_complement_factorization` are reused. `OrientedClosedBaseExtension` consumes this
node in its proof plan but does not state the present general result.

### Validation

Compiled the delivered module through the prescribed `scompile.py` wrapper, first as a
sandbox module and then at its eventual library module path. Both passes were clean:
no errors and no warnings. A first trial exposed a line-break parsing issue before
`.FullSubcategory`; it was repaired and the full compile was rerun successfully.
The Lean source has no line longer than 100 characters, has `autoImplicit false`, and
contains exactly one postponed theorem, whose entire proof is `sorry`.

## Second reading by NJ

Independent maintainer second reading of immutable delivery
`db6409f65e2891808d66c773a6dd93565183f3f4`, completed 2026-10-18. This reading was
performed by the external second reader, not by the author or an NJ worker. The original
section contained only a disclaimer; this complete report replacement repairs H11.

I read the item node, all eleven statement-dependency records, the delivered module and
its docstrings, and the exact dependency declarations in the read-only group clone and
pinned Mathlib. I checked the three source paragraphs against Stacks `sites.tex`
08LY/08LZ/08M0/08M1 and 00YV, `sites-modules.tex` 08M3, and
`etale-cohomology.tex` 04CA(1). The worker's correspondence table above is correct; the
following is my independent clause audit.

- Arbitrary Grothendieck topos and subterminal: the first conjunct binds `E`, its category,
  `IsGrothendieckTopos.{w} E`, `U`, and `IsSubterminal U`. Binary products are supplied in
  the conclusion, rather than imposed as an additional hypothesis.
- The closed category is the existing `closedComplementObjects U` full subcategory,
  defined by invertibility of the actual first product projection. `closedTopos`, `i`,
  `inclusion`, and `fullyFaithful` give exactly the claimed topos and embedding. The open
  morphism is tied to the slice by `openInverse : j.inverse ≅ Over.star U`.
- `factorization` states both essential surjectivity onto morphisms annihilating U and
  bijectivity of whiskering on all direct-image natural transformations. This includes
  noninvertible 2-morphisms and gives the specified categorical universal property.
- `baseChange` uses the full subcategory for `a.inverse.obj U`, supplies its inclusion,
  comparison square, and the factorization criterion for every test topos G, together
  with bijectivity on transformations. With the closed embeddings this is the inverse
  image universal property; it is stronger data packaging of the same property, not a
  different base-change map.
- `ModuleAssertion` has the right closed-essential-image and open-slice hypotheses on
  the presentations. They identify i and j, rather than assuming the desired module
  conclusion. For each commutative ring it quantifies over normalized lifts of the actual
  two geometric adjunctions. These are nonvacuous: the recorded
  `constant_left_module_inverse_image` supplies them. Its `Modules` abbreviation is the
  recorded `ringedSiteModules` of the sheafified constant ring. The lift's underlying-set,
  addition, scalar, direct-image, and unit equations exclude unrelated functors.
- The module conclusions contain finite-limit and finite-colimit preservation of the
  direct image (exactness in these abelian categories), Full and Faithful, invertibility
  of every actual counit component, the exact supported essential image, and
  invertibility of the actual unit for every supported module. None is only asserted for
  chosen representatives. Preservation of finite limits and colimits also determines
  the additive exact functor structure.
- The scheme clause quantifies over every closed immersion without finiteness or
  nonemptiness assumptions. `representedOpenComplement` constructs the sheafified
  lifted representable of the actual `k.openComplement.ι`. Subcanonicality identifies it
  with the represented subterminal. The equivalence has a natural isomorphism over the
  ambient category to the exact scheme-induced `etaleSetDirectImage k`, so it expresses
  the claimed geometric identification, not an unrelated equivalence.

The source proof is consistent: 08LY constructs the closed full subcategory, and 00YV
transports algebraic operations. The module proof explicitly descends addition, zero and
constant scalars by full faithfulness, then uses supported ambient cokernels and exact
inverse image to prove exactness. I did not silently apply 08M3 for arbitrary structural
ring maps: the constant-coefficient normalized construction and descent argument are
essential here. The scheme argument uses the set-valued part of 04CA, not its abelian
part as a substitute. All three steps are present in the theorem docstring.

Universes are explicitly bound with `autoImplicit false`. The topos parameters retain
independent object and morphism levels. The same w bounds the presenting sites and
coefficient sets exactly as in `IsGrothendieckTopos` and the recorded constant-module
interface. This does not force a small-etale site into its morphism universe: the scheme
clause separately has Scheme.{t}, site objects in t+1, morphisms in t, and values in t+1.
No extra size equality, noetherianity, quasi-compactness, reducedness, characteristic,
invertibility or nonzero-ring hypothesis was introduced.

Edge cases checked: U initial (whole closed complement), U terminal (degenerate closed
topos and zero module category), zero coefficient ring, identity base change, degenerate
test topoi, noninvertible natural transformations, F empty, F=S, and S empty. Each remains
within the quantifiers and gives the expected specialization.

Independent `rg` searches in Mathlib, upstream `WeilConjectures`, and project
`lean/Sheaf` for subtopos/subtopoi, closed complements and supported module sheaves,
plus exact declaration names, found no existing theorem with the whole statement.
The existing `closedComplementObjects`, `topos_complement_factorization`, normalized
module lift and etale set direct image are reused. Scheme module pushforward and
open/closed derived-module results are different specializations. The worker report
also records LeanFinder, Loogle, LeanSearch and grep searches. There is no duplicate
notion, hollow definition, arbitrary chosen map or missing helper/prerequisite.

The module has source/blueprint docstrings on all four declarations, exactly one theorem
with `sorry` as its entire proof, no data sorry, and no over-100-character line.
`lean.statement` is byte-for-byte the theorem signature before `:= by`. All eleven
statement dependencies resolve to the recorded notions; no dependency module, new node,
or statement correction is needed. No citer audit is triggered.

The current route-pivot dropped-node list has no intersection with the item's statement
or proof dependencies. There is no route-pivot repair note for this item. The item path
is absent at `7f4ff2255f^`, so there is no pre-pivot version there to compare. The proof is
ordinary topos/module theory throughout, with no dropped enhancement or pro-etale
substitute.

Reproduced compiler command:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py NJ \
  lem-trf-oriented-closed-base-localization \
  snapshot/lean/Sheaf/CategoryTheory/Sites/OrientedClosedBaseLocalization.lean
```

Exit code 0. Sandbox probe `Sheaf/Stage2/Sandbox0.lean`: 6.0 seconds; library probe
`Sheaf/CategoryTheory/Sites/OrientedClosedBaseLocalization.lean`: 10.2 seconds.
Both were clean, with no errors or warnings. The installed wrapper currently delegates
to the server side-overlay compiler; it was used as prescribed, without direct SSH,
global/lake build, or edits to a clone/live Lean source. The delivered Lean is unchanged.

Finding and repair: H11, the delivered second-reading section was a disclaimer, not a
reading. This section now supplies the completed independent audit. No mathematical
finding remains. Full replacement report is supplied as the merge tool's accepted
`lem-trf-oriented-closed-base-localization.report.md` basename.
