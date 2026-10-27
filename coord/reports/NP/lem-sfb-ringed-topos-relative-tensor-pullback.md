## Worker report

The module `Sheaf.Algebra.Homology.RelativeTensorPullback` states
`SheafOfModules.RelativeTensorPullback.relativeTensorPullback`, with one postponed proof.
Source read: `literature/stacks-project/sites-cohomology.tex`, lines 3727–3760,
Tag 08I6, `lemma-variant-derived-pullback`, including its ordinary balanced-tensor proof.
The node's four expanded proof steps are reproduced as a complete proof plan in the
main declaration docstring. The mathematical statement is unchanged.

Hypotheses and clauses, matched individually:

- Chosen size convention: explicit `uC vC uD vD r w`; sites have independent object
  and Hom universes and `EssentiallySmall.{r}` instances. No equality of site universes
  is imposed. All three derived localizations have the chosen morphism bound `w`.
- Arbitrary ringed-topos morphism: `L`, `V`, `adj : L ⊣ V`, and
  `[PreservesFiniteLimits L]` present the geometric morphism. `A RI B` are
  `Sheaf _ CommRingCat.{r}`; `I : AlgebraicInverseImage L B RI` identifies RI with
  inverse-image B and specifies its induced module functor, including ring/module
  operations on generalized elements; `c : RI ⟶ A` is the structural ring map.
  This is the unpacked geometric-morphism presentation already used by the recorded
  ringed derived-pullback theorem, without requiring a functor between presented sites.
  The `RingedToposMorphism` dependency is imported; its module-direct-image bundle is
  not an additional input because only the geometric morphism and inverse image enter 08I6.
- Module categories: `Mod J A`, `Mod J RI`, `Mod K B` are existing transparent
  abbreviations of `CategoryTheory.ringedSiteModules`, hence Mathlib `SheafOfModules`.
  `DerivedCategory` is the ordinary localization at quasi-isomorphisms, with no
  boundedness condition.
- Module pullback is exactly `uStar`, with `hobj` identifying its objects with
  `changeOfRings c (I.modules.obj M)` and `hmap` fixing the induced maps, including
  the equality transports. The additive instances express properties of these
  specified induced functors, not arbitrary additional functors.
- Total left-derived pullback: `LF`, `epsilon`, `hLF : LF.IsLeftDerivedFunctor ...`
  specify its universal derived comparison. The existing independent-universe
  ringed-pullback theorem supplies these data; they are not new existence assumptions.
- K-flat and flat terms: `flatRepresentatives` is only a named full-subcategory
  predicate combining the recorded `IsKFlatIndependentCoefficients` with
  `∀ n, IsFlatOnSite ... (P.X n)`. The former quantifies over every acyclic test
  complex; it is not flatness of cohomology or termwise flatness alone.
- Ordinary total tensor is `total`, an abbreviation for the existing
  `curriedTensor.map₂HomologicalComplex`, with direct-sum totalization and the
  Koszul sign. `qRep` and `tensorRep` only abbreviate localization functor composites.
- Derived tensor: `TA`, `TC`, with natural representative comparisons `rA`, `rC`,
  are presentations of the existing resolving-class derived tensor. The recorded
  site-derived-tensor-descent theorem supplies them. Universal quantification over
  compatible presentations permits the library's existing choices without defining
  a second derived tensor.
- Relative tensor retaining A-action: the conclusion supplies an actual
  complex-valued bifunctor `T`. The natural isomorphism `under` identifies its scalar
  restriction with the existing RI-total tensor of Res(P) and H. The first conjunct
  specifies the A-action, transported by `under.inv`, as multiplication on P on every
  local pure tensor in every summand. It imposes no K-flatness on Res(P).
- Ordinary canonical comparison: `b` is a natural chain isomorphism from
  total(P tensor_A uStar(Q)) to T(P,I(Q)). The second conjunct is the forward formula
  e tensor (a tensor h) maps to ae tensor h; the third conjunct is the inverse
  e tensor h maps to e tensor (1 tensor h). `totalPure` uses the existing
  sheafification-unit pure tensor followed by the actual total-complex summand
  inclusion. `ringedComparisonScalarSection` uses the canonical change-of-rings
  sheafification unit from the cited definition node. Neither formula treats every sheaf section as a sectionwise
  finite sum of pure tensors.
- Exact termwise inverse image: the conclusion supplies `IDer` and a natural
  `rI : Q ⋙ IDer ≅ I.modules.mapHomologicalComplex ... ⋙ Q` on all complexes.
  This identifies inverse image as the exact termwise functor on the unbounded
  derived category, not its left-derived tensor pullback.
- Relative derived tensor in D(A): `Urel` is a bifunctor with target
  `DerivedCategory (Mod J A)`, and `rrel` is a natural comparison with T on the
  product of the A and B flat-term K-flat resolving classes. Thus the action is
  retained in D(A), not supplied only after forgetting to RI.
- Underlying RI-object: `Nonempty (Urel ⋙ (res c).mapDerivedCategory ≅
  (((res c).mapDerivedCategory).prod IDer) ⋙ TC)` gives exactly the stated
  underlying derived tensor of scalar-restricted E with inverse-image G.
- The desired canonical natural isomorphism is `alpha : ((𝟭 _).prod LF) ⋙ TA ≅ Urel`.
  Its final equation for every pair of flat-term K-flat representatives identifies
  it with the chain map `b` via the specified tensor comparison `rA`, the item-owned
  `pullbackComplexComparison`, and `rrel`. The existential `hQ` records that
  pullback Q remains in the required resolving class. This states the derived
  isomorphism itself, not merely isomorphisms of cohomology objects.
- No flatness of `c`, boundedness, coherence or finite Tor dimension hypothesis occurs.
  Objects E and G range over all derived objects through the bifunctor domains.

No new tensor data are defined by a postponed existence theorem. The six helper
names are transparent compositions or the exact recorded resolving-class predicate;
`pullbackComplexComparison` is the explicit Mathlib composite required by the returned review.
The theorem existentially asserts the relative construction and its characterizing
maps and equations; there is no `Classical.choose` of an unconstrained object.
The returned review required one dependency addition and one item-owned helper; both are
now recorded below. No new independent notion is introduced.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`:
  geometric adjunction, finite limits, structural map; unpacked as described above.
- `Sheaf.CategoryTheory.AlgebraicInverseImage`, `SheafOfModules.AlgebraicInverseImage`:
  exact equal-coefficient/module-universe presentation, public alongside the recorded
  `AlgebraicInverseImageOfUniverses` presentation. Its site universes are independent.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `cochainModulesMonoidal`, `cochainModulesPreadditive`, and tensor colimit instances.
  The imported existing scalar-extension helpers are
  `SheafOfModules.ringedComparisonPure` and
  `SheafOfModules.ringedComparisonScalarSection` in
  `Sheaf.Paper.RingedTopoiTensorComparisonData`, owned by
  `def-weil-pbc-canonical-ringed-tensor-comparison`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`; `WeilConjectures.SemilinearSections.res` is the
  existing transparent spelling, whose exactness instances support `mapDerivedCategory`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
  `SheafOfModules.changeOfRings` and `changeOfRingsHom`.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`,
  `SheafOfModules.ringedTopoiDerivedPullbackIndependent` and its full resolution
  comparison interface. It already imports the existing `Mod` and `res` abbreviations.
- `Sheaf.Algebra.Homology.RelativeTensorPullback`,
  `SheafOfModules.RelativeTensorPullback.pullbackComplexComparison`, the item-owned
  explicit composite transporting epsilon from Qh through the quotient comparison
  isomorphisms and homotopy-category factor.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
  `site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`: same-ring resolving-class tensor.
- All other stated proof dependencies are imported as plain proof imports:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
  `SheafOfModules.isKFlat_ringedToposPullback`,
  `SheafOfModules.TotalTensorSigns.totalTensorHomotopyConeSigns`,
  `CochainComplex.mapBifunctor`, and
  `PresheafOfModules.existsUnique_bilinear_sheafification_extension`.
  Their source signatures and docstrings were read. The last theorem's larger-universe
  signature can be applied after transport to a small model if needed in the proof;
  its size convention has not been imposed on the item.

`stmt_deps` gains the already-landed algebraic inverse image, K-flatness, flatness,
scalar restriction, derived pullback, tensor descent, and canonical ringed tensor
comparison nodes actually used to type this interface. Their recorded declarations are imported; no node statement changes.

Edge cases checked mathematically: f = identity and c = identity give ordinary tensor
associativity; a nonflat quotient Z → Z/2 is allowed and the proof uses K-flat I(Q),
never K-flatness of scalar-restricted P; zero E, zero G, and the zero coefficient ring
are allowed. Empty sites and unbounded complexes are not excluded. The explicit
site-object and site-Hom universe variables may differ. The sign is inherited from
Mathlib's integer cochain totalization. Both formulas have the correct order of the
scalar action, and the A-action occurs in the target category itself.

Searches actually run (2026-10-24; wrapper log `searches.jsonl`):

- leanfinder: "Derived tensor of an A module with derived pullback is relative tensor
  over the inverse image ring for ringed topoi". Eight hits, ordinary module pullback
  and tensor only, including `SheafOfModules.pullbackIso`; no 08I6 derived comparison.
- loogle: `"SheafOfModules", "tensor"`. Ten hits on the presheaf monoidal tensor,
  no relative unbounded comparison retaining A-action.
- msearch grep: `relativeTensor|tensor.*[Rr]estrict|[Rr]estrict.*tensor` in
  `Algebra/Category/ModuleCat`. Two hits: ordinary ring scalar extension and descent.
- leansearch: "Relative tensor product of sheaves with retained module action along a
  ring map". Eight hits, ordinary tensor, scalar restriction and ring tensor maps;
  no matching derived ringed-topos statement.
- Local rg of `lean/WeilConjectures` and `lean/Sheaf` for relative tensor, inverse-image
  tensor, and derived pullback found the cited tensor/pullback interfaces and scheme-only
  relative tensor lemmas. Those scheme lemmas do not state arbitrary ringed-topos 08I6.
  Search by item id in `lean/WeilConjectures` and in `dag/lean_names_upstream.json`
  returned no attachment. Searches for the new full declaration name found no collision.

No STATEMENT-DISPUTED finding and no source correction.


## Returned-delivery repairs

The immutable review at head `a771f5e41766` accepted the mathematics and requested two
interface repairs. For R1 (H2/H4), `totalPure` and the forward/inverse scalar clauses
now use `SheafOfModules.ringedComparisonPure` and
`SheafOfModules.ringedComparisonScalarSection`, the canonical helpers owned by
`def-weil-pbc-canonical-ringed-tensor-comparison`. That definition node was added to
`stmt_deps`; the old scalar-extension-coherence import and names are absent.

For R2 (H2), the module now defines
`SheafOfModules.RelativeTensorPullback.pullbackComplexComparison` with real data. Its
body is exactly the Mathlib composite
`LF.map (quotientCompQhIso.inv)`, `epsilon`, `Qh.map mapHomotopyCategoryFactors`, and
`quotientCompQhIso.hom`, with explicit independent abelian-category and derived-category
universes. The final representative equation uses this item-owned helper, so it no
longer depends on the plain definition attached to the uncited theorem node.
The node's `stmt_deps` and `lean.declarations` record both repairs. The theorem statement,
source, proof, and proof dependencies are unchanged.

## Second reading by NP

Author self-check under the dispatcher instruction not to start other agents;
independent review is left to the maintainer's delivery review. This is not represented
as an independent reading. With the node, source 08I6 and final module open, I checked
both forward and inverse formulas, the scalar action in D(A), the RI-underlying tensor,
and the final canonical representative equation against every clause above. The first
compile exposed only missing universe annotations and scalar-action type annotations;
these were repaired without restricting the universes. A later compile required explicit
source and target objects of `TA.map` to fix the intended representative square.
All helper definitions have real data and the sole theorem proof is `sorry`.

## Validation

The validation below first records the original submission. After the returned-review
repairs, the prescribed server compiler passed again for both sandbox and final library
module names, with no messages other than timing (54.5 s and 141.0 s including server
slot acquisition). One initial parser error from placing a universe command between a
docstring and its declaration was fixed before this passing compile.


`scompile.py NP lem-sfb-ringed-topos-relative-tensor-pullback` compiled the module
both under the sandbox module name and its final library module name, with no errors
or warnings (35.9 s and 12.6 s for the passing run). Delivery dry-run and final delivery
are recorded below after running the prescribed wrappers.

The prescribed `deliver2.py ... --no-push` passed: `OK (dry run): commit
029b7d9cab4 passes the preflight and compiles; nothing pushed`. It checked exactly
one module, the item's node record, and this report. The final submission uses the
same prescribed delivery wrapper.

Repair dry run: `deliver2.py NP lem-sfb-ringed-topos-relative-tensor-pullback --no-push`
reported `OK (dry run): commit eee55633b78 passes the preflight and compiles; nothing
pushed`. The repaired module, updated dependency record and this report were staged.
